"""Conservative exact evaluation of closed polynomial interval-integral probes.

This module is a heuristic witness finder, never a proof authority. It accepts
only a deliberately small Lean surface grammar, evaluates it over exact SymPy
rationals, and returns evidence only when every hypothesis and residual symbol
is accounted for. The ordinary Lean full-negation replay remains the sole
promotion path.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from fractions import Fraction

from .generators import (
    _binder_names_and_type,
    _first_forall_chunk,
    _split_top_level_arrow,
    _unwrap_transparent_parens,
    function_binder_domain,
)


_RELATIONS = {"=", "≠", "<", "≤", ">", "≥"}
_SUPPORTED_ASCRIBED_TYPES = {"ℝ", "Real"}
_SIMPLE_TOKENS = set("()+-*/^,:")
_MAX_SOURCE_CHARS = 8_000
_MAX_TOKENS = 1_024
_MAX_POLYNOMIAL_EXPONENT = 16
_MAX_POLYNOMIAL_TERMS = 4_096
_MAX_ALGEBRA_OPERATIONS = 200_000


Monomial = tuple[tuple[str, int], ...]


class _Polynomial:
    """Small exact multivariate polynomial with a shared operation budget."""

    def __init__(
        self,
        terms: dict[Monomial, Fraction],
        budget: list[int],
    ) -> None:
        normalized = {
            tuple(monomial): Fraction(coefficient)
            for monomial, coefficient in terms.items()
            if coefficient
        }
        if len(normalized) > _MAX_POLYNOMIAL_TERMS:
            raise ValueError("polynomial term count exceeds the safe bound")
        self.terms = normalized
        self._budget = budget

    def _charge(self, amount: int) -> None:
        amount = max(1, int(amount))
        if amount > self._budget[0]:
            raise ValueError("exact algebra operation budget exhausted")
        self._budget[0] -= amount

    @classmethod
    def constant(cls, value: int | Fraction, budget: list[int]) -> "_Polynomial":
        coefficient = Fraction(value)
        return cls({(): coefficient} if coefficient else {}, budget)

    @classmethod
    def variable(cls, name: str, budget: list[int]) -> "_Polynomial":
        return cls({((str(name), 1),): Fraction(1)}, budget)

    @property
    def free_symbols(self) -> frozenset[str]:
        return frozenset(
            name for monomial in self.terms for name, exponent in monomial if exponent
        )

    @property
    def constant_value(self) -> Fraction:
        if self.free_symbols:
            raise ValueError("expected a constant polynomial")
        return self.terms.get((), Fraction(0))

    def __neg__(self) -> "_Polynomial":
        self._charge(len(self.terms))
        return _Polynomial(
            {monomial: -coefficient for monomial, coefficient in self.terms.items()},
            self._budget,
        )

    def __add__(self, other: "_Polynomial") -> "_Polynomial":
        self._charge(len(self.terms) + len(other.terms))
        terms = dict(self.terms)
        for monomial, coefficient in other.terms.items():
            terms[monomial] = terms.get(monomial, Fraction(0)) + coefficient
            if not terms[monomial]:
                terms.pop(monomial)
        return _Polynomial(terms, self._budget)

    def __sub__(self, other: "_Polynomial") -> "_Polynomial":
        return self + (-other)

    def __mul__(self, other: "_Polynomial") -> "_Polynomial":
        self._charge(max(1, len(self.terms) * len(other.terms)))
        terms: dict[Monomial, Fraction] = {}
        for left_monomial, left_coefficient in self.terms.items():
            for right_monomial, right_coefficient in other.terms.items():
                powers: dict[str, int] = dict(left_monomial)
                for name, exponent in right_monomial:
                    powers[name] = powers.get(name, 0) + exponent
                    if powers[name] > _MAX_POLYNOMIAL_EXPONENT:
                        raise ValueError("polynomial degree exceeds the safe bound")
                monomial = tuple(sorted(powers.items()))
                terms[monomial] = (
                    terms.get(monomial, Fraction(0))
                    + left_coefficient * right_coefficient
                )
                if not terms[monomial]:
                    terms.pop(monomial)
                if len(terms) > _MAX_POLYNOMIAL_TERMS:
                    raise ValueError("polynomial term count exceeds the safe bound")
        return _Polynomial(terms, self._budget)

    def __truediv__(self, other: "_Polynomial") -> "_Polynomial":
        divisor = other.constant_value
        if not divisor:
            raise ValueError("division by zero in exact probe")
        self._charge(len(self.terms))
        return _Polynomial(
            {
                monomial: coefficient / divisor
                for monomial, coefficient in self.terms.items()
            },
            self._budget,
        )

    def __pow__(self, exponent: int) -> "_Polynomial":
        exponent = int(exponent)
        if exponent < 0 or exponent > _MAX_POLYNOMIAL_EXPONENT:
            raise ValueError("polynomial exponent is outside the safe bound")
        result = _Polynomial.constant(1, self._budget)
        factor = self
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = result * factor
            remaining >>= 1
            if remaining:
                factor = factor * factor
        return result

    def integrate(
        self,
        variable: str,
        lower: Fraction,
        upper: Fraction,
    ) -> "_Polynomial":
        self._charge(len(self.terms))
        terms: dict[Monomial, Fraction] = {}
        for monomial, coefficient in self.terms.items():
            powers = dict(monomial)
            exponent = powers.pop(variable, 0)
            integrated_exponent = exponent + 1
            interval_factor = (
                upper**integrated_exponent - lower**integrated_exponent
            ) / integrated_exponent
            reduced = tuple(sorted(powers.items()))
            terms[reduced] = (
                terms.get(reduced, Fraction(0)) + coefficient * interval_factor
            )
            if not terms[reduced]:
                terms.pop(reduced)
        return _Polynomial(terms, self._budget)

    def antiderivative(self, variable: str) -> "_Polynomial":
        """Return the exact polynomial antiderivative with zero constant."""

        self._charge(len(self.terms))
        terms: dict[Monomial, Fraction] = {}
        for monomial, coefficient in self.terms.items():
            powers = dict(monomial)
            exponent = powers.get(variable, 0) + 1
            powers[variable] = exponent
            integrated = tuple(sorted(powers.items()))
            terms[integrated] = (
                terms.get(integrated, Fraction(0)) + coefficient / exponent
            )
        return _Polynomial(terms, self._budget)

    def lean_expression(self) -> str:
        """Render a closed, deterministic real-polynomial expression."""

        if not self.terms:
            return "(0 : ℝ)"
        rendered: list[str] = []
        for monomial, coefficient in sorted(self.terms.items()):
            factors = [_fraction_lean(coefficient)]
            factors.extend(
                name if exponent == 1 else f"({name} ^ {exponent})"
                for name, exponent in monomial
            )
            rendered.append("(" + " * ".join(factors) + ")")
        return "(" + " + ".join(rendered) + ")"

    def antiderivative_proof_term(self, variable: str) -> str:
        """Build a HasDerivAt term for ``self.antiderivative(variable)``."""

        if not self.terms:
            return f"(hasDerivAt_const {variable} (0 : ℝ))"
        proofs: list[str] = []
        for monomial, coefficient in sorted(self.terms.items()):
            powers = dict(monomial)
            original_exponent = powers.pop(variable, 0)
            antiderivative_exponent = original_exponent + 1
            constant_factors = [_fraction_lean(coefficient / antiderivative_exponent)]
            constant_factors.extend(
                name if exponent == 1 else f"({name} ^ {exponent})"
                for name, exponent in sorted(powers.items())
            )
            constant_expression = "(" + " * ".join(constant_factors) + ")"
            proofs.append(
                f"((hasDerivAt_const {variable} {constant_expression}).mul "
                f"((hasDerivAt_id {variable}).pow {antiderivative_exponent}))"
            )
        combined = proofs[0]
        for proof in proofs[1:]:
            combined = f"({combined}.add {proof})"
        return combined


@dataclass(frozen=True)
class ExactIntegralRefutation:
    function_name: str
    relation: str
    lhs: str
    rhs: str
    difference: str
    certification_steps: tuple[str, ...] = ()
    hypothesis_proofs: tuple[str, ...] = ()
    top_level_integral_names: tuple[str, ...] = ()


@dataclass(frozen=True)
class _IntegralEvaluation:
    variable: str
    lower: Fraction
    upper: Fraction
    source_expression: str
    integrand: _Polynomial
    result: _Polynomial
    nested_indices: tuple[int, ...]


def _fraction_lean(value: Fraction) -> str:
    value = Fraction(value)
    if value.denominator == 1:
        return f"({value.numerator} : ℝ)"
    return f"({value.numerator} / {value.denominator} : ℝ)"


def _tokenize(source: str) -> tuple[str, ...]:
    text = str(source or "")
    if len(text) > _MAX_SOURCE_CHARS:
        raise ValueError("expression exceeds exact-evaluation source limit")
    tokens: list[str] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char.isspace():
            index += 1
            continue
        if text.startswith("..", index):
            tokens.append("..")
            index += 2
            continue
        if char in _SIMPLE_TOKENS or char in "∫=≠<≤>≥":
            tokens.append(char)
            index += 1
            continue
        if char.isdigit():
            end = index + 1
            while end < len(text) and text[end].isdigit():
                end += 1
            tokens.append(text[index:end])
            index = end
            continue
        if char.isalpha() or char == "_":
            end = index + 1
            while end < len(text) and (text[end].isalnum() or text[end] in "_'."):
                end += 1
            tokens.append(text[index:end])
            index = end
            continue
        raise ValueError(f"unsupported exact-evaluation character {char!r}")
    if len(tokens) > _MAX_TOKENS:
        raise ValueError("expression exceeds exact-evaluation token limit")
    return tuple(tokens)


def _strip_lean_line_comments(source: str) -> str:
    """Remove Lean ``--`` comments while preserving line boundaries.

    The exact evaluator accepts no string/character literal grammar in which
    ``--`` could be data.  Stripping through the physical line ending is
    therefore both faithful to Lean lexing and safer than tokenizing the two
    hyphens as nested unary negation.
    """

    return re.sub(r"--[^\r\n]*", "", str(source or ""))


def _bounded_natural_power(base: int, exponent: int) -> int:
    """Evaluate a literal Nat power only while it remains a safe exponent."""

    base = int(base)
    exponent = int(exponent)
    if base < 0 or exponent < 0:
        raise ValueError("polynomial exponent must be a natural-number literal")
    if exponent == 0:
        return 1
    if base in {0, 1}:
        return base
    if base > _MAX_POLYNOMIAL_EXPONENT or exponent > _MAX_POLYNOMIAL_EXPONENT:
        raise ValueError("polynomial exponent is outside the safe bound")
    value = base**exponent
    if value > _MAX_POLYNOMIAL_EXPONENT:
        raise ValueError("polynomial exponent is outside the safe bound")
    return value


class _PolynomialIntegralParser:
    def __init__(self, source: str, *, function_name: str) -> None:
        self.tokens = _tokenize(source)
        self.index = 0
        self.function_name = str(function_name)
        self._budget = [_MAX_ALGEBRA_OPERATIONS]
        self.bound_symbols: dict[str, _Polynomial] = {}
        self.integral_evaluations: list[_IntegralEvaluation] = []

    def _peek(self) -> str:
        return self.tokens[self.index] if self.index < len(self.tokens) else ""

    def _pop(self, expected: str | None = None) -> str:
        token = self._peek()
        if not token or (expected is not None and token != expected):
            raise ValueError(
                f"expected {expected or 'token'!r}, found {token or '<eof>'!r}"
            )
        self.index += 1
        return token

    def parse_relation(self) -> tuple[_Polynomial, str, _Polynomial]:
        lhs = self._parse_expression(stop=_RELATIONS)
        relation = self._pop()
        if relation not in _RELATIONS:
            raise ValueError("exact evaluator requires one relation")
        rhs = self._parse_expression(stop=frozenset())
        if self._peek():
            raise ValueError(f"unexpected trailing token {self._peek()!r}")
        return lhs, relation, rhs

    def _parse_expression(
        self,
        *,
        stop: set[str] | frozenset[str],
    ) -> _Polynomial:
        value = self._parse_term(stop=stop)
        while self._peek() not in stop and self._peek() in {"+", "-"}:
            operator = self._pop()
            other = self._parse_term(stop=stop)
            value = value + other if operator == "+" else value - other
        return value

    def _parse_term(
        self,
        *,
        stop: set[str] | frozenset[str],
    ) -> _Polynomial:
        value = self._parse_unary(stop=stop)
        while self._peek() not in stop and self._peek() in {"*", "/"}:
            operator = self._pop()
            other = self._parse_unary(stop=stop)
            value = value * other if operator == "*" else value / other
        return value

    def _parse_unary(
        self,
        *,
        stop: set[str] | frozenset[str],
    ) -> _Polynomial:
        if self._peek() == "-":
            self._pop("-")
            # Lean's prefix minus and power precedence make ``-x ^ 2`` parse
            # as ``-(x ^ 2)``. Recurse through unary syntax, then let the
            # non-minus branch consume the complete right-associated power.
            return -self._parse_unary(stop=stop)
        return self._parse_power(stop=stop)

    def _parse_power(
        self,
        *,
        stop: set[str] | frozenset[str],
    ) -> _Polynomial:
        value = self._parse_atom(stop=stop)
        if self._peek() == "^":
            self._pop("^")
            value = value ** self._parse_exponent_literal()
        return value

    def _parse_exponent_literal(self) -> int:
        """Parse Lean's right-associated chain of Nat numeral exponents."""

        token = self._peek()
        if not token.isdigit():
            raise ValueError(
                "polynomial exponent must be a nonnegative integer literal"
            )
        base = int(self._pop())
        if self._peek() != "^":
            return base
        self._pop("^")
        exponent = self._parse_exponent_literal()
        return _bounded_natural_power(base, exponent)

    def _parse_atom(
        self,
        *,
        stop: set[str] | frozenset[str],
    ) -> _Polynomial:
        token = self._peek()
        if token == "(":
            self._pop("(")
            value = self._parse_expression(stop={":", ")"})
            if self._peek() == ":":
                self._pop(":")
                ascribed_type = self._pop()
                if ascribed_type not in _SUPPORTED_ASCRIBED_TYPES:
                    raise ValueError(
                        f"unsupported exact-evaluation type ascription "
                        f"{ascribed_type!r}"
                    )
            self._pop(")")
            return value
        if token == "∫":
            return self._parse_integral(stop=stop)
        if token.isdigit():
            self._pop()
            return _Polynomial.constant(int(token), self._budget)
        if token == self.function_name:
            self._pop()
            # The only synthesized polynomial witness currently admitted is
            # identity. Requiring a single bound-variable argument prevents
            # accidental interpretation of arbitrary Lean application syntax.
            argument = self._parse_atom(stop=stop)
            if argument not in self.bound_symbols.values():
                raise ValueError("identity witness applied to an unbound term")
            return argument
        if token in self.bound_symbols:
            self._pop()
            return self.bound_symbols[token]
        raise ValueError(f"unsupported exact-evaluation atom {token!r}")

    def _parse_integral(
        self,
        *,
        stop: set[str] | frozenset[str],
    ) -> _Polynomial:
        self._pop("∫")
        parenthesized = self._peek() == "("
        if parenthesized:
            self._pop("(")
        name = self._pop()
        if not (name[:1].isalpha() or name.startswith("_")):
            raise ValueError("invalid integral binder")
        if self._peek() == ":":
            self._pop(":")
            binder_type = self._pop()
            if binder_type not in _SUPPORTED_ASCRIBED_TYPES:
                raise ValueError(
                    f"unsupported exact-evaluation integral binder type {binder_type!r}"
                )
        if parenthesized:
            self._pop(")")
        self._pop("in")
        lower = self._parse_expression(stop={".."})
        self._pop("..")
        upper = self._parse_expression(stop={","})
        self._pop(",")
        lower_value = lower.constant_value
        upper_value = upper.constant_value
        prior = self.bound_symbols.get(name)
        symbol = _Polynomial.variable(name, self._budget)
        self.bound_symbols[name] = symbol
        integrand_start = self.index
        nested_start = len(self.integral_evaluations)
        try:
            integrand = self._parse_expression(stop=stop)
            value = integrand.integrate(name, lower_value, upper_value)
        finally:
            if prior is None:
                self.bound_symbols.pop(name, None)
            else:
                self.bound_symbols[name] = prior
        identity_source = " ".join(
            token
            for token in self.tokens[integrand_start : self.index]
            if token != self.function_name
        ).replace(" .. ", "..")
        self.integral_evaluations.append(
            _IntegralEvaluation(
                variable=name,
                lower=lower_value,
                upper=upper_value,
                source_expression=identity_source,
                integrand=integrand,
                result=value,
                nested_indices=tuple(
                    range(nested_start, len(self.integral_evaluations))
                ),
            )
        )
        return value


def _right_spine_parts(
    statement: str,
) -> tuple[tuple[tuple[str, str], ...], tuple[str, ...], str]:
    binders: list[tuple[str, str]] = []
    hypotheses: list[str] = []
    current = str(statement or "").strip()
    while current:
        unwrapped = _unwrap_transparent_parens(current)
        forall = _first_forall_chunk(unwrapped)
        if forall is not None:
            chunk, body = forall
            names, type_text = _binder_names_and_type(chunk)
            if not names or not type_text:
                raise ValueError("malformed forall binder")
            binders.append((names[0], type_text.strip()))
            current = (
                f"∀ ({' '.join(names[1:])} : {type_text}), {body}"
                if len(names) > 1
                else body
            )
            continue
        arrow = _split_top_level_arrow(unwrapped)
        if arrow is None:
            return tuple(binders), tuple(hypotheses), unwrapped
        hypothesis, current = arrow
        hypotheses.append(_unwrap_transparent_parens(hypothesis))
    raise ValueError("empty right-spine conclusion")


def _identity_hypothesis_is_supported(hypothesis: str, function_name: str) -> bool:
    compact = re.sub(r"\s+", "", str(hypothesis or "")).replace("Set.Icc", "Icc")
    escaped = re.escape(function_name)
    if re.fullmatch(rf"(?:ContinuousOn|StrictMonoOn){escaped}\(Icc[^()]+\)", compact):
        return True
    nonnegative = re.fullmatch(
        rf"∀([A-Za-z_][A-Za-z0-9_']*)∈Icc(-?[0-9]+)(-?[0-9]+),"
        rf"0≤{escaped}\1",
        compact,
    )
    if nonnegative is not None:
        return int(nonnegative.group(2)) >= 0
    return False


def _identity_hypothesis_proof(
    hypothesis: str,
    function_name: str,
) -> str | None:
    compact = re.sub(r"\s+", "", str(hypothesis or "")).replace("Set.Icc", "Icc")
    escaped = re.escape(function_name)
    if re.fullmatch(rf"ContinuousOn{escaped}\(Icc[^()]+\)", compact):
        return "(by fun_prop)"
    if re.fullmatch(rf"StrictMonoOn{escaped}\(Icc[^()]+\)", compact):
        return "(by exact strictMono_id.strictMonoOn)"
    nonnegative = re.fullmatch(
        rf"∀([A-Za-z_][A-Za-z0-9_']*)∈Icc(-?[0-9]+)(-?[0-9]+),"
        rf"0≤{escaped}\1",
        compact,
    )
    if nonnegative is None or int(nonnegative.group(2)) < 0:
        return None
    variable = nonnegative.group(1)
    lower = nonnegative.group(2)
    return (
        f"(by intro {variable} hmem; "
        f"exact le_trans (by norm_num : (0 : ℝ) ≤ {lower}) hmem.1)"
    )


def _integral_certification_steps(
    evaluations: tuple[_IntegralEvaluation, ...],
) -> tuple[str, ...]:
    """Generate bounded FTC lemmas for the parser-audited integral tree."""

    lines: list[str] = []
    for index, evaluation in enumerate(evaluations):
        name = f"h_mini_exact_integral_{index}"
        parameters = " ".join(
            f"({symbol} : ℝ)" for symbol in sorted(evaluation.result.free_symbols)
        )
        parameter_suffix = f" {parameters}" if parameters else ""
        lower = _fraction_lean(evaluation.lower)
        upper = _fraction_lean(evaluation.upper)
        integrand = evaluation.integrand.lean_expression()
        antiderivative = evaluation.integrand.antiderivative(
            evaluation.variable
        ).lean_expression()
        result = evaluation.result.lean_expression()
        proof_term = evaluation.integrand.antiderivative_proof_term(evaluation.variable)
        lines.extend(
            (
                f"have {name}{parameter_suffix} :",
                f"    (∫ ({evaluation.variable} : ℝ) in {lower}..{upper}, "
                f"{evaluation.source_expression}) = {result} := by",
            )
        )
        if evaluation.nested_indices:
            nested_names = ", ".join(
                f"h_mini_exact_integral_{nested}"
                for nested in evaluation.nested_indices
            )
            lines.append(f"  simp_rw [{nested_names}]")
        lines.extend(
            (
                "  have h_mini_deriv :",
                f"      ∀ {evaluation.variable} ∈ uIcc {lower} {upper},",
                f"        HasDerivAt (fun {evaluation.variable} : ℝ => "
                f"{antiderivative}) ({integrand}) {evaluation.variable} := by",
                f"    intro {evaluation.variable} h_mini_mem",
                f"    convert {proof_term} using 1 <;>",
                "      (try funext h_mini_point) <;>",
                "      simp [id_eq] <;> ring",
                "  have h_mini_integrable :",
                f"      IntervalIntegrable (fun {evaluation.variable} : ℝ => "
                f"{integrand}) MeasureTheory.volume {lower} {upper} :=",
                f"    (by fun_prop : Continuous (fun {evaluation.variable} : ℝ => "
                f"{integrand})).intervalIntegrable {lower} {upper}",
                "  convert intervalIntegral.integral_eq_sub_of_hasDerivAt",
                f"      (f := fun {evaluation.variable} : ℝ => {antiderivative})",
                f"      (f' := fun {evaluation.variable} : ℝ => {integrand})",
                "      h_mini_deriv h_mini_integrable using 1 <;> ring",
            )
        )
    return tuple(lines)


def exact_identity_polynomial_integral_refutation(
    statement: str,
) -> ExactIntegralRefutation | None:
    """Return an exact counterexample hint for one supported identity probe."""

    try:
        source = _strip_lean_line_comments(statement)
        binders, hypotheses, conclusion = _right_spine_parts(source)
        function_binders = [
            (name, type_text)
            for name, type_text in binders
            if function_binder_domain(type_text)
        ]
        if len(binders) != 1 or len(function_binders) != 1:
            return None
        function_name, type_text = function_binders[0]
        if function_binder_domain(type_text) != "real_function":
            return None
        if "∫" not in conclusion or any(
            not _identity_hypothesis_is_supported(item, function_name)
            for item in hypotheses
        ):
            return None
        parser = _PolynomialIntegralParser(
            conclusion,
            function_name=function_name,
        )
        lhs, relation, rhs = parser.parse_relation()
        if lhs.free_symbols or rhs.free_symbols:
            return None
        lhs_value = lhs.constant_value
        rhs_value = rhs.constant_value
        difference = lhs_value - rhs_value
        if relation == "=":
            relation_holds = difference == 0
        elif relation == "≠":
            relation_holds = difference != 0
        elif relation == "<":
            relation_holds = lhs_value < rhs_value
        elif relation == "≤":
            relation_holds = lhs_value <= rhs_value
        elif relation == ">":
            relation_holds = lhs_value > rhs_value
        else:
            relation_holds = lhs_value >= rhs_value
        if relation_holds:
            return None
        hypothesis_proofs = tuple(
            proof
            for hypothesis in hypotheses
            for proof in [_identity_hypothesis_proof(hypothesis, function_name)]
            if proof is not None
        )
        if len(hypothesis_proofs) != len(hypotheses):
            return None
        return ExactIntegralRefutation(
            function_name=function_name,
            relation=relation,
            lhs=str(lhs_value),
            rhs=str(rhs_value),
            difference=str(difference),
            certification_steps=_integral_certification_steps(
                tuple(parser.integral_evaluations)
            ),
            hypothesis_proofs=hypothesis_proofs,
            top_level_integral_names=tuple(
                f"h_mini_exact_integral_{index}"
                for index in range(len(parser.integral_evaluations))
                if index
                not in {
                    nested
                    for evaluation in parser.integral_evaluations
                    for nested in evaluation.nested_indices
                }
            ),
        )
    except (ArithmeticError, RecursionError, TypeError, ValueError):
        return None


__all__ = [
    "ExactIntegralRefutation",
    "exact_identity_polynomial_integral_refutation",
]

"""Conservative Lean-to-SMT candidate search with killable subprocesses."""

from __future__ import annotations

import asyncio
import json
import re
import sys
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from .generators import binder_domain, leading_forall_binders, normalize_type
from .model import content_hash
from ..subprocess_cleanup import communicate_with_hard_timeout


class SmtTranslationError(ValueError):
    pass


@dataclass(frozen=True)
class SmtBinder:
    lean_name: str
    lean_type: str
    domain: str
    smt_name: str
    fin_size: int = 0


@dataclass(frozen=True)
class SmtTranslation:
    statement: str
    script: str
    binders: tuple[SmtBinder, ...]
    query_hash: str


_TOKEN_RE = re.compile(
    r"\s*(?:(?P<num>[0-9]+)|(?P<id>[^\W\d][\w']*)|"
    r"(?P<op>↔|<->|→|->|&&|\|\||≤|≥|≠|!=|<=|>=|==|[()¬!∧∨=<>+*\-^]))",
    re.UNICODE,
)


def _tokenize(text: str) -> list[str]:
    tokens: list[str] = []
    position = 0
    while position < len(text):
        match = _TOKEN_RE.match(text, position)
        if match is None:
            if not text[position:].strip():
                break
            raise SmtTranslationError(
                f"unsupported token near {text[position : position + 24]!r}"
            )
        token = match.group("num") or match.group("id") or match.group("op")
        tokens.append(token)
        position = match.end()
    return tokens


class _Parser:
    def __init__(self, tokens: Sequence[str]) -> None:
        self.tokens = list(tokens)
        self.index = 0

    def _peek(self) -> str:
        return self.tokens[self.index] if self.index < len(self.tokens) else ""

    def _take(self, expected: str = "") -> str:
        token = self._peek()
        if not token or (expected and token != expected):
            raise SmtTranslationError(
                f"expected {expected or 'expression'}, got {token!r}"
            )
        self.index += 1
        return token

    def parse(self) -> Any:
        node = self._iff()
        if self._peek():
            raise SmtTranslationError(f"unexpected token {self._peek()!r}")
        return node

    def _iff(self) -> Any:
        # Lean's implication parser binds more tightly than `↔`:
        # `P → Q ↔ R` means `(P → Q) ↔ R`.
        left = self._implication()
        if self._peek() in {"↔", "<->"}:
            self._take()
            return ("iff", left, self._iff())
        return left

    def _implication(self) -> Any:
        left = self._or_expr()
        token = self._peek()
        if token in {"→", "->"}:
            self._take()
            return ("implies", left, self._implication())
        return left

    def _or_expr(self) -> Any:
        node = self._and_expr()
        while self._peek() in {"∨", "||"}:
            self._take()
            node = ("or", node, self._and_expr())
        return node

    def _and_expr(self) -> Any:
        node = self._comparison()
        while self._peek() in {"∧", "&&"}:
            self._take()
            node = ("and", node, self._comparison())
        return node

    def _comparison(self) -> Any:
        node = self._additive()
        token = self._peek()
        if token in {"=", "==", "≠", "!=", "<", "≤", "<=", ">", "≥", ">="}:
            self._take()
            node = (token, node, self._additive())
        return node

    def _additive(self) -> Any:
        node = self._multiplicative()
        while self._peek() in {"+", "-"}:
            token = self._take()
            node = (token, node, self._multiplicative())
        return node

    def _multiplicative(self) -> Any:
        node = self._unary()
        while self._peek() == "*":
            self._take()
            node = ("*", node, self._unary())
        return node

    def _power(self) -> Any:
        node = self._atom()
        if self._peek() == "^":
            self._take()
            exponent = self._unary()
            node = ("^", node, exponent)
        return node

    def _unary(self) -> Any:
        token = self._peek()
        if token in {"¬", "!"}:
            self._take()
            return ("not", self._unary())
        if token == "-":
            self._take()
            return ("neg", self._unary())
        return self._power()

    def _atom(self) -> Any:
        token = self._take()
        if token == "(":
            node = self._iff()
            self._take(")")
            return node
        if token.isdigit():
            return ("num", int(token))
        if token in {"True", "true"}:
            return ("bool", True)
        if token in {"False", "false"}:
            return ("bool", False)
        return ("var", token)


def _unify_numeric(left: str, right: str) -> str:
    if left == "num":
        return right if right != "num" else "int"
    if right == "num":
        return left
    if left != right or left not in {"nat", "pnat", "fin", "int", "rat"}:
        raise SmtTranslationError(f"mixed or nonnumeric sorts: {left}/{right}")
    return left


def _compile(node: Any, variables: Mapping[str, tuple[str, str]]) -> tuple[str, str]:
    op = node[0]
    if op == "var":
        if node[1] not in variables:
            raise SmtTranslationError(f"free or unsupported identifier {node[1]!r}")
        return variables[node[1]]
    if op == "num":
        return str(node[1]), "num"
    if op == "bool":
        return ("true" if node[1] else "false"), "bool"
    if op == "not":
        value, sort = _compile(node[1], variables)
        if sort != "bool":
            raise SmtTranslationError("logical negation requires a proposition")
        return f"(not {value})", "bool"
    if op == "neg":
        value, sort = _compile(node[1], variables)
        if sort in {"nat", "pnat", "fin"}:
            raise SmtTranslationError("negative terms are invalid in unsigned domains")
        if sort not in {"num", "int", "rat"}:
            raise SmtTranslationError("unary minus requires arithmetic")
        return f"(- {value})", sort
    left, left_sort = _compile(node[1], variables)
    right, right_sort = _compile(node[2], variables)
    if op in {"and", "or", "implies", "iff"}:
        if left_sort != "bool" or right_sort != "bool":
            raise SmtTranslationError(f"{op} requires propositions")
        smt_op = {"and": "and", "or": "or", "implies": "=>", "iff": "="}[op]
        return f"({smt_op} {left} {right})", "bool"
    if op in {"=", "==", "≠", "!="}:
        if left_sort == "num" and right_sort == "num":
            left_sort = right_sort = "int"
        elif left_sort == "num":
            left_sort = right_sort
        elif right_sort == "num":
            right_sort = left_sort
        if left_sort != right_sort:
            raise SmtTranslationError("equality operands have different sorts")
        equal = f"(= {left} {right})"
        return (f"(not {equal})" if op in {"≠", "!="} else equal), "bool"
    if op in {"<", "≤", "<=", ">", "≥", ">="}:
        _unify_numeric(left_sort, right_sort)
        smt_op = {"≤": "<=", "≥": ">=", "<=": "<=", ">=": ">="}.get(op, op)
        return f"({smt_op} {left} {right})", "bool"
    if op in {"+", "-", "*"}:
        if op == "-" and left_sort == right_sort == "num":
            raise SmtTranslationError(
                "numeral-only subtraction has Lean-defaulted Nat semantics"
            )
        sort = _unify_numeric(left_sort, right_sort)
        if sort == "fin":
            raise SmtTranslationError(
                "Fin arithmetic is modular in Lean and is not translated as Int arithmetic"
            )
        if op == "-" and sort in {"nat", "pnat", "fin"}:
            raise SmtTranslationError("truncated natural subtraction is not translated")
        return f"({op} {left} {right})", sort
    if op == "^":
        if node[2][0] != "num" or not 0 <= int(node[2][1]) <= 8:
            raise SmtTranslationError(
                "power exponent must be a numeral from 0 through 8"
            )
        if left_sort == "fin":
            raise SmtTranslationError(
                "Fin powers are modular in Lean and are not translated as Int powers"
            )
        if left_sort not in {"nat", "pnat", "int", "rat"}:
            raise SmtTranslationError("power base must be arithmetic")
        exponent = int(node[2][1])
        if exponent == 0:
            return "1", left_sort
        return (
            left if exponent == 1 else f"(* {' '.join([left] * exponent)})",
            left_sort,
        )
    raise SmtTranslationError(f"unsupported operator {op!r}")


def translate_universal_statement(statement: str) -> SmtTranslation:
    binders, body = leading_forall_binders(statement)
    if not binders:
        raise SmtTranslationError("SMT search requires visible leading forall binders")
    smt_binders: list[SmtBinder] = []
    variables: dict[str, tuple[str, str]] = {}
    declarations: list[str] = ["(set-logic ALL)"]
    constraints: list[str] = []
    for index, binder in enumerate(binders):
        domain = binder_domain(binder.type_text)
        if domain not in {"bool", "nat", "pnat", "int", "rat", "fin"}:
            raise SmtTranslationError(
                f"unsupported SMT binder type {binder.type_text!r}"
            )
        smt_name = f"mini_smt_{index}"
        sort = "Bool" if domain == "bool" else "Real" if domain == "rat" else "Int"
        fin_size = 0
        if domain == "fin":
            match = re.search(r"([0-9]+)", normalize_type(binder.type_text))
            fin_size = int(match.group(1)) if match else 0
            if fin_size < 1:
                raise SmtTranslationError(
                    "Fin 0 has no witness for universal falsification"
                )
        declarations.append(f"(declare-const {smt_name} {sort})")
        if domain == "nat":
            constraints.append(f"(>= {smt_name} 0)")
        elif domain == "pnat":
            constraints.append(f"(>= {smt_name} 1)")
        elif domain == "fin":
            constraints.extend((f"(>= {smt_name} 0)", f"(< {smt_name} {fin_size})"))
        variables[binder.name] = (smt_name, domain)
        smt_binders.append(
            SmtBinder(
                lean_name=binder.name,
                lean_type=binder.type_text,
                domain=domain,
                smt_name=smt_name,
                fin_size=fin_size,
            )
        )
    expression, expression_sort = _compile(_Parser(_tokenize(body)).parse(), variables)
    if expression_sort != "bool":
        raise SmtTranslationError("SMT body did not elaborate to a proposition")
    assertions = [f"(assert {item})" for item in constraints]
    assertions.append(f"(assert (not {expression}))")
    script = "\n".join((*declarations, *assertions))
    return SmtTranslation(
        statement=statement,
        script=script,
        binders=tuple(smt_binders),
        query_hash=content_hash({"schema": 1, "script": script}),
    )


async def run_smt_query(
    translation: SmtTranslation,
    *,
    timeout_s: float,
    backends: Sequence[str] = ("z3", "cvc5"),
) -> dict[str, Any]:
    """Run both native APIs in a killable JSON-only child process."""

    payload = {
        "schema": 1,
        "script": translation.script,
        "symbols": [
            {
                "name": binder.smt_name,
                "sort": (
                    "Bool"
                    if binder.domain == "bool"
                    else "Real"
                    if binder.domain == "rat"
                    else "Int"
                ),
            }
            for binder in translation.binders
        ],
        "backends": [str(item) for item in backends],
        # The worker runs backends sequentially.  Divide the native budget so
        # one solver cannot consume the entire outer watchdog and starve the
        # independent cross-check.
        "timeout_ms": max(
            1,
            int(float(timeout_s) * 1000 / max(1, len(tuple(backends)))),
        ),
    }
    encoded = json.dumps(payload, separators=(",", ":")).encode("utf-8")
    if len(encoded) > 1_000_000:
        raise SmtTranslationError("SMT query exceeds one-megabyte safety cap")
    process = await asyncio.create_subprocess_exec(
        sys.executable,
        "-m",
        "ensemble_prover.mini_falsification.smt_worker",
        stdin=asyncio.subprocess.PIPE,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )
    try:
        stdout, stderr = await communicate_with_hard_timeout(
            process,
            encoded,
            timeout_s=max(0.05, float(timeout_s)),
        )
    except BaseException:
        raise
    if process.returncode != 0:
        return {
            "status": "error",
            "error": stderr.decode("utf-8", errors="replace")[:2000],
            "results": [],
        }
    if len(stdout) > 1_000_000:
        return {
            "status": "error",
            "error": "SMT worker output cap exceeded",
            "results": [],
        }
    try:
        result = json.loads(stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        return {
            "status": "error",
            "error": f"invalid SMT worker output: {exc}",
            "results": [],
        }
    return (
        dict(result)
        if isinstance(result, Mapping)
        else {"status": "error", "results": []}
    )


def model_value_to_lean(value: str, binder: SmtBinder) -> str:
    raw = str(value or "").strip()
    integer_match = re.fullmatch(r"-?[0-9]+", raw)
    neg_integer_match = re.fullmatch(r"\(-\s+([0-9]+)\)", raw)
    rational_match = re.fullmatch(r"\(/\s+(-?[0-9]+)\s+([1-9][0-9]*)\)", raw)
    signed_numerator_rational_match = re.fullmatch(
        r"\(/\s+\(-\s+([0-9]+)\)\s+([1-9][0-9]*)\)", raw
    )
    infix_rational_match = re.fullmatch(r"(-?[0-9]+)/([1-9][0-9]*)", raw)
    decimal_match = re.fullmatch(r"(-?)([0-9]+)\.([0-9]+)", raw)
    neg_decimal_match = re.fullmatch(r"\(-\s+([0-9]+)\.([0-9]+)\)", raw)
    neg_rational_match = re.fullmatch(r"\(-\s+\(/\s+([0-9]+)\s+([1-9][0-9]*)\)\)", raw)
    if binder.domain == "bool":
        raw = raw.lower()
        if raw not in {"true", "false"}:
            raise SmtTranslationError(f"non-Boolean model value {raw!r}")
        return raw
    if neg_integer_match:
        raw = "-" + neg_integer_match.group(1)
        integer_match = re.fullmatch(r"-?[0-9]+", raw)
    if binder.domain == "rat":
        if integer_match:
            return f"({raw} : ℚ)"
        if rational_match:
            return f"(({rational_match.group(1)} : ℚ) / {rational_match.group(2)})"
        if signed_numerator_rational_match:
            return (
                f"((-{signed_numerator_rational_match.group(1)} : ℚ) / "
                f"{signed_numerator_rational_match.group(2)})"
            )
        if infix_rational_match:
            return (
                f"(({infix_rational_match.group(1)} : ℚ) / "
                f"{infix_rational_match.group(2)})"
            )
        if decimal_match or neg_decimal_match:
            if neg_decimal_match:
                sign, whole, fractional = "-", *neg_decimal_match.groups()
            else:
                assert decimal_match is not None
                sign, whole, fractional = decimal_match.groups()
            numerator = int(whole + fractional)
            if sign == "-":
                numerator = -numerator
            denominator = 10 ** len(fractional)
            return f"(({numerator} : ℚ) / {denominator})"
        if neg_rational_match:
            return f"(-(({neg_rational_match.group(1)} : ℚ) / {neg_rational_match.group(2)}))"
        raise SmtTranslationError(f"unsupported rational model value {raw!r}")
    if not integer_match:
        raise SmtTranslationError(f"non-integral model value {raw!r}")
    number = int(raw)
    if binder.domain in {"nat", "fin"} and number < 0:
        raise SmtTranslationError("solver violated unsigned-domain bound")
    if binder.domain == "pnat" and number < 1:
        raise SmtTranslationError("solver violated positive-natural bound")
    if binder.domain == "fin":
        if number >= binder.fin_size:
            raise SmtTranslationError("solver violated Fin upper bound")
        return f"({number} : Fin {binder.fin_size})"
    lean_type = {"nat": "ℕ", "pnat": "ℕ+", "int": "ℤ"}[binder.domain]
    return f"({number} : {lean_type})"

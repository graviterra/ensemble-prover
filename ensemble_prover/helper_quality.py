"""Stable structural admission quality for auxiliary theorem statements.

This module intentionally does not inspect the active root, graph, or route.
Those are dynamic dispositions and must not be baked into durable admission
evidence.  The conservative classifier answers only whether an auxiliary
statement is structurally capable of adding mathematical information.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Mapping, Tuple

from .contract_identity import has_lean_contract_identity
from .proof_graph import (
    graph_statement_contract_ambiguities,
    graph_statement_key,
    graph_statement_premises_and_conclusion,
    helper_decl_statement,
)


HELPER_ADMISSION_QUALITY_SCHEMA_VERSION = 3


@dataclass(frozen=True)
class HelperAdmissionQuality:
    schema_version: int
    classification: str
    generic_novelty: bool
    cache_publishable: bool
    auxiliary_target_admissible: bool
    conclusion: str = ""
    premise_keys: Tuple[str, ...] = ()

    @property
    def structurally_vacuous(self) -> bool:
        return self.classification in {
            "true_conclusion",
            "false_premise",
            "premise_restatement",
            "premise_entailed_conclusion",
            "reflexive_conclusion",
            "tautological_connective",
            "neutral_identity",
        }


def _right_spine_conclusion_and_premises(
    statement: str,
) -> tuple[str, tuple[str, ...]]:
    """Peel only outer Pi/implication consequents.

    Quantifiers inside an antecedent remain part of that antecedent.  This is
    deliberately a stable surface characterization; Lean elaboration remains
    the authority for theorem correctness and exact target identity.
    """

    # Import lazily: ``finite_claim_check`` consumes helper declaration
    # adapters from ``proof_dossier``, while the dossier itself imports this
    # stable quality policy.  Keeping the parser dependency at call time
    # prevents a module-initialization cycle without duplicating its syntax
    # rules.
    from .finite_claim_check import (
        _first_forall_chunk,
        _split_top_level_arrow,
        _unwrap_transparent_parens,
    )

    current = str(statement or "").strip()
    premises: list[str] = []
    proposition_variables: set[str] = set()
    while current:
        unwrapped = _unwrap_transparent_parens(current)
        forall = _first_forall_chunk(unwrapped)
        if forall is not None:
            binder, current = forall
            binder_raw = str(binder or "").strip()
            if (
                len(binder_raw) >= 2
                and binder_raw[0] in "({["
                and binder_raw[-1] in ")}]"
            ):
                binder_raw = binder_raw[1:-1].strip()
            if ":" in binder_raw:
                names_raw, binder_type = binder_raw.rsplit(":", 1)
                names = tuple(
                    item
                    for item in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", names_raw)
                    if item
                )
                binder_type = _unwrap_transparent_parens(binder_type.strip())
                if binder_type == "Prop":
                    proposition_variables.update(names)
                elif binder_type in proposition_variables or binder_type in {
                    "False",
                    "True",
                }:
                    premises.append(binder_type)
            continue
        arrow = _split_top_level_arrow(unwrapped)
        if arrow is None:
            surface_conclusion = unwrapped.strip()
            break
        premise, current = arrow
        premise = _unwrap_transparent_parens(str(premise or "").strip())
        if premise:
            premises.append(premise)
    else:
        surface_conclusion = ""

    # Use the shared graph telescope classifier to recognize explicit proof
    # binders such as ``(h : n = 0)`` and ``(h : P ∧ Q)``.  A statement-only
    # parser must not guess that an unresolved application-shaped family
    # (for example ``foo n``) returns ``Prop``: retain such a premise only when
    # it was independently exposed by an implication or a known Prop-valued
    # binder in the conservative surface walk above.
    graph_premises, graph_conclusion, _bound_names = (
        graph_statement_premises_and_conclusion(statement)
    )
    ambiguous_types = graph_statement_contract_ambiguities(statement)
    ambiguous_keys = {
        graph_statement_key(item)
        for item in ambiguous_types
        if graph_statement_key(item)
    }
    surface_keys = {
        graph_statement_key(item) for item in premises if graph_statement_key(item)
    }
    for graph_premise in graph_premises:
        key = graph_statement_key(graph_premise)
        if (
            key in ambiguous_keys
            and key not in surface_keys
            and not _syntactically_prop_valued_type(graph_premise)
        ):
            continue
        premises.append(graph_premise)
    for ambiguous_type in ambiguous_types:
        if _syntactically_prop_valued_type(ambiguous_type):
            premises.append(ambiguous_type)
    return (
        str(graph_conclusion or surface_conclusion or "").strip(),
        tuple(dict.fromkeys(premises)),
    )


def _syntactically_prop_valued_type(type_text: str) -> bool:
    """Recognize only syntax that unambiguously denotes a proposition.

    Unknown applications stay excluded even when their binder name looks like
    a hypothesis.  This covers Lean's core prefix proposition constructors in
    addition to the relation/connective notation already understood by the
    shared graph telescope parser.
    """

    from .finite_claim_check import _unwrap_transparent_parens

    raw = _unwrap_transparent_parens(str(type_text or "").strip())
    if raw in {"True", "False"}:
        return True
    if raw.startswith(("¬", "∀", "∃")):
        return True
    if any(token in raw for token in ("→", "->", "↔", "∧", "∨")):
        return True
    if any(token in raw for token in (" = ", " ≠ ", " < ", " > ", " ≤ ", " ≥ ", " ∈ ", " ∉ ", " ∣ ")):
        return True
    return bool(
        re.match(
            r"^(?:Eq|HEq|Ne|And|Or|Not|Exists|Nonempty)(?:\s|$)",
            raw,
        )
    )


def _top_level_reflexive_relation(statement: str) -> bool:
    from .finite_claim_check import _unwrap_transparent_parens

    raw = _unwrap_transparent_parens(str(statement or "").strip())
    # Keep the first slice intentionally narrow.  Equality is by far the most
    # common reflexive laundering shape; other relations remain eligible
    # until Lean-backed contract evidence classifies them.
    depth = 0
    for index, char in enumerate(raw):
        if char in "([{⟨":
            depth += 1
            continue
        if char in ")]}⟩":
            depth = max(0, depth - 1)
            continue
        if char != "=" or depth != 0:
            continue
        before = raw[index - 1] if index else ""
        after = raw[index + 1] if index + 1 < len(raw) else ""
        if before in {"<", ">", "!", ":"} or after in {">", "="}:
            continue
        left = raw[:index].strip()
        right = raw[index + 1 :].strip()
        return bool(
            left
            and right
            and graph_statement_key(left) == graph_statement_key(right)
        )
    return False


def _structurally_tautological_proposition(statement: str) -> bool:
    from .finite_claim_check import (
        _split_top_level_token,
        _unwrap_transparent_parens,
    )

    raw = _unwrap_transparent_parens(str(statement or "").strip())
    if raw == "True":
        return True
    conjunction = _split_top_level_token(raw, ("∧", "/\\"))
    if conjunction is not None:
        return all(_structurally_tautological_proposition(item) for item in conjunction)
    disjunction = _split_top_level_token(raw, ("∨", "\\/"))
    if disjunction is not None:
        return any(_structurally_tautological_proposition(item) for item in disjunction)
    return False


def _conclusion_is_projection_of_premise(
    statement: str,
    *,
    premise_keys: set[str],
) -> bool:
    """Recognize conservative connective wrappers of an existing premise.

    This is deliberately one-way: every conjunct must already follow from a
    premise (or be ``True``), while one disjunct is enough.  It catches
    syntactic laundering such as ``P -> P ∧ True`` without attempting
    general propositional proof search.
    """

    from .finite_claim_check import (
        _split_top_level_token,
        _unwrap_transparent_parens,
    )

    raw = _unwrap_transparent_parens(str(statement or "").strip())
    if not raw:
        return False
    key = graph_statement_key(raw)
    if key and key in premise_keys:
        return True
    if raw == "True":
        return True
    conjunction = _split_top_level_token(raw, ("∧", "/\\"))
    if conjunction is not None:
        return all(
            _conclusion_is_projection_of_premise(
                item,
                premise_keys=premise_keys,
            )
            for item in conjunction
        )
    disjunction = _split_top_level_token(raw, ("∨", "\\/"))
    if disjunction is not None:
        return any(
            _conclusion_is_projection_of_premise(
                item,
                premise_keys=premise_keys,
            )
            for item in disjunction
        )
    return False


_PROPOSITIONAL_CLOSURE_LIMIT = 128
_PROPOSITIONAL_RECURSION_LIMIT = 12
_PROPOSITIONAL_ATOM_LIMIT = 10


def _split_top_level_connective(
    statement: str,
    tokens: tuple[str, ...],
) -> tuple[str, str] | None:
    from .finite_claim_check import (
        _split_top_level_token,
        _unwrap_transparent_parens,
    )

    return _split_top_level_token(
        _unwrap_transparent_parens(str(statement or "").strip()),
        tokens,
    )


def _as_implication(statement: str) -> tuple[str, str] | None:
    from .finite_claim_check import (
        _split_top_level_arrow,
        _unwrap_transparent_parens,
    )

    raw = _unwrap_transparent_parens(str(statement or "").strip())
    arrow = _split_top_level_arrow(raw)
    if arrow is not None:
        return arrow
    if raw.startswith("¬"):
        antecedent = _unwrap_transparent_parens(raw[1:].strip())
        if antecedent:
            return antecedent, "False"
    return None


def _top_level_application_parts(statement: str) -> tuple[str, ...]:
    """Split a simple prefix application without descending into arguments."""

    from .finite_claim_check import _unwrap_transparent_parens

    raw = _unwrap_transparent_parens(str(statement or "").strip())
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(raw):
        char = raw[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char.isspace() and depth == 0:
            part = raw[start:index].strip()
            if part:
                parts.append(part)
            while index + 1 < len(raw) and raw[index + 1].isspace():
                index += 1
            start = index + 1
        index += 1
    tail = raw[start:].strip()
    if tail:
        parts.append(tail)
    return tuple(parts)


def _propositional_ast(
    statement: str,
    *,
    node_budget: list[int],
) -> tuple[Any, ...] | None:
    """Parse only the core propositional surface; domain terms stay atoms."""

    from .finite_claim_check import _unwrap_transparent_parens

    if node_budget[0] <= 0:
        return None
    node_budget[0] -= 1
    raw = _unwrap_transparent_parens(str(statement or "").strip())
    if not raw:
        return None
    if raw == "True":
        return ("const", True)
    if raw == "False":
        return ("const", False)
    for kind, tokens in (
        ("iff", ("↔", "<->")),
        ("imp", ("→", "->")),
        ("or", ("∨", "\\/")),
        ("and", ("∧", "/\\")),
    ):
        split = _split_top_level_connective(raw, tokens)
        if split is None:
            continue
        left = _propositional_ast(split[0], node_budget=node_budget)
        right = _propositional_ast(split[1], node_budget=node_budget)
        return (kind, left, right) if left is not None and right is not None else None
    if raw.startswith("¬"):
        child = _propositional_ast(raw[1:].strip(), node_budget=node_budget)
        return ("not", child) if child is not None else None
    application = _top_level_application_parts(raw)
    prefix_arities = {"And": ("and", 2), "Or": ("or", 2), "Iff": ("iff", 2), "Not": ("not", 1)}
    if application and application[0] in prefix_arities:
        kind, arity = prefix_arities[application[0]]
        if len(application) == arity + 1:
            children = tuple(
                _propositional_ast(item, node_budget=node_budget)
                for item in application[1:]
            )
            if all(child is not None for child in children):
                return (kind, *children)
    key = graph_statement_key(raw)
    return ("atom", key) if key else None


def _propositional_atoms(ast: tuple[Any, ...]) -> set[str]:
    if ast[0] == "atom":
        return {str(ast[1])}
    atoms: set[str] = set()
    for child in ast[1:]:
        if isinstance(child, tuple):
            atoms.update(_propositional_atoms(child))
    return atoms


def _evaluate_propositional_ast(
    ast: tuple[Any, ...],
    assignment: Mapping[str, bool],
) -> bool:
    kind = ast[0]
    if kind == "const":
        return bool(ast[1])
    if kind == "atom":
        return bool(assignment.get(str(ast[1]), False))
    if kind == "not":
        return not _evaluate_propositional_ast(ast[1], assignment)
    left = _evaluate_propositional_ast(ast[1], assignment)
    right = _evaluate_propositional_ast(ast[2], assignment)
    if kind == "and":
        return left and right
    if kind == "or":
        return left or right
    if kind == "imp":
        return (not left) or right
    if kind == "iff":
        return left == right
    return False


def _bounded_propositional_entailment(
    premises: tuple[str, ...],
    conclusion: str,
) -> bool | None:
    """Decide a small propositional abstraction, failing open past its caps."""

    node_budget = [_PROPOSITIONAL_CLOSURE_LIMIT]
    premise_asts = tuple(
        _propositional_ast(premise, node_budget=node_budget) for premise in premises
    )
    conclusion_ast = _propositional_ast(conclusion, node_budget=node_budget)
    if conclusion_ast is None or any(ast is None for ast in premise_asts):
        return None
    typed_premise_asts = tuple(ast for ast in premise_asts if ast is not None)
    atoms = sorted(
        set().union(
            _propositional_atoms(conclusion_ast),
            *(_propositional_atoms(ast) for ast in typed_premise_asts),
        )
    )
    if len(atoms) > _PROPOSITIONAL_ATOM_LIMIT:
        return None
    for mask in range(1 << len(atoms)):
        assignment = {
            atom: bool(mask & (1 << index)) for index, atom in enumerate(atoms)
        }
        if all(
            _evaluate_propositional_ast(ast, assignment)
            for ast in typed_premise_asts
        ) and not _evaluate_propositional_ast(conclusion_ast, assignment):
            return False
    return True


def _premise_entailment_closure(premises: tuple[str, ...]) -> dict[str, str]:
    """Compute a bounded, intuitionistically sound surface closure.

    This is not a theorem prover.  It only performs conjunction elimination
    and modus ponens over already-present premises.  Those two rules close the
    common laundering gap between ``P ∧ Q`` and ``P`` without guessing the
    semantics of opaque predicates or data-bearing binder types.
    """

    from .finite_claim_check import _unwrap_transparent_parens

    known: dict[str, str] = {}

    def add(raw: str) -> bool:
        if len(known) >= _PROPOSITIONAL_CLOSURE_LIMIT:
            return False
        normalized = _unwrap_transparent_parens(str(raw or "").strip())
        key = graph_statement_key(normalized)
        if not normalized or not key or key in known:
            return False
        known[key] = normalized
        return True

    for premise in premises:
        add(premise)
    add("True")

    changed = True
    rounds = 0
    while changed and rounds < _PROPOSITIONAL_RECURSION_LIMIT:
        changed = False
        rounds += 1
        snapshot = tuple(known.values())
        for proposition in snapshot:
            conjunction = _split_top_level_connective(
                proposition,
                ("∧", "/\\"),
            )
            if conjunction is not None:
                changed = add(conjunction[0]) or changed
                changed = add(conjunction[1]) or changed
        snapshot = tuple(known.values())
        for proposition in snapshot:
            implication = _as_implication(proposition)
            if implication is None:
                continue
            antecedent, consequent = implication
            if _proposition_entailed(
                antecedent,
                known,
                depth=0,
                permit_implication=False,
            ):
                changed = add(consequent) or changed
    return known


def _proposition_entailed(
    statement: str,
    known: Mapping[str, str],
    *,
    depth: int,
    permit_implication: bool = True,
) -> bool:
    from .finite_claim_check import _unwrap_transparent_parens

    if depth >= _PROPOSITIONAL_RECURSION_LIMIT:
        return False
    raw = _unwrap_transparent_parens(str(statement or "").strip())
    key = graph_statement_key(raw)
    if not raw:
        return False
    if raw == "True" or (key and key in known):
        return True
    conjunction = _split_top_level_connective(raw, ("∧", "/\\"))
    if conjunction is not None:
        return all(
            _proposition_entailed(
                item,
                known,
                depth=depth + 1,
                permit_implication=permit_implication,
            )
            for item in conjunction
        )
    disjunction = _split_top_level_connective(raw, ("∨", "\\/"))
    if disjunction is not None:
        return any(
            _proposition_entailed(
                item,
                known,
                depth=depth + 1,
                permit_implication=permit_implication,
            )
            for item in disjunction
        )
    iff = _split_top_level_connective(raw, ("↔", "<->"))
    if iff is not None:
        left, right = iff
        left_key = graph_statement_key(left)
        right_key = graph_statement_key(right)
        if left_key and left_key == right_key:
            return True
        if not permit_implication:
            return False
        return _proposition_entailed(
            f"{left} → {right}",
            known,
            depth=depth + 1,
        ) and _proposition_entailed(
            f"{right} → {left}",
            known,
            depth=depth + 1,
        )
    implication = _as_implication(raw) if permit_implication else None
    if implication is not None:
        antecedent, consequent = implication
        extended = _premise_entailment_closure(
            tuple([*known.values(), antecedent])
        )
        return _proposition_entailed(
            consequent,
            extended,
            depth=depth + 1,
        )
    return False


def _top_level_neutral_identity(statement: str) -> bool:
    from .finite_claim_check import (
        _split_top_level_equals,
        _unwrap_transparent_parens,
    )

    equality = _split_top_level_equals(
        _unwrap_transparent_parens(str(statement or "").strip())
    )
    if equality is None:
        return False
    left, right = (
        _unwrap_transparent_parens(str(item or "").strip()) for item in equality
    )
    if not left or not right:
        return False

    def one_step_neutral_forms(term: str) -> set[str]:
        raw = _unwrap_transparent_parens(str(term or "").strip())
        base_key = graph_statement_key(raw)
        forms = {base_key} if base_key else set()
        for token, left_neutral, right_neutral in (
            ("+", "0", "0"),
            ("*", "1", "1"),
            ("-", "", "0"),
            ("/", "", "1"),
        ):
            split = _split_top_level_connective(raw, (token,))
            if split is None:
                continue
            left, right = split
            reduced = ""
            if right_neutral and _unwrap_transparent_parens(right) == right_neutral:
                reduced = left
            elif left_neutral and _unwrap_transparent_parens(left) == left_neutral:
                reduced = right
            reduced_key = graph_statement_key(reduced) if reduced else ""
            if reduced_key:
                forms.add(reduced_key)
        return forms

    return bool(one_step_neutral_forms(left) & one_step_neutral_forms(right))


def classify_auxiliary_statement_quality(
    statement: str,
    *,
    proof_binder_types: tuple[str, ...] = (),
) -> HelperAdmissionQuality:
    from .finite_claim_check import _unwrap_transparent_parens

    conclusion, surface_premises = _right_spine_conclusion_and_premises(statement)
    premises = tuple(
        dict.fromkeys(
            str(item or "").strip()
            for item in (*surface_premises, *proof_binder_types)
            if str(item or "").strip()
        )
    )
    conclusion_key = graph_statement_key(conclusion) if conclusion else ""
    premise_keys = tuple(
        key
        for key in (graph_statement_key(premise) for premise in premises)
        if key
    )
    premise_closure = _premise_entailment_closure(premises)
    classification = "substantive"
    if _proposition_entailed(
        "False",
        premise_closure,
        depth=0,
    ) or _bounded_propositional_entailment(premises, "False") is True:
        classification = "false_premise"
    elif _unwrap_transparent_parens(conclusion) == "True":
        classification = "true_conclusion"
    elif _structurally_tautological_proposition(
        conclusion
    ) or _proposition_entailed(
        conclusion,
        _premise_entailment_closure(()),
        depth=0,
    ) or _bounded_propositional_entailment((), conclusion) is True:
        classification = "tautological_connective"
    elif conclusion_key and conclusion_key in set(premise_keys):
        classification = "premise_restatement"
    elif premises and (
        _conclusion_is_projection_of_premise(
            conclusion,
            premise_keys=set(premise_keys),
        )
        or _proposition_entailed(
            conclusion,
            premise_closure,
            depth=0,
        )
        or _bounded_propositional_entailment(premises, conclusion) is True
    ):
        classification = "premise_entailed_conclusion"
    elif _top_level_reflexive_relation(conclusion):
        classification = "reflexive_conclusion"
    elif _top_level_neutral_identity(conclusion):
        classification = "neutral_identity"
    vacuous = classification != "substantive"
    return HelperAdmissionQuality(
        schema_version=HELPER_ADMISSION_QUALITY_SCHEMA_VERSION,
        classification=classification,
        generic_novelty=not vacuous,
        cache_publishable=not vacuous,
        auxiliary_target_admissible=not vacuous,
        conclusion=conclusion,
        premise_keys=premise_keys,
    )


def auxiliary_statement_is_structurally_admissible(statement: str) -> bool:
    return classify_auxiliary_statement_quality(
        statement
    ).auxiliary_target_admissible


def verified_helper_admission_quality(helper: Any) -> HelperAdmissionQuality:
    """Classify a helper object, record, source block, or bare statement.

    This adapter keeps consumers from inferring quality from visibility,
    helper counts, or dynamic graph tags.  It deliberately reads only the
    stable theorem statement.
    """

    statement = ""
    source = ""
    proof_binder_types: tuple[str, ...] = ()
    contract_identity = ""
    if isinstance(helper, Mapping):
        statement = str(helper.get("statement") or "").strip()
        source = str(helper.get("source") or "").strip()
        contract_identity = str(helper.get("contract_identity") or "").strip()
        proof_binder_types = tuple(
            str(item or "").strip()
            for item in list(helper.get("contract_proof_binder_types") or [])
            if str(item or "").strip()
        )
    elif isinstance(helper, str):
        source = helper.strip()
    else:
        statement = str(getattr(helper, "statement", "") or "").strip()
        source = str(getattr(helper, "source", "") or "").strip()
        contract_identity = str(
            getattr(helper, "contract_identity", "") or ""
        ).strip()
        proof_binder_types = tuple(
            str(item or "").strip()
            for item in list(
                getattr(helper, "contract_proof_binder_types", []) or []
            )
            if str(item or "").strip()
        )
    if not statement and source:
        statement = str(helper_decl_statement(source) or "").strip()
    if not statement and isinstance(helper, str):
        statement = helper.strip()
    if not has_lean_contract_identity(contract_identity):
        proof_binder_types = ()
    return classify_auxiliary_statement_quality(
        statement,
        proof_binder_types=proof_binder_types,
    )

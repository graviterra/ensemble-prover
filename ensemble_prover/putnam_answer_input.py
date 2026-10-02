"""Source-bound, model-proposed answers for opaque Putnam constants.

The candidate is a new concrete theorem, never an equality assumption about
the benchmark's opaque axiom. Ordinary Lean verification must still prove it.
"""

from __future__ import annotations

import re

from .answer_input import AnswerTemplate, _answer_code
from .mini_lean_extract import _strip_lean_comments
from .theorem_project import (
    PUTNAMBENCH_ADAPTER_ID,
    TheoremProblem,
    TheoremProjectRequest,
    scan_lean_theorems,
    select_lean_theorem,
    theorem_reusable_preamble,
)

PUTNAM_ANSWER_MARKER = "-- ensemble-putnam-answer-input: source-bound candidate"


def find_putnam_answer_template(
    source: str, theorem_name: str | None = None
) -> AnswerTemplate | None:
    """Adapt one top-level, nonparameterized answer constant without its value.

    Put the slot outside the theorem telescope: the answer to a global question
    cannot depend on a quantified variable introduced by that question.
    Unsupported scopes fail explicitly rather than inventing a substitution.
    """
    from .putnam import _sanitize_preamble

    declarations = scan_lean_theorems(source)
    if not declarations:
        raise ValueError("Putnam input contains no theorem or lemma declaration")
    declaration = (
        select_lean_theorem(declarations, theorem_name)
        if theorem_name
        else declarations[0]
    )
    symbol = declaration.canonical_name + "_solution"
    # A following dot can introduce field notation or a tuple projection.
    # Keep the left namespace boundary and the right identifier boundary.
    pattern = re.compile(r"(?<![\w.'«»])" + re.escape(symbol) + r"(?![\w'«»])")
    root = declaration.statement_type
    if f"«{symbol}»" in root:
        raise ValueError(
            "Putnam answer discovery does not support escaped answer references"
        )
    occurrences = list(pattern.finditer(_answer_code(root)))
    if not occurrences:
        return None
    preamble, scope = theorem_reusable_preamble(source, declaration)
    # An already opaque axiom can still have a next-line/inline answer comment.
    # Preserve executable strings and escaped names while excluding comments.
    safe_preamble = _strip_lean_comments(
        _sanitize_preamble(preamble, fill_values=False)
    )
    if (
        declaration.namespace
        or declaration.private
        or scope.strip()
        or re.search(
            r"(?m)^\s*(?:variable|include|omit|section)\b", _answer_code(preamble)
        )
    ):
        raise ValueError(
            "Putnam answer discovery requires a top-level answer and theorem without section variables"
        )
    axiom = re.compile(
        r"(?m)^[ \t]*axiom[ \t]+"
        + re.escape(symbol)
        + r"[ \t]*:[ \t]*(?P<type>[^\n]+)$"
    )
    matches = list(axiom.finditer(safe_preamble))
    if len(matches) != 1:
        raise ValueError(
            "Putnam answer discovery requires one nonparameterized opaque solution constant"
        )
    match = matches[0]
    answer_type = match.group("type").strip()
    safe_preamble = safe_preamble[: match.start()] + safe_preamble[match.end() :]
    if pattern.search(_answer_code(safe_preamble)):
        raise ValueError(
            "Putnam answer discovery does not support preamble dependencies on the answer"
        )
    # Rename local occurrences together with the global answer reference.
    # Parenthesized type ascriptions are not evidence of shadowing. Lean's
    # mandatory abstract-question equivalence probe below checks the resulting
    # binding/field interpretation before any answer proposal can be requested.
    fresh = "_ensembleMachineAnswer"
    # Escaped identifiers denote the same Lean name as their unescaped form.
    # Include their raw spelling in freshness checks, or an inner binder such
    # as «_ensembleMachineAnswer» can capture the substituted global answer.
    while fresh in safe_preamble + root:
        fresh += "_"
    for occurrence in reversed(occurrences):
        root = root[: occurrence.start()] + fresh + root[occurrence.end() :]
    header = (
        PUTNAM_ANSWER_MARKER
        + "\n"
        + safe_preamble.rstrip()
        + "\n"
        + f"theorem {declaration.source_name}{declaration.universe_suffix} :\n"
        + f"  let {fresh} : {answer_type}\n    := ("
    )
    start = len(header)
    question = header + "sorry);\n" + root + " := by sorry\n"
    selected = select_lean_theorem(
        scan_lean_theorems(question), declaration.canonical_name
    )
    return AnswerTemplate(question, selected, ((start, start + 5),), source)


def putnam_question_equivalence_probe(template: AnswerTemplate) -> tuple[str, str]:
    """Check the adapted question against the original opaque constant in Lean.

    This uses the abstract symbol, never an official value or proposed answer.
    Definitional equality detects any accidental change in binding or scope.
    """
    from .putnam import _sanitize_preamble

    if template.original_source is None:
        raise ValueError("Putnam question probe requires the original source")
    name = template.declaration.canonical_name
    original = select_lean_theorem(scan_lean_theorems(template.original_source), name)
    preamble, _ = theorem_reusable_preamble(template.original_source, original)
    preamble = _strip_lean_comments(_sanitize_preamble(preamble, fill_values=False))
    abstract = template.fill([name + "_solution"])
    adapted = select_lean_theorem(scan_lean_theorems(abstract), name)
    probe_name = "_ensembleQuestionEquivalent"
    while probe_name in preamble + original.statement_type + adapted.statement_type:
        probe_name += "_"
    # Type*/Sort* create fresh rigid universe parameters at declaration time.
    # Elaborate the original exactly once in the header, then let `change`
    # instantiate only the adapted side against those fixed original levels.
    # Inference must happen inside the proof; underscores in an equality's
    # header would be generalized independently before `rfl` can unify them.
    adapted_type = adapted.statement_type
    anonymous_sorts = list(re.finditer(
        r"(?<![\w.'«»])(?:Type|Sort)\*", _answer_code(adapted_type)
    ))
    for occurrence in reversed(anonymous_sorts):
        adapted_type = (
            adapted_type[:occurrence.start()]
            + occurrence[0][:-1] + " _"
            + adapted_type[occurrence.end():]
        )
    question_name = probe_name + "Original"
    return (
        preamble
        + f"\ntheorem {probe_name}{original.universe_suffix} :\n"
        + f"  let {question_name} : Prop := (\n{original.statement_type}\n  );\n"
        + f"  {question_name} = {question_name} := by\n"
        + f"  change _ = (\n{adapted_type}\n  )\n  rfl\n",
        probe_name,
    )


def load_putnam_answer_project(
    request: TheoremProjectRequest,
) -> TheoremProblem:
    """Validate the discovery receipt on every startup/resume, then load Lean."""
    from .answer_project import load_answer_project

    return load_answer_project(
        request, template_finder=find_putnam_answer_template,
        adapter_id=PUTNAMBENCH_ADAPTER_ID, label="Putnam",
    )

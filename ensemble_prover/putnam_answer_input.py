"""Source-bound, model-proposed answers for opaque Putnam constants.

The candidate is a new concrete theorem, never an equality assumption about
the benchmark's opaque axiom. Ordinary Lean verification must still prove it.
"""

from __future__ import annotations

import dataclasses
import hashlib
import json
import re
from pathlib import Path

from .answer_input import AnswerTemplate, _answer_code, load_candidate
from .mini_lean_extract import _strip_lean_comments
from .nl_input import _unique_fields
from .theorem_project import (
    PUTNAMBENCH_ADAPTER_ID,
    TheoremProblem,
    TheoremProjectRequest,
    _resolve_theorem_project,
    scan_lean_theorems,
    select_lean_theorem,
    theorem_reusable_preamble,
    with_theorem_execution_context,
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
    declaration = (
        select_lean_theorem(declarations, theorem_name)
        if theorem_name
        else declarations[0]
    )
    symbol = declaration.canonical_name + "_solution"
    pattern = re.compile(r"(?<![\w.'«»])" + re.escape(symbol) + r"(?![\w.'«»])")
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
    if re.search(
        r"(?:∀|fun|λ|let|[({\[])\s*" + re.escape(symbol) + r"(?=\s*[:,=])",
        _answer_code(root),
    ):
        raise ValueError("Putnam answer symbol is shadowed in the theorem")
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
    return (
        preamble
        + f"\ntheorem {probe_name} :\n"
        + f"({original.statement_type}) = ({adapted.statement_type}) := by rfl\n",
        probe_name,
    )


def load_putnam_answer_project(
    request: TheoremProjectRequest,
) -> TheoremProblem:
    """Validate the discovery receipt on every startup/resume, then load Lean."""
    request = request.normalized()
    directory = request.lean_file.parent
    record = json.loads(
        (directory / "answer_discovery.json").read_bytes(),
        object_pairs_hook=_unique_fields,
    )
    origin = record["input_request"]
    original_request = TheoremProjectRequest(
        lean_file=Path(origin["lean_file"]),
        theorem_name=origin["theorem_name"],
        project_path=Path(origin["project_path"]),
        imports=tuple(origin["imports"]),
        source_dirs=tuple(Path(path) for path in origin["source_dirs"]),
        description=origin["description"],
    ).normalized()
    if (
        original_request.lean_file == request.lean_file
        or original_request.theorem_name != request.theorem_name
        or original_request.project_path != request.project_path
        or original_request.imports != request.imports
        or original_request.source_dirs != request.source_dirs
    ):
        raise ValueError(
            "Putnam candidate execution context differs from its discovery receipt"
        )
    source = original_request.lean_file.read_bytes().decode("utf-8")
    template = find_putnam_answer_template(source, request.theorem_name)
    if template is None:
        raise ValueError("Putnam candidate has no original answer question")
    candidate = load_candidate(directory, template, original_request)
    if candidate.lean_file.resolve() != request.lean_file:
        raise ValueError("Putnam candidate is not the admitted answer file")
    problem = _resolve_theorem_project(
        dataclasses.replace(
            request, description=candidate.description_path.read_text(encoding="utf-8")
        ),
        adapter_id=PUTNAMBENCH_ADAPTER_ID,
    )
    return with_theorem_execution_context(
        problem,
        preamble=problem.preamble,
        lean_preamble=problem.lean_preamble,
        adapter_metadata={
            "machine_proposed_answer": True,
            "answer_original_source_path": str(original_request.lean_file),
            "answer_original_source_sha256": hashlib.sha256(
                template.original_bytes
            ).hexdigest(),
            "answer_template_sha256": hashlib.sha256(
                template.source.encode("utf-8")
            ).hexdigest(),
            "answer_candidate_sha256": candidate.source_sha256,
            "excluded_source_paths": [
                str(original_request.lean_file),
                str(directory / "original.lean"),
            ],
            "exclude_entire_source_from_retrieval": True,
        },
    )

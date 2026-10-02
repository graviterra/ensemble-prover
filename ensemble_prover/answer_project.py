"""Load source-bound machine answers without granting mathematical authority."""

from __future__ import annotations

import dataclasses
import hashlib
import json
import re
from pathlib import Path
from typing import Callable

from .answer_input import AnswerTemplate, find_answer_template, load_candidate
from .nl_input import _unique_fields
from .theorem_project import (
    GENERIC_ADAPTER_ID, TheoremProblem, TheoremProjectRequest,
    _resolve_theorem_project, with_theorem_execution_context,
)


def has_answer_candidate_receipt(request: TheoremProjectRequest) -> bool:
    """Find a named admitted artifact without granting authority by filename.

    Internal discovery validates proposals through the raw theorem resolver.
    Public candidate opens always use the complete handoff verifier.
    A damaged adjacent receipt cannot silently demote a reserved candidate file
    to an ordinary theorem; unrelated neighboring Lean files remain ordinary.
    """
    path = Path(request.lean_file).expanduser().resolve()
    receipt_path = path.parent / "answer_discovery.json"
    if not receipt_path.exists() and not receipt_path.is_symlink():
        return False
    reserved_name = re.fullmatch(r"candidate_[0-9]+\.lean", path.name) is not None
    try:
        record = json.loads(receipt_path.read_bytes(), object_pairs_hook=_unique_fields)
        if not isinstance(record, dict):
            raise ValueError("invalid answer discovery receipt")
    except (OSError, ValueError, UnicodeError, RecursionError):
        if reserved_name:
            raise ValueError("cannot verify the adjacent answer candidate receipt") from None
        return False
    attempts = record.get("attempts")
    last = attempts[-1] if isinstance(attempts, list) and attempts else None
    return (reserved_name or record.get("candidate_file") == path.name
            or isinstance(last, dict) and last.get("candidate_file") == path.name)


def load_answer_project(
    request: TheoremProjectRequest, *,
    template_finder: Callable[[str, str | None], AnswerTemplate | None] = find_answer_template,
    adapter_id: str = GENERIC_ADAPTER_ID,
    label: str = "Answer",
) -> TheoremProblem:
    """Validate the discovery receipt on every startup/resume, then load Lean."""
    request = request.normalized()
    directory = request.lean_file.parent
    record = json.loads(
        (directory / "answer_discovery.json").read_bytes(),
        object_pairs_hook=_unique_fields,
    )
    origin = record.get("input_request") if isinstance(record, dict) else None
    if (
        not isinstance(origin, dict)
        or any(not isinstance(origin.get(key), str) or not origin[key]
               for key in ("lean_file", "theorem_name", "project_path"))
        or any(not isinstance(origin.get(key), list)
               or any(not isinstance(item, str) for item in origin[key])
               for key in ("imports", "source_dirs"))
        or "description" not in origin
        or (origin["description"] is not None and not isinstance(origin["description"], str))
    ):
        raise ValueError(f"{label} candidate has an invalid original question receipt")
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
            f"{label} candidate execution context differs from its discovery receipt"
        )
    source = original_request.lean_file.read_bytes().decode("utf-8")
    template = template_finder(source, request.theorem_name)
    if template is None:
        raise ValueError(f"{label} candidate has no original answer question")
    candidate = load_candidate(directory, template, original_request)
    if candidate.lean_file.resolve() != request.lean_file:
        raise ValueError(f"{label} candidate is not the admitted answer file")
    problem = _resolve_theorem_project(
        dataclasses.replace(
            request, description=candidate.description_path.read_text(encoding="utf-8")
        ),
        adapter_id=adapter_id,
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

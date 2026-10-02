"""Keep independently checked source imports in the session's structured context."""

from dataclasses import replace
from typing import Any

from ensemble_prover.mini_theory.context import TheoryContext, TheoryContextPair


def source_import_context(pair: TheoryContextPair, module: str) -> TheoryContextPair:
    """Append one complete Lean module name, preserving quoted identifiers."""
    if not isinstance(module, str) or not module:
        raise ValueError("Invalid source import module")
    parsed = TheoryContext.from_preamble("import " + module)
    if (parsed.base_imports != (module,) or parsed.base_header
            or parsed.base_preamble):
        raise ValueError("Source import must name exactly one module")

    def extend(context: TheoryContext) -> TheoryContext:
        return replace(context, base_imports=tuple(dict.fromkeys(
            (*context.base_imports, module),
        )))

    return replace(pair, llm=extend(pair.llm), lean=extend(pair.lean))


def prepare_source_import(session: Any, module: str) -> TheoryContextPair:
    """Prepare without mutating the session before independent Lean admission."""
    pair = getattr(session, "theory_context_pair", None)
    if pair is None:
        pair = TheoryContextPair.from_preambles(
            llm_preamble=session.conv.preamble,
            lean_preamble=session.conv.lean_preamble,
        )
    elif (pair.llm.render() != session.conv.preamble
          or pair.lean.render() != session.conv.lean_preamble):
        raise ValueError("Source import context differs from the live session")
    return source_import_context(pair, module)


def apply_source_import(
    session: Any, pair: TheoryContextPair, *, module: str,
    declaration: str, statement: str,
) -> None:
    """Commit the checked context and its replayable admission together."""
    if prepare_source_import(session, module) != pair:
        raise ValueError("Source import context changed during admission")
    previous = getattr(session, "theory_context_pair", None)
    if previous is None:
        previous = TheoryContextPair.from_preambles(
            llm_preamble=session.conv.preamble,
            lean_preamble=session.conv.lean_preamble,
        )
    if not hasattr(session, "_checkpoint_initial_theory_context_hash"):
        session._checkpoint_initial_theory_context_hash = previous.snapshot_hash
    receipt = {"module": module, "declaration": declaration, "statement": statement}
    receipts = list(getattr(session, "_checked_source_imports", ()))
    if receipt not in receipts:
        receipts.append(receipt)
    session._checked_source_imports = receipts
    session.theory_context_pair = pair
    session.conv.preamble = pair.llm.render()
    session.conv.lean_preamble = pair.lean.render()

"""Fresh typed evidence for accepted helpers with ambiguous surface binders."""

from __future__ import annotations

import copy
import asyncio
import logging
import inspect
import re
import time
from typing import Any, Callable, Mapping, Sequence

from .contract_identity import (
    has_lean_contract_identity,
    make_lean_contract_binder_evidence_receipt,
    make_lean_contract_evidence_receipt,
    lean_contract_statement_source_key,
)
from .lean_runner import LeanStatementContractAnalysis
from .proof_graph import graph_statement_contract_ambiguities


_LOGGER = logging.getLogger(__name__)
_SCOPE_CLASSIFICATION_MAX_CHARS = 16_384
_SCOPE_COMMAND = re.compile(
    r"\b(?:namespace|section|end|open|export|local|scoped|notation|infix|infixl|infixr|"
    r"prefix|postfix|syntax|macro|macro_rules|elab|elab_rules|initialize|run_cmd|"
    r"variable|variables|include|omit|parameter|parameters|axiom|constant|constants|"
    r"attribute|set_option|def|abbrev|opaque|instance|structure|class|inductive)\b"
)


def _plain_root_theorem(source: str) -> bool:
    from .proof_graph import _large_lexical_result

    return _large_lexical_result(
        ("contract_plain_root_theorem", source), lambda: _uncached_plain_root_theorem(source),
    )


def _uncached_plain_root_theorem(source: str) -> bool:
    from .lean_source_lexing import _mask_noncode
    from .proof_graph import _helper_decl_header, _graph_looks_like_proof_premise_type, helper_decl_statement
    from .proof_state import lean_statement_bound_names

    header = _helper_decl_header(source)
    if header is None or header[0] not in {"theorem", "lemma"} or "." in header[1]:
        return False
    masked = _mask_noncode(source, mask_quoted_identifiers=True)
    if any(
        not _graph_looks_like_proof_premise_type(name, ("h",)) or name in {"True", "False"}
        for name in lean_statement_bound_names(helper_decl_statement(source))
    ):
        return False
    return bool(re.match(r"^\s*(?:theorem|lemma)\b", masked)) and not _SCOPE_COMMAND.search(masked)


def _import_only_preamble(preamble: str) -> bool:
    from .proof_graph import _large_lexical_result

    return _large_lexical_result(
        ("contract_import_only_preamble", preamble), lambda: _uncached_import_only_preamble(preamble),
    )


def _uncached_import_only_preamble(preamble: str) -> bool:
    from .lean_source_lexing import _mask_noncode, _scan_lean_header

    # Only these trusted standard-library entry points retain their ordinary
    # syntax assumption. Project modules may redefine even familiar names.
    commands, body_start = _scan_lean_header(preamble)
    return not _mask_noncode(preamble[body_start:]).strip() and all(
        command.kind == "import"
        and preamble[command.module_start:command.end] in {"Init", "Lean", "Std", "Mathlib"}
        for command in commands
    )


def helper_contract_context_is_plain(lean: Any, *, preamble: str, context: Sequence[str]) -> bool:
    """Allow surface sorts only in an import-only root with plain theorem prefixes."""
    from .lean_source_lexing import _mask_noncode

    config = getattr(lean, "cfg", None)
    configured = str(getattr(config, "preamble_tactics", "") or "")
    if (
        len(preamble) > _SCOPE_CLASSIFICATION_MAX_CHARS
        or len(configured) > _SCOPE_CLASSIFICATION_MAX_CHARS
        or not _import_only_preamble(preamble)
        or _mask_noncode(configured).strip()
        or getattr(config, "extra_imports", ())
        or getattr(config, "project_imports", ())
        or getattr(config, "project_import_sources", {})
        or getattr(config, "module_search_paths", ())
    ):
        return False
    return all(
        len(source) <= _SCOPE_CLASSIFICATION_MAX_CHARS and _plain_root_theorem(source)
        for source in context
    )


def helper_source_requires_contract_analysis(source: str, *, context_is_plain: bool) -> bool:
    """A known spelling such as Nat can name a proposition in a local scope."""
    from .proof_graph import helper_decl_statement

    statement = helper_decl_statement(source)
    return bool(
        "\n" in statement or "\r" in statement
        or graph_statement_contract_ambiguities(statement)
        or helper_source_contract_is_context_sensitive(source, context_is_plain=context_is_plain)
    )


def helper_source_contract_is_context_sensitive(source: str, *, context_is_plain: bool) -> bool:
    """Track scopes where surface type names cannot bind a checked declaration."""
    return bool(
        not context_is_plain
        or len(source) > _SCOPE_CLASSIFICATION_MAX_CHARS
        or not _plain_root_theorem(source)
    )


class _ContractAnalysisCancelled(BaseException):
    """Preserve explicit adapter cancellation across result-only watchdogs."""


async def analyze_verified_helper_declarations(
    lean: Any, sources: Sequence[str], *, preamble: str,
    environment_hash: str, timeout_s: float,
    context_is_current: Callable[[], bool] = lambda: True,
    bind_source_positions: bool = False,
) -> Mapping[str, Mapping[str, Any]]:
    """Observe actual constants in an independently checked declaration batch.

    Later declarations can change how earlier statement text elaborates. Only
    an analyzer that supports declared-constant observation can share a batch;
    callers retain prefix-specific analysis as the conservative fallback.
    """
    from .proof_dossier import helper_decl_name, helper_decl_statement

    analyzer = getattr(lean, "analyze_statement_contracts", None)
    if not callable(analyzer):
        return {}
    try:
        supported = {"declaration_names", "declaration_context"} <= set(
            inspect.signature(analyzer).parameters
        )
    except (TypeError, ValueError):
        supported = False
    context_is_plain = helper_contract_context_is_plain(lean, preamble=preamble, context=sources)
    selected = tuple(source for source in sources if helper_source_requires_contract_analysis(
        source, context_is_plain=context_is_plain,
    ))
    if not supported or not selected or timeout_s <= 0 or not context_is_current():
        return {}
    statements = tuple(helper_decl_statement(source) for source in selected)
    names = tuple(helper_decl_name(source) for source in selected)
    if not all(names) or len(set(names)) != len(names):
        return {}
    try:
        from .mini_formal_state_search import _run_serialized_lean_operation

        deadline = time.monotonic() + timeout_s

        async def analyze() -> Any:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return (), "contract analysis budget exhausted", 1
            try:
                return await analyzer(
                    statements, declaration_names=names,
                    preamble_override=preamble, declaration_context=tuple(sources),
                    timeout_s=remaining,
                    **({"declaration_sources": selected} if bind_source_positions
                       and "declaration_sources" in inspect.signature(analyzer).parameters else {}),
                )
            except asyncio.CancelledError as exc:
                raise _ContractAnalysisCancelled from exc

        analyses, _output, returncode = await _run_serialized_lean_operation(
            lean, analyze, operation_timeout_s=timeout_s, admission_timeout_s=timeout_s,
        )
        if returncode != 0 or len(analyses) != len(selected) or not context_is_current():
            return {}
        return {
            source: fields
            for source, statement, analysis in zip(selected, statements, analyses)
            if (fields := verified_helper_contract_fields(
                analysis, statement=statement, environment_hash=environment_hash,
            ))
        }
    except _ContractAnalysisCancelled as exc:
        raise asyncio.CancelledError from exc
    except Exception:
        _LOGGER.debug("Accepted helper declaration analysis unavailable", exc_info=True)
        return {}


async def analyze_verified_helper_contract(
    lean: Any,
    statement: str,
    *,
    preamble: str,
    context: Sequence[str],
    environment_hash: str,
    timeout_s: float,
    context_is_current: Callable[[], bool] = lambda: True,
    declaration_source: str = "",
) -> Mapping[str, Any]:
    """Enrich a proved declaration; incomplete evidence never relaxes policy.

    Call only after body verification. Known surface sorts avoid another Lean
    operation. Failure is advisory, cancellation propagates, and callers retain
    ownership of their acceptance deadline and publication transaction.
    """

    analyzer = getattr(lean, "analyze_statement_contracts", None)
    if (
        not callable(analyzer)
        or timeout_s <= 0
        or not (
            helper_source_requires_contract_analysis(
                declaration_source,
                context_is_plain=helper_contract_context_is_plain(lean, preamble=preamble, context=context),
            ) if declaration_source else graph_statement_contract_ambiguities(statement)
        )
        or not context_is_current()
    ):
        return {}
    observation_options: dict[str, Any] = {}
    if declaration_source:
        from .proof_dossier import helper_decl_name

        try:
            supported = {"declaration_sources", "declaration_context"} <= set(
                inspect.signature(analyzer).parameters
            )
        except (TypeError, ValueError):
            supported = False
        name = helper_decl_name(declaration_source)
        if not supported or not name:
            return {}
        observation_options = {
            "declaration_names": (name,),
            "declaration_sources": (declaration_source,),
            "declaration_context": (*context, declaration_source),
        }
    try:
        from .mini_formal_state_search import _run_serialized_lean_operation

        deadline = time.monotonic() + timeout_s

        async def analyze() -> Any:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return (), "contract analysis budget exhausted", 1
            try:
                return await analyzer(
                    [statement],
                    preamble_override=preamble if declaration_source else "\n\n".join(
                        part for part in (preamble, *context, declaration_source) if part
                    ),
                    timeout_s=remaining,
                    **observation_options,
                )
            except asyncio.CancelledError as exc:
                raise _ContractAnalysisCancelled from exc

        # Use the existing Lean lease/watchdog: a cancellation-resistant tail
        # keeps its lease until it stops, and cannot publish a late receipt.
        # Lean owns its process deadline; the outer guard includes teardown
        # headroom instead of racing the process at the same instant.
        analyses, _output, returncode = await _run_serialized_lean_operation(
            lean, analyze, operation_timeout_s=timeout_s,
            admission_timeout_s=timeout_s,
        )
        analysis = analyses[0] if len(analyses) == 1 else None
        if returncode != 0 or not context_is_current():
            return {}
        return verified_helper_contract_fields(
            analysis, statement=statement, environment_hash=environment_hash,
        )
    except _ContractAnalysisCancelled as exc:
        raise asyncio.CancelledError from exc
    except Exception:
        # A transient analysis failure cannot erase a completed body check.
        # The empty result keeps conservative visibility; it is not cached.
        _LOGGER.debug("Accepted helper binder analysis unavailable", exc_info=True)
        return {}


async def analyze_verified_helper_source_contract(
    lean: Any, source: str, *, preamble: str, context: Sequence[str],
    environment_hash: str, timeout_s: float,
    context_is_current: Callable[[], bool] = lambda: True,
) -> Mapping[str, Any]:
    """Observe the checked declaration at its original identifier source span.

    Qualified declarations elaborate their types inside their own namespace.
    Re-elaborating extracted statement text in the ambient namespace can change
    a proof binder into data. Source-bound observation reads the kernel type;
    an adapter without this capability leaves typed evidence unavailable.
    """
    from .proof_dossier import helper_decl_statement

    return await analyze_verified_helper_contract(
        lean, helper_decl_statement(source), preamble=preamble, context=context,
        environment_hash=environment_hash, timeout_s=timeout_s,
        context_is_current=context_is_current, declaration_source=source,
    )


def helper_contract_runner_context(lean: Any) -> tuple[Any, ...]:
    """Snapshot configured statement meaning without scanning imported files."""
    from pathlib import Path
    from .lean_runner import LeanREPL
    from .formalization.environment import runtime_selector_snapshot

    config = getattr(lean, "cfg", None)
    raw_project = getattr(lean, "project_dir", "")
    project = str(Path(raw_project).resolve()) if raw_project else ""
    epoch = LeanREPL.global_env_epoch(project)
    path = str(getattr(config, "resolved_lean_path", "") or "").strip()
    executable = str(getattr(config, "resolved_lean_executable", "") or "").strip()
    configured_epoch = getattr(config, "resolved_lean_environment_epoch", None)
    if configured_epoch is None and epoch == 0 and path and executable:
        configured_epoch = 0
    return (
        id(config), project, getattr(lean, "_execution_environment_generation", 0), epoch,
        tuple(copy.deepcopy(getattr(config, name, None)) for name in (
            "project_dir", "preamble_import", "preamble_tactics", "extra_imports",
            "project_imports", "project_import_sources", "support_project_builds",
            "module_search_paths",
        )),
        runtime_selector_snapshot(),
        (path, executable, configured_epoch if path or executable else None),
    )


def helper_contract_context_guard(lean: Any) -> Callable[[], bool]:
    """Keep analysis in the checked context, permitting authenticated bootstrap."""
    import os
    from .lean_runner import LeanREPL

    def live_coordinates() -> tuple[str, str] | None:
        repl = getattr(lean, "_repl", None)
        admitted = repl._admit_check_environment() if isinstance(repl, LeanREPL) else None
        if admitted is None:
            return None
        executable, environment = admitted
        return environment.get("LEAN_PATH", ""), executable

    expected = helper_contract_runner_context(lean)
    with LeanREPL._GLOBAL_ENV_CACHE_LOCK:
        known_coordinates = LeanREPL._GLOBAL_ENV_CACHE.get(expected[1])
    known_live_coordinates = live_coordinates()

    def current() -> bool:
        nonlocal expected, known_coordinates, known_live_coordinates
        observed = helper_contract_runner_context(lean)
        with LeanREPL._GLOBAL_ENV_CACHE_LOCK:
            current_coordinates = LeanREPL._GLOBAL_ENV_CACHE.get(expected[1])
        if known_coordinates is not None and current_coordinates != known_coordinates:
            return False
        if known_coordinates is None and current_coordinates is not None:
            known_coordinates = current_coordinates
        current_live_coordinates = live_coordinates()
        if current_live_coordinates is not None:
            if known_live_coordinates is not None and current_live_coordinates != known_live_coordinates:
                return False
            if known_live_coordinates is None:
                roots = tuple(dict.fromkeys(
                    str(root) for root in getattr(getattr(lean, "cfg", None), "module_search_paths", ())
                    if str(root).strip()
                ))
                base_pairs = [pair for pair in (known_coordinates, expected[-1][:2])
                              if pair is not None and all(pair)]
                if current_live_coordinates not in {
                    (os.pathsep.join((*roots, path)), executable) for path, executable in base_pairs
                }:
                    return False
                known_live_coordinates = current_live_coordinates
        if observed == expected:
            return True
        if observed[:-1] != expected[:-1] or expected[-1] != ("", "", None):
            return False
        path, executable, epoch = observed[-1]
        if not path or not executable or type(epoch) is not int or epoch != expected[3]:
            return False
        if known_coordinates is not None and known_coordinates != (path, executable):
            return False
        # The runner's public pre-resolved binding only changes its config.
        # Normal lazy resolution must also have an authenticated Lake cache
        # entry at this same generation. Freeze that first resolved pair.
        with LeanREPL._GLOBAL_ENV_CACHE_LOCK:
            if (LeanREPL._GLOBAL_ENV_CACHE.get(expected[1]) != (path, executable)
                    or LeanREPL._GLOBAL_ENV_EPOCH.get(expected[1], 0) != epoch):
                return False
        expected = observed
        return True

    return current


async def analyze_verified_helper_context(
    lean: Any, sources: Sequence[str], *, preamble: str,
    environment_hash: str, timeout_s: float,
    context_is_current: Callable[[], bool] = lambda: True,
) -> Mapping[str, Mapping[str, Any]]:
    """Enrich a checked context under one deadline, retaining missing-type policy.

    Observe declarations together first. Source-specific fallback is needed
    only for declarations that the final namespace could not identify. The
    caller still owns the checked-source transaction and publication guard.
    """
    runner_is_current = helper_contract_context_guard(lean)

    def current() -> bool:
        return context_is_current() and runner_is_current()

    def require_current() -> None:
        if not current():
            raise ValueError("checked Lean context changed during helper contract observation")

    require_current()
    sources = tuple(sources)
    deadline = time.monotonic() + max(0.0, timeout_s)
    observations = await analyze_verified_helper_declarations(
        lean, sources, preamble=preamble, environment_hash=environment_hash,
        timeout_s=max(0.0, deadline - time.monotonic()),
        context_is_current=current,
        bind_source_positions=True,
    )
    require_current()
    prefix: list[str] = []
    prefix_is_plain = helper_contract_context_is_plain(lean, preamble=preamble, context=())
    result: dict[str, Mapping[str, Any]] = {}
    for source in sources:
        require_current()
        required = helper_source_contract_is_context_sensitive(source, context_is_plain=prefix_is_plain)
        fields = observations.get(source, {})
        if not fields and helper_source_requires_contract_analysis(source, context_is_plain=prefix_is_plain):
            fields = await analyze_verified_helper_source_contract(
                lean, source, preamble=preamble, context=tuple(prefix),
                environment_hash=environment_hash,
                timeout_s=max(0.0, deadline - time.monotonic()),
                context_is_current=current,
            )
            require_current()
        result[source] = {"contract_observation_required": required, **fields}
        prefix.append(source)
        prefix_is_plain = prefix_is_plain and not required
    require_current()
    return result


def verified_helper_contract_fields(
    analysis: Any, *, statement: str, environment_hash: str,
) -> Mapping[str, Any]:
    """Bind a complete fresh Lean observation to its exact source statement."""
    if (
        not isinstance(analysis, LeanStatementContractAnalysis)
        or not has_lean_contract_identity(analysis.structural_identity)
        or (not analysis.binder_sorts and not analysis.profile_complete)
        or any(sort not in {"proof", "data"} for sort in analysis.binder_sorts)
        or len(analysis.binder_types) != len(analysis.binder_sorts)
        or any(not isinstance(value, str) or not value.strip()
               for value in analysis.binder_types)
        or analysis.binder_sorts.count("proof") != len(analysis.proof_binder_types)
        or any(not isinstance(value, str) or not value.strip()
               for value in analysis.proof_binder_types)
    ):
        return {}
    return {
        "contract_identity": analysis.structural_identity,
        "contract_display_statement": analysis.display_type,
        "contract_binder_sorts": tuple(analysis.binder_sorts),
        "contract_proof_binder_types": tuple(analysis.proof_binder_types),
        "_contract_identity_statement": statement,
        "_verification_environment_hash": environment_hash,
        "_contract_binder_observation_complete": True,
    }


def refresh_verified_helper_contract(
    dossier: Any, helper: Any, fields: Mapping[str, Any], *, contract_observation_required: bool = False,
) -> bool:
    """Attach fresh same-environment evidence through the normal import gate."""

    if not fields and not contract_observation_required:
        return False
    incoming = copy.deepcopy(helper)
    incoming.contract_observation_required = bool(
        getattr(incoming, "contract_observation_required", False) or contract_observation_required
    )
    if not fields:
        return bool(dossier.refresh_imported_verified_helper_evidence(helper.name, incoming))
    for name in (
        "contract_identity", "contract_display_statement",
        "contract_binder_sorts", "contract_proof_binder_types",
    ):
        value = fields[name]
        setattr(incoming, name, list(value) if isinstance(value, tuple) else value)
    key = lean_contract_statement_source_key(fields["_contract_identity_statement"])
    environment = str(fields["_verification_environment_hash"])
    incoming.contract_identity_statement_key = key
    incoming.contract_identity_environment_hash = environment
    incoming.contract_identity_evidence_receipt = make_lean_contract_evidence_receipt(
        incoming.contract_identity, key, environment,
    )
    incoming.contract_binder_evidence_receipt = make_lean_contract_binder_evidence_receipt(
        incoming.contract_identity, key, environment,
        tuple(incoming.contract_binder_sorts), tuple(incoming.contract_proof_binder_types),
        allow_empty_binders=True,
    )
    return bool(dossier.refresh_imported_verified_helper_evidence(helper.name, incoming))

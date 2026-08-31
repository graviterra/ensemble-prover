"""Retrieve, validate, and activate mathematical premises before proof search."""

from __future__ import annotations

import time
from typing import Any, ClassVar, FrozenSet

from ...proof_dossier import text_hash
from ...theorem_project import merge_imports
from ..action import MiniOutcome


class PremiseRetrievalAction:
    id: str = "premise_retrieval"
    priority: int = 5
    cost_estimate_s: float = 0.05
    WRITES: ClassVar[FrozenSet[str]] = frozenset({"session_state"})  # writes to session.last_premise_block

    def __init__(self, *, top_k: int = 8) -> None:
        self.top_k = int(top_k or 0)
        self._fired = False



    def is_applicable(self, session: Any) -> bool:
        if self._fired:
            return False
        if self.top_k <= 0:
            return False
        if session.searcher is None:
            return False
        if session.problem is None:
            return False
        return True

    def frontier_is_applicable_probe(self, session: Any) -> bool:
        """Read-only scheduler probe.

        Premise retrieval's applicability is pure today, but exposing the
        explicit protocol prevents scheduler quotation from silently falling
        back to an arbitrary future ``is_applicable`` implementation.
        """

        return self.is_applicable(session)

    async def run(self, session: Any) -> MiniOutcome:
        from ensemble_prover.premise_retrieval import (
            format_premise_block,
            record_premise_retrieval_metrics,
            retrieve_premise_record_async,
        )
        from ensemble_prover.proof_dossier import active_root_target_statement

        started = time.monotonic()
        budget = dict(getattr(session, "budgets", {}) or {}).get(self.id)
        action_cap_s = float(getattr(budget, "max_total_seconds", 0.0) or 0.0)
        already_spent_s = float(getattr(budget, "total_seconds", 0.0) or 0.0)
        action_deadline = (
            started + max(0.05, action_cap_s - already_spent_s)
            if action_cap_s > 0.0
            else float("inf")
        )

        def remaining_s() -> float:
            return max(0.0, action_deadline - time.monotonic())

        def action_deadline_exhausted() -> bool:
            return remaining_s() <= 0.0

        activated_bundle_ids: tuple[str, ...] = ()
        rechecked_helper_names: tuple[str, ...] = ()
        imported_project_modules: tuple[str, ...] = ()
        imported_modules: tuple[str, ...] = ()
        activation_errors: list[str] = []
        goal_statement = (
            active_root_target_statement(
                getattr(session, "dossier", None),
                require_single=True,
                require_no_hypotheses=False,
                include_hypotheses=True,
            )
            or str(
                getattr(getattr(session, "dossier", None), "root_statement", "")
                or ""
            ).strip()
            or getattr(session.problem, "statement_type", "")
        )
        try:
            retrieval_timeout_s = max(
                0.01,
                min(
                    remaining_s(),
                    float(
                        getattr(session.searcher, "operation_timeout_s", 30.0)
                        or 30.0
                    ),
                ),
            )
            retrieval_record = await retrieve_premise_record_async(
                session.searcher,
                goal_statement=goal_statement,
                exploration=None,
                top_k=self.top_k,
                timeout_s=retrieval_timeout_s,
                deadline_monotonic=(
                    action_deadline
                    if action_deadline != float("inf")
                    else None
                ),
                deadline_exhausted=action_deadline_exhausted,
            )
            hits = list(getattr(retrieval_record, "hits", ()) or ())
            # A lower-ranked imported fallback must not suppress activation of
            # the most relevant project/theory/helper discovery candidate.
            already_usable = bool(
                hits
                and str(getattr(hits[0], "availability", "") or "")
                == "already_imported"
            )
            if not already_usable:
                from ensemble_prover.proof_state_executor import (
                    _accept_proof_state_helper,
                )

                for hit in hits[:1]:
                    if (
                        str(getattr(hit, "availability", "") or "")
                        != "requires_helper_recheck"
                    ):
                        continue
                    helper_source = str(
                        getattr(hit, "helper_source", "") or ""
                    ).strip()
                    source_hash = str(
                        getattr(hit, "source_hash", "") or ""
                    ).strip()
                    if not helper_source or not source_hash:
                        continue
                    try:
                        acceptance_status: dict[str, Any] = {}
                        accepted = await _accept_proof_state_helper(
                            lean=session.lean,
                            conv=session.conv,
                            dossier=session.dossier,
                            helper_block=helper_source,
                            phase="premise_retrieval_helper_recheck",
                            turn_index=int(getattr(session, "iteration", 0) or 0),
                            timeout_s=max(
                                0.1,
                                float(
                                    getattr(
                                        session,
                                        "proof_cache_seed_timeout_s",
                                        12.0,
                                    )
                                    or 12.0
                                ),
                            ),
                            proof_cache=None,
                            proof_state=getattr(session, "proof_state", None),
                            target_statement=goal_statement,
                            require_relevance_gate=True,
                            deadline_exhausted=action_deadline_exhausted,
                            deadline_monotonic=action_deadline,
                            status_out=acceptance_status,
                            verified_helper_accept_callback=getattr(
                                session,
                                "theory_verified_helper_accept_callback",
                                None,
                            ),
                        )
                    except Exception as exc:
                        activation_errors.append(
                            "helper recheck "
                            f"{getattr(hit, 'name', '?')}: "
                            f"{type(exc).__name__}: {exc}"
                        )
                        continue
                    if not accepted:
                        continue
                    mark_rechecked = getattr(
                        session.searcher,
                        "mark_verified_helper_rechecked",
                        None,
                    )
                    if callable(mark_rechecked):
                        landed_name = str(
                            acceptance_status.get("accepted_helper_name")
                            or getattr(hit, "name", "")
                        )
                        try:
                            mark_rechecked(source_hash, helper_name=landed_name)
                        except TypeError:
                            mark_rechecked(source_hash)
                    rechecked_helper_names = (
                        str(
                            acceptance_status.get("accepted_helper_name")
                            or getattr(hit, "name", "")
                            or ""
                        ),
                    )
                    increment = getattr(session, "_increment_dossier_metric", None)
                    if callable(increment):
                        increment("mini_mathematical_retrieval_helper_rechecks", 1)
                    retrieval_record = await retrieve_premise_record_async(
                        session.searcher,
                        goal_statement=goal_statement,
                        exploration=None,
                        top_k=self.top_k,
                        timeout_s=max(
                            0.01,
                            min(retrieval_timeout_s, remaining_s()),
                        ),
                        deadline_monotonic=action_deadline,
                        deadline_exhausted=action_deadline_exhausted,
                    )
                    hits = list(getattr(retrieval_record, "hits", ()) or ())
                    already_usable = True
                    break
            if not already_usable:
                attempted_imports: set[tuple[str, str]] = set()
                for hit in hits:
                    if (
                        str(getattr(hit, "availability", "") or "")
                        != "importable"
                    ):
                        continue
                    module_name = str(
                        getattr(hit, "module_name", "") or ""
                    ).strip()
                    source_id = str(
                        getattr(hit, "source_id", "") or ""
                    ).strip()
                    declaration_name = str(
                        getattr(hit, "name", "") or ""
                    ).strip()
                    declaration_type = str(
                        getattr(hit, "full_type_signature", "")
                        or getattr(hit, "type_signature", "")
                        or ""
                    ).strip()
                    if not module_name or not source_id or not declaration_name or not declaration_type:
                        continue
                    import_key = (module_name, declaration_name)
                    if import_key in attempted_imports:
                        continue
                    attempted_imports.add(import_key)
                    current_lean_preamble = str(
                        getattr(session.conv, "lean_preamble", "")
                        or getattr(session.conv, "preamble", "")
                        or ""
                    )
                    proposed_preamble = merge_imports(
                        current_lean_preamble,
                        (module_name,),
                    )
                    try:
                        from ensemble_prover.proof_state_executor import (
                            _await_serialized_lean_operation,
                        )

                        lean_timeout_s = max(
                            0.01,
                            min(
                                remaining_s(),
                                float(
                                    getattr(
                                        session,
                                        "proof_cache_seed_timeout_s",
                                        12.0,
                                    )
                                    or 12.0
                                ),
                            ),
                        )
                        probe = await _await_serialized_lean_operation(
                            session.lean,
                            lambda: session.lean.check(
                                declaration_type,
                                f"by exact @{declaration_name}",
                                [],
                                preamble_override=proposed_preamble,
                                timeout_s=lean_timeout_s,
                                check_kind="precheck",
                            ),
                            timeout_s=lean_timeout_s,
                            deadline_monotonic=action_deadline,
                        )
                    except Exception as exc:
                        activation_errors.append(
                            f"project import {module_name}: "
                            f"{type(exc).__name__}: {exc}"
                        )
                        continue
                    if not bool(getattr(probe, "ok", False)):
                        diagnostic = " ".join(
                            str(getattr(probe, "output", "") or "").split()
                        )[:300]
                        activation_errors.append(
                            f"project import {module_name}: Lean rejected import"
                            + (f": {diagnostic}" if diagnostic else "")
                        )
                        continue
                    if action_deadline_exhausted():
                        activation_errors.append(
                            f"project import {module_name}: action deadline exhausted"
                        )
                        break
                    session.conv.lean_preamble = proposed_preamble
                    if session.dossier is not None:
                        previous_environment_hash = str(
                            getattr(
                                session.dossier,
                                "current_lean_environment_hash",
                                "",
                            )
                            or ""
                        )
                        next_environment_hash = text_hash(proposed_preamble)
                        record_environment = getattr(
                            session.dossier,
                            "record_lean_environment",
                            None,
                        )
                        if callable(record_environment):
                            try:
                                record_environment(
                                    next_environment_hash,
                                    extends_environment_hash=(
                                        previous_environment_hash
                                    ),
                                    environment_source_text=proposed_preamble,
                                )
                            except TypeError:
                                # Lightweight dossiers may predate the
                                # content-verified ancestry signature.
                                record_environment(
                                    next_environment_hash,
                                    extends_environment_hash=(
                                        previous_environment_hash
                                    ),
                                )
                        else:
                            session.dossier.current_lean_environment_hash = (
                                next_environment_hash
                            )
                    llm_preamble = str(getattr(session.conv, "preamble", "") or "")
                    session.conv.preamble = merge_imports(
                        llm_preamble,
                        (module_name,),
                    )
                    source_kind = str(
                        getattr(hit, "source_kind", "") or ""
                    )
                    if source_kind == "project":
                        mark_declaration = getattr(
                            session.searcher,
                            "mark_source_declaration_imported",
                            None,
                        )
                        project_source_ids = tuple(
                            getattr(hit, "project_origin_source_ids", ()) or ()
                        ) or (source_id,)
                        for project_source_id in project_source_ids:
                            if callable(mark_declaration):
                                mark_declaration(
                                    project_source_id,
                                    module_name,
                                    declaration_name,
                                    declaration_type,
                                )
                            activation_record = {
                                "source_id": project_source_id,
                                "module_name": module_name,
                                "declaration_name": declaration_name,
                                "declaration_type": declaration_type,
                            }
                            if activation_record not in session.retrieval_imported_declarations:
                                session.retrieval_imported_declarations.append(
                                    activation_record
                                )
                    else:
                        mark_imported = getattr(
                            session.searcher,
                            "mark_source_module_imported",
                            None,
                        )
                        if callable(mark_imported):
                            mark_imported(source_id, module_name)
                        source_modules = session.retrieval_imported_source_modules.setdefault(
                            source_id,
                            [],
                        )
                        if isinstance(source_modules, str):
                            source_modules = [source_modules]
                            session.retrieval_imported_source_modules[source_id] = source_modules
                        if module_name not in source_modules:
                            source_modules.append(module_name)
                    imported_modules = (module_name,)
                    if source_kind == "project":
                        imported_project_modules = (module_name,)
                    increment = getattr(session, "_increment_dossier_metric", None)
                    if callable(increment):
                        increment("mini_mathematical_retrieval_module_imports", 1)
                        if imported_project_modules:
                            increment("mini_mathematical_retrieval_project_imports", 1)
                    retrieval_record = await retrieve_premise_record_async(
                        session.searcher,
                        goal_statement=goal_statement,
                        exploration=None,
                        top_k=self.top_k,
                        timeout_s=max(
                            0.01,
                            min(retrieval_timeout_s, remaining_s()),
                        ),
                        deadline_monotonic=action_deadline,
                        deadline_exhausted=action_deadline_exhausted,
                    )
                    hits = list(getattr(retrieval_record, "hits", ()) or ())
                    already_usable = True
                    break
            if not already_usable:
                attempted_bundles: set[tuple[str, ...]] = set()
                for hit in hits:
                    bundle_ids = tuple(
                        str(item).strip()
                        for item in (
                            getattr(hit, "required_bundle_ids", ()) or ()
                        )
                        if str(item).strip()
                    )
                    if not bundle_ids or bundle_ids in attempted_bundles:
                        continue
                    attempted_bundles.add(bundle_ids)
                    activation_succeeded = False
                    try:
                        from ensemble_prover.mathematical_retrieval.async_runtime import (
                            run_sync_abandonment_safe,
                        )

                        theory_lock_getter = getattr(
                            session.searcher,
                            "theory_operation_lock",
                            None,
                        )
                        theory_lock = (
                            theory_lock_getter(session.theory_library)
                            if callable(theory_lock_getter)
                            else None
                        )

                        def prepare_theory() -> Any:
                            if theory_lock is None:
                                return session.prepare_theory_bundles(bundle_ids)
                            with theory_lock:
                                return session.prepare_theory_bundles(bundle_ids)

                        prepared = await run_sync_abandonment_safe(
                            prepare_theory,
                            timeout_s=max(
                                0.01,
                                min(
                                    remaining_s(),
                                    float(
                                        getattr(
                                            session.searcher,
                                            "operation_timeout_s",
                                            30.0,
                                        )
                                        or 30.0
                                    ),
                                ),
                            ),
                            deadline_exhausted=action_deadline_exhausted,
                        )
                        if (
                            prepared is not None
                            and not action_deadline_exhausted()
                            and session.apply_prepared_theory_bundles(prepared)
                        ):
                            activated_bundle_ids = bundle_ids
                            activation_succeeded = True
                            increment = getattr(
                                session,
                                "_increment_dossier_metric",
                                None,
                            )
                            if callable(increment):
                                increment(
                                    "mini_mathematical_retrieval_bundle_activations",
                                    len(bundle_ids),
                                )
                    except Exception as exc:
                        activation_errors.append(
                            "theory activation "
                            f"{','.join(bundle_ids)}: {type(exc).__name__}: {exc}"
                        )
                        continue
                    if not activation_succeeded:
                        activation_errors.append(
                            "theory activation "
                            f"{','.join(bundle_ids)}: prepared bundle was not applied"
                        )
                        continue
                    set_active = getattr(
                        session.searcher,
                        "set_active_bundle_ids",
                        None,
                    )
                    if callable(set_active):
                        set_active(
                            tuple(
                                getattr(
                                    session,
                                    "theory_imported_bundle_ids",
                                    (),
                                )
                                or ()
                            )
                        )
                    retrieval_record = await retrieve_premise_record_async(
                        session.searcher,
                        goal_statement=goal_statement,
                        exploration=None,
                        top_k=self.top_k,
                        timeout_s=max(
                            0.01,
                            min(retrieval_timeout_s, remaining_s()),
                        ),
                        deadline_monotonic=action_deadline,
                        deadline_exhausted=action_deadline_exhausted,
                    )
                    hits = list(getattr(retrieval_record, "hits", ()) or ())
                    break
            # Render from already-fetched hits even under a spent deadline —
            # format_premise_block is pure formatting, and discarding retrieved
            # premises just because the clock expired wastes the retrieval.
            block = format_premise_block(hits) if hits else ""
        except Exception as exc:
            cost = time.monotonic() - started
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={"error": f"{type(exc).__name__}: {exc}"},
                exception=exc,
            )
        cost = time.monotonic() - started
        # Stash the rendered block on the session so the
        # ConversationTurnAction (M1.5) can include it in the LLM prompt.
        if action_deadline_exhausted() and not hits:
            # No hits to publish and the clock is spent: mark the one-shot done.
            # When hits DO exist we fall through and publish them below rather
            # than discarding already-fetched premises forever.
            self._fired = True
            return MiniOutcome(
                action_id=self.id,
                solved=False,
                proof=None,
                helpers_added=(),
                progress=False,
                cost_seconds=cost,
                metadata={
                    "hit_count": 0,
                    "retrieval_deadline_exhausted": True,
                    "retrieval_activation_errors": activation_errors,
                },
            )
        session.last_premise_block = block
        session.last_premise_names = [
            str(getattr(hit, "name", "") or "").strip()
            for hit in list(hits or [])
            if str(getattr(hit, "name", "") or "").strip()
        ]
        # Installing a retrieval record creates new provider input even when
        # the prior target's block had already been injected.  Keep the block,
        # names, and injection state atomic so an A -> retrieve B -> switch B
        # sequence cannot misclassify the fresh B block as already shown and
        # clear it during target-local history retirement.
        session._last_premise_block_injected = False
        record_metadata = (
            retrieval_record.metadata()
            if hasattr(retrieval_record, "metadata")
            else {}
        )
        session.last_premise_retrieval_record = dict(record_metadata)
        policy_metadata = {}
        observe = getattr(session, "observe_premise_retrieval_record", None)
        if callable(observe):
            policy_metadata = dict(observe(record_metadata) or {})
        increment = getattr(session, "_increment_dossier_metric", None)
        if callable(increment):
            record_premise_retrieval_metrics(
                increment,
                record_metadata,
                policy_metadata,
            )
        self._fired = True
        return MiniOutcome(
            action_id=self.id,
            solved=False,
            proof=None,
            helpers_added=(),
            progress=False,  # premise retrieval doesn't itself prove anything
            cost_seconds=cost,
            metadata={
                "hit_count": len(hits) if hits else 0,
                "block_length": len(block),
                "retrieval_activated_bundle_ids": list(
                    activated_bundle_ids
                ),
                "retrieval_rechecked_helper_names": list(
                    rechecked_helper_names
                ),
                "retrieval_imported_project_modules": list(
                    imported_project_modules
                ),
                "retrieval_imported_modules": list(imported_modules),
                "retrieval_activation_errors": activation_errors,
                **record_metadata,
                **policy_metadata,
            },
        )

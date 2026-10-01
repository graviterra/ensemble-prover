"""Run-scoped memory projection and authorized source evidence delivery."""

from __future__ import annotations

import time
import sqlite3
import os
from pathlib import Path
from typing import Any

from console.live_math import memory_record
from ensemble_prover.mathematical_memory.evidence import (
    EvidenceRegistry,
    EvidenceSource,
    EvidenceUnavailable,
    MaterializedEvidenceStore,
)
from ensemble_prover.mathematical_memory.model import (
    EligibilityPolicy,
    content_digest,
    thaw,
)

DEFAULT_MEMORY_ROOT = Path.home() / ".local/share/ensemble-prover/mathematical-memory"
LEASE_SECONDS = 15


class MemoryBackend:
    """Resolve only the service-configured catalog; never a browser-supplied path."""

    def __init__(self, root: Path, *, catalog_factory: Any = None) -> None:
        self.root = Path(os.path.abspath(Path(root).expanduser()))
        self.catalog_factory = catalog_factory

    def context(self, attached: Any) -> tuple[Any, EligibilityPolicy]:
        cfg = attached.state.live_math.memory_config
        policy_record = attached.state.live_math.memory_policy
        if (
            cfg.get("mode") not in {"observe", "assist", "develop"}
            or not isinstance(cfg.get("root"), str)
            or not Path(cfg["root"]).is_absolute()
            or Path(cfg["root"]).absolute() != self.root
            or not policy_record
        ):
            raise EvidenceUnavailable("memory_configuration_unavailable")
        policy = EligibilityPolicy.from_record(policy_record)
        if not policy.visible_scopes:
            raise EvidenceUnavailable("memory_policy_unavailable")
        if self.catalog_factory is None:
            from ensemble_prover.mathematical_memory.catalog import MemoryCatalog

            if not self.root.is_dir():
                raise EvidenceUnavailable("memory_store_unavailable")
            catalog = MemoryCatalog(self.root, read_only=True)
        else:
            catalog = self.catalog_factory(self.root)
        return catalog, policy

    def project(self, attached: Any) -> dict[str, Any]:
        deadline = time.monotonic() + 1
        raw = attached.state.live_math.memory
        empty = {
            "mode": raw.get("mode", "off"),
            "status": "unavailable",
            "candidates": [],
            "applications": [],
            "obstructions": [],
            "proposals": [],
            "notes": [],
            "partial": True,
            "omitted": None,
            "eligibility_lease_until": 0,
            "goal_id": "",
            "environment_id": "",
            "policy_id": "",
        }
        if not raw:
            return empty
        try:
            catalog, policy = self.context(attached)
            if raw.get("policy_id") != policy.policy_id:
                return empty
            output = memory_record(raw, scope=raw.get("scope", "problem"))
            hidden = False
            hidden_rows = False
            for group in (
                "candidates",
                "applications",
                "obstructions",
                "proposals",
                "notes",
            ):
                output[group] = []
                hidden_rows = hidden_rows or len(raw.get(group, ())) > 16
                for row in raw.get(group, ())[:16]:
                    if time.monotonic() >= deadline:
                        hidden = True
                        hidden_rows = True
                        break
                    event_id = row.get("event_id", "")
                    event = (
                        catalog.get_event(event_id, policy, deadline_monotonic=deadline)
                        if event_id
                        else None
                    )
                    if event is None:
                        hidden = True
                        hidden_rows = True
                        continue
                    # The trace only describes a report. Artifact availability
                    # comes from current source delivery checks, never its flag.
                    payload = thaw(event.payload)
                    proposal = payload.get("proposal")
                    if not isinstance(proposal, dict) and isinstance(
                        payload.get("result"), dict
                    ):
                        proposal = payload["result"].get("proposal")
                    if isinstance(proposal, dict):
                        for key in (
                            "statement",
                            "instance_ids",
                            "source_instances",
                            "changed_assumptions",
                            "specialization_links",
                            "intended_consumers",
                            "expected_use",
                            "observed_use",
                        ):
                            if key not in payload and key in proposal:
                                payload[key] = proposal[key]
                    recipe = (
                        payload.get("recipe")
                        if isinstance(payload.get("recipe"), dict)
                        else {}
                    )
                    payload.update(
                        event_id=event.event_id,
                        scope=event.provenance.scope,
                        name=payload.get("name")
                        or payload.get("declaration_name")
                        or recipe.get("declaration_name", ""),
                        operation=payload.get("operation") or recipe.get("kind", ""),
                        direction=payload.get("direction")
                        or recipe.get("direction", ""),
                        reason=payload.get("reason")
                        or "; ".join(
                            str(item) for item in payload.get("reasons", ())[:16]
                        ),
                        freshness="historical report",
                    )
                    copied = memory_record({group: [payload]})[group][0]
                    copied["evidence_digest"] = (
                        event.evidence[0].digest if event.evidence else ""
                    )
                    copied["evidence_digests"] = [
                        ref.digest for ref in event.evidence[:16]
                    ]
                    copied["artifact_available"] = False
                    if row.get("artifact_id"):
                        try:
                            binding, _data = self.read_artifact(
                                attached, row["artifact_id"], deadline=deadline
                            )
                            if binding.get("consumer_id") != event.event_id:
                                raise EvidenceUnavailable("artifact_event_mismatch")
                            copied["artifact_id"] = row["artifact_id"]
                            copied["artifact_available"] = True
                        except (EvidenceUnavailable, OSError, ValueError, sqlite3.Error):
                            pass
                    output[group].append(copied)
                    output["partial"] = (
                        output.get("partial", False) or copied["partial"]
                    )
            # Notes are durable campaign data even when a later action emits an
            # empty transient note list. They still use the same current policy.
            note_view = (
                catalog.query(
                    policy, kind="note", limit=16, deadline_monotonic=deadline
                )
                if time.monotonic() < deadline
                else None
            )
            if note_view is None:
                hidden = True
                output["omitted"] = None
            else:
                hidden = hidden or not note_view.complete
                notes = memory_record(
                    {
                        "notes": [
                            {
                                **thaw(event.payload),
                                "event_id": event.event_id,
                                "scope": event.provenance.scope,
                                "freshness": "historical report",
                            }
                            for event in note_view.events
                        ]
                    }
                )["notes"]
                existing_ids = {row["event_id"] for row in notes}
                merged = notes + [
                    row
                    for row in output["notes"]
                    if row["event_id"] not in existing_ids
                ]
                dropped = max(0, len(merged) - 16)
                output["notes"] = merged[:16]
                prior_omitted = output.get("omitted")
                if prior_omitted is None or note_view.omitted is None:
                    output["omitted"] = None
                else:
                    output["omitted"] = prior_omitted + note_view.omitted + dropped
                hidden = hidden or dropped > 0 or note_view.omitted not in (0, None)
            output["partial"] = output.get("partial", False) or hidden
            if hidden_rows:
                # Ineligible identities are not disclosed or counted. A
                # complete notes query cannot establish total trace coverage.
                output["omitted"] = None
            output["status"] = (
                "partial" if output["partial"] else raw.get("status", "observed")
            )
            output["eligibility_lease_until"] = time.time() + LEASE_SECONDS
            output["policy_id"] = policy.policy_id
            return output
        except (
            EvidenceUnavailable,
            sqlite3.Error,
            OSError,
            ValueError,
            KeyError,
            TypeError,
            RuntimeError,
        ):
            return empty

    def registry(
        self,
        catalog: Any,
        policy: EligibilityPolicy,
        event_id: str,
        digest: str,
        *,
        deadline: float | None = None,
    ) -> tuple[EvidenceRegistry, str]:
        event = catalog.get_event(event_id, policy, deadline_monotonic=deadline)
        if event is None:
            raise EvidenceUnavailable("source_ineligible")
        reference = next(
            (item for item in event.evidence if item.digest == digest), None
        )
        if reference is None:
            raise EvidenceUnavailable("evidence_unbound")
        evidence_id = content_digest({"event_id": event_id, "digest": digest})

        def allowed(provenance: Any, active_policy: Any) -> bool:
            current = catalog.get_event(
                event_id, active_policy, deadline_monotonic=deadline
            )
            return (
                current is not None
                and current.provenance == provenance
                and reference in current.evidence
            )

        def read(limit: int, deadline: float | None) -> bytes:
            if (
                reference.size > limit
                or deadline is not None
                and time.monotonic() >= deadline
            ):
                raise EvidenceUnavailable("evidence_limit")
            data = catalog.read_artifact(reference, deadline_monotonic=deadline)
            if deadline is not None and time.monotonic() >= deadline:
                raise EvidenceUnavailable("deadline_exhausted")
            return data

        registry = EvidenceRegistry()
        registry.register(
            evidence_id,
            EvidenceSource(
                reader=read,
                provenance=event.provenance,
                validator=allowed,
                reconciled=lambda: catalog.get_event(
                    event_id, policy, deadline_monotonic=deadline
                )
                is not None,
                digest=reference.digest,
                size=reference.size,
                store_id=content_digest(str(self.root)),
                consumer_id=event_id,
            ),
        )
        return registry, evidence_id

    def materialize(self, attached: Any, event_id: str, digest: str) -> dict[str, Any]:
        catalog, policy = self.context(attached)
        deadline = time.monotonic() + 1
        registry, evidence_id = self.registry(
            catalog, policy, event_id, digest, deadline=deadline
        )
        return MaterializedEvidenceStore(attached.run_dir, registry).materialize(
            evidence_id, policy, deadline_monotonic=deadline
        )

    def read_artifact(
        self, attached: Any, artifact_id: str, *, deadline: float | None = None
    ) -> tuple[dict[str, Any], bytes]:
        # Binding reads are descriptor-relative. Resolve the consumer event in
        # the service's trusted catalog, then the store repeats validation.
        from ensemble_prover.mathematical_memory.evidence import (
            contained_directory,
            read_contained,
        )
        import json
        import re

        if not re.fullmatch(r"[a-f0-9]{64}", artifact_id):
            raise EvidenceUnavailable("invalid_artifact")
        with contained_directory(attached.run_dir, "memory_evidence") as fd:
            binding = json.loads(
                read_contained(fd, f"{artifact_id}.json", 65536, deadline)
            )
        if not isinstance(binding, dict):
            raise EvidenceUnavailable("invalid_artifact_binding")
        catalog, policy = self.context(attached)
        registry, _evidence_id = self.registry(
            catalog,
            policy,
            binding.get("consumer_id", ""),
            binding.get("source_digest", ""),
            deadline=deadline,
        )
        return MaterializedEvidenceStore(attached.run_dir, registry).read(
            artifact_id, policy, deadline_monotonic=deadline
        )

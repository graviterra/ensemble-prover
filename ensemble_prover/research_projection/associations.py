"""Explicit advisory links stored independently of mathematical owners.

The host supplies the complete authoring inputs separately from proposal JSON.
Omitting those inputs cannot broaden a note: unestablished provenance remains
private to its operator authoring scope. All returned content is reauthorized.
"""

from __future__ import annotations

import json
import re
import sqlite3
from collections.abc import Iterator, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Any

from .policy import AccessContext, HostPolicy, PolicyRedactionError, assert_visible_output, authorize_envelope, context_binding, merge_envelopes, redact_output, redact_values
from .references import ProjectionError, canonical_json, sha256_digest, validate_ref
from .render import _selected_text, _selected_values, read_view_page


KINDS = frozenset({
    "investigates", "may_help", "related", "possibly_same_question",
    "proposed_sufficient", "proposed_necessary", "proposed_equivalent",
    "obstructed_under_scope",
})
STATUSES = frozenset({"proposed", "withdrawn", "superseded"})
_FIELDS = frozenset({
    "kind", "source", "target", "scope", "evidence_refs", "prose", "argument",
    "status", "relation_id", "expected_revision",
})
_HEX = re.compile(r"^[0-9a-f]{64}$")
_KEY = re.compile(r"^[A-Za-z0-9_.-]{1,160}$")
MAX_PROPOSALS = 16
MAX_INLINE_REFERENCES = 16
MAX_METADATA_BYTES = 32 * 1024
MAX_QUERY_CHARS = 4096
MAX_PROJECTED_BYTES = 128 * 1024 * 1024
MAX_POLICY_CONTEXTS = 4096
MAX_POLICY_DEPTH = 64


@dataclass
class _PolicyEvaluation:
    results: dict[tuple, bool | str] = field(default_factory=dict)
    pending: set[tuple] = field(default_factory=set)
    failed: bool = False


_POLICY_EVALUATION: ContextVar[_PolicyEvaluation | None] = ContextVar(
    "association_policy_evaluation", default=None,
)


@contextmanager
def _policy_evaluation(*, fresh: bool = False) -> Iterator[_PolicyEvaluation]:
    """Share bounded memoization only within one current policy evaluation."""
    active = _POLICY_EVALUATION.get()
    if active is not None and not fresh:
        yield active
        return
    active = _PolicyEvaluation()
    token = _POLICY_EVALUATION.set(active)
    try:
        yield active
    finally:
        _POLICY_EVALUATION.reset(token)


class _Rejected(Exception):
    def __init__(self, status: str):
        self.status = status
        super().__init__(status)


def _load_json(raw: bytes | str) -> Any:
    return json.loads(raw)


def _value_at(value: Any, path: Sequence[Any]) -> Any:
    if not isinstance(path, (list, tuple)) or len(path) > 64:
        raise _Rejected("invalid_reference")
    try:
        for part in path:
            if isinstance(value, dict) and isinstance(part, str):
                value = value[part]
            elif isinstance(value, list) and type(part) is int and part >= 0:
                value = value[part]
            else:
                raise _Rejected("invalid_reference")
    except (KeyError, IndexError):
        raise _Rejected("invalid_reference") from None
    return value


class AssociationStore:
    """Durable CAS and replay journal for explicit advisory commands.

    A command may contain individually invalid proposals. Successful siblings
    and their journal entry commit together; retry uses deterministic item keys.
    Storage failure never returns a saved handle from the failed transaction.
    """

    def __init__(self, view_store: Any):
        self.views = view_store
        self.namespace = view_store.namespace

    def command_id(self, key: str) -> str:
        """Qualify a caller's stable retry key in this sidecar namespace."""
        if not isinstance(key, str) or not _KEY.fullmatch(key):
            raise ValueError("command key must be 1..160 ASCII identifier characters")
        return f"{self.namespace}:command:{key}"

    def _valid_command_id(self, value: Any) -> bool:
        prefix = f"{self.namespace}:command:"
        return isinstance(value, str) and value.startswith(prefix) and bool(
            _KEY.fullmatch(value[len(prefix):])
        )

    def _relation_ref(self, relation_id: str, revision: int, digest: str) -> dict:
        return {"kind": "association", "version": 1, "namespace": self.namespace,
                "relation_id": relation_id, "revision": revision, "body_digest": digest}

    def _check_relation_ref(self, ref: Any) -> None:
        try:
            validate_ref(ref)
        except (TypeError, ValueError):
            raise _Rejected("invalid_reference") from None
        if (not isinstance(ref, dict) or ref.get("kind") != "association"
                or type(ref.get("version")) is not int or ref["version"] != 1
                or ref.get("namespace") != self.namespace
                or not isinstance(ref.get("relation_id"), str)
                or not ref["relation_id"].startswith(f"{self.namespace}:relation:")
                or type(ref.get("revision")) is not int or ref["revision"] < 1
                or not isinstance(ref.get("body_digest"), str)
                or not _HEX.fullmatch(ref["body_digest"])):
            raise _Rejected("invalid_reference")

    def _load_relation(self, ref: Any, db: sqlite3.Connection | None = None) -> dict:
        self._check_relation_ref(ref)
        if db is None:
            with self.views._connect(readonly=True) as connection:
                return self._load_relation(ref, connection)
        row = db.execute(
            "SELECT body_digest, body_object_ref FROM associations "
            "WHERE relation_id=? AND revision=?", (ref["relation_id"], ref["revision"])
        ).fetchone()
        if row is None or row[0] != ref["body_digest"] or row[0] != row[1]:
            raise _Rejected("association_unavailable")
        try:
            raw = self.views._read_object(row[1])
        except (OSError, ProjectionError):
            raise _Rejected("association_unavailable") from None
        if sha256_digest(raw) != row[0]:
            raise _Rejected("association_unavailable")
        body = _load_json(raw)
        if (not isinstance(body, dict) or body.get("relation_id") != ref["relation_id"]
                or body.get("revision") != ref["revision"]
                or body.get("kind") not in KINDS or body.get("status") not in STATUSES
                or not isinstance(body.get("envelope"), dict)):
            raise _Rejected("association_unavailable")
        return body

    def _allowed(self, envelope: dict, policy: HostPolicy, context: AccessContext) -> bool:
        # Preserve restrictions even with a host policy implementation that only
        # understands source dependencies and private scope.
        if envelope.get("operator_only") and context.audience != "operator":
            return False
        if (envelope.get("private_principals") is not None
                and context.principal not in envelope["private_principals"]):
            return False
        try:
            return bool(self.views._authorize_envelope(envelope, policy, context))
        except Exception:
            return False

    def _check_policy(self, envelope: dict, policy: HostPolicy,
                      context: AccessContext) -> None:
        if not authorize_envelope({**envelope, "redaction_witnesses": []}, policy, context):
            raise _Rejected("not_authorized")
        if not self._allowed(envelope, policy, context):
            raise _Rejected("stale_policy")

    def _check_relation_policy(self, body: dict, *, policy: HostPolicy,
                               context: AccessContext) -> None:
        """Every endpoint carries the complete revision's visibility conditions."""
        if not body["envelope"].get("context_bindings"):
            # Old notes did not retain all authoring access conditions. The
            # author name alone cannot reconstruct the missing audience/scope.
            raise _Rejected("stale_policy")
        self._check_policy(body["envelope"], policy, context)
        if redact_values(body, policy, context) != body:
            raise _Rejected("stale_policy")
        descriptor = body.get("argument")
        if descriptor:
            raw = self.views._read_object(descriptor["object_digest"])
            if len(raw) != descriptor["byte_length"]:
                raise _Rejected("argument_unavailable")
            text = raw.decode("utf-8")
            if descriptor["encoding"] == "canonical_json":
                argument = _load_json(text)
                assert_visible_output(argument, context)
                if redact_values(argument, policy, context) != argument:
                    raise _Rejected("stale_policy")
            elif descriptor["encoding"] != "utf8":
                raise _Rejected("argument_unavailable")
            if policy.redact(text, context) != text:
                raise _Rejected("stale_policy")

    def _output_result(self, body: dict, ref: dict, applicability: dict) -> dict:
        result = {"status": "ok", "association_ref": ref, "association": body,
                  "endpoint_applicability": applicability}
        if body.get("argument"):
            result["argument_ref"] = {
                "kind": "argument", "version": 1, "namespace": self.namespace,
                "association": ref, "object_digest": body["argument"]["object_digest"],
            }
        return result

    def _check_output_policy(self, result: dict, *, policy: HostPolicy,
                             context: AccessContext) -> None:
        """Check the exact final output contexts before any text is inherited.

        These contexts include the final relation reference and opaque public
        envelope binding. They are derived from an existing body, so downstream
        witnesses can retain them without placing its own digest inside a body.
        """
        body = result["association"]
        public = {**result, "association": {
            **body, "envelope": self.views._public_envelope(body["envelope"]),
        }}
        assert_visible_output(public, context)
        if redact_output(public, policy, context) != public:
            raise _Rejected("stale_policy")
        if body.get("argument"):
            text = self._argument_text(body)
            argument = {"status": "ok", "argument_ref": result["argument_ref"],
                        "text": text, "start": 0, "end": len(text), "complete": True,
                        "descriptor": body["argument"]}
            projected = {**public, "argument_content": {
                "encoding": body["argument"]["encoding"], "text": text,
            }}
            if (redact_output(argument, policy, context) != argument
                    or redact_output(projected, policy, context) != projected):
                raise _Rejected("stale_policy")

    def _input_envelope(self, body: dict, ref: dict, *, policy: HostPolicy,
                        context: AccessContext, result: dict | None = None) -> dict:
        with _policy_evaluation() as active:
            if result is None:
                result = self._output_result(body, ref, {
                    key: self._endpoint_status(body[key], policy=policy, context=context)
                    for key in ("source", "target")
                })
            self._check_output_policy(result, policy=policy, context=context)
            if active.failed:
                raise _Rejected("stale_policy")
            return self._merge([body["envelope"], {
                "dependencies": [], "redaction_witnesses": [{
                    "encoding": "association-output-v1", "object_digest": ref["body_digest"],
                    "endpoint_applicability": result["endpoint_applicability"],
                }],
            }])

    def _policy_key(self, kind: str, identity: Any, policy: HostPolicy,
                    context: AccessContext) -> tuple:
        return (str(self.views.directory), self.namespace, id(policy),
                context_binding(context), kind, canonical_json(identity))

    @staticmethod
    def _begin_policy_context(active: _PolicyEvaluation, key: tuple) -> bool:
        if (active.failed or key in active.pending or len(active.pending) >= MAX_POLICY_DEPTH
                or len(active.results) + len(active.pending) >= MAX_POLICY_CONTEXTS):
            active.failed = True
            return False
        active.pending.add(key)
        return True

    def _output_witness_valid(self, body: dict, digest: str, applicability: dict,
                              *, policy: HostPolicy, context: AccessContext) -> bool:
        """Retain the inspected context and enforce the source's current output.

        Current endpoint status can change after deletion or policy revocation.
        Memoization shares endpoint and guard checks across a flattened ancestry;
        cycles and oversized dependency walks fail closed within this operation.
        """
        with _policy_evaluation() as active:
            key = self._policy_key("output", [digest, applicability], policy, context)
            if key in active.results:
                return active.results[key] is True and not active.failed
            if not self._begin_policy_context(active, key):
                return False
            valid = False
            try:
                ref = self._relation_ref(body["relation_id"], body["revision"], digest)
                self._check_relation_ref(ref)
                self._check_output_policy(self._output_result(body, ref, applicability),
                                          policy=policy, context=context)
                current = {name: self._endpoint_status(body[name], policy=policy, context=context)
                           for name in ("source", "target")}
                if current != applicability:
                    self._check_output_policy(self._output_result(body, ref, current),
                                              policy=policy, context=context)
                valid = not active.failed
            except (KeyError, TypeError, ValueError, RecursionError, OSError, ProjectionError, _Rejected):
                pass
            finally:
                active.pending.remove(key)
            active.results[key] = valid
            return valid

    @staticmethod
    def _merge(envelopes: Sequence[dict]) -> dict:
        return merge_envelopes(*envelopes)

    def _reference_envelope(self, ref: Any, *, policy: HostPolicy,
                            context: AccessContext, authoring: bool = False) -> dict:
        try:
            ref = validate_ref(ref)
        except (TypeError, ValueError):
            raise _Rejected("invalid_reference")
        kind = ref.get("kind")
        if kind in {"view", "view_item"}:
            view_ref = ref if kind == "view" else ref.get("view_ref")
            result = self.views._read_view_authorized(
                view_ref, policy=policy, context=context, include_original_values=kind == "view_item",
            )
            if result.get("status") != "ok":
                raise _Rejected("not_authorized" if result.get("status") in {
                    "not_authorized", "stale_policy"
                } else "invalid_reference")
            snapshot = result["snapshot"]
            if kind == "view_item":
                value = _value_at(snapshot.get("values", {}), ref.get("path"))
                selected = _selected_text(result, ref["path"], "json-v1", policy, context)
                if sha256_digest(selected.encode("utf-8")) != ref["value_digest"]:
                    # Older unfiltered handles can be recognized when selection
                    # policy now differs from the parent-visible record. Other
                    # mismatches have no retained exact selection to resolve.
                    raise _Rejected("stale_policy" if sha256_digest(canonical_json(value))
                                    == ref["value_digest"] else "invalid_reference")
            envelope = snapshot.get("envelope")
            if not isinstance(envelope, dict) or not self._allowed(envelope, policy, context):
                raise _Rejected("not_authorized")
            # Legacy snapshots predate envelope context bindings. The manifest
            # still binds their exact reader, including audience and answer
            # visibility, and copied content must retain that restriction.
            envelope = self._merge([envelope, {
                "dependencies": [], "context_bindings": [result["policy_binding"]],
            }])
            if kind == "view_item" and authoring:
                original, _ = _selected_values(result, ref["path"], policy, context)
                # A record-specific filter can change while its parent view's
                # serialized policy context stays unchanged. Every authoring
                # role retains the selected original's baseline conditions.
                witness = self.views._install_policy_witness(original, policy=policy, context=context)
                return self._merge([envelope, {
                    "dependencies": [], "redaction_witnesses": [witness],
                }])
            return envelope
        if kind == "derived" and authoring:
            result = read_view_page(self.views, ref, policy=policy, context=context)
            if result.get("status") != "ok":
                raise _Rejected(result.get("status", "invalid_reference"))
            parent = self.views._read_view_authorized(
                ref["view"], policy=policy, context=context, include_original_values=True,
            )
            if parent.get("status") != "ok":
                raise _Rejected(parent.get("status", "invalid_reference"))
            original, _ = _selected_values(parent, ref["path"], policy, context)
            # Retain the original complete selection's policy conditions, even
            # when the author inspected only a page within it. Baseline digests
            # permit non-idempotent host filters without filtering visible text
            # a second time. The parent keeps whole-view and source conditions.
            witness = self.views._install_policy_witness(original, policy=policy, context=context)
            return self._merge([parent["snapshot"]["envelope"], {
                "dependencies": [], "redaction_witnesses": [witness],
                "context_bindings": [parent["policy_binding"]],
            }])
        if kind == "association":
            body = self._load_relation(ref)
            self._check_relation_policy(body, policy=policy, context=context)
            return self._input_envelope(body, ref, policy=policy, context=context) if authoring else body["envelope"]
        if kind == "argument":
            if ref.get("namespace") != self.namespace:
                raise _Rejected("invalid_reference")
            body = self._load_relation(ref.get("association"))
            self._check_relation_policy(body, policy=policy, context=context)
            descriptor = body.get("argument")
            if not descriptor or descriptor.get("object_digest") != ref.get("object_digest"):
                raise _Rejected("invalid_reference")
            raw = self.views._read_object(ref["object_digest"])
            if sha256_digest(raw) != ref["object_digest"]:
                raise _Rejected("invalid_reference")
            return self._input_envelope(body, ref["association"], policy=policy, context=context) if authoring else body["envelope"]
        # Bare owner IDs, arbitrary object hashes and paths have no installed
        # value or host-derived policy binding and are never resolver endpoints.
        raise _Rejected("invalid_reference")

    def _prepare(self, proposal: Any, *, policy: HostPolicy, context: AccessContext,
                 host_envelope: dict) -> dict:
        if not isinstance(proposal, dict) or set(proposal) - _FIELDS:
            raise _Rejected("invalid_reference")
        if (not isinstance(proposal.get("kind"), str) or proposal["kind"] not in KINDS
                or not isinstance(proposal.get("status", "proposed"), str)
                or proposal.get("status", "proposed") not in STATUSES):
            raise _Rejected("invalid_reference")
        expected = proposal.get("expected_revision", 0)
        relation_id = proposal.get("relation_id")
        if type(expected) is not int or expected < 0:
            raise _Rejected("invalid_reference")
        if relation_id is not None and (
            not isinstance(relation_id, str)
            or not relation_id.startswith(f"{self.namespace}:relation:") or expected < 1
        ):
            raise _Rejected("invalid_reference")
        if relation_id is None and expected != 0:
            raise _Rejected("invalid_reference")
        evidence = proposal.get("evidence_refs", [])
        if not isinstance(evidence, list) or len(evidence) + 2 > MAX_INLINE_REFERENCES:
            raise _Rejected("invalid_reference")
        prose = proposal.get("prose", "")
        if not isinstance(prose, str):
            raise _Rejected("invalid_reference")
        if policy.redact(prose, context) != prose:
            raise _Rejected("not_authorized")
        refs = [proposal.get("source"), proposal.get("target"), *evidence]
        envelopes = [host_envelope]
        # Updating a protected revision must never declassify its inherited text.
        prior = None
        if relation_id:
            with self.views._connect(readonly=True) as db:
                row = db.execute("SELECT body_digest FROM associations WHERE relation_id=? AND revision=?",
                                 (relation_id, expected)).fetchone()
            if row is None:
                raise _Rejected("stale_revision")
            prior_ref = self._relation_ref(relation_id, expected, row[0])
            prior = self._load_relation(prior_ref)
            self._check_relation_policy(prior, policy=policy, context=context)
            envelopes.append(self._input_envelope(prior, prior_ref, policy=policy, context=context))
            if proposal.get("status") == "withdrawn":
                retained_fields = {"kind": proposal["kind"], "source": refs[0],
                                   "target": refs[1], "scope": proposal.get("scope"),
                                   "evidence_refs": evidence, "prose": prose}
                if any(canonical_json(value) != canonical_json(prior[key])
                       for key, value in retained_fields.items()):
                    raise _Rejected("invalid_reference")
                argument = proposal.get("argument")
                descriptor = prior.get("argument")
                if argument is None:
                    if descriptor is not None:
                        raise _Rejected("invalid_reference")
                else:
                    if not isinstance(argument, (str, dict)) or not descriptor:
                        raise _Rejected("invalid_reference")
                    raw = argument.encode("utf-8") if isinstance(argument, str) else canonical_json(argument)
                    encoding = "utf8" if isinstance(argument, str) else "canonical_json"
                    if (descriptor["object_digest"] != sha256_digest(raw)
                            or descriptor["encoding"] != encoding):
                        raise _Rejected("invalid_reference")
        for index, ref in enumerate(refs):
            if isinstance(ref, dict) and ref.get("kind") == "derived":
                raise _Rejected("invalid_reference")
            retained: list[dict[str, Any]] = []
            if prior is not None and proposal.get("status") == "withdrawn":
                retained = ([prior["source"]] if index == 0 else [prior["target"]]
                            if index == 1 else prior["evidence_refs"])
            if any(canonical_json(ref) == canonical_json(old) for old in retained):
                # Deletion may make an exact old endpoint unavailable. Its
                # authorized prior revision remains enough to withdraw the note.
                continue
            envelopes.append(self._reference_envelope(ref, policy=policy, context=context, authoring=True))
        body = {"kind": proposal["kind"], "source": refs[0], "target": refs[1],
                "scope": proposal.get("scope"), "evidence_refs": evidence, "prose": prose,
                "status": proposal.get("status", "proposed"), "author": context.principal,
                "predecessor_revision": expected, "envelope": self._merge(envelopes)}
        assert_visible_output(body, context)
        if not self._allowed(body["envelope"], policy, context):
            raise _Rejected("not_authorized")
        if redact_values(body, policy, context) != body:
            raise _Rejected("not_authorized")
        argument = proposal.get("argument")
        if argument is not None:
            if not isinstance(argument, (str, dict)):
                raise _Rejected("invalid_reference")
            if isinstance(argument, dict):
                assert_visible_output(argument, context)
                antecedents = argument.get("antecedents")
                if antecedents is not None and not isinstance(antecedents, list):
                    raise _Rejected("invalid_reference")
                if "connective" in argument and (
                        not isinstance(argument["connective"], str)
                        or argument["connective"] not in {"AND", "OR"}):
                    raise _Rejected("invalid_reference")
                if redact_values(argument, policy, context) != argument:
                    raise _Rejected("not_authorized")
            raw = argument.encode("utf-8") if isinstance(argument, str) else canonical_json(argument)
            if policy.redact(raw.decode("utf-8"), context) != raw.decode("utf-8"):
                raise _Rejected("not_authorized")
            digest = self.views._install_object(raw)
            body["argument"] = {
                "object_digest": digest, "byte_length": len(raw),
                "encoding": "utf8" if isinstance(argument, str) else "canonical_json",
                "antecedent_count": len(argument["antecedents"])
                if isinstance(argument, dict) and "antecedents" in argument else None,
                "unexpanded": True,
            }
            body["envelope"] = self._merge([body["envelope"], {
                "dependencies": [], "redaction_witnesses": [{
                    "object_digest": digest,
                    "encoding": "text-v1" if isinstance(argument, str) else "json-v1",
                }],
            }])
        return {"body": body, "relation_id": relation_id, "expected": expected}

    def write_command(self, command_id: str, proposals: Sequence[dict], *,
                      policy: HostPolicy, context: AccessContext,
                      authoring_refs: Sequence[dict] = (),
                      provenance_complete: bool = False) -> dict:
        """Apply an explicit host-bound command, preserving its retry identity."""
        try:
            with self.views.write_lock(), _policy_evaluation():
                return self._write_command(command_id, proposals, policy=policy, context=context,
                                           authoring_refs=authoring_refs,
                                           provenance_complete=provenance_complete)
        except Exception:
            return {"status": "storage_unavailable", "command_id": command_id}

    def _write_command(self, command_id: str, proposals: Sequence[dict], *,
                       policy: HostPolicy, context: AccessContext,
                       authoring_refs: Sequence[dict], provenance_complete: bool) -> dict:
        retry = {"command_id": command_id}
        if not self._valid_command_id(command_id):
            return {"status": "invalid_reference", **retry}
        if not isinstance(proposals, (list, tuple)) or not 1 <= len(proposals) <= MAX_PROPOSALS:
            return {"status": "invalid_reference", **retry}
        if not isinstance(authoring_refs, (list, tuple)):
            return {"status": "invalid_reference", **retry}
        if type(provenance_complete) is not bool:
            return {"status": "invalid_reference", **retry}
        try:
            # Canonical request includes raw arguments, input order, expected
            # revisions, host provenance, and author. No field is replay-exempt.
            request = {"proposals": list(proposals), "authoring_refs": list(authoring_refs),
                       "provenance_complete": provenance_complete,
                       "author": context.principal, "scope": context.scope}
            request_bytes = canonical_json(request)
            request = _load_json(request_bytes)
            proposals = request["proposals"]
            authoring_refs = request["authoring_refs"]
            digest = sha256_digest(request_bytes)
            metadata = {**request, "proposals": [
                {k: v for k, v in p.items() if k != "argument"} if isinstance(p, dict) else p
                for p in proposals
            ]}
            if len(canonical_json(metadata)) > MAX_METADATA_BYTES:
                return {"status": "invalid_reference", **retry}
            # Journal replay uses the retained envelope, so deleting an endpoint
            # cannot make a previously saved exact command lose its identity.
            with self.views._connect(readonly=True) as db:
                existing = db.execute(
                    "SELECT canonical_body_digest,outcome,envelope FROM association_commands WHERE command_id=?",
                    (command_id,),
                ).fetchone()
            if existing is not None:
                return self._replay(existing, digest, command_id, policy, context)
            envelopes: list[dict[str, Any]] = [{
                "dependencies": [], "context_bindings": [context_binding(context)],
            }]
            envelopes.extend(self._reference_envelope(ref, policy=policy, context=context, authoring=True)
                             for ref in authoring_refs)
            if not provenance_complete:
                if not context.scope or context.role != "operator" or context.audience != "operator":
                    return {"status": "not_authorized", **retry}
                envelopes.append({"dependencies": [], "private_scope": context.scope,
                                  "private_principals": [context.principal], "operator_only": True})
            host_envelope = self._merge(envelopes)
            if host_envelope["dependencies"] and not self._allowed(host_envelope, policy, context):
                return {"status": "not_authorized", **retry}
            prepared = []
            for proposal in proposals:
                try:
                    with _policy_evaluation(fresh=True):
                        prepared.append(self._prepare(proposal, policy=policy, context=context,
                                                      host_envelope=host_envelope))
                except _Rejected as exc:
                    prepared.append({"status": exc.status})
                except (ValueError, TypeError, UnicodeError, RecursionError):
                    prepared.append({"status": "invalid_reference"})
            outcomes, pending, saved_envelopes = self._prepare_revisions(command_id, prepared, policy=policy, context=context)
            # Capacity includes SQLite journal overhead, in addition to immutable
            # content checked by each installation.
            self.views._check_capacity(MAX_METADATA_BYTES)
            with self.views._connect() as db:
                existing = db.execute(
                    "SELECT canonical_body_digest,outcome,envelope FROM association_commands WHERE command_id=?",
                    (command_id,),
                ).fetchone()
                if existing is not None:
                    return self._replay(existing, digest, command_id, policy, context, db=db)
                for relation_id, revision, predecessor, body_digest in pending:
                    row = db.execute("SELECT revision FROM association_heads WHERE relation_id=?",
                                     (relation_id,)).fetchone()
                    current = row[0] if row else 0
                    if current != predecessor:
                        raise ProjectionError("storage_unavailable")
                    db.execute("INSERT INTO associations VALUES (?,?,?,?,?,?)", (
                        relation_id, revision, predecessor, body_digest, body_digest, command_id))
                    db.execute("INSERT INTO association_heads VALUES (?,?) "
                               "ON CONFLICT(relation_id) DO UPDATE SET revision=excluded.revision",
                               (relation_id, revision))
                result = {"status": "saved", **retry, "items": outcomes}
                journal_envelope = self._merge([host_envelope, *saved_envelopes])
                if not journal_envelope["dependencies"]:
                    # Invalid-only commands have no retained source content. A
                    # caller may recover only their exact context-bound outcome.
                    journal_envelope = self._merge([journal_envelope, {
                        "dependencies": [], "private_scope": context.scope,
                        "private_principals": [context.principal],
                    }])
                # A command receipt must survive a fresh replay evaluation,
                # without preparation's memoized dependency results. Failure
                # here rolls back every pending row before any acknowledgement.
                if journal_envelope["dependencies"]:
                    with _policy_evaluation(fresh=True):
                        self._check_policy(journal_envelope, policy, context)
                db.execute("INSERT INTO association_commands VALUES (?,?,?,?)", (
                    command_id, digest, canonical_json(result).decode("utf-8"),
                    canonical_json(journal_envelope).decode("utf-8")))
            return result
        except _Rejected as exc:
            return {"status": exc.status, **retry}
        except (TypeError, ValueError, UnicodeError):
            return {"status": "invalid_reference", **retry}
        except Exception:
            return {"status": "storage_unavailable", **retry}

    def _prepare_revisions(self, command_id: str, prepared: list[dict], *,
                           policy: HostPolicy, context: AccessContext) -> tuple[list, list, list]:
        """Install bodies before budgeting SQLite growth, under the writer lock."""
        outcomes = []
        pending = []
        envelopes = []
        heads: dict[str, int] = {}
        with self.views._connect(readonly=True) as db:
            for index, item in enumerate(prepared):
                item_key = sha256_digest(canonical_json([command_id, index]))
                if "status" in item:
                    outcomes.append({"item_key": item_key, "status": item["status"]})
                    continue
                relation_id = item["relation_id"] or f"{self.namespace}:relation:{item_key}"
                if relation_id not in heads:
                    row = db.execute("SELECT revision FROM association_heads WHERE relation_id=?",
                                     (relation_id,)).fetchone()
                    heads[relation_id] = row[0] if row else 0
                current = heads[relation_id]
                if current != item["expected"]:
                    outcomes.append({"item_key": item_key, "status": "stale_revision"})
                    continue
                revision = current + 1
                body = {**item["body"], "relation_id": relation_id, "revision": revision}
                # Revision identity is part of the policy context. Establish the
                # witness only once CAS has selected the final identity. Keeping
                # its own envelope out avoids a content-digest cycle.
                witness = self.views._install_policy_witness({
                    key: value for key, value in body.items() if key != "envelope"
                })
                body["envelope"] = self._merge([body["envelope"], {
                    "dependencies": [], "redaction_witnesses": [witness],
                }])
                try:
                    with _policy_evaluation(fresh=True):
                        self._check_relation_policy(body, policy=policy, context=context)
                    body_digest = self.views._install_object(canonical_json(body))
                    ref = self._relation_ref(relation_id, revision, body_digest)
                    # Validate the prospective exact read and inherited/journal
                    # guard separately, with the same empty memo as a later
                    # process. Warm preparation can otherwise conceal a walk
                    # that exceeds the evaluator's depth or context bound.
                    with _policy_evaluation(fresh=True):
                        result = self._authorized_result(body, ref, policy=policy, context=context)
                        envelope = self._input_envelope(body, ref, policy=policy, context=context,
                                                        result=result)
                    with _policy_evaluation(fresh=True):
                        self._check_policy(envelope, policy, context)
                except _Rejected as exc:
                    outcomes.append({"item_key": item_key, "status": exc.status})
                    continue
                except PolicyRedactionError:
                    outcomes.append({"item_key": item_key, "status": "stale_policy"})
                    continue
                pending.append((relation_id, revision, current, body_digest))
                outcomes.append({"item_key": item_key, "status": "saved",
                                 "association_ref": self._relation_ref(relation_id, revision, body_digest)})
                envelopes.append(envelope)
                heads[relation_id] = revision
        return outcomes, pending, envelopes

    def _replay(self, row: Sequence[Any], digest: str, command_id: str,
                policy: HostPolicy, context: AccessContext,
                db: sqlite3.Connection | None = None) -> dict:
        try:
            envelope = self._merge([_load_json(row[2])])
            bound_context = envelope["context_bindings"] == [context_binding(context)]
            legacy_operator = (not envelope["context_bindings"]
                               and envelope["operator_only"] and bool(context.scope)
                               and context.role == context.audience == "operator")
            private_empty = (not envelope["deny"] and not envelope["dependencies"]
                             and not envelope["redaction_witnesses"]
                             and envelope["private_principals"] == [context.principal]
                             and envelope["private_scope"] == context.scope
                             and (bound_context or legacy_operator)
                             and (not envelope["operator_only"]
                                  or context.role == context.audience == "operator"))
            if not private_empty:
                if envelope["dependencies"] and not envelope["context_bindings"]:
                    raise _Rejected("stale_policy")
                self._check_policy(envelope, policy, context)
        except _Rejected as exc:
            return {"status": exc.status, "command_id": command_id}
        if row[0] != digest:
            self.views._check_capacity(8192)
            if db is None:
                with self.views._connect() as connection:
                    connection.execute("INSERT OR IGNORE INTO association_command_conflicts VALUES (?,?)",
                                       (command_id, digest))
            else:
                db.execute("INSERT OR IGNORE INTO association_command_conflicts VALUES (?,?)",
                           (command_id, digest))
            return {"status": "conflicting_replay", "command_id": command_id}
        result = _load_json(row[1])
        result["status"] = "already_saved"
        for item in result["items"]:
            if item["status"] == "saved":
                item["status"] = "already_saved"
        if db is None:
            self.views._acknowledge_replay()
        return result

    def _endpoint_status(self, ref: dict, *, policy: HostPolicy, context: AccessContext) -> str:
        with _policy_evaluation() as active:
            try:
                key = self._policy_key("endpoint", ref, policy, context)
            except (TypeError, ValueError, RecursionError):
                return "unavailable"
            if key in active.results:
                return str(active.results[key]) if not active.failed else "unavailable"
            if not self._begin_policy_context(active, key):
                return "unavailable"
            status = "unavailable"
            try:
                self._reference_envelope(ref, policy=policy, context=context)
                if ref.get("kind") in {"association", "argument"}:
                    parent = ref if ref["kind"] == "association" else ref["association"]
                    result = self._read_authorized(parent, policy=policy, context=context)
                    if result.get("status") == "ok":
                        status = "historical"
                else:
                    status = "historical"
            except Exception:
                pass
            finally:
                active.pending.remove(key)
            if active.failed:
                status = "unavailable"
            active.results[key] = status
            return status

    def _read_authorized(self, ref: dict, *, policy: HostPolicy, context: AccessContext,
                         check_output: bool = True) -> dict:
        """Trusted internal read including the retained dependency envelope."""
        with _policy_evaluation() as active:
            result = self._read_authorized_current(ref, policy=policy, context=context,
                                                    check_output=check_output)
            return {"status": "stale_policy"} if active.failed else result

    def _authorized_result(self, body: dict, ref: dict, *, policy: HostPolicy,
                           context: AccessContext, check_output: bool = True) -> dict:
        """Validate the same exact revision before saving and when reading it."""
        with _policy_evaluation() as active:
            self._check_relation_policy(body, policy=policy, context=context)
            result = self._output_result(body, ref, {
                key: self._endpoint_status(body[key], policy=policy, context=context)
                for key in ("source", "target")
            })
            if check_output:
                self._check_output_policy(result, policy=policy, context=context)
            if active.failed:
                raise _Rejected("stale_policy")
            return result

    def _read_authorized_current(self, ref: dict, *, policy: HostPolicy, context: AccessContext,
                                 check_output: bool) -> dict:
        try:
            body = self._load_relation(ref)
            return self._authorized_result(body, ref, policy=policy, context=context,
                                           check_output=check_output)
        except _Rejected as exc:
            return {"status": exc.status if exc.status in {"not_authorized", "stale_policy"}
                    else "association_unavailable"}
        except Exception:
            return {"status": "association_unavailable"}

    def _public_read(self, result: dict, *, policy: HostPolicy, context: AccessContext) -> dict:
        if result.get("status") != "ok":
            return result
        body = result["association"]
        public = {**result, "association": {
            **body, "envelope": self.views._public_envelope(body["envelope"]),
        }}
        return redact_output(public, policy, context)

    def read(self, ref: dict, *, policy: HostPolicy, context: AccessContext) -> dict:
        """Read one exact revision; deletion never changes its endpoint binding."""
        try:
            result = self._read_authorized(ref, policy=policy, context=context)
            return self._public_read(result, policy=policy, context=context)
        except (ValueError, TypeError, UnicodeError, RecursionError):
            return {"status": "stale_policy"}

    def _authorized_heads(self, *, policy: HostPolicy, context: AccessContext,
                          check_output: bool = True) -> Iterator[dict]:
        with self.views._connect(readonly=True) as db:
            rows = db.execute(
                "SELECT a.relation_id,a.revision,a.body_digest FROM associations a "
                "JOIN association_heads h ON a.relation_id=h.relation_id AND a.revision=h.revision "
                "ORDER BY a.relation_id"
            )
            for row in rows:
                result = self._read_authorized(self._relation_ref(row[0], row[1], row[2]),
                                               policy=policy, context=context, check_output=check_output)
                if result.get("status") == "ok":
                    yield result

    def _argument_text(self, body: dict) -> str:
        descriptor = body["argument"]
        raw = self.views._read_object(descriptor["object_digest"])
        if len(raw) != descriptor["byte_length"]:
            raise _Rejected("argument_unavailable")
        return raw.decode("utf-8")

    def list(self, *, policy: HostPolicy, context: AccessContext, limit: int = 100) -> dict:
        return self.search("", policy=policy, context=context, limit=limit)

    def search(self, query: str, *, policy: HostPolicy, context: AccessContext,
               limit: int = 100) -> dict:
        """Search authorized heads only; no protected totals or skipped counts."""
        if (not isinstance(query, str) or len(query) > MAX_QUERY_CHARS
                or type(limit) is not int or not 1 <= limit <= 1000):
            return {"status": "invalid_reference"}
        try:
            items = []
            needle = query.casefold()
            for result in self._authorized_heads(policy=policy, context=context):
                try:
                    public = self._public_read(result, policy=policy, context=context)
                    body = public["association"]
                    if needle not in canonical_json(body).decode("utf-8").casefold():
                        if not body.get("argument") or needle not in self._argument_text(body).casefold():
                            continue
                except (ValueError, TypeError, UnicodeError, RecursionError, OSError, ProjectionError, _Rejected):
                    continue
                items.append(public)
                if len(items) == limit:
                    break
            return redact_output({"status": "ok", "items": items}, policy, context)
        except Exception:
            return {"status": "storage_unavailable"}

    def project_into(self, snapshot: dict, *, policy: HostPolicy,
                     context: AccessContext) -> dict:
        """Pin authorized current revisions into a closed owner snapshot.

        This is a pure read. A failed/corrupt association remains absent, never
        replaced with a different revision. The enclosing view inherits every
        copied relation's immutable policy envelope.
        """
        snapshot_bytes = canonical_json(snapshot)
        remaining = MAX_PROJECTED_BYTES - len(snapshot_bytes) - 1024
        if remaining < 0:
            raise ProjectionError("storage_unavailable")
        projected = _load_json(snapshot_bytes)
        records = []
        envelopes = [projected.get("envelope", {"dependencies": []})]
        try:
            for result in self._authorized_heads(policy=policy, context=context, check_output=False):
                body = result["association"]
                public = self._public_read(result, policy=policy, context=context)
                record_bytes = len(canonical_json(public))
                envelope_bytes = len(canonical_json(body["envelope"]))
                available = remaining - record_bytes - envelope_bytes
                if available < 0:
                    raise ProjectionError("storage_unavailable")
                if body.get("argument"):
                    # A UTF-8 byte requires at most six JSON bytes when escaped.
                    # Reserve before constructing argument output contexts or
                    # retaining another large argument in the projection.
                    reserve = body["argument"]["byte_length"] * 6 + 256
                    if reserve > available:
                        raise ProjectionError("storage_unavailable")
                try:
                    envelope = self._input_envelope(
                        body, result["association_ref"], policy=policy, context=context, result=result,
                    )
                except _Rejected:
                    continue
                remaining = available - len(canonical_json(envelope)) + envelope_bytes
                if remaining < 0:
                    raise ProjectionError("storage_unavailable")
                if body.get("argument"):
                    public["argument_content"] = {
                        "encoding": body["argument"]["encoding"],
                        "text": self._argument_text(body),
                    }
                    remaining -= len(canonical_json(public)) - record_bytes
                records.append(public)
                envelopes.append(envelope)
                if len(records) == 1000:
                    break
        except (OSError, sqlite3.Error, ValueError, TypeError, _Rejected) as exc:
            raise ProjectionError("storage_unavailable") from exc
        projected.setdefault("values", {})["associations"] = records
        projected["association_coverage"] = {
            "selection": "authorized_current_heads", "maximum_selected": 1000,
        }
        projected["envelope"] = self._merge(envelopes)
        # The bound applies to the resulting view object, independently of the
        # source adapter's budget. Return no partially materialized projection.
        if len(canonical_json(projected)) > MAX_PROJECTED_BYTES:
            raise ProjectionError("storage_unavailable")
        return projected

    def read_argument(self, ref: dict, *, policy: HostPolicy, context: AccessContext,
                      start: int = 0, end: int | None = None) -> dict:
        """Resolve an exact argument object through its owning revision policy."""
        try:
            if not isinstance(ref, dict) or ref.get("kind") != "argument" or ref.get("version") != 1:
                raise _Rejected("invalid_reference")
            self._reference_envelope(ref, policy=policy, context=context, authoring=True)
            body = self._load_relation(ref["association"])
            raw = self.views._read_object(ref["object_digest"])
            descriptor = body["argument"]
            if len(raw) != descriptor["byte_length"]:
                raise _Rejected("argument_unavailable")
            text = raw.decode("utf-8")
            if policy.redact(text, context) != text:
                return {"status": "stale_policy"}
            if type(start) is not int or start < 0 or start > len(text):
                raise _Rejected("invalid_reference")
            stop = len(text) if end is None else end
            if type(stop) is not int or stop < start or stop > len(text):
                raise _Rejected("invalid_reference")
            return redact_output({
                "status": "ok", "argument_ref": ref, "text": text[start:stop],
                "start": start, "end": stop, "complete": start == 0 and stop == len(text),
                "descriptor": descriptor,
            }, policy, context)
        except _Rejected as exc:
            return {"status": exc.status}
        except Exception:
            return {"status": "argument_unavailable"}

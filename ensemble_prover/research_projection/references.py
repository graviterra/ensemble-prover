"""Exact, versioned references; identities never grant read permission."""
from __future__ import annotations

from dataclasses import asdict, dataclass, field
import hashlib
import json
import re
from typing import Any

VERSION = 1
_DIGEST = re.compile(r"[0-9a-f]{64}\Z")


def canonical_json(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")


def sha256_digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def valid_digest(value: Any) -> bool:
    return isinstance(value, str) and bool(_DIGEST.fullmatch(value))


class ProjectionError(RuntimeError):
    def __init__(self, status: str, message: str = ""):
        super().__init__(message or status)
        self.status = status
        self.code = status


class InvalidReference(ValueError):
    """Malformed or ambiguous identity."""


@dataclass(frozen=True)
class _Ref:
    namespace: str
    version: int = field(default=VERSION, kw_only=True)

    def to_dict(self) -> dict[str, Any]:
        return validate_ref(asdict(self))


@dataclass(frozen=True)
class SourceRef(_Ref):
    content_digest: str
    item: str
    digest_algorithm: str = "sha256"
    span: Any = None
    dispatch: str | None = None
    kind: str = field(default="source", init=False)


@dataclass(frozen=True)
class TargetRef(_Ref):
    root_lineage: Any
    active_target: Any
    statement_identity: Any
    revision: Any
    frame: Any
    attempt: Any
    lane: Any
    kind: str = field(default="target", init=False)


@dataclass(frozen=True)
class ContextRef(_Ref):
    statement_environment: Any
    verification_context: Any
    digest_algorithm: str
    kind: str = field(default="context", init=False)


@dataclass(frozen=True)
class QuestionRef(_Ref):
    ledger: str
    question_id: str
    formulation_revision: Any
    kind: str = field(default="question", init=False)


@dataclass(frozen=True)
class HelperRef(_Ref):
    attempt: Any
    lane: Any
    helper_name: str
    source_digest: str
    contract: Any
    verification_context: Any
    owner_revision: Any
    snapshot_locator: Any
    digest_algorithm: str = "sha256:utf8"
    kind: str = field(default="helper", init=False)


@dataclass(frozen=True)
class GraphRef(_Ref):
    node_id: str
    statement: str
    frame: Any
    environment: Any
    owner_revision: Any
    snapshot_locator: Any
    kind: str = field(default="graph", init=False)


@dataclass(frozen=True)
class ViewRef(_Ref):
    manifest_digest: str
    kind: str = field(default="view", init=False)


@dataclass(frozen=True)
class DerivedRef(_Ref):
    view: dict[str, Any]
    path: list[str | int]
    transform: str
    start: int
    end: int
    content_digest: str
    selection_digest: str
    policy_binding: str
    kind: str = field(default="derived", init=False)


_REQUIRED = {
    "source": ("content_digest", "digest_algorithm", "item"),
    "target": ("root_lineage", "active_target", "statement_identity", "revision", "frame", "attempt", "lane"),
    "context": ("statement_environment", "verification_context", "digest_algorithm"),
    "question": ("ledger", "question_id", "formulation_revision"),
    "helper": ("attempt", "lane", "helper_name", "source_digest", "digest_algorithm", "contract", "verification_context", "owner_revision", "snapshot_locator"),
    "graph": ("node_id", "statement", "frame", "environment", "owner_revision", "snapshot_locator"),
    "view": ("manifest_digest",),
    "view_item": ("view_ref", "path", "value_digest"),
    "association": ("relation_id", "revision", "body_digest"),
    "argument": ("association", "object_digest"),
    "derived": ("view", "path", "transform", "start", "end", "content_digest", "selection_digest", "policy_binding"),
}
_OPTIONAL = {"source": {"span", "dispatch"}}


def validate_ref(ref: Any) -> dict[str, Any]:
    if hasattr(ref, "to_dict"):
        ref = ref.to_dict()
    if not isinstance(ref, dict) or type(ref.get("version")) is not int or ref["version"] != VERSION:
        raise InvalidReference("unsupported reference version")
    kind = ref.get("kind")
    if not isinstance(kind, str) or kind not in _REQUIRED or not isinstance(ref.get("namespace"), str) or not ref["namespace"]:
        raise InvalidReference("reference needs a kind and owner namespace")
    if any(key not in ref for key in _REQUIRED[kind]):
        raise InvalidReference("reference omits an exact identity field")
    if set(ref) - {"kind", "version", "namespace", *_REQUIRED[kind], *_OPTIONAL.get(kind, ())}:
        raise InvalidReference("reference contains unsupported fields")
    if kind == "source" and (ref["digest_algorithm"] != "sha256" or not valid_digest(ref["content_digest"]) or not isinstance(ref["item"], str)):
        raise InvalidReference("source requires a complete SHA256 and exact item")
    if kind == "helper" and (ref["digest_algorithm"] != "sha256:utf8" or not valid_digest(ref["source_digest"])):
        raise InvalidReference("legacy helper hashes are not full source digests")
    if kind in {"helper", "graph"} and ref["owner_revision"] is None and ref["snapshot_locator"] is None:
        raise InvalidReference("historical identity needs a revision or snapshot locator")
    if kind == "context" and ref["digest_algorithm"] not in {"sha256", "sha256:utf8", "owner_opaque"}:
        raise InvalidReference("unknown context digest algorithm")
    if kind == "view" and not valid_digest(ref["manifest_digest"]):
        raise InvalidReference("invalid manifest digest")
    if kind == "association":
        if not isinstance(ref["relation_id"], str) or not ref["relation_id"].startswith(ref["namespace"] + ":") or type(ref["revision"]) is not int or ref["revision"] < 1 or not valid_digest(ref["body_digest"]):
            raise InvalidReference("invalid association reference")
    if kind == "argument":
        parent = validate_ref(ref["association"])
        if parent["kind"] != "association" or parent["namespace"] != ref["namespace"] or not valid_digest(ref["object_digest"]):
            raise InvalidReference("invalid argument reference")
    if kind == "view_item":
        parent = validate_ref(ref["view_ref"])
        if parent["kind"] != "view" or parent["namespace"] != ref["namespace"] or not valid_digest(ref["value_digest"]):
            raise InvalidReference("invalid view item reference")
        if not isinstance(ref["path"], list) or len(ref["path"]) > 64 or any(type(p) not in {str, int} or (type(p) is int and p < 0) for p in ref["path"]):
            raise InvalidReference("invalid item path")
    if kind == "derived":
        view = validate_ref(ref["view"])
        if view["kind"] != "view" or view["namespace"] != ref["namespace"]:
            raise InvalidReference("derived namespace differs from view")
        if not isinstance(ref["path"], list) or len(ref["path"]) > 64 or any(type(p) not in {str, int} or (type(p) is int and p < 0) for p in ref["path"]):
            raise InvalidReference("invalid value path")
        if type(ref["start"]) is not int or type(ref["end"]) is not int or not 0 <= ref["start"] <= ref["end"]:
            raise InvalidReference("invalid range")
        if any(not valid_digest(ref[k]) for k in ("content_digest", "selection_digest", "policy_binding")):
            raise InvalidReference("invalid derived digest")
        if not isinstance(ref["transform"], str):
            raise InvalidReference("invalid transform")
    canonical_json(ref)
    return dict(ref)

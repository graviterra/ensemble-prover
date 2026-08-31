"""Immutable records used by the Mini domain-theory subsystem."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import asdict, dataclass, field
from types import MappingProxyType
from typing import Any, Iterable, Literal, Mapping, Sequence


MINI_THEORY_SCHEMA_VERSION = 3
# 15: verifier audit now (a) namespaces dotted declaration names, (b) rejects
# `_root_`-escaping declarations, (c) tracks `end NAME` with Lean's real
# per-segment popping (a partial-width `end` previously desynchronised the
# namespace stack and could drop a declaration from the per-declaration
# audit entirely), and (d) adds a fail-closed environment-level backstop that
# rejects any constant under the bundle namespace whose transitive axiom
# closure escapes the allowlist — regardless of how the name parser behaved.
# Receipts issued under <=14 may have skipped the axiom/anti-shortcut audits
# for a mis-namespaced declaration, so bundles verified under <=14 must not be
# served or reused.
THEORY_POLICY_VERSION = 15

TheoryNeedKind = Literal[
    "definition",
    "structure",
    "instance",
    "notation",
    "bridge_lemma",
    "theorem_family",
]


def _freeze_json(value: Any) -> Any:
    if isinstance(value, dict):
        return MappingProxyType({key: _freeze_json(item) for key, item in value.items()})
    if isinstance(value, list):
        return tuple(_freeze_json(item) for item in value)
    return value


def _thaw_json(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {key: _thaw_json(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_thaw_json(item) for item in value]
    return value


def _clean_text(value: Any) -> str:
    return str(value or "").strip()


def _clean_tuple(values: Iterable[Any]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(_clean_text(value) for value in values if _clean_text(value)))


def _canonical_json(payload: Mapping[str, Any]) -> str:
    return json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def content_hash(payload: str | bytes, *, length: int = 16) -> str:
    raw = payload.encode("utf-8") if isinstance(payload, str) else bytes(payload)
    return hashlib.sha256(raw).hexdigest()[: max(8, int(length or 16))]


def sanitize_module_segment(value: str, *, fallback: str = "General") -> str:
    """Return a stable Lean module/namespace segment."""

    words = re.findall(r"[A-Za-z0-9]+", _clean_text(value))
    segment = "".join(word[:1].upper() + word[1:] for word in words)
    if not segment:
        segment = fallback
    if segment[0].isdigit():
        segment = f"D{segment}"
    return segment


def _theory_body_without_imports(source: str) -> str:
    lines = []
    for line in _clean_text(source).splitlines():
        if re.match(r"^\s*import\s+[^\s]+\s*$", line):
            continue
        lines.append(line)
    return "\n".join(lines).strip()


def render_theory_module(
    *,
    namespace: str,
    imports: Sequence[str],
    body: str,
) -> str:
    import_block = "\n".join(f"import {module}" for module in imports)
    parts = [
        import_block,
        "set_option autoImplicit false",
        f"namespace {namespace}",
        _clean_text(body),
        f"end {namespace}",
    ]
    return "\n\n".join(part for part in parts if part).strip()


@dataclass(frozen=True)
class TheoryNeed:
    need_id: str
    domain: str
    target_statement: str
    need_kind: TheoryNeedKind
    mathematical_description: str
    originating_root: str
    consumer_node_id: str
    consumer_statement: str
    required_name_hint: str = ""
    evidence_kind: str = ""
    evidence_payload: Mapping[str, Any] = field(default_factory=dict)
    required_imports: tuple[str, ...] = ()
    dependency_need_ids: tuple[str, ...] = ()

    @staticmethod
    def derive_need_id(
        *,
        originating_root: str,
        domain: str,
        consumer_node_id: str,
        consumer_statement: str,
        required_name_hint: str = "",
        need_kind: str,
        required_imports: Sequence[str] = (),
        dependency_need_ids: Sequence[str] = (),
    ) -> str:
        """Derive the stable identity of an executable need contract."""

        identity = "|".join(
            (
                _clean_text(originating_root),
                _clean_text(domain),
                _clean_text(consumer_node_id),
                _clean_text(consumer_statement),
                _clean_text(required_name_hint),
                _clean_text(need_kind),
                ",".join(sorted(_clean_tuple(required_imports))),
                ",".join(sorted(_clean_tuple(dependency_need_ids))),
            )
        )
        return "need_" + hashlib.sha256(identity.encode()).hexdigest()[:16]

    def revised_with_dependencies(
        self,
        dependency_need_ids: Sequence[str],
    ) -> "TheoryNeed":
        """Return a new version when the executable dependency plan changes."""

        dependencies = tuple(sorted(_clean_tuple(dependency_need_ids)))
        return TheoryNeed(
            **{
                **self.to_dict(),
                "need_id": self.derive_need_id(
                    originating_root=self.originating_root,
                    domain=self.domain,
                    consumer_node_id=self.consumer_node_id,
                    consumer_statement=self.consumer_statement,
                    required_name_hint=self.required_name_hint,
                    need_kind=self.need_kind,
                    required_imports=self.required_imports,
                    dependency_need_ids=dependencies,
                ),
                "dependency_need_ids": dependencies,
            }
        )

    def __post_init__(self) -> None:
        required_text_fields = (
            "need_id",
            "domain",
            "target_statement",
            "mathematical_description",
            "originating_root",
            "consumer_node_id",
            "consumer_statement",
        )
        for field_name in required_text_fields:
            value = _clean_text(getattr(self, field_name))
            if not value:
                raise ValueError(f"TheoryNeed.{field_name} must be non-empty")
            object.__setattr__(self, field_name, value)
        need_kind = _clean_text(self.need_kind)
        if need_kind not in {
            "definition",
            "structure",
            "instance",
            "notation",
            "bridge_lemma",
            "theorem_family",
        }:
            raise ValueError(f"unsupported theory need kind: {need_kind!r}")
        object.__setattr__(self, "need_kind", need_kind)
        object.__setattr__(
            self,
            "required_name_hint",
            _clean_text(self.required_name_hint),
        )
        object.__setattr__(self, "evidence_kind", _clean_text(self.evidence_kind))
        object.__setattr__(self, "required_imports", _clean_tuple(self.required_imports))
        object.__setattr__(
            self,
            "dependency_need_ids",
            tuple(sorted(_clean_tuple(self.dependency_need_ids))),
        )
        evidence = json.loads(
            json.dumps(dict(self.evidence_payload or {}), ensure_ascii=False, default=str)
        )
        object.__setattr__(self, "evidence_payload", _freeze_json(evidence))

    def to_dict(self) -> dict[str, Any]:
        return {
            "need_id": self.need_id,
            "domain": self.domain,
            "target_statement": self.target_statement,
            "need_kind": self.need_kind,
            "mathematical_description": self.mathematical_description,
            "originating_root": self.originating_root,
            "consumer_node_id": self.consumer_node_id,
            "consumer_statement": self.consumer_statement,
            "required_name_hint": self.required_name_hint,
            "evidence_kind": self.evidence_kind,
            "evidence_payload": _thaw_json(self.evidence_payload),
            "required_imports": self.required_imports,
            "dependency_need_ids": self.dependency_need_ids,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "TheoryNeed":
        data = dict(payload)
        data["required_imports"] = tuple(data.get("required_imports") or ())
        data["dependency_need_ids"] = tuple(data.get("dependency_need_ids") or ())
        return cls(**data)


@dataclass(frozen=True)
class TheoryDeclaration:
    fq_name: str
    declaration_kind: str
    type_text: str
    referenced_constants: tuple[str, ...] = ()
    axioms: tuple[str, ...] = ()
    docstring: str = ""

    def __post_init__(self) -> None:
        if not _clean_text(self.fq_name):
            raise ValueError("TheoryDeclaration.fq_name must be non-empty")
        if not _clean_text(self.declaration_kind):
            raise ValueError("TheoryDeclaration.declaration_kind must be non-empty")
        if not _clean_text(self.type_text):
            raise ValueError("TheoryDeclaration.type_text must be non-empty")
        object.__setattr__(
            self, "referenced_constants", _clean_tuple(self.referenced_constants)
        )
        object.__setattr__(self, "axioms", _clean_tuple(self.axioms))

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "TheoryDeclaration":
        data = dict(payload)
        data["referenced_constants"] = tuple(data.get("referenced_constants") or ())
        data["axioms"] = tuple(data.get("axioms") or ())
        return cls(**data)


@dataclass(frozen=True)
class TheoryBundleCandidate:
    candidate_id: str
    bundle_id: str
    domain: str
    module_name: str
    namespace: str
    imports: tuple[str, ...]
    source: str
    source_hash: str
    dependency_bundle_ids: tuple[str, ...] = ()
    satisfies_need_ids: tuple[str, ...] = ()
    generated_by_run: str = ""
    generated_by_model: str = ""
    source_theorem: str = ""

    @classmethod
    def create(
        cls,
        *,
        domain: str,
        source: str,
        imports: Sequence[str] = (),
        dependency_bundle_ids: Sequence[str] = (),
        satisfies_need_ids: Sequence[str] = (),
        generated_by_run: str = "",
        generated_by_model: str = "",
        source_theorem: str = "",
    ) -> "TheoryBundleCandidate":
        clean_domain = _clean_text(domain)
        clean_source = _theory_body_without_imports(source)
        if not clean_domain:
            raise ValueError("domain must be non-empty")
        if not clean_source:
            raise ValueError("source must be non-empty")
        clean_imports = _clean_tuple(imports)
        clean_dependencies = _clean_tuple(dependency_bundle_ids)
        clean_needs = _clean_tuple(satisfies_need_ids)
        identity = {
            "schema_version": MINI_THEORY_SCHEMA_VERSION,
            "domain": clean_domain,
            "source": clean_source,
            "imports": clean_imports,
            "dependency_bundle_ids": clean_dependencies,
        }
        bundle_id = content_hash(_canonical_json(identity))
        domain_segment = sanitize_module_segment(clean_domain)
        module_name = (
            f"MiniTheory.Domains.{domain_segment}.Bundles.B_{bundle_id}.Theory"
        )
        namespace = f"MiniTheory.Domains.{domain_segment}.B_{bundle_id}"
        rendered_source = render_theory_module(
            namespace=namespace,
            imports=clean_imports,
            body=clean_source,
        )
        return cls(
            candidate_id=f"candidate_{bundle_id}",
            bundle_id=bundle_id,
            domain=clean_domain,
            module_name=module_name,
            namespace=namespace,
            imports=clean_imports,
            source=rendered_source,
            source_hash=content_hash(rendered_source, length=64),
            dependency_bundle_ids=clean_dependencies,
            satisfies_need_ids=clean_needs,
            generated_by_run=_clean_text(generated_by_run),
            generated_by_model=_clean_text(generated_by_model),
            source_theorem=_clean_text(source_theorem),
        )

    def to_dict(self, *, include_source: bool = True) -> dict[str, Any]:
        payload = asdict(self)
        if not include_source:
            payload.pop("source", None)
        return payload


@dataclass(frozen=True)
class TheoryVerificationReceipt:
    accepted: bool
    bundle_id: str
    module_name: str
    source_hash: str
    declarations: tuple[TheoryDeclaration, ...] = ()
    lean_toolchain: str = ""
    mathlib_revision: str = ""
    policy_version: int = THEORY_POLICY_VERSION
    verification_output_hash: str = ""
    compiled_artifact_hash: str = ""
    diagnostic: str = ""

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["declarations"] = [item.to_dict() for item in self.declarations]
        return payload

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "TheoryVerificationReceipt":
        data = dict(payload)
        data["declarations"] = tuple(
            TheoryDeclaration.from_dict(item)
            for item in list(data.get("declarations") or ())
        )
        return cls(**data)


@dataclass(frozen=True)
class PublishedTheoryBundle:
    schema_version: int
    bundle_id: str
    domain: str
    module_name: str
    namespace: str
    source_hash: str
    imports: tuple[str, ...]
    dependency_bundle_ids: tuple[str, ...]
    satisfies_need_ids: tuple[str, ...]
    declarations: tuple[TheoryDeclaration, ...]
    lean_toolchain: str
    mathlib_revision: str
    policy_version: int
    verification_output_hash: str
    compiled_artifact_hash: str
    generated_by_run: str = ""
    generated_by_model: str = ""
    source_theorem: str = ""
    created_ts: float = 0.0
    status: str = "published"
    manifest_hash: str = ""

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["declarations"] = [item.to_dict() for item in self.declarations]
        return payload

    def computed_manifest_hash(self) -> str:
        payload = self.to_dict()
        payload.pop("manifest_hash", None)
        return content_hash(_canonical_json(payload), length=64)

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "PublishedTheoryBundle":
        data = dict(payload)
        for key in ("imports", "dependency_bundle_ids", "satisfies_need_ids"):
            data[key] = tuple(data.get(key) or ())
        data["declarations"] = tuple(
            TheoryDeclaration.from_dict(item)
            for item in list(data.get("declarations") or ())
        )
        return cls(**data)

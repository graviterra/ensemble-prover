"""Host authorization and immutable dependency envelopes for projection output."""

from __future__ import annotations
from dataclasses import asdict, dataclass
from typing import Any, Callable
from .references import canonical_json, sha256_digest, valid_digest


@dataclass(frozen=True)
class AccessContext:
    principal: str
    role: str = "reader"
    audience: str = "public"
    answer_visibility: str = "public"
    scope: str | None = None


class HostPolicy:
    """Callbacks are supplied by the trusted host, never by a command body."""

    def __init__(
        self,
        authorize: Callable[[dict[str, Any], AccessContext], bool] | None = None,
        redact: Callable[[str, AccessContext], str] | None = None,
    ):
        self._authorize = authorize
        self._redact = redact

    def authorize(self, dependency: dict[str, Any], context: AccessContext) -> bool:
        try:
            return (
                self._authorize is not None
                and self._authorize(dependency, context) is True
            )
        except Exception:
            return False

    def redact(self, text: str, context: AccessContext) -> str:
        result = text if self._redact is None else self._redact(text, context)
        if not isinstance(result, str):
            raise ValueError("policy redaction must return text")
        return result


def context_binding(context: AccessContext) -> str:
    if (not isinstance(context, AccessContext)
            or any(not isinstance(value, str) or not value for value in (
                context.principal, context.role, context.audience, context.answer_visibility,
            ))
            or (context.scope is not None
                and (not isinstance(context.scope, str) or not context.scope))):
        raise ValueError("an authenticated context is required")
    return sha256_digest(canonical_json(asdict(context)))


def merge_envelopes(*envelopes: dict[str, Any]) -> dict[str, Any]:
    dependencies: dict[bytes, dict[str, Any]] = {}
    witnesses: dict[bytes, dict[str, Any]] = {}
    scopes: set[str] = set()
    context_bindings: set[str] = set()
    principal_sets: list[set[str]] = []
    operator_only = False
    deny = not envelopes
    for envelope in envelopes:
        if not isinstance(envelope, dict) or not isinstance(
            envelope.get("dependencies"), list
        ):
            deny = True
            continue
        deny = deny or bool(envelope.get("deny", False))
        operator_only = operator_only or bool(envelope.get("operator_only", False))
        bindings = envelope.get("context_bindings", [])
        if not isinstance(bindings, list) or any(not valid_digest(binding) for binding in bindings):
            deny = True
        else:
            context_bindings.update(bindings)
        if envelope.get("private_principals") is not None:
            principals = envelope["private_principals"]
            if not isinstance(principals, list) or any(
                not isinstance(p, str) or not p for p in principals
            ):
                deny = True
            else:
                principal_sets.append(set(principals))
        for dependency in envelope["dependencies"]:
            if (
                not isinstance(dependency, dict)
                or not isinstance(dependency.get("namespace"), str)
                or not dependency["namespace"]
            ):
                deny = True
                continue
            dependencies[canonical_json(dependency)] = dependency
        guards = envelope.get("redaction_witnesses", [])
        if not isinstance(guards, list):
            deny = True
        else:
            for witness in guards:
                if not isinstance(witness, dict):
                    deny = True
                    continue
                encoding = witness.get("encoding")
                expected_keys = {"object_digest", "encoding"}
                if encoding == "association-output-v1":
                    expected_keys.add("endpoint_applicability")
                    applicability = witness.get("endpoint_applicability")
                    if (not isinstance(applicability, dict)
                            or set(applicability) != {"source", "target"}
                            or any(not isinstance(value, str) or value not in {"historical", "unavailable"}
                                   for value in applicability.values())):
                        deny = True
                        continue
                if (set(witness) != expected_keys
                        or not valid_digest(witness.get("object_digest"))
                        or not isinstance(encoding, str)
                        or encoding not in {"json-v1", "text-v1", "visible-json-v1",
                                            "association-output-v1"}):
                    deny = True
                    continue
                witnesses[canonical_json(witness)] = dict(witness)
        scope = envelope.get("private_scope")
        if scope is not None:
            if isinstance(scope, str) and scope:
                scopes.add(scope)
            else:
                deny = True
        for scope in envelope.get("private_scopes", []):
            if isinstance(scope, str) and scope:
                scopes.add(scope)
            else:
                deny = True
    principals = set.intersection(*principal_sets) if principal_sets else None
    return {
        "private_principals": sorted(principals) if principals is not None else None,
        "operator_only": operator_only,
        "dependencies": [dependencies[k] for k in sorted(dependencies)],
        "redaction_witnesses": [witnesses[k] for k in sorted(witnesses)],
        "private_scope": next(iter(scopes)) if len(scopes) == 1 else None,
        "private_scopes": sorted(scopes),
        "context_bindings": sorted(context_bindings),
        "deny": deny or len(scopes) > 1 or len(context_bindings) > 1 or principals == set(),
    }


def authorize_envelope(
    envelope: dict[str, Any],
    policy: HostPolicy,
    context: AccessContext,
    *,
    witness_validator: Callable[[dict[str, Any]], bool] | None = None,
) -> bool:
    try:
        binding = context_binding(context)
        envelope = merge_envelopes(envelope)
        if envelope["deny"] or not envelope["dependencies"]:
            return False
        if envelope["context_bindings"] and envelope["context_bindings"] != [binding]:
            return False
        if (
            envelope["private_scope"] is not None
            and context.scope != envelope["private_scope"]
        ):
            return False
        if (
            envelope["private_principals"] is not None
            and context.principal not in envelope["private_principals"]
        ):
            return False
        if envelope["operator_only"] and (
            context.role != "operator" or context.audience != "operator"
        ):
            return False
        if not all(
            policy.authorize(dependency, context) is True
            for dependency in envelope["dependencies"]
        ):
            return False
        return all(
            witness_validator is not None and witness_validator(witness) is True
            for witness in envelope["redaction_witnesses"]
        )
    except Exception:
        return False


def redact_values(value: Any, policy: HostPolicy, context: AccessContext) -> Any:
    if isinstance(value, str):
        return policy.redact(value, context)
    if isinstance(value, list):
        return [redact_values(v, policy, context) for v in value]
    if isinstance(value, dict):
        result = {}
        for key, item in value.items():
            filtered_key = policy.redact(key, context)
            if filtered_key in result:
                raise ValueError("redaction collides with another visible key")
            result[filtered_key] = redact_values(item, policy, context)
        return result
    return value


class PolicyRedactionError(ValueError):
    """The host filter cannot produce a faithful structured projection."""


def assert_visible_output(value: Any, context: AccessContext) -> None:
    """Reject hidden owner values before output or installation.

    Source adapters remove hidden records before issuing a view. A retained raw
    library snapshot cannot silently drop records later: that would change exact
    membership and positional references beneath an issued digest.
    """
    context_binding(context)
    markers = {"hidden", "private", "checker_only", "checker-only"}
    marker_fields = {"visibility", "visibility_policy", "answer_visibility",
                     "verified_helper_visibility_policy"}
    hidden_fields = {"preamble", "lean_preamble", "checker_preamble", "checker_only_preamble",
                     "verification_preamble", "official_answer", "official_answer_payload",
                     "hidden_answer", "hidden_checker", "checker_only", "solution_payload"}
    pending = [(value, 0)]
    visited = 0
    while pending:
        item, depth = pending.pop()
        visited += 1
        if depth > 256 or visited > 1_000_000:
            raise PolicyRedactionError("visibility evaluation exceeds the projection bound")
        if isinstance(item, dict):
            if any(key.lower() in hidden_fields for key in item):
                raise PolicyRedactionError("hidden owner fields cannot be projected")
            if any(isinstance(item.get(key), str) and item[key].lower() in markers
                   for key in marker_fields):
                raise PolicyRedactionError("hidden owner records cannot be projected")
            pending.extend((child, depth + 1) for child in item.values())
        elif isinstance(item, list):
            pending.extend((child, depth + 1) for child in item)


def _merge_filtered_values(original: Any, decoded: Any, serialized: Any) -> Any:
    """Combine independently filtered representations without a second pass."""
    if decoded == original:
        return serialized
    if serialized == original or decoded == serialized:
        return decoded
    if (
        isinstance(original, dict)
        and isinstance(decoded, dict)
        and isinstance(serialized, dict)
        and original.keys() == decoded.keys() == serialized.keys()
    ):
        return {
            key: _merge_filtered_values(original[key], decoded[key], serialized[key])
            for key in original
        }
    if (
        isinstance(original, list)
        and isinstance(decoded, list)
        and isinstance(serialized, list)
        and len(original) == len(decoded) == len(serialized)
    ):
        return [
            _merge_filtered_values(a, b, c)
            for a, b, c in zip(original, decoded, serialized)
        ]
    raise PolicyRedactionError("incompatible structured redaction")


def _check_reference_identity(original: Any, filtered: Any) -> None:
    """A filtered label must never masquerade as a changed exact reference."""
    if isinstance(original, dict):
        if (
            original.get("version") == 1
            and isinstance(original.get("namespace"), str)
            and isinstance(original.get("kind"), str)
            and original["kind"]
            in {
                "source",
                "target",
                "context",
                "question",
                "helper",
                "graph",
                "view",
                "view_item",
                "association",
                "argument",
                "derived",
            }
        ):
            if canonical_json(original) != canonical_json(filtered):
                raise PolicyRedactionError("redaction changes an exact reference")
            return
        if isinstance(filtered, dict):
            for key, value in original.items():
                if key in filtered:
                    _check_reference_identity(value, filtered[key])
    elif isinstance(original, list) and isinstance(filtered, list):
        if len(original) != len(filtered):
            # Membership changes cannot safely retain positional source refs.
            raise PolicyRedactionError("redaction changes selected membership")
        for before, after in zip(original, filtered):
            _check_reference_identity(before, after)


def redact_output(value: Any, policy: HostPolicy, context: AccessContext) -> Any:
    """Filter decoded strings and the complete serialized selection before output.

    The two filters start from the same input. This avoids applying a literal
    replacement twice while still detecting escaped strings and contextual JSON
    policies. Incompatible filters and changed exact identities fail closed.
    """
    import json

    def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result = {}
        for key, item in pairs:
            if key in result:
                raise PolicyRedactionError("redaction collides with a visible key")
            result[key] = item
        return result

    decoded = redact_values(value, policy, context)
    text = canonical_json(value).decode("utf-8")
    filtered_text = policy.redact(text, context)
    try:
        serialized = (
            value
            if filtered_text == text
            else json.loads(filtered_text, object_pairs_hook=unique_object)
        )
        canonical_json(serialized)
    except (ValueError, TypeError, RecursionError) as exc:
        raise PolicyRedactionError("redaction is not valid structured data") from exc
    filtered = _merge_filtered_values(value, decoded, serialized)
    _check_reference_identity(value, filtered)

    def references(item: Any) -> list[bytes]:
        found = []
        pending = [item]
        while pending:
            current = pending.pop()
            if isinstance(current, dict):
                if (
                    current.get("version") == 1
                    and isinstance(current.get("namespace"), str)
                    and isinstance(current.get("kind"), str)
                    and current["kind"]
                    in {
                        "source",
                        "target",
                        "context",
                        "question",
                        "helper",
                        "graph",
                        "view",
                        "view_item",
                        "association",
                        "argument",
                        "derived",
                    }
                ):
                    found.append(canonical_json(current))
                else:
                    pending.extend(current.values())
            elif isinstance(current, list):
                pending.extend(current)
        return sorted(found)

    # Renaming a parent dictionary key must not hide an altered nested ref from
    # the path-by-path comparison above.
    if references(value) != references(filtered):
        raise PolicyRedactionError("redaction changes selected exact references")
    return filtered

"""Lifecycle-tied provenance for dispatch-sanitized exceptions.

Projected exceptions use authority-free subclasses of safe exception bases.
Their original SDK identity is needed by retry policy, but exception fields are
caller-writable and cannot attest provenance.  The private registry therefore
keys records by weak identity of the projected exception itself: metadata is
stable while the exception is live and disappears automatically afterward.
"""

from __future__ import annotations

import sys
import threading
import weakref
from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True, slots=True)
class DispatchExceptionProjection:
    original_module: str
    original_name: str
    is_canonical_original_type: bool


@dataclass(frozen=True, slots=True)
class _ProjectionRecord:
    original_module: str
    original_name: str
    is_canonical_original_type: bool


_PROJECTION_LOCK = threading.RLock()
_PROJECTIONS: dict[int, tuple[weakref.ReferenceType[BaseException], _ProjectionRecord]] = {}  # noqa: E501
_PROJECTED_TYPE_CACHE: dict[type[BaseException], type[BaseException]] = {}


def dispatch_projection_exception_type(
    safe_base: type[BaseException],
) -> type[BaseException]:
    """Return an authority-free weak-referenceable subtype of ``safe_base``."""

    with _PROJECTION_LOCK:
        cached = _PROJECTED_TYPE_CACHE.get(safe_base)
        if cached is not None:
            return cached
        safe_name = type.__dict__["__name__"].__get__(
            safe_base,
            type(safe_base),
        )
        if type(safe_name) is not str:
            safe_name = "BaseException"
        namespace = {
            "__slots__": ("__weakref__",),
            "__module__": __name__,
        }
        try:
            projected_type = type.__new__(
                type,
                f"_DispatchProjected{safe_name}",
                (safe_base,),
                namespace,
            )
        except TypeError:
            # Some trusted control exceptions already inherit weak-reference
            # storage (notably asyncio.CancelledError). Re-declaring the slot
            # is illegal, but an empty-slotted subtype remains weakrefable.
            projected_type = type.__new__(
                type,
                f"_DispatchProjected{safe_name}",
                (safe_base,),
                {"__slots__": (), "__module__": __name__},
            )
        _PROJECTED_TYPE_CACHE[safe_base] = projected_type
        return projected_type


def _canonical_original_type(
    original_type: type[BaseException],
    original_module: str,
    original_name: str,
) -> bool:
    module = sys.modules.get(original_module)
    module_namespace = (
        object.__getattribute__(module, "__dict__")
        if module is not None
        else None
    )
    return bool(
        type(module_namespace) is dict
        and dict.get(module_namespace, original_name) is original_type
    )


def _source_identity(source: BaseException) -> _ProjectionRecord:
    existing = _projection_record(source)
    if existing is not None:
        return existing
    original_type = type(source)
    namespace = type.__dict__["__dict__"].__get__(
        original_type,
        type(original_type),
    )
    original_module = namespace.get("__module__", "")
    if type(original_module) is not str:
        original_module = ""
    original_name = type.__dict__["__name__"].__get__(
        original_type,
        type(original_type),
    )
    if type(original_name) is not str:
        original_name = "BaseException"
    if not original_module:
        import builtins

        if vars(builtins).get(original_name) is original_type:
            original_module = "builtins"

    return _ProjectionRecord(
        original_module=original_module,
        original_name=original_name,
        is_canonical_original_type=_canonical_original_type(
            original_type,
            original_module,
            original_name,
        ),
    )


def project_dispatch_exception(
    source: BaseException,
    projected: BaseException,
) -> None:
    """Attest ``projected`` with identity derived solely from ``source``."""

    identity = id(projected)
    record = _source_identity(source)

    def discard(reference: weakref.ReferenceType[BaseException]) -> None:
        with _PROJECTION_LOCK:
            current = _PROJECTIONS.get(identity)
            if current is not None and current[0] is reference:
                _PROJECTIONS.pop(identity, None)

    reference = weakref.ref(projected, discard)
    with _PROJECTION_LOCK:
        _PROJECTIONS[identity] = (reference, record)


def _projection_record(exception: BaseException) -> Optional[_ProjectionRecord]:
    identity = id(exception)
    with _PROJECTION_LOCK:
        entry = _PROJECTIONS.get(identity)
        if entry is None or entry[0]() is not exception:
            return None
        return entry[1]


def dispatch_exception_projection(
    exception: BaseException,
) -> Optional[DispatchExceptionProjection]:
    """Return a detached inert copy of attested metadata for ``exception``."""

    record = _projection_record(exception)
    if record is None:
        return None
    return DispatchExceptionProjection(
        original_module=record.original_module,
        original_name=record.original_name,
        is_canonical_original_type=record.is_canonical_original_type,
    )


def dispatch_exception_projection_is_canonical(
    projection: DispatchExceptionProjection,
) -> bool:
    """Whether the recorded type is the module's exact exported class."""

    return bool(projection.is_canonical_original_type)


def _dispatch_exception_projection_registry_size() -> int:
    """Testing/diagnostic count of live projection attestations."""

    with _PROJECTION_LOCK:
        return len(_PROJECTIONS)

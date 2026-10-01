"""Stable error codes that cannot carry URLs, secrets, or filesystem paths."""

from __future__ import annotations

import re

_CODE = re.compile(r"^[a-z][a-z0-9_]{0,63}$")
_IDENTIFIER = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]{0,63}$")


class LocalInferenceError(ValueError):
    """Contract failure whose text is a code and optional identifier-safe ids."""

    def __init__(self, code: str, *safe_ids: str) -> None:
        if type(code) is not str or _CODE.fullmatch(code) is None:
            raise ValueError("unsafe_error_detail")
        checked: list[str] = []
        for item in safe_ids:
            if type(item) is not str or _IDENTIFIER.fullmatch(item) is None:
                raise ValueError("unsafe_error_detail")
            checked.append(item)
        self.code = code
        self.safe_ids = tuple(checked)
        message = code if not checked else code + ":" + ",".join(checked)
        super().__init__(message)

    def __reduce__(self) -> tuple[object, tuple[object, ...]]:
        return (_restore_local_inference_error, (self.code, self.safe_ids))


class ContextCapacityInsufficient(LocalInferenceError):
    """Declared prompt plus output does not fit the deployment context."""

    def __init__(self, *, needed: int, available: int) -> None:
        if type(needed) is not int or type(available) is not int:
            raise ValueError("unsafe_error_detail")
        super().__init__("context_capacity_insufficient")
        self.needed = needed
        self.available = available

    def __reduce__(self) -> tuple[object, tuple[object, ...]]:
        return (_restore_context_capacity, (self.needed, self.available))


def _restore_local_inference_error(code: str, safe_ids: tuple[str, ...]) -> LocalInferenceError:
    return LocalInferenceError(code, *safe_ids)


def _restore_context_capacity(needed: int, available: int) -> ContextCapacityInsufficient:
    return ContextCapacityInsufficient(needed=needed, available=available)

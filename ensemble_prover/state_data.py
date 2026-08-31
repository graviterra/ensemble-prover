"""Hook-free cloning for JSON-shaped execution records.

Execution-record handling must not invoke application-defined copy, reduction,
mapping, or iterator protocols. These helpers admit only exact builtin
containers and traverse them through their builtin implementations. Mapping
proxies are accepted only when their hidden backing object is an exact dict.
"""

from __future__ import annotations

import gc
import math
import types
from typing import Any


class StateDataError(TypeError):
    """A value is outside the hook-free execution-record data model."""


def mappingproxy_backing_dict(value: types.MappingProxyType) -> dict[Any, Any]:
    """Return a proxy's exact-dict backing without calling mapping methods."""

    referents = gc.get_referents(value)
    if len(referents) != 1 or type(referents[0]) is not dict:
        raise StateDataError(
            "mappingproxy state value must wrap an exact dict"
        )
    return referents[0]


def clone_json_value(value: Any, *, label: str = "state value") -> Any:
    """Clone a JSON-shaped graph without invoking object-controlled hooks.

    Tuples are retained because several in-memory execution codecs use them;
    canonical JSON serialization already represents them as arrays. Aliases
    are preserved and cycles are rejected with a field path.
    """

    memo: dict[int, Any] = {}
    active: dict[int, str] = {}

    def clone(item: Any, path: str) -> Any:
        item_type = type(item)
        if item is None or item_type in {str, bool, int}:
            return item
        if item_type is float:
            if not math.isfinite(item):
                raise StateDataError(f"{path} contains a non-finite float")
            return item

        identity = id(item)
        if identity in active:
            raise StateDataError(
                f"{path} contains a cycle through {active[identity]}"
            )
        if identity in memo:
            return memo[identity]

        if item_type is list:
            result: list[Any] = []
            memo[identity] = result
            active[identity] = path
            try:
                for index, child in enumerate(list.__iter__(item)):
                    list.append(result, clone(child, f"{path}[{index}]"))
            finally:
                active.pop(identity, None)
            return result

        if item_type is tuple:
            active[identity] = path
            try:
                result_tuple = tuple(
                    clone(child, f"{path}[{index}]")
                    for index, child in enumerate(tuple.__iter__(item))
                )
            finally:
                active.pop(identity, None)
            memo[identity] = result_tuple
            return result_tuple

        source: dict[Any, Any] | None = None
        if item_type is dict:
            source = item
        elif item_type is types.MappingProxyType:
            source = mappingproxy_backing_dict(item)
        if source is not None:
            result_dict: dict[Any, Any] = {}
            memo[identity] = result_dict
            active[identity] = path
            try:
                for index, (key, child) in enumerate(dict.items(source)):
                    cloned_key = clone(key, f"{path}.key[{index}]")
                    if type(cloned_key) not in {str, bool, int, float, type(None)}:
                        raise StateDataError(
                            f"{path} contains a non-JSON object key of type "
                            f"{type(key).__module__}.{type(key).__qualname__}"
                        )
                    dict.__setitem__(
                        result_dict,
                        cloned_key,
                        clone(child, f"{path}[{cloned_key!r}]"),
                    )
            finally:
                active.pop(identity, None)
            return result_dict

        raise StateDataError(
            f"{path} has unsupported type "
            f"{item_type.__module__}.{item_type.__qualname__}"
        )

    return clone(value, label)

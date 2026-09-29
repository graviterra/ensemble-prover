"""Serving identity and owned clones for explicitly transparent Mini fences.

Keep this adapter separate from the transport and session modules: a running
worker may lazily load research after caching earlier versions of those modules.
"""

from __future__ import annotations

from typing import Any


class _OwnedResearchClient:
    """Dispatch through all donor leases; close only the isolated transport."""

    __slots__ = ("__fenced_client", "__owned_transport")

    def __init__(self, fenced_client: Any, owned_transport: Any) -> None:
        object.__setattr__(self, "_OwnedResearchClient__fenced_client", fenced_client)
        object.__setattr__(
            self, "_OwnedResearchClient__owned_transport", owned_transport
        )

    def __getattr__(self, name: str) -> Any:
        client = object.__getattribute__(self, "_OwnedResearchClient__fenced_client")
        return getattr(client, name)

    def __setattr__(self, name: str, value: Any) -> None:
        client = object.__getattribute__(self, "_OwnedResearchClient__fenced_client")
        setattr(client, name, value)

    def __bool__(self) -> bool:
        client = object.__getattribute__(self, "_OwnedResearchClient__fenced_client")
        return bool(client)

    async def close(self) -> None:
        # Closing a clone remains safe after the donor lease is revoked. Its
        # shared parent transport is never reachable through this cleanup path.
        transport = object.__getattribute__(
            self, "_OwnedResearchClient__owned_transport"
        )
        await transport.close()


def mini_request_transparent_client_binding(client: Any) -> tuple[Any, tuple[Any, ...]]:
    """Return the serving client and its active, outer-to-inner lease fences.

    Arbitrary ``client`` attributes and identity hooks establish neither
    transparency nor cloning permission. Known fences remain authoritative for
    dispatch and must be restored when cloning a transport.
    """
    from .mini_session.recursive_helper_prover import (
        _RevocableRecursiveHelperCapability,
    )

    fences: list[Any] = []
    seen: set[int] = set()
    while type(client) in {_RevocableRecursiveHelperCapability, _OwnedResearchClient}:
        if id(client) in seen:
            raise RuntimeError("model wrapper cycle in Mini request envelope")
        seen.add(id(client))
        if type(client) is _OwnedResearchClient:
            client = object.__getattribute__(
                client, "_OwnedResearchClient__fenced_client"
            )
        else:
            client._require_active("serving-client identity")
            fences.append(client)
            client = client._dispatch_capability_identity_token()
    return client, tuple(fences)


def bind_owned_research_client(transport: Any, fences: tuple[Any, ...]) -> Any:
    """Preserve the donor's existing lease chain on a newly owned transport.

    Rebinding grants no fresh authority, even if a lease was revoked during
    clone allocation. Cleanup remains possible without reopening generation.
    """
    from .mini_session.recursive_helper_prover import (
        _RevocableRecursiveHelperCapability,
    )

    client = transport
    for fence in reversed(fences):
        client = _RevocableRecursiveHelperCapability(
            client,
            object.__getattribute__(
                fence, "_RevocableRecursiveHelperCapability__lease"
            ),
            label=object.__getattribute__(
                fence,
                "_RevocableRecursiveHelperCapability__capability_label",
            ),
        )
    return _OwnedResearchClient(client, transport) if fences else transport

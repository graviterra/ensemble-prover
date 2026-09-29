"""Browser and request-size boundaries for a loopback HTTP service."""

from __future__ import annotations

import asyncio
import json
import secrets
from urllib.parse import urlsplit

from starlette.datastructures import MutableHeaders
from starlette.responses import JSONResponse
from starlette.types import ASGIApp, Message, Receive, Scope, Send

MAX_BODY_BYTES = 64 * 1024
MAX_JSON_DEPTH = 32
MAX_JSON_ITEMS = 4096
BODY_TIMEOUT_S = 10.0


def browser_boundary(port: int, web_origin: str | None = None) -> tuple[set[str], set[str]]:
    """Return exact HTTP authorities and explicitly trusted browser origins."""
    if not 1 <= port <= 65535:
        raise ValueError("port must be between 1 and 65535")
    hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
    origins = {f"http://{host}" for host in hosts}
    if port == 80:
        hosts.update({"127.0.0.1", "localhost"})
        origins.update({"http://127.0.0.1", "http://localhost"})
    if web_origin is not None:
        parsed = urlsplit(web_origin)
        try:
            valid = (
                parsed.scheme == "http"
                and parsed.hostname in {"127.0.0.1", "localhost"}
                and parsed.port is not None
                and 1 <= parsed.port <= 65535
                and parsed.username is None
                and parsed.password is None
                and not parsed.path and not parsed.query and not parsed.fragment
                and web_origin == f"http://{parsed.hostname}:{parsed.port}"
            )
        except ValueError:
            valid = False
        if not valid:
            raise ValueError("web origin must be http://127.0.0.1:PORT or http://localhost:PORT")
        origins.add(web_origin)
    return hosts, origins


def _bounded_json(body: bytes | bytearray) -> bool:
    try:
        value = json.loads(body) if body.strip() else {}
    except (ValueError, RecursionError):
        return False
    if not isinstance(value, dict):
        return False
    pending = [(value, 0)]
    items = 0
    while pending:
        node, depth = pending.pop()
        items += 1
        if depth > MAX_JSON_DEPTH or items > MAX_JSON_ITEMS:
            return False
        if isinstance(node, dict):
            pending.extend((item, depth + 1) for item in node.values())
        elif isinstance(node, list):
            pending.extend((item, depth + 1) for item in node)
    return True


class LocalBoundary:
    """Reject unauthorized mutations before reading a byte of their bodies.

    Browser capability discovery is protected by exact host/origin checks,
    fetch metadata, and the browser's same-origin response policy. The random
    capability is held in page memory, never in a URL or a browser cookie.
    """

    def __init__(
        self, app: ASGIApp, *, allowed_hosts: set[str], allowed_origins: set[str],
        csrf_token: str, control: bool,
    ) -> None:
        self.app = app
        self.allowed_hosts = frozenset(allowed_hosts)
        self.allowed_origins = frozenset(allowed_origins)
        self.csrf_token = csrf_token
        self.control = control

    async def __call__(self, scope: Scope, receive: Receive, send: Send) -> None:
        if scope["type"] != "http":
            await self.app(scope, receive, send)
            return
        is_api = scope.get("path", "").startswith("/api/")

        async def protected_send(message: Message) -> None:
            if message["type"] == "http.response.start":
                headers = MutableHeaders(scope=message)
                headers["X-Frame-Options"] = "DENY"
                headers["X-Content-Type-Options"] = "nosniff"
                headers["Referrer-Policy"] = "no-referrer"
                headers["Content-Security-Policy"] = (
                    "default-src 'self'; script-src 'self'; style-src 'self'; "
                    "img-src 'self' data:; connect-src 'self'; frame-ancestors 'none'; "
                    "base-uri 'none'; object-src 'none'; form-action 'self'"
                )
                if is_api:
                    headers["Cache-Control"] = "no-store"
            await send(message)

        async def reject(status: int, error: str) -> None:
            await JSONResponse({"error": error}, status_code=status)(scope, receive, protected_send)

        headers: dict[bytes, list[bytes]] = {}
        for key, value in scope.get("headers", []):
            headers.setdefault(key.lower(), []).append(value)

        def single(key: bytes) -> str | None:
            values = headers.get(key, [])
            return values[0].decode("latin-1") if len(values) == 1 else None

        host = single(b"host")
        if host is None or host.lower() not in self.allowed_hosts:
            await reject(400, "host_rejected")
            return
        if b"origin" in headers and single(b"origin") not in self.allowed_origins:
            await reject(403, "origin_rejected")
            return
        if is_api and b"sec-fetch-site" in headers and single(b"sec-fetch-site") not in {"same-origin", "none"}:
            await reject(403, "origin_rejected")
            return
        if not is_api or scope.get("method") in {"GET", "HEAD", "OPTIONS"}:
            await self.app(scope, receive, protected_send)
            return
        if not self.control:
            await reject(403, "control_disabled")
            return
        capability = single(b"x-ensemble-csrf") or ""
        if not secrets.compare_digest(capability.encode("latin-1"), self.csrf_token.encode("ascii")):
            await reject(403, "csrf_rejected")
            return
        media_type = (single(b"content-type") or "").split(";", 1)[0].strip().lower()
        if media_type != "application/json":
            await reject(415, "json_required")
            return
        length = single(b"content-length")
        declared_length = None
        if b"content-length" in headers:
            if length is None or not length.isascii() or not length.isdecimal():
                await reject(400, "invalid_content_length")
                return
            # Compare digit length first so very long decimal headers stay cheap.
            normalized = length.lstrip("0") or "0"
            if len(normalized) > len(str(MAX_BODY_BYTES)) or int(normalized) > MAX_BODY_BYTES:
                await reject(413, "body_too_large")
                return
            declared_length = int(normalized)
        body = bytearray()
        try:
            async with asyncio.timeout(BODY_TIMEOUT_S):
                while True:
                    message = await receive()
                    if message["type"] == "http.disconnect":
                        return
                    if message["type"] != "http.request":
                        await reject(400, "invalid_body")
                        return
                    chunk = message.get("body", b"")
                    if len(body) + len(chunk) > MAX_BODY_BYTES:
                        await reject(413, "body_too_large")
                        return
                    body.extend(chunk)
                    if not message.get("more_body", False):
                        break
        except TimeoutError:
            await reject(408, "body_timeout")
            return
        if declared_length is not None and len(body) != declared_length:
            await reject(400, "invalid_content_length")
            return
        if not _bounded_json(body):
            await reject(400, "invalid_json")
            return
        replayed = False

        async def bounded_receive() -> Message:
            nonlocal replayed
            if not replayed:
                replayed = True
                return {"type": "http.request", "body": bytes(body), "more_body": False}
            return await receive()

        await self.app(scope, bounded_receive, protected_send)

"""Local HTTP interface for browsing runs and, when enabled, launching them.

Read endpoints project an attached console session. They do not decide whether
a run is solved; export state comes from ``console.summary``, which applies
the canonical solved-export policy. Launch and stop are refused unless this
process was created with control enabled. Request bodies cannot supply a
shell command or a free-form argument vector.
"""

from __future__ import annotations

import json
import secrets
import threading
import time
from pathlib import Path
from typing import Any

from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from starlette.concurrency import run_in_threadpool

from console.launcher import RegistryStateError
from console.runs import RunInfo, discover_runs, inspect_run_dir, is_run_dir, resolve_contained_directory
from console.session import AttachedRun
from console.viewmodel import cost_text, root_status_text
from .projection import (
    FormalizationCache,
    FormalizationDetailCache,
    SessionCache,
    decorate_detail,
    launch_by_path,
    launch_detail,
    launch_process,
    launch_updated_at,
    launches_for_request,
    library_launch,
    library_run,
)
from .catalog import CatalogError, ProjectCatalog
from .security import LocalBoundary, browser_boundary
from .options import OptionValidationError, option_args, option_schema

_STOP_TOKEN_TTL_S = 60.0
_STOP_MESSAGES = {
    "signalled": "One cooperative interrupt was delivered to the owned launch group.",
    "already_requested": "A stop was already requested; no second signal was sent.",
    "refused": "The launch is no longer running or its process identity could not be verified; no signal was sent.",
    "delivery_unknown": "The interrupt could not be confirmed. Check the local console for details.",
    "unknown": "The stop outcome is unavailable. Check the local console for details.",
}
_LIBRARY_LIMIT = 500
_FORBIDDEN_KEYS = frozenset({"command", "argv", "args", "shell"})
_ROLE_FLAGS = (
    ("prover", "--prover"),
    ("proverModel", "--prover-model"),
    ("refiner", "--refiner"),
    ("refinerModel", "--refiner-model"),
)
# mini_prover's parser flag. The request field is ``theorem``.
_THEOREM_FLAG = "--theorem-name"
_UI_DIST = Path(__file__).resolve().parent.parent / "web" / "dist"


def create_app(
    *,
    run_root: Path,
    state_root: Path,
    repo_root: Path,
    control: bool = False,
    registry: Any = None,
    port: int = 8765,
    web_origin: str | None = None,
    serve_ui: bool = True,
    project_roots: list[Path] | None = None,
) -> FastAPI:
    """Build the loopback service.

    ``registry`` is the console launch registry. When control is on and no
    registry is supplied, one is created for ``state_root``. When control is
    off, no registry is created and launch or stop handlers do not call one.
    """
    run_root = Path(run_root)
    state_root = Path(state_root)
    repo_root = Path(repo_root)
    if registry is None and control:
        from console.launcher import LaunchRegistry

        registry = LaunchRegistry(state_root, repo_root=repo_root, run_root=run_root)

    app = FastAPI(
        title="Ensemble Prover",
        description=(
            "Local library of prover runs. Export badges follow the canonical "
            "solved-export policy. Starting or stopping a run requires the "
            "service to be started with control enabled."
        ),
    )
    app.state.run_root = run_root
    app.state.state_root = state_root
    app.state.repo_root = repo_root
    app.state.control = bool(control)
    app.state.registry = registry
    app.state.csrf_token = secrets.token_urlsafe(32)
    app.state.sessions = SessionCache()
    app.state.formalizations = FormalizationCache()
    app.state.formalization_details = FormalizationDetailCache()
    app.state.stop_grants = {}
    app.state.stop_lock = threading.Lock()
    app.state.catalog = ProjectCatalog(repo_root, state_root, roots=project_roots)
    allowed_hosts, allowed_origins = browser_boundary(port, web_origin)
    app.add_middleware(
        LocalBoundary,
        allowed_hosts=allowed_hosts,
        allowed_origins=allowed_origins,
        csrf_token=app.state.csrf_token,
        control=app.state.control,
    )

    @app.exception_handler(RegistryStateError)
    async def registry_state_error(_request: Request, _error: RegistryStateError) -> JSONResponse:
        return JSONResponse({
            "error": "registry_state_unavailable",
            "detail": (
                "Saved launch state cannot be read or updated safely. An action may have been dispatched. "
                "Preserve the state and this request's retry identity; restore valid state before retrying."
            ),
        }, status_code=503)

    @app.get("/api/session")
    def session() -> JSONResponse:
        return JSONResponse(
            {"csrfToken": app.state.csrf_token, "control": app.state.control}
        )

    @app.get("/api/options")
    def options() -> JSONResponse:
        return JSONResponse(option_schema())

    @app.get("/api/library")
    def library() -> JSONResponse:
        launches = launches_for_request(app.state.state_root, app.state.registry)
        by_path = launch_by_path(launches, app.state.run_root)
        return JSONResponse({"runs": _library_rows(app, by_path)})

    @app.get("/api/catalog")
    def catalog_home() -> JSONResponse:
        return JSONResponse(app.state.catalog.workspace(control=app.state.control))

    @app.get("/api/browse")
    def catalog_browse(path: str = "") -> JSONResponse:
        try:
            return JSONResponse(app.state.catalog.browse(path))
        except CatalogError as exc:
            return JSONResponse({"error": exc.public_message}, status_code=400)

    @app.get("/api/project")
    def catalog_project(path: str = "") -> JSONResponse:
        try:
            return JSONResponse(app.state.catalog.project(path))
        except CatalogError as exc:
            return JSONResponse({"error": exc.public_message}, status_code=400)

    @app.get("/api/theorems")
    def catalog_theorems(project: str = "", file: str = "") -> JSONResponse:
        try:
            return JSONResponse(app.state.catalog.theorems(project, file))
        except CatalogError as exc:
            return JSONResponse({"error": exc.public_message}, status_code=400)

    @app.get("/api/runs/{run_id:path}")
    def run_detail(run_id: str) -> JSONResponse:
        launches = launches_for_request(app.state.state_root, app.state.registry)
        by_path = launch_by_path(launches, app.state.run_root)
        run_dir = _resolve_contained(app.state.run_root, run_id)
        if run_dir is None:
            owned_dir, record = _owned_directory(app, run_id, by_path)
            if owned_dir is None or record is None:
                return JSONResponse({"error": "not_found"}, status_code=404)
            projected = launch_detail(
                record, app.state.run_root, app.state.state_root, app.state.formalization_details,
            )
            return JSONResponse(projected) if projected is not None else JSONResponse({"error": "not_found"}, status_code=404)
        record = by_path.get(run_dir.resolve()) or _registry_owned(app, run_dir)
        body = app.state.sessions.project(
            run_dir,
            lambda attached: _run_detail_body(app, run_dir, record, attached),
        )
        return JSONResponse(body)

    @app.post("/api/attempts")
    async def start_attempt(request: Request) -> JSONResponse:
        payload = await _json_object(request)
        if isinstance(payload, JSONResponse):
            return payload
        if _has_forbidden_key(payload):
            return JSONResponse(
                {"error": "command is not accepted; this service does not run a shell"},
                status_code=400,
            )
        if not app.state.control or app.state.registry is None:
            return JSONResponse({"error": "control_disabled"}, status_code=403)
        validate_state = getattr(app.state.registry, "validate_state", None)
        if callable(validate_state):
            await run_in_threadpool(validate_state)
        kind = payload.get("kind")
        if kind == "english":
            return await run_in_threadpool(_start_english, app, payload)
        if kind == "lean":
            return await run_in_threadpool(_start_lean, app, payload)
        return JSONResponse({"error": "kind must be english or lean"}, status_code=400)

    @app.post("/api/runs/{run_id:path}/stop")
    async def stop_run(run_id: str, request: Request) -> JSONResponse:
        if not app.state.control or app.state.registry is None:
            return JSONResponse({"error": "control_disabled"}, status_code=403)
        payload = await _json_object(request)
        if isinstance(payload, JSONResponse):
            return payload
        run_dir = _resolve_contained(app.state.run_root, run_id)
        if run_dir is None:
            run_dir, _record = await run_in_threadpool(_owned_directory, app, run_id, {})
        if run_dir is None:
            return JSONResponse({"error": "not_found"}, status_code=404)
        owned = await run_in_threadpool(app.state.registry.owned, run_dir)
        if owned is None:
            return JSONResponse({"error": "not_owned", "signalled": False}, status_code=403)
        launch_id = str(getattr(owned, "launch_id", "") or "")
        if not launch_id:
            return JSONResponse({"error": "not_owned", "signalled": False}, status_code=403)
        subject = _public_id(app.state.run_root, run_dir)
        token = payload.get("confirmToken")
        if "confirmToken" not in payload or token == "":
            issued = _issue_stop_token(app, subject, launch_id)
            return JSONResponse({"signalled": False, "confirmToken": issued})
        if not isinstance(token, str) or not _consume_stop_token(app, subject, token, launch_id):
            return JSONResponse(
                {"error": "confirmation_rejected", "signalled": False},
                status_code=409,
            )
        result = await run_in_threadpool(app.state.registry.stop, launch_id, request_id=token)
        raw_outcome = getattr(result, "outcome", "")
        outcome = raw_outcome if isinstance(raw_outcome, str) and raw_outcome in _STOP_MESSAGES else "unknown"
        return JSONResponse(
            {
                "signalled": outcome == "signalled",
                "outcome": outcome,
                "detail": _STOP_MESSAGES[outcome],
            }
        )

    if serve_ui and (_UI_DIST / "index.html").is_file():
        app.mount("/", StaticFiles(directory=_UI_DIST, html=True), name="ui")
    elif serve_ui:
        @app.get("/", response_class=HTMLResponse)
        def missing_ui() -> HTMLResponse:
            return HTMLResponse(
                "<h1>Browser page is not built</h1>"
                "<p>From the repository root run:</p>"
                "<pre>cd interface/web\nnpm ci\nnpm run build</pre>"
                "<p>See interface/README.md for setup.</p>",
                status_code=503,
            )
    return app


def _library_rows(app: FastAPI, by_path: dict[Path, Any]) -> list[dict[str, Any]]:
    run_root = app.state.run_root
    state_root = app.state.state_root
    candidates: dict[Path, tuple[RunInfo | None, Any | None, float]] = {}
    for info in discover_runs(run_root, limit=_LIBRARY_LIMIT):
        path = info.path.resolve()
        candidates[path] = (info, by_path.get(path), info.last_write_ts or 0.0)
    for path, record in by_path.items():
        info, _previous, written = candidates.get(path, (None, None, 0.0))
        latest = launch_updated_at(record, state_root, include_created=info is None)
        candidates[path] = (info, record, max(written, latest or 0.0))
    selected = sorted(
        candidates.items(),
        key=lambda item: (item[1][2], _public_id(run_root, item[0])),
        reverse=True,
    )[:_LIBRARY_LIMIT]
    rows: list[dict[str, Any]] = []
    for path, (info, record, _written) in selected:
        if info is None and is_run_dir(path):
            info = inspect_run_dir(path)
        if info is not None:
            row = library_run(info, run_root, record, state_root, app.state.formalizations)
        else:
            row = library_launch(record, run_root, state_root, app.state.formalizations)
        if row is not None:
            rows.append(row)
    rows.sort(key=lambda row: (row.get("lastWriteTs") or 0.0, row["id"]), reverse=True)
    return rows


def _problem(attached: AttachedRun) -> str:
    return attached.summary.problem or attached.state.theorem or ""


def _run_detail_body(
    app: FastAPI, run_dir: Path, record: Any | None, attached: AttachedRun
) -> dict[str, Any]:
    state = attached.state
    summary = attached.summary
    body = {
        "id": _public_id(app.state.run_root, run_dir),
        "label": attached.info.label,
        "kind": attached.info.kind,
        "problem": _problem(attached),
        "exportState": summary.export_state,
        "internalSolved": summary.internal_solved,
        "rootStatus": root_status_text(state, summary),
        "hasSummary": attached.info.has_summary,
        "childRootFinalizations": int(state.child_root_finalizations),
        "lastEventS": state.last_elapsed_s if state.rows else None,
        "cost": cost_text(state, summary),
        "process": launch_process(record) if record is not None else {
            "status": attached.liveness.status,
            "detail": attached.liveness.detail,
        },
        "lanes": [
            {"name": lane.name, "count": lane.count, "lastText": lane.last_text,
             "lastElapsedS": lane.last_elapsed_s}
            for lane in state.lanes.values()
        ],
        "graph": _graph(attached),
        "events": [
            {"elapsedS": line.elapsed_s, "scope": line.scope, "kind": line.kind, "text": line.text}
            for line in list(state.transcript)[-100:]
        ],
    }
    decorate_detail(body, attached, record, app.state.state_root, app.state.formalization_details)
    return body


def _public_id(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.name


def _owned_directory(
    app: FastAPI, selector: str, by_path: dict[Path, Any]
) -> tuple[Path | None, Any | None]:
    """A launch directory that exists before the prover has written a marker."""

    candidate = resolve_contained_directory(Path(app.state.run_root), selector)
    if candidate is None:
        return None, None
    record = by_path.get(candidate) or _registry_owned(app, candidate)
    return (candidate, record) if record is not None else (None, None)


def _registry_owned(app: FastAPI, run_dir: Path) -> Any | None:
    registry = app.state.registry
    owned = getattr(registry, "owned", None)
    if not callable(owned):
        return None
    try:
        return owned(run_dir)
    except Exception:  # noqa: BLE001 - browsing fails closed if registry state is unavailable
        return None


def _resolve_contained(root: Path, selector: str) -> Path | None:
    found = resolve_contained_directory(root, selector)
    return found if found is not None and is_run_dir(found) else None


def _graph(attached: AttachedRun) -> list[dict[str, Any]]:
    """Root first, then accepted helpers.

    ``verified_export`` is used only when the summary's export state is
    ``verified``. Internal root acceptance stays ``selected``.
    """
    summary = attached.summary
    state = attached.state
    if summary.export_state == "verified":
        status = "verified_export"
    else:
        status = {
            "unresolved": "unresolved",
            "root_finalization_accepted": "selected",
            "root_solved_internal": "selected",
        }.get(state.root_status, "unresolved")
        if status == "verified_export":
            status = "unresolved"
    nodes = [
        {
            "id": "root",
            "label": _problem(attached) or "root",
            "kind": "root",
            "status": status,
            "supports": [f"helper:{name}" for name in dict.fromkeys(state.root_dependency_helper_names)
                         if name in state.helpers_accepted],
            "recordedAtS": state.root_status_elapsed_s,
        }
    ]
    for name, elapsed in sorted(state.helpers_accepted.items(), key=lambda item: (item[1], item[0])):
        nodes.append(
            {
                "id": f"helper:{name}",
                "label": name,
                "kind": "helper",
                "status": "recorded",
                "supports": [f"helper:{support}" for support in dict.fromkeys(state.helper_supports.get(name, []))
                             if support in state.helpers_accepted and support != name],
                "recordedAtS": elapsed,
            }
        )
    return nodes


async def _json_object(request: Request) -> dict[str, Any] | JSONResponse:
    raw = await request.body()
    if not raw.strip():
        return {}
    try:
        parsed = json.loads(raw)
    except ValueError:
        return JSONResponse({"error": "invalid JSON"}, status_code=400)
    if not isinstance(parsed, dict):
        return JSONResponse({"error": "expected a JSON object"}, status_code=400)
    return parsed


def _has_forbidden_key(value: Any) -> bool:
    if isinstance(value, dict):
        for key, item in value.items():
            if str(key).lower() in _FORBIDDEN_KEYS or _has_forbidden_key(item):
                return True
        return False
    if isinstance(value, list):
        return any(_has_forbidden_key(item) for item in value)
    return False


def _line(payload: dict[str, Any], key: str, *, required: bool = False) -> str | JSONResponse:
    if key not in payload or payload[key] in (None, ""):
        if required:
            return JSONResponse({"error": f"{key} is required"}, status_code=400)
        return ""
    value = payload[key]
    if not isinstance(value, str) or any(ch in value for ch in "\0\n\r") or value.startswith("-"):
        return JSONResponse({"error": f"{key} must be a single line string"}, status_code=400)
    return value


def _role_args(payload: dict[str, Any]) -> list[str] | JSONResponse:
    args: list[str] = []
    for key, flag in _ROLE_FLAGS:
        value = _line(payload, key)
        if isinstance(value, JSONResponse):
            return value
        if value:
            args.extend([flag, value])
    return args


def _idempotency_key(payload: dict[str, Any]) -> str | JSONResponse:
    if "idempotencyKey" not in payload or payload["idempotencyKey"] in (None, ""):
        return secrets.token_hex(16)
    value = payload["idempotencyKey"]
    if not isinstance(value, str) or not value.strip() or any(ch in value for ch in "\0\n\r \t"):
        return JSONResponse({"error": "idempotencyKey must be a single token"}, status_code=400)
    if len(value) > 200:
        return JSONResponse({"error": "idempotencyKey is too long"}, status_code=400)
    return value


def _slug(value: str) -> str:
    slug = "".join(ch.lower() if ch.isalnum() else "_" for ch in value.strip())
    while "__" in slug:
        slug = slug.replace("__", "_")
    return slug.strip("_")[:48] or "run"


def _launch_body(run_root: Path, record: Any) -> dict[str, str]:
    output_dir = str(getattr(record, "output_dir", "") or "")
    return {
        "runId": _public_id(run_root, Path(output_dir)) if output_dir else "",
        "launchId": str(getattr(record, "launch_id", "") or ""),
        "launchStatus": str(getattr(record, "status", "") or ""),
    }


def _launch_response(run_root: Path, record: Any) -> JSONResponse:
    if str(getattr(record, "status", "") or "") == "launch_failed":
        error = str(getattr(record, "spawn_error", "") or "")
        if error.startswith("FileNotFoundError:"):
            detail = "The launcher executable was not found."
        elif error.startswith("PermissionError:"):
            detail = "The launcher executable could not be started due to its permissions."
        else:
            detail = "The launcher could not start the process."
        return JSONResponse(
            {"error": "launch_failed", "detail": detail},
            status_code=503,
        )
    return JSONResponse(_launch_body(run_root, record), status_code=201)


def _public_launch_rejection(detail: object) -> str:
    """Keep validator stderr and exception details in the local console only."""
    messages = {
        "invalid provider choice": "invalid provider choice",
        "empty theorem text": "The theorem text must not be empty.",
        "project path must contain a Lake project (lakefile.toml or lakefile.lean)":
            "Choose a Lake project containing lakefile.toml or lakefile.lean.",
        "translate-only does not accept prover arguments":
            "Translation only does not accept prover arguments.",
        "argument contains an invalid character":
            "A launch setting contains an invalid character.",
    }
    if isinstance(detail, str) and detail in messages:
        return messages[detail]
    return "The launch settings were rejected. Check the selected project, theorem and options."


def _start_english(app: FastAPI, payload: dict[str, Any]) -> JSONResponse:
    text = payload.get("text")
    if not isinstance(text, str) or not text.strip() or any(ch in text for ch in "\0"):
        return JSONResponse({"error": "text is required"}, status_code=400)
    project = _line(payload, "projectPath", required=True)
    if isinstance(project, JSONResponse):
        return project
    try:
        project_path = Path(project).expanduser()
        if not project_path.is_absolute():
            project_path = app.state.repo_root / project_path
        project_path = project_path.resolve()
    except (OSError, RuntimeError, ValueError):
        return JSONResponse({"error": "projectPath must identify a valid local path"}, status_code=400)
    formalize_only = payload.get("formalizeOnly", False)
    if not isinstance(formalize_only, bool):
        return JSONResponse({"error": "formalizeOnly must be true or false"}, status_code=400)
    try:
        settings_args = option_args(
            payload.get("options", {}), refiner_enabled=bool(payload.get("refiner")),
            proof_search=not formalize_only,
        )
    except OptionValidationError as exc:
        return JSONResponse({"error": exc.public_message}, status_code=400)
    except ValueError:
        return JSONResponse({"error": "Invalid launch options. Choose settings from the available options."}, status_code=400)
    user_args = [] if formalize_only else _role_args(payload)
    if isinstance(user_args, JSONResponse):
        return user_args
    if not formalize_only:
        user_args.extend(settings_args)
        verdict = app.state.registry.validate_args([
            "--lean-file", "Problem.lean", "--theorem-name", "formalized_problem",
            "--project-path", str(project_path), *user_args,
        ])
        if not verdict.ok:
            return JSONResponse({"error": _public_launch_rejection(verdict.error)}, status_code=400)
    idempotency_key = _idempotency_key(payload)
    if isinstance(idempotency_key, JSONResponse):
        return idempotency_key
    record, detail = app.state.registry.launch_nl(
        text,
        project_path=project_path,
        user_args=user_args,
        idempotency_key=idempotency_key,
        formalize_only=formalize_only,
    )
    if record is None:
        return JSONResponse({"error": _public_launch_rejection(detail)}, status_code=400)
    return _launch_response(app.state.run_root, record)


def _start_lean(app: FastAPI, payload: dict[str, Any]) -> JSONResponse:
    fields: dict[str, str] = {}
    for key in ("projectPath", "leanFile", "theorem"):
        value = _line(payload, key, required=True)
        if isinstance(value, JSONResponse):
            return value
        fields[key] = value
    try:
        project = Path(fields["projectPath"]).expanduser()
        if not project.is_absolute():
            project = app.state.repo_root / project
        project = project.resolve()
        lean_file = Path(fields["leanFile"]).expanduser()
        if not lean_file.is_absolute():
            lean_file = project / lean_file
        fields["projectPath"] = str(project)
        fields["leanFile"] = str(lean_file.resolve())
    except (OSError, RuntimeError, ValueError):
        return JSONResponse({"error": "projectPath and leanFile must identify valid local paths"}, status_code=400)
    user_args = _role_args(payload)
    if isinstance(user_args, JSONResponse):
        return user_args
    try:
        user_args.extend(option_args(
            payload.get("options", {}), refiner_enabled=bool(payload.get("refiner")),
        ))
    except OptionValidationError as exc:
        return JSONResponse({"error": exc.public_message}, status_code=400)
    except ValueError:
        return JSONResponse({"error": "Invalid launch options. Choose settings from the available options."}, status_code=400)
    idempotency_key = _idempotency_key(payload)
    if isinstance(idempotency_key, JSONResponse):
        return idempotency_key
    constructed = [
        "--lean-file",
        fields["leanFile"],
        _THEOREM_FLAG,
        fields["theorem"],
        "--project-path",
        fields["projectPath"],
        *user_args,
    ]
    record, detail = app.state.registry.launch(
        constructed,
        slug=_slug(fields["theorem"]),
        idempotency_key=idempotency_key,
    )
    if record is None:
        return JSONResponse({"error": _public_launch_rejection(detail)}, status_code=400)
    return _launch_response(app.state.run_root, record)


def _issue_stop_token(app: FastAPI, run_id: str, launch_id: str) -> str:
    token = secrets.token_urlsafe(24)
    now = time.monotonic()
    with app.state.stop_lock:
        grants: dict[str, dict[str, Any]] = app.state.stop_grants
        for key, grant in list(grants.items()):
            same_run = grant["run_id"] == run_id and grant["launch_id"] == launch_id
            if grant["expires_at"] <= now or (same_run and not grant["used"]):
                del grants[key]
        grants[token] = {
            "run_id": run_id,
            "launch_id": launch_id,
            "expires_at": now + _STOP_TOKEN_TTL_S,
            "used": False,
        }
    return token


def _consume_stop_token(app: FastAPI, run_id: str, token: str, launch_id: str) -> bool:
    now = time.monotonic()
    with app.state.stop_lock:
        grant = app.state.stop_grants.get(token)
        if grant is None:
            return False
        if grant["used"] or grant["expires_at"] <= now:
            return False
        if grant["run_id"] != run_id or grant["launch_id"] != launch_id:
            return False
        grant["used"] = True
        return True

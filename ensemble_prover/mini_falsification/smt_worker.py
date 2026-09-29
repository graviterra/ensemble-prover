"""Internal isolated worker for optional native SMT candidate generation.

The falsification service launches this module with bounded schema-versioned
JSON over standard input/output. Solver models are advisory candidates only;
the parent must replay every proposed counterexample in Lean.
"""

from __future__ import annotations

import json
import sys
from typing import Any


def _z3(
    script: str,
    symbols: list[dict[str, str]],
    timeout_ms: int,
) -> dict[str, Any]:
    import z3

    solver = z3.Solver()
    solver.set(timeout=timeout_ms, random_seed=0)
    solver.from_string(script)
    status = solver.check()
    if status == z3.sat:
        model = solver.model()
        values: dict[str, str] = {}
        sort_builders = {
            "Bool": z3.BoolSort,
            "Int": z3.IntSort,
            "Real": z3.RealSort,
        }
        for symbol in symbols:
            name = symbol["name"]
            sort_name = symbol["sort"]
            if sort_name not in sort_builders:
                raise ValueError(f"unsupported model sort {sort_name!r}")
            term = z3.Const(name, sort_builders[sort_name]())
            # model_completion is essential for binders eliminated as
            # irrelevant by simplification (especially unconstrained Bool).
            rendered = str(model.eval(term, model_completion=True))
            values[name] = rendered.lower() if sort_name == "Bool" else rendered
        return {
            "backend": "z3",
            "status": "sat",
            "values": values,
            "version": z3.get_version_string(),
        }
    return {
        "backend": "z3",
        "status": "unsat" if status == z3.unsat else "unknown",
        "reason": solver.reason_unknown() if status == z3.unknown else "",
        "version": z3.get_version_string(),
    }


def _cvc5(
    script: str,
    symbols: list[dict[str, str]],
    timeout_ms: int,
) -> dict[str, Any]:
    import cvc5

    solver = cvc5.Solver()
    solver.setOption("produce-models", "true")
    solver.setOption("tlimit-per", str(timeout_ms))
    parser = cvc5.InputParser(solver)
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, script, "mini_falsification")
    symbol_manager = parser.getSymbolManager()
    while not parser.done():
        command = parser.nextCommand()
        if not command.isNull():
            command.invoke(solver, symbol_manager)
    status = solver.checkSat()
    version = solver.getVersion()
    version_text = version.decode() if isinstance(version, bytes) else str(version)
    if status.isSat():
        declared = {str(term): term for term in symbol_manager.getDeclaredTerms()}
        values: dict[str, str] = {}
        for symbol in symbols:
            name = symbol["name"]
            if name not in declared:
                raise ValueError(f"declared SMT symbol {name!r} missing from model")
            values[name] = str(solver.getValue(declared[name]))
        return {
            "backend": "cvc5",
            "status": "sat",
            "values": values,
            "version": version_text,
        }
    return {
        "backend": "cvc5",
        "status": "unsat" if status.isUnsat() else "unknown",
        "version": version_text,
    }


def main() -> int:
    try:
        raw = sys.stdin.buffer.read(1_000_001)
        if len(raw) > 1_000_000:
            raise ValueError("input cap exceeded")
        payload = json.loads(raw.decode("utf-8"))
        if int(payload.get("schema") or 0) != 1:
            raise ValueError("unsupported worker schema")
        script = str(payload.get("script") or "")
        raw_symbols = payload.get("symbols") or ()
        if not isinstance(raw_symbols, list):
            raise ValueError("symbols must be a list")
        symbols: list[dict[str, str]] = []
        for item in raw_symbols:
            if not isinstance(item, dict):
                raise ValueError("symbol descriptors must be objects")
            name = str(item.get("name") or "")
            sort = str(item.get("sort") or "")
            if not name or sort not in {"Bool", "Int", "Real"}:
                raise ValueError("invalid symbol descriptor")
            symbols.append({"name": name, "sort": sort})
        timeout_ms = max(1, min(300_000, int(payload.get("timeout_ms") or 1)))
        results = []
        for backend in payload.get("backends") or ():
            try:
                if backend == "z3":
                    results.append(_z3(script, symbols, timeout_ms))
                elif backend == "cvc5":
                    results.append(_cvc5(script, symbols, timeout_ms))
            except Exception as exc:
                results.append(
                    {
                        "backend": str(backend),
                        "status": "error",
                        "error": f"{type(exc).__name__}: {exc}"[:1000],
                    }
                )
        output = json.dumps({"status": "ok", "results": results}, separators=(",", ":"))
        sys.stdout.write(output[:1_000_000])
        return 0
    except Exception as exc:
        sys.stderr.write(f"{type(exc).__name__}: {exc}"[:2000])
        return 2


if __name__ == "__main__":
    raise SystemExit(main())

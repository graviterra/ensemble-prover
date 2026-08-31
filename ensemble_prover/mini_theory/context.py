"""Structured composition of problem preambles and published theory imports."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable

from .model import content_hash
from ..theorem_project import _mask_noncode


_IMPORT_LINE_RE = re.compile(r"^\s*import\s+([^\s]+)\s*$")
_MODULE_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")


@dataclass(frozen=True)
class TheoryContext:
    base_header: str
    base_preamble: str
    base_imports: tuple[str, ...]
    theory_imports: tuple[str, ...] = ()
    bundle_ids: tuple[str, ...] = ()
    theory_inventory: tuple[str, ...] = ()

    @classmethod
    def from_preamble(cls, preamble: str) -> "TheoryContext":
        imports: list[str] = []
        header_lines: list[str] = []
        body_lines: list[str] = []
        source = str(preamble or "")
        source_lines = source.splitlines()
        masked_lines = _mask_noncode(source).splitlines()
        for index, line in enumerate(source_lines):
            masked_line = masked_lines[index] if index < len(masked_lines) else ""
            stripped = masked_line.strip()
            if stripped == "prelude" or stripped == "module" or stripped.startswith("module "):
                header_lines.append(line)
                continue
            match = _IMPORT_LINE_RE.match(masked_line)
            if match is None:
                body_lines.append(line)
                continue
            module = match.group(1).strip()
            if module not in imports:
                imports.append(module)
        return cls(
            base_header="\n".join(header_lines).strip(),
            base_preamble="\n".join(body_lines).strip(),
            base_imports=tuple(imports),
        )

    def with_theory(
        self,
        *,
        modules: Iterable[str],
        bundle_ids: Iterable[str],
        inventory: Iterable[str] = (),
    ) -> "TheoryContext":
        clean_modules = tuple(
            dict.fromkeys(str(item or "").strip() for item in modules if str(item or "").strip())
        )
        for module in clean_modules:
            if _MODULE_NAME_RE.fullmatch(module) is None:
                raise ValueError(f"invalid Lean module name: {module!r}")
        return TheoryContext(
            base_header=self.base_header,
            base_preamble=self.base_preamble,
            base_imports=self.base_imports,
            theory_imports=tuple(dict.fromkeys((*self.theory_imports, *clean_modules))),
            bundle_ids=tuple(
                dict.fromkeys(
                    (*self.bundle_ids, *(str(item or "").strip() for item in bundle_ids if str(item or "").strip()))
                )
            ),
            theory_inventory=tuple(
                dict.fromkeys(
                    (*self.theory_inventory, *(str(item or "").strip() for item in inventory if str(item or "").strip()))
                )
            ),
        )

    def render(self) -> str:
        imports = tuple(dict.fromkeys((*self.base_imports, *self.theory_imports)))
        import_block = "\n".join(f"import {module}" for module in imports)
        inventory_block = ""
        if self.theory_inventory:
            inventory_block = "\n".join(
                (
                    "-- MiniTheory verified declaration inventory:",
                    *(
                        "-- " + " ".join(item.split())
                        for item in self.theory_inventory
                    ),
                )
            )
        return "\n\n".join(
            part
            for part in (
                self.base_header,
                import_block,
                self.base_preamble,
                inventory_block,
            )
            if part.strip()
        ).strip()

    @property
    def snapshot_hash(self) -> str:
        payload = "\n".join(
            (
                content_hash(self.base_preamble, length=64),
                content_hash(self.base_header, length=64),
                *self.base_imports,
                "-- theory --",
                *self.theory_imports,
                "-- bundles --",
                *self.bundle_ids,
                "-- inventory --",
                *self.theory_inventory,
            )
        )
        return content_hash(payload, length=64)


@dataclass(frozen=True)
class TheoryContextPair:
    llm: TheoryContext
    lean: TheoryContext

    @classmethod
    def from_preambles(
        cls,
        *,
        llm_preamble: str,
        lean_preamble: str,
    ) -> "TheoryContextPair":
        return cls(
            llm=TheoryContext.from_preamble(llm_preamble),
            lean=TheoryContext.from_preamble(lean_preamble),
        )

    def with_theory(
        self,
        *,
        modules: Iterable[str],
        bundle_ids: Iterable[str],
        inventory: Iterable[str] = (),
    ) -> "TheoryContextPair":
        module_tuple = tuple(modules)
        bundle_tuple = tuple(bundle_ids)
        inventory_tuple = tuple(inventory)
        return TheoryContextPair(
            llm=self.llm.with_theory(
                modules=module_tuple,
                bundle_ids=bundle_tuple,
                inventory=inventory_tuple,
            ),
            lean=self.lean.with_theory(
                modules=module_tuple,
                bundle_ids=bundle_tuple,
                inventory=inventory_tuple,
            ),
        )

    @property
    def snapshot_hash(self) -> str:
        return content_hash(
            f"{self.llm.snapshot_hash}:{self.lean.snapshot_hash}",
            length=64,
        )

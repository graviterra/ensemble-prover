"""Structured composition of problem preambles and published theory imports."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable, Optional

from .model import content_hash
from ..lean_source_lexing import (
    _mask_noncode,
    _scan_lean_header,
)


_MODULE_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
_PLAIN_EDGE = " \t\r\n"


def _ends_in_open_quote(text: str) -> bool:
    open_quote = False
    for char in _mask_noncode(text):
        if open_quote:
            if char == "»":
                open_quote = False
        elif char == "«":
            open_quote = True
    return open_quote


def _trim_plain_edges(text: str) -> str:
    """Drop surrounding spaces and physical newlines without eating name characters.

    ``str.strip()`` also removes Unicode separators. A trailing space or
    newline that is still inside an unclosed ``«»`` is part of that name.
    """

    quote_at: Optional[int] = None
    open_quote = False
    for index, char in enumerate(_mask_noncode(text)):
        if open_quote:
            if char == "»":
                open_quote = False
                quote_at = None
        elif char == "«":
            open_quote = True
            quote_at = index
    if quote_at is not None:
        return text[:quote_at].lstrip(_PLAIN_EDGE) + text[quote_at:]
    return text.strip(_PLAIN_EDGE)




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
        source = str(preamble or "")
        commands, _ = _scan_lean_header(source)
        retain_import_order = any(command.decorated for command in commands)
        imports: list[str] = []
        headers: list[str] = []
        removed: list[tuple[int, int]] = []
        for command in commands:
            if command.kind == "import" and not retain_import_order:
                module = source[command.module_start:command.end]
                if module not in imports:
                    imports.append(module)
            else:
                # A modified import keeps the original header sequence ahead
                # of appended theory imports, preserving phase and visibility.
                headers.append(" ".join(source[start:end] for start, end in command.code_spans))
            removed.extend(command.code_spans)
        body_parts: list[str] = []
        cursor = 0
        for start, end in removed:
            body_parts.append(source[cursor:start])
            cursor = end
        body_parts.append(source[cursor:])
        return cls(
            base_header=_trim_plain_edges("\n".join(headers)),
            base_preamble=_trim_plain_edges("".join(body_parts)),
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
        header = self.base_header
        header_commands, _ = _scan_lean_header(header)
        pending_header = ""
        if header_commands and _ends_in_open_quote(header):
            pending_header = header[header_commands[-1].start:]
            header = header[:header_commands[-1].start].rstrip(_PLAIN_EDGE)
            header_commands = header_commands[:-1]
        existing = {
            header[command.module_start:command.end]
            for command in header_commands
            if command.kind == "import" and not any(
                header[start:end] in {"meta", "all"}
                for start, end in command.code_spans[:-1]
            )
        }
        imports = tuple(
            module for module in dict.fromkeys((*self.base_imports, *self.theory_imports))
            if module not in existing
        )
        import_block = "\n".join(
            f"import {module}" for module in imports if not _ends_in_open_quote(module)
        )
        pending_imports = "\n".join(
            f"import {module}" for module in imports if _ends_in_open_quote(module)
        )
        if any(command.kind == "import" for command in header_commands):
            header = "\n".join(part for part in (header, import_block) if part)
            import_block = ""
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
        body = [self.base_preamble, inventory_block]
        if _ends_in_open_quote(self.base_preamble):
            body.reverse()
        return _trim_plain_edges(
            "\n\n".join(
                part
                for part in (
                    header,
                    import_block,
                    *body,
                    pending_imports,
                    pending_header,
                )
                if _trim_plain_edges(part)
            )
        )

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

"""Structured composition of problem preambles and published theory imports."""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Iterable, Optional

from .model import content_hash
from ..lean_source_lexing import (
    _mask_noncode,
    _quoted_identifier_open_before,
    _unclosed_block_comment_at,
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


def _suffix_after_import(source_line: str, module: str) -> str:
    """Text on an import line after the module token, such as a trailing comment."""

    marker = source_line.find("import")
    if marker < 0:
        return ""
    rest = source_line[marker + len("import") :].lstrip(" \t")
    if not rest.startswith(module):
        return ""
    return rest[len(module) :].lstrip(" \t")


def _import_module_text(masked_line: str) -> Optional[str]:
    """Return the module token on one masked import line.

    An unclosed ``«`` keeps every remaining character, including spaces.
    A closed quoted name or ordinary token must occupy the rest of the line.
    """

    matched = re.match(r"^\s*import\s+(.*)$", masked_line)
    if matched is None:
        return None
    rest = matched.group(1)
    if rest.startswith("«"):
        close = rest.find("»")
        if close < 0:
            return rest
        if rest[close + 1 :].strip():
            return None
        return rest[: close + 1]
    token = re.match(r"\S+", rest)
    if token is None or rest[token.end() :].strip():
        return None
    return token.group(0)


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
        # Only split on the physical newline preserved by both lexical masks.
        # str.splitlines() also splits Unicode characters that may belong to
        # an escaped identifier and are correctly blanked in the command mask.
        source_lines = source.split("\n")
        masked_lines = _mask_noncode(source).split("\n")
        command_lines = _mask_noncode(source, mask_quoted_identifiers=True).split("\n")
        index = 0
        limit = len(source_lines)
        while index < limit:
            if _quoted_identifier_open_before(masked_lines, index):
                body_lines.append(source_lines[index])
                index += 1
                continue
            line = source_lines[index]
            masked_line = masked_lines[index]
            command_line = command_lines[index] if index < len(command_lines) else ""
            head = len(masked_line) - len(masked_line.lstrip())
            if head == len(masked_line) or (
                head < len(command_line) and command_line[head].isspace()
            ):
                body_lines.append(line)
                index += 1
                continue
            stripped = masked_line.strip()
            if stripped == "prelude" or stripped == "module" or stripped.startswith("module "):
                comment_at = _unclosed_block_comment_at(line)
                if comment_at is None:
                    header_lines.append(line)
                else:
                    header_lines.append(line[:comment_at].rstrip(" \t"))
                    body_lines.append(line[comment_at:])
                index += 1
                if comment_at is None:
                    while index < limit and _quoted_identifier_open_before(masked_lines, index):
                        extra = source_lines[index]
                        comment_at = _unclosed_block_comment_at(extra, quote_open=True)
                        if comment_at is None:
                            header_lines.append(extra)
                            index += 1
                            continue
                        header_lines.append(extra[:comment_at].rstrip(" \t"))
                        body_lines.append(extra[comment_at:])
                        index += 1
                        break
                continue
            module = _import_module_text(masked_line)
            if module is None:
                body_lines.append(line)
                index += 1
                continue
            suffix = _suffix_after_import(line, module)
            if suffix:
                body_lines.append(suffix)
            index += 1
            while not suffix and index < limit and _quoted_identifier_open_before(masked_lines, index):
                extra = source_lines[index]
                close = extra.find("»")
                if close < 0:
                    module += "\n" + extra
                    index += 1
                    continue
                module += "\n" + extra[: close + 1]
                remainder = extra[close + 1 :].lstrip(" \t")
                index += 1
                if remainder.strip("\r"):
                    body_lines.append(remainder)
                break
            if module not in imports:
                imports.append(module)
        return cls(
            base_header=_trim_plain_edges("\n".join(header_lines)),
            base_preamble=_trim_plain_edges("\n".join(body_lines)),
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
        header_first = not _ends_in_open_quote(self.base_header)
        return _trim_plain_edges(
            "\n\n".join(
                part
                for part in (
                    self.base_header if header_first else "",
                    import_block,
                    "" if header_first else self.base_header,
                    self.base_preamble,
                    inventory_block,
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

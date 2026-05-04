#!/usr/bin/env python3
"""Shared helpers for ArkLib knowledge-base scripts."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import json
import re


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BIB_PATH = REPO_ROOT / "blueprint" / "src" / "references.bib"
DEFAULT_REFERENCES_JSON = REPO_ROOT / "docs" / "kb" / "_generated" / "references.json"
DEFAULT_CITATIONS_JSON = REPO_ROOT / "docs" / "kb" / "_generated" / "lean-citations.json"
DEFAULT_LEAN_ROOT = REPO_ROOT / "ArkLib"


@dataclass(frozen=True)
class BibEntry:
    """Structured view of one BibTeX entry."""

    key: str
    entry_type: str
    fields: dict[str, str]

    def to_json(self) -> dict[str, object]:
        authors_text = self.fields.get("author", "")
        authors = [part.strip() for part in authors_text.split(" and ") if part.strip()]
        result: dict[str, object] = {
            "key": self.key,
            "entry_type": self.entry_type,
            "authors": authors,
            "authors_text": authors_text,
            "title": self.fields.get("title", ""),
            "year": self.fields.get("year", ""),
            "venue": self.fields.get("journal") or self.fields.get("booktitle", ""),
            "url": self.fields.get("url", ""),
            "doi": self.fields.get("doi", ""),
            "fields": self.fields,
        }
        return result


def load_bib_entries(path: Path = DEFAULT_BIB_PATH) -> list[BibEntry]:
    """Parse a BibTeX file using a small brace-aware parser."""

    text = path.read_text(encoding="utf-8")
    entries: list[BibEntry] = []
    i = 0
    while True:
        start = text.find("@", i)
        if start == -1:
            break
        i = start + 1
        while i < len(text) and text[i].isspace():
            i += 1
        type_start = i
        while i < len(text) and (text[i].isalnum() or text[i] in "_-"):
            i += 1
        entry_type = text[type_start:i].strip().lower()
        while i < len(text) and text[i].isspace():
            i += 1
        if i >= len(text) or text[i] != "{":
            continue
        i += 1
        key_start = i
        while i < len(text) and text[i] != ",":
            i += 1
        key = text[key_start:i].strip()
        if i >= len(text):
            break
        i += 1
        body_start = i
        depth = 1
        in_quote = False
        while i < len(text) and depth > 0:
            char = text[i]
            prev = text[i - 1] if i > 0 else ""
            if char == '"' and prev != "\\":
                in_quote = not in_quote
            elif not in_quote:
                if char == "{":
                    depth += 1
                elif char == "}":
                    depth -= 1
            i += 1
        body = text[body_start : i - 1]
        fields = parse_bib_fields(body)
        if key:
            entries.append(BibEntry(key=key, entry_type=entry_type, fields=fields))
    return entries


def parse_bib_fields(body: str) -> dict[str, str]:
    """Parse the comma-separated field list inside one BibTeX entry."""

    fields: dict[str, str] = {}
    i = 0
    while i < len(body):
        while i < len(body) and (body[i].isspace() or body[i] == ","):
            i += 1
        if i >= len(body):
            break

        name_start = i
        while i < len(body) and (body[i].isalnum() or body[i] in "_-"):
            i += 1
        name = body[name_start:i].strip().lower()
        if not name:
            break

        while i < len(body) and body[i].isspace():
            i += 1
        if i >= len(body) or body[i] != "=":
            while i < len(body) and body[i] != ",":
                i += 1
            continue
        i += 1
        while i < len(body) and body[i].isspace():
            i += 1

        value, i = parse_bib_value(body, i)
        fields[name] = normalize_space(value)
    return fields


def parse_bib_value(text: str, start: int) -> tuple[str, int]:
    """Parse one BibTeX field value starting at ``start``."""

    if start >= len(text):
        return "", start

    char = text[start]
    if char == "{":
        return parse_braced_value(text, start)
    if char == '"':
        return parse_quoted_value(text, start)

    i = start
    while i < len(text) and text[i] not in ",\n":
        i += 1
    return text[start:i].strip(), i


def parse_braced_value(text: str, start: int) -> tuple[str, int]:
    """Parse a brace-delimited BibTeX value, preserving inner content."""

    depth = 0
    i = start
    chunk_start = start + 1
    while i < len(text):
        char = text[i]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[chunk_start:i], i + 1
        i += 1
    return text[start + 1 :].strip(), len(text)


def parse_quoted_value(text: str, start: int) -> tuple[str, int]:
    """Parse a quote-delimited BibTeX value."""

    i = start + 1
    chunk_start = i
    while i < len(text):
        if text[i] == '"' and text[i - 1] != "\\":
            return text[chunk_start:i], i + 1
        i += 1
    return text[start + 1 :].strip(), len(text)


def normalize_space(text: str) -> str:
    """Collapse internal whitespace without altering non-whitespace characters."""

    return re.sub(r"\s+", " ", text).strip()


def ensure_parent_dir(path: Path) -> None:
    """Create the parent directory for ``path`` if needed."""

    path.parent.mkdir(parents=True, exist_ok=True)


def write_json(path: Path, payload: dict[str, object]) -> None:
    """Write deterministic JSON with a trailing newline."""

    ensure_parent_dir(path)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

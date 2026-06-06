#!/usr/bin/env python3
"""Catalog every Lean `def`/`theorem`/`lemma`/etc. across the library.

Scans `ArkLib/**/*.lean` and emits a JSON catalog of every declaration with
its file, line, kind, namespace, short name, fully-qualified name, a brief
signature snippet, and the head of its docstring. The catalog supports
library-wide tooling: search/navigation indexes, duplicate-spotting,
documentation coverage reports, and review context.

Usage::

    python3 ./scripts/kb/extract_declarations.py
    python3 ./scripts/kb/extract_declarations.py \
        --root ArkLib/Data/CodingTheory --out /tmp/ct-decls.json

The output is a JSON document with two top-level keys:

* ``files``  — file → list of declarations (with line, kind, namespace,
  short-name, fully-qualified name, brief signature, docstring head).
* ``stats``  — per-root summary counts.

Parsing strategy: pure regex over source text (standard library only, no
`lake env`). Lean's elaborator would be more accurate but introduces a heavy
dependency. The regex catches the canonical declaration kinds and tracks the
current `namespace`/`section`/`end` stack to attach fully-qualified names.

Caveats:

* Multi-line declarations are recognised by their opening line only; the
  signature snippet is truncated to the first line after the name.
* Anonymous instances (``instance : Foo where ...``) are recorded under the
  synthetic name ``_anon_instance_<lineno>``.
* `where`-clauses, `theorem ... :=`, `by`-blocks etc. are not parsed beyond
  what is needed to attribute the declaration to a namespace.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from common import DEFAULT_DECLARATIONS_JSON, DEFAULT_LEAN_ROOT, REPO_ROOT, write_json

import re

DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "alias", "structure",
    "inductive", "instance", "class", "opaque", "axiom",
)

# Match a declaration opener, optionally preceded by attributes / modifiers.
DECL_RE = re.compile(
    r"""^
        (?P<indent>\s*)
        (?:@\[[^\]]*\]\s*)*
        (?:private\s+|protected\s+|noncomputable\s+|partial\s+|mutual\s+)*
        (?P<kind>theorem|lemma|def|abbrev|alias|structure|inductive
                 |instance|class|opaque|axiom)
        (?:\s+(?P<name>[A-Za-z_][\w.'']*))?
        (?P<tail>.*)$
    """,
    re.VERBOSE,
)

NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.]*)\s*$")
SECTION_RE = re.compile(r"^\s*section(?:\s+([A-Za-z_][\w.]*))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.]*))?\s*$")
DOCSTRING_OPEN_RE = re.compile(r"^\s*/--")
DOCSTRING_CLOSE_RE = re.compile(r"-/\s*$")


def _docstring_head(text: str) -> str:
    """Strip Lean doc-comment delimiters and return up to ~600 chars of body.

    Captures more than just the first line so that downstream similarity
    tooling sees the whole "what does this declaration do" description, not
    just the first sentence. Two declarations whose first lines happen to
    match (a common artefact of copy-pasted preambles like "Prover's function
    for processing the next round...") otherwise look identical even when
    their bodies clearly distinguish them; capturing more of the body avoids
    those false matches.
    """
    body = text.strip()
    if body.startswith("/--"):
        body = body[3:]
    if body.endswith("-/"):
        body = body[:-2]
    # Join lines, collapse whitespace, take up to a soft cap.
    joined = " ".join(line.strip() for line in body.splitlines() if line.strip())
    return joined[:600]


def parse_file(path: Path) -> list[dict]:
    """Return a list of declaration records for one Lean file.

    Maintains a single stack of (kind, name) entries where `kind` is
    ``"ns"`` (`namespace Foo`) or ``"section"`` (`section` or
    `section Foo`). The *current namespace* is the dot-concatenation
    of the `"ns"` entries. A bare `end` pops the top of the stack
    (whichever kind it is); `end Foo` pops back through the matching
    `"ns"` entry. Lean tolerates `end Foo` closing a section labelled
    `Foo` too — we treat that identically to popping the most recent
    matching label.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    stack: list[tuple[str, str]] = []
    decls: list[dict] = []
    pending_doc: str = ""
    in_doc = False
    doc_buf: list[str] = []

    def current_namespace() -> str:
        return ".".join(name for kind, name in stack if kind == "ns")

    for idx, raw in enumerate(lines, start=1):
        # Track docstring buffer.
        if in_doc:
            doc_buf.append(raw)
            if DOCSTRING_CLOSE_RE.search(raw):
                pending_doc = "\n".join(doc_buf)
                doc_buf = []
                in_doc = False
            continue
        if DOCSTRING_OPEN_RE.match(raw) and "-/" not in raw:
            doc_buf = [raw]
            in_doc = True
            continue
        if DOCSTRING_OPEN_RE.match(raw):
            pending_doc = raw
            continue

        # Track namespace / section / end.
        m_ns = NAMESPACE_RE.match(raw)
        if m_ns:
            stack.append(("ns", m_ns.group(1)))
            pending_doc = ""
            continue
        m_sec = SECTION_RE.match(raw)
        if m_sec:
            stack.append(("section", m_sec.group(1) or ""))
            pending_doc = ""
            continue
        m_end = END_RE.match(raw)
        if m_end:
            label = m_end.group(1)
            if label:
                # Pop entries until we drop one whose name matches `label`,
                # regardless of kind. (Lean is permissive: `end Foo` will
                # close a section labelled `Foo` or a namespace `Foo`.)
                while stack and stack[-1][1] != label:
                    stack.pop()
                if stack:
                    stack.pop()
            elif stack:
                stack.pop()
            pending_doc = ""
            continue

        m_decl = DECL_RE.match(raw)
        if m_decl:
            kind = m_decl.group("kind")
            name = m_decl.group("name")
            tail = m_decl.group("tail").strip()
            if name is None:
                name = f"_anon_{kind}_{idx}"
                tail_for_sig = raw.strip()
            else:
                tail_for_sig = (name + " " + tail).strip()
            namespace = current_namespace()
            full_name = f"{namespace}.{name}" if namespace else name
            decls.append({
                "short_name": name,
                "name": full_name,
                "kind": kind,
                "namespace": namespace,
                "line": idx,
                "signature": (kind + " " + tail_for_sig)[:200],
                "doc": _docstring_head(pending_doc),
            })
            pending_doc = ""
        elif raw.strip() and not raw.lstrip().startswith("--"):
            # Non-blank, non-comment line that's not a decl drops pending doc.
            # (Real-world: a doc-comment immediately preceding the decl pairs;
            # intervening blank lines are OK, but other content breaks the link.)
            if not raw.lstrip().startswith(("@[", "open ", "set_option", "variable")):
                pending_doc = ""

    return decls


def extract_declarations(roots: list[Path]) -> dict[str, object]:
    """Scan ``roots`` and build the file → declarations catalog with stats."""

    files: dict[str, dict] = {}
    stats: dict[str, dict] = {}
    for root in roots:
        root_count = 0
        root_decls = 0
        for path in sorted(root.rglob("*.lean")):
            rel = str(path.relative_to(REPO_ROOT))
            decls = parse_file(path)
            files[rel] = {"declarations": decls}
            root_count += 1
            root_decls += len(decls)
        stats[str(root.relative_to(REPO_ROOT))] = {
            "files": root_count,
            "declarations": root_decls,
        }
    return {"files": files, "stats": stats}


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""

    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument(
        "--root", nargs="+", type=Path, default=[DEFAULT_LEAN_ROOT],
        help="One or more directories to scan (default: the whole ArkLib tree).",
    )
    parser.add_argument(
        "--out", type=Path, default=DEFAULT_DECLARATIONS_JSON,
        help="Output JSON path (default: docs/kb/_generated/declarations.json).",
    )
    return parser.parse_args()


def main() -> int:
    """Entry point."""

    args = parse_args()
    roots = [r if r.is_absolute() else REPO_ROOT / r for r in args.root]
    missing = [r for r in roots if not r.exists()]
    if missing:
        raise SystemExit(f"Missing roots: {missing}")

    payload = extract_declarations(roots)
    write_json(args.out.resolve(), payload)
    total = sum(s["declarations"] for s in payload["stats"].values())
    file_count = sum(s["files"] for s in payload["stats"].values())
    print(
        f"Wrote declaration catalog with {total} declarations across "
        f"{file_count} files to {args.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

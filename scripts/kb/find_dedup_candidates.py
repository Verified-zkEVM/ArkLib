#!/usr/bin/env python3
"""Find likely-duplicated declarations across the library.

Consumes the catalog produced by `extract_declarations.py` and surfaces:

* **same-short-name** groups across multiple files / namespaces, ranked
  by how likely the entries are to be unintentional duplicates;
* **near-duplicate docstrings** between distinct declarations in *different*
  files (Jaccard similarity over word sets), useful for spotting "same
  concept, different name" cases.

The output is a markdown report intended for human review when assessing a
PR: regenerate it alongside `declarations.json`, and any new name-collision
or doc-overlap a change introduces shows up directly in the report diff.
It is a *review aid*, not an automatic verdict — eyeball the flagged groups;
most are legitimate (overloaded interfaces, paper-shape vs general form).

Usage::

    python3 ./scripts/kb/find_dedup_candidates.py
    python3 ./scripts/kb/find_dedup_candidates.py \
        --in /tmp/decls.json --out /tmp/dedup.md --doc-threshold 0.9
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

from common import (
    DEFAULT_DECLARATIONS_JSON,
    DEFAULT_DEDUP_REPORT,
    REPO_ROOT,
)

# Defaults shared by the CLI and the freshness check, so a no-argument run
# reproduces the committed report exactly.
DEFAULT_MIN_GROUP = 2
DEFAULT_DOC_THRESHOLD = 0.85
DOC_SIMILARITY_CAP = 80

# Short names so common they'd dominate the report without telling us
# anything. (Conservative blacklist; expand on demand.)
TRIVIAL_NAMES = frozenset({
    "mk", "rec", "noConfusion", "casesOn", "recOn", "ext", "intro",
    "elim", "id", "comp", "default", "instance", "cast",
    "add", "sub", "mul", "div", "neg", "one", "zero", "inv",
    "le", "lt", "ge", "gt", "eq", "ne",
    "and", "or", "not", "iff", "imp",
    "succ", "pred", "min", "max",
    "of", "from", "to", "coe", "val",
    "true", "false",
    # Mathlib-bridge metanames that occur all over.
    "isUnit", "isEmpty", "isSubsingleton", "isFinite",
})

DOC_WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_-]+")


def _doc_words(doc: str) -> set[str]:
    return {w.lower() for w in DOC_WORD_RE.findall(doc) if len(w) >= 4}


def _jaccard(a: set[str], b: set[str]) -> float:
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def collect_groups(data: dict) -> dict[str, list[dict]]:
    """Bucket declarations by short_name."""
    groups: dict[str, list[dict]] = defaultdict(list)
    for fpath, entry in data["files"].items():
        for d in entry["declarations"]:
            short = d.get("short_name") or ""
            if not short or short.startswith("_anon_"):
                continue
            d2 = dict(d)
            d2["file"] = fpath
            groups[short].append(d2)
    return groups


def _interestingness(group: list[dict]) -> int:
    """Heuristic ranking: bigger = more likely worth a look."""
    files = {d["file"] for d in group}
    namespaces = {d["namespace"] for d in group}
    n_files = len(files)
    n_ns = len(namespaces)
    # Cross-file is more interesting than within-file (within-file is
    # usually overloaded notation / typeclass instances of distinct kinds).
    return n_files * 10 + n_ns


def render_short_name_report(groups: dict[str, list[dict]], min_group: int) -> list[str]:
    lines: list[str] = []
    candidates = []
    for short, ds in groups.items():
        if short in TRIVIAL_NAMES or len(short) <= 2:
            continue
        if len(ds) < min_group:
            continue
        # Skip groups where everything is in the same file (likely
        # intentional overloads / typeclass instances).
        if len({d["file"] for d in ds}) <= 1:
            continue
        candidates.append((short, ds))
    candidates.sort(key=lambda kv: (-_interestingness(kv[1]), kv[0]))

    lines.append(f"## Same short-name across multiple files ({len(candidates)} groups)")
    lines.append("")
    lines.append(
        "Each group lists declarations sharing a short name across "
        "≥2 files. Most are legitimate (overloaded interface, paper-"
        "shape vs general form), but the list is the right anchor to "
        "look for duplicates."
    )
    lines.append("")
    for short, ds in candidates:
        lines.append(f"### `{short}` ({len(ds)} declarations, "
                     f"{len({d['file'] for d in ds})} files)")
        lines.append("")
        for d in sorted(ds, key=lambda x: (x["file"], x["line"])):
            doc = d["doc"][:100].replace("|", "\\|")
            lines.append(
                f"- `{d['kind']} {d['name']}` "
                f"[{d['file']}:{d['line']}](../../../{d['file']}#L{d['line']}) "
                f"— {doc or '(no docstring)'}"
            )
        lines.append("")
    return lines


def render_doc_similarity_report(data: dict, threshold: float) -> list[str]:
    """Pairs of cross-file declarations with high docstring Jaccard similarity."""
    decls: list[dict] = []
    for fpath, entry in data["files"].items():
        for d in entry["declarations"]:
            short = d.get("short_name") or ""
            if not short or short.startswith("_anon_"):
                continue
            words = _doc_words(d["doc"])
            if len(words) < 5:
                continue
            d2 = dict(d)
            d2["file"] = fpath
            d2["_words"] = words
            decls.append(d2)

    # Bucket by sorted word-prefix to avoid the n^2 explosion across the
    # whole library.
    buckets: dict[str, list[dict]] = defaultdict(list)
    for d in decls:
        # Anchor each decl in 3 buckets keyed by the longest words present.
        anchors = sorted(d["_words"], key=lambda w: (-len(w), w))[:3]
        for a in anchors:
            buckets[a].append(d)

    seen_pairs: set[tuple[str, str]] = set()
    hits: list[tuple[float, dict, dict]] = []
    for bucket in buckets.values():
        if len(bucket) < 2 or len(bucket) > 40:
            # >40 = bucket too broad; >1 needed for any pair.
            continue
        for i, a in enumerate(bucket):
            for b in bucket[i + 1:]:
                if a["name"] == b["name"]:
                    continue
                # Cross-file only: same-file collisions are usually
                # overloads, and cross-file dups are the point of the report.
                if a["file"] == b["file"]:
                    continue
                key = tuple(sorted([a["name"], b["name"]]))
                if key in seen_pairs:
                    continue
                seen_pairs.add(key)
                s = _jaccard(a["_words"], b["_words"])
                if s >= threshold:
                    hits.append((s, a, b))
    hits.sort(key=lambda h: (-h[0], h[1]["name"], h[2]["name"]))

    lines: list[str] = []
    lines.append(f"## Near-duplicate docstrings (Jaccard ≥ {threshold:.2f}, "
                 f"{len(hits)} cross-file pairs)")
    lines.append("")
    lines.append(
        "Each pair has docstrings sharing a high fraction of (4+-letter) "
        "words, in different files. Most are unrelated coincidences in "
        "boilerplate; look for pairs where the *concept* matches."
    )
    lines.append("")
    for s, a, b in hits[:DOC_SIMILARITY_CAP]:
        lines.append(
            f"- **{s:.2f}** `{a['name']}` "
            f"[{a['file']}:{a['line']}](../../../{a['file']}#L{a['line']}) "
            f"vs `{b['name']}` "
            f"[{b['file']}:{b['line']}](../../../{b['file']}#L{b['line']})"
        )
        lines.append(f"    - a: {a['doc'][:100]}")
        lines.append(f"    - b: {b['doc'][:100]}")
    lines.append("")
    return lines


def render_stats(data: dict) -> list[str]:
    lines = ["## Stats", ""]
    for root, s in data["stats"].items():
        lines.append(f"- `{root}` — {s['files']} files, {s['declarations']} declarations")
    lines.append("")
    return lines


def build_report(
    data: dict,
    *,
    min_group: int = DEFAULT_MIN_GROUP,
    doc_threshold: float = DEFAULT_DOC_THRESHOLD,
) -> str:
    """Render the full dedup-candidate markdown report for a catalog payload.

    Deterministic given ``data`` (which is itself deterministic), so it is
    safe to freshness-check the committed report against a fresh extraction.
    """
    groups = collect_groups(data)
    lines: list[str] = []
    lines.append("# ArkLib dedup-candidate report")
    lines.append("")
    lines.append(
        "Generated from `docs/kb/_generated/declarations.json`. "
        "**Eyeball, do not auto-rewrite.** The point is to surface "
        "name collisions and doc-string overlap that *might* indicate "
        "an opportunity to consolidate."
    )
    lines.append("")
    lines.extend(render_stats(data))
    lines.extend(render_short_name_report(groups, min_group))
    lines.extend(render_doc_similarity_report(data, doc_threshold))
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments."""
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument("--in", dest="inp", type=Path, default=DEFAULT_DECLARATIONS_JSON,
                   help="Catalog JSON from extract_declarations.py "
                        "(default: docs/kb/_generated/declarations.json)")
    p.add_argument("--out", type=Path, default=DEFAULT_DEDUP_REPORT,
                   help="Markdown report path "
                        "(default: docs/kb/_generated/dedup-report.md)")
    p.add_argument("--min-group", type=int, default=DEFAULT_MIN_GROUP,
                   help=f"Minimum group size to report (default {DEFAULT_MIN_GROUP})")
    p.add_argument("--doc-threshold", type=float, default=DEFAULT_DOC_THRESHOLD,
                   help=f"Jaccard similarity threshold (default {DEFAULT_DOC_THRESHOLD})")
    return p.parse_args()


def main() -> int:
    """Entry point."""
    args = parse_args()
    inp = args.inp if args.inp.is_absolute() else REPO_ROOT / args.inp
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    data = json.loads(inp.read_text(encoding="utf-8"))
    report = build_report(data, min_group=args.min_group, doc_threshold=args.doc_threshold)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(report + "\n", encoding="utf-8")
    print(f"Wrote {out.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Inventory source constructs that an environment-level axiom sweep cannot always see.

The scanner is deliberately lexical rather than a grep: it removes nested Lean comments,
line comments, strings, and quoted identifiers before matching exact tokens.  It does not
decide whether an admission is intentional.  Its job is to make source-only debt visible,
including debt in examples, default values/autoparams, and tracked files outside an import
root.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Iterable


ZERO_SHA = "0" * 40


@dataclass(frozen=True)
class Occurrence:
    path: str
    line: int
    column: int
    kind: str
    token: str
    source: str

    @property
    def identity(self) -> tuple[str, str, str, str]:
        """A line-number-independent identity used for baseline diffs."""
        return (self.path, self.kind, self.token, self.source)


# Admission/command keywords cannot be qualified names.  Excluding a preceding dot or
# backtick avoids counting `Foo.sorry` and name quotations such as `` `sorry``.
KEYWORD_PATTERNS = {
    "admission": re.compile(r"(?<![`.\w'])(?:sorryAx|sorry|admit)(?![\w'])"),
    "example": re.compile(r"(?<![`.\w'])example(?![\w'])"),
    "explicit_axiom": re.compile(r"(?<![`.\w'])axiom(?![\w'])"),
}
# Native/compiler-trust references are intentionally report-only here. In metaprogram
# source, a token may occur inside a syntax quotation rather than execute as a tactic;
# the enforcing zero-allowlist floor remains the kernel-level axiomsweep verdict.
NATIVE_PATTERN = re.compile(
    r"(?<![`\w'])(?:Lean\.ofReduceBool|Lean\.trustCompiler|native_decide)(?![\w'])"
)


def mask_noncode(text: str) -> str:
    """Replace comments, strings, and quoted identifiers with spaces, preserving lines."""
    out = list(text)
    i = 0
    block_depth = 0
    line_comment = False
    string = False
    escaped = False
    quoted_identifier = False

    def blank(index: int) -> None:
        if out[index] != "\n":
            out[index] = " "

    while i < len(text):
        pair = text[i : i + 2]
        char = text[i]

        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                blank(i)
            i += 1
            continue

        if block_depth:
            if pair == "/-":
                blank(i)
                blank(i + 1)
                block_depth += 1
                i += 2
            elif pair == "-/":
                blank(i)
                blank(i + 1)
                block_depth -= 1
                i += 2
            else:
                blank(i)
                i += 1
            continue

        if string:
            blank(i)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                string = False
            i += 1
            continue

        if quoted_identifier:
            blank(i)
            if char == "»":
                quoted_identifier = False
            i += 1
            continue

        if pair == "--":
            blank(i)
            blank(i + 1)
            line_comment = True
            i += 2
        elif pair == "/-":
            blank(i)
            blank(i + 1)
            block_depth = 1
            i += 2
        elif char == '"':
            blank(i)
            string = True
            i += 1
        elif char == "«":
            blank(i)
            quoted_identifier = True
            i += 1
        else:
            i += 1

    return "".join(out)


def scan_source(path: str, text: str) -> list[Occurrence]:
    masked = mask_noncode(text)
    lines = masked.splitlines()
    occurrences: list[Occurrence] = []

    patterns = list(KEYWORD_PATTERNS.items()) + [("native_trust", NATIVE_PATTERN)]
    for kind, pattern in patterns:
        for match in pattern.finditer(masked):
            line = masked.count("\n", 0, match.start()) + 1
            line_start = masked.rfind("\n", 0, match.start()) + 1
            column = match.start() - line_start + 1
            source = " ".join(lines[line - 1].strip().split())
            occurrences.append(
                Occurrence(path, line, column, kind, match.group(0), source)
            )
    return sorted(occurrences, key=lambda item: (item.path, item.line, item.column, item.kind))


def git(*args: str) -> str:
    result = subprocess.run(
        ["git", *args], check=False, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or f"git {' '.join(args)} failed")
    return result.stdout


def tracked_sources(ref: str | None = None) -> list[tuple[str, str]]:
    if ref is None:
        paths = [
            path
            for path in git("ls-files", "--", "ArkLib").splitlines()
            if path.endswith(".lean")
        ]
        return [(path, Path(path).read_text(encoding="utf-8")) for path in sorted(paths)]

    paths = [
        path
        for path in git("ls-tree", "-r", "--name-only", ref, "--", "ArkLib").splitlines()
        if path.endswith(".lean")
    ]
    return [(path, git("show", f"{ref}:{path}")) for path in sorted(paths)]


def scan_tree(ref: str | None = None) -> list[Occurrence]:
    return [
        occurrence
        for path, source in tracked_sources(ref)
        for occurrence in scan_source(path, source)
    ]


def multiset_difference(
    left: Iterable[Occurrence], right: Iterable[Occurrence]
) -> list[Occurrence]:
    """Return occurrences in left beyond the matching multiplicity in right."""
    remaining = Counter(item.identity for item in right)
    result: list[Occurrence] = []
    for item in left:
        if remaining[item.identity]:
            remaining[item.identity] -= 1
        else:
            result.append(item)
    return result


def counts(items: Iterable[Occurrence]) -> dict[str, int]:
    result = Counter(item.kind for item in items)
    return {kind: result.get(kind, 0) for kind in (*KEYWORD_PATTERNS, "native_trust")}


def markdown_report(
    current: list[Occurrence], base: list[Occurrence] | None, base_ref: str | None
) -> str:
    current_counts = counts(current)
    lines = ["## Source trust inventory", ""]
    if base is None:
        lines.extend(["No comparison ref supplied; reporting the current tracked source tree.", ""])
        lines.extend(["| Construct | Current |", "| --- | ---: |"])
        lines.extend(f"| `{kind}` | {value} |" for kind, value in current_counts.items())
        return "\n".join(lines) + "\n"

    base_counts = counts(base)
    added = multiset_difference(current, base)
    removed = multiset_difference(base, current)
    lines.extend(
        [
            f"Compared every tracked `ArkLib/**/*.lean` file with `{base_ref}`. "
            "This report is visibility, not a `sorry`-debt freeze.",
            "",
            "| Construct | Base | Current | Delta |",
            "| --- | ---: | ---: | ---: |",
        ]
    )
    for kind, value in current_counts.items():
        delta = value - base_counts[kind]
        lines.append(f"| `{kind}` | {base_counts[kind]} | {value} | {delta:+d} |")

    for heading, occurrences in (("Added", added), ("Removed", removed)):
        lines.extend(["", f"### {heading} source constructs", ""])
        if not occurrences:
            lines.append("None.")
            continue
        for item in occurrences:
            lines.append(
                f"- `{item.kind}` `{item.token}` at `{item.path}:{item.line}:{item.column}`: "
                f"`{item.source}`"
            )
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", help="Git ref to compare against")
    parser.add_argument("--json", type=Path, help="Write the full deterministic inventory")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    base_ref = args.base_ref
    if base_ref == ZERO_SHA:
        base_ref = None
    try:
        current = scan_tree()
        base = scan_tree(base_ref) if base_ref else None
    except (OSError, RuntimeError, UnicodeError) as error:
        print(f"source-trust-audit: infrastructure failure: {error}", file=sys.stderr)
        return 2

    added = multiset_difference(current, base or []) if base is not None else []
    report = markdown_report(current, base, base_ref)
    print(report, end="")

    if args.json:
        payload = {
            "version": 1,
            "baseRef": base_ref,
            "counts": counts(current),
            "occurrences": [asdict(item) for item in current],
            "added": [asdict(item) for item in added],
            "removed": [
                asdict(item) for item in multiset_difference(base or [], current)
            ],
        }
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

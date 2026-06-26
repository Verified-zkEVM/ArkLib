#!/usr/bin/env python3
"""Fail when a revision increases Lean text-style lint errors.

This wraps ArkLib's legacy Python style checks for CI. The workflow runs the
mathlib Lean text-style linter separately; the Python checks stay here for
checks that have not yet been ported upstream.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]

HUMAN_RE = re.compile(
    r"^(?P<path>.+?) : line (?P<line>\d+) : (?P<code>ERR_[A-Z_]+) : (?P<message>.*)$"
)
GITHUB_RE = re.compile(
    r"^::(?P<kind>error|warning) file=(?P<path>[^,]+),line=(?P<line>\d+),"
    r"code=(?P<code>[^:]+)::(?P<text>.*)$"
)


@dataclass(frozen=True)
class StyleError:
    path: str
    line: int
    code: str
    message: str
    raw: str


def git(
    args: list[str],
    *,
    cwd: Path = ROOT,
    check: bool = True,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=cwd,
        check=check,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


def normalize_path(path_text: str, root: Path) -> str:
    path = Path(path_text)
    if path.is_absolute():
        try:
            return path.resolve().relative_to(root.resolve()).as_posix()
        except ValueError:
            return path.as_posix()
    return path.as_posix()


def parse_lint_output(output: str, root: Path) -> list[StyleError]:
    errors: list[StyleError] = []
    for line in output.splitlines():
        human = HUMAN_RE.match(line)
        if human:
            errors.append(
                StyleError(
                    path=normalize_path(human.group("path"), root),
                    line=int(human.group("line")),
                    code=human.group("code"),
                    message=human.group("message"),
                    raw=line,
                )
            )
            continue

        github = GITHUB_RE.match(line)
        if github:
            text = github.group("text")
            message = text.split(": ", 1)[1] if ": " in text else text
            errors.append(
                StyleError(
                    path=normalize_path(github.group("path"), root),
                    line=int(github.group("line")),
                    code=github.group("code"),
                    message=message,
                    raw=line,
                )
            )
    return errors


def deduplicate_errors(errors: list[StyleError]) -> list[StyleError]:
    seen: set[tuple[str, int, str, str]] = set()
    deduplicated: list[StyleError] = []
    for error in errors:
        key = (error.path, error.line, error.code, error.message)
        if key in seen:
            continue
        seen.add(key)
        deduplicated.append(error)
    return deduplicated


def run_command(command: list[str], *, cwd: Path, source_root: Path) -> list[StyleError]:
    proc = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.stderr:
        sys.stderr.write(proc.stderr)

    errors = parse_lint_output(proc.stdout, source_root)
    if proc.returncode not in (0, 1):
        sys.stdout.write(proc.stdout)
        raise SystemExit(proc.returncode)
    if proc.returncode == 1 and not errors:
        sys.stdout.write(proc.stdout)
        raise SystemExit(
            f"{command[0]} failed, but no parseable style errors were found"
        )
    return errors


def run_style_linter(source_root: Path, files: list[str]) -> list[StyleError]:
    if not files:
        return []

    absolute_files = [(source_root / path).resolve().as_posix() for path in files]
    legacy_script = ROOT / "scripts" / "lint-style.py"
    errors = (
        run_command(
            [sys.executable, str(legacy_script), *absolute_files],
            cwd=ROOT,
            source_root=source_root,
        )
        if legacy_script.exists()
        else []
    )
    return deduplicate_errors(errors)


def changed_lean_files(base: str, head: str) -> list[str]:
    proc = git(["diff", "--name-only", "--diff-filter=ACMRTUXB", base, head, "--", "ArkLib"])
    return sorted(
        path
        for path in proc.stdout.splitlines()
        if path.startswith("ArkLib/") and path.endswith(".lean")
    )


def path_exists_at_revision(revision: str, path: str) -> bool:
    return git(["cat-file", "-e", f"{revision}:{path}"], check=False).returncode == 0


def add_base_worktree(base: str) -> tuple[Path, Path]:
    tmp_parent = Path(tempfile.mkdtemp(prefix="arklib-style-base-"))
    worktree = tmp_parent / "base"
    proc = git(["worktree", "add", "--detach", "--quiet", str(worktree), base], check=False)
    if proc.returncode != 0:
        shutil.rmtree(tmp_parent, ignore_errors=True)
        sys.stderr.write(proc.stderr)
        raise SystemExit(proc.returncode)
    return tmp_parent, worktree


def remove_base_worktree(tmp_parent: Path, worktree: Path) -> None:
    git(["worktree", "remove", "--force", str(worktree)], check=False)
    shutil.rmtree(tmp_parent, ignore_errors=True)


def count_by_file_and_code(errors: list[StyleError]) -> Counter[tuple[str, str]]:
    return Counter((error.path, error.code) for error in errors)


def print_error(error: StyleError, *, github: bool) -> None:
    if github:
        print(
            f"::error file={error.path},line={error.line},code={error.code}::"
            f"{error.path}:{error.line} {error.code}: {error.message}"
        )
    else:
        print(error.raw)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, help="base commit or ref to compare against")
    parser.add_argument(
        "--head",
        default="HEAD",
        help="head commit or ref used for changed-file detection",
    )
    parser.add_argument(
        "--github",
        action="store_true",
        help="emit GitHub workflow annotations for affected style errors",
    )
    args = parser.parse_args()

    files = changed_lean_files(args.base, args.head)
    if not files:
        print("No changed ArkLib Lean files to style-lint.")
        return 0

    current_head = git(["rev-parse", "HEAD"]).stdout.strip()
    requested_head = git(["rev-parse", args.head]).stdout.strip()
    if current_head != requested_head:
        print(
            "WARNING: lint-style-diff.py lints the current checkout, but --head resolved to "
            f"{requested_head[:12]} while HEAD is {current_head[:12]}.",
            file=sys.stderr,
        )

    head_files = [path for path in files if (ROOT / path).is_file()]
    base_files = [path for path in files if path_exists_at_revision(args.base, path)]
    print(f"Checking {len(head_files)} changed ArkLib Lean file(s) for style regressions.")

    head_errors = run_style_linter(ROOT, head_files)

    tmp_parent, base_worktree = add_base_worktree(args.base)
    try:
        base_errors = run_style_linter(base_worktree, base_files)
    finally:
        remove_base_worktree(tmp_parent, base_worktree)

    base_counts = count_by_file_and_code(base_errors)
    head_counts = count_by_file_and_code(head_errors)
    increases = [
        (path, code, base_counts[(path, code)], head_count)
        for (path, code), head_count in sorted(head_counts.items())
        if head_count > base_counts[(path, code)]
    ]

    if not increases:
        print("Style lint regression check passed.")
        return 0

    affected = {(path, code) for path, code, _, _ in increases}
    print("Style lint regressions detected:")
    for path, code, base_count, head_count in increases:
        print(f"- {path} {code}: {base_count} -> {head_count}")

    print()
    print("Current-checkout style errors for affected files and codes:")
    for error in head_errors:
        if (error.path, error.code) in affected:
            print_error(error, github=args.github)

    print()
    print(
        "This check compares counts by file and error code, so the listed lines can include "
        "pre-existing errors of the same kind."
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Tests for pr-scope.py on temporary Git repositories."""

from __future__ import annotations

import contextlib
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().with_name("pr-scope.py")
SPEC = importlib.util.spec_from_file_location("pr_scope", SCRIPT)
assert SPEC and SPEC.loader
SCOPE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SCOPE
SPEC.loader.exec_module(SCOPE)


def run(*args: str) -> None:
    subprocess.run(["git", *args], check=True, capture_output=True)


def write(path: str, text: str) -> None:
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(text, encoding="utf-8")


@contextlib.contextmanager
def repository(files: dict[str, str]):
    """Create a repository with `files` on `main`, a fork remote, and a `topic` branch."""
    previous = Path.cwd()
    with tempfile.TemporaryDirectory() as directory:
        os.chdir(directory)
        try:
            run("init", "-q", "-b", "main")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            for path, text in files.items():
                write(path, text)
            run("add", "-A")
            run("commit", "-q", "-m", "base")
            run("remote", "add", "origin", "https://github.com/Verified-zkEVM/ArkLib.git")
            run("update-ref", "refs/remotes/origin/main", "main")
            run("checkout", "-q", "-b", "topic")
            yield
        finally:
            os.chdir(previous)


def commit(message: str = "change") -> None:
    run("add", "-A")
    run("commit", "-q", "-m", message)


class ScopeTests(unittest.TestCase):
    def test_committed_and_uncommitted_changes(self) -> None:
        with repository({"a.lean": "a\n", "b.lean": "b\n"}):
            write("a.lean", "changed\n")
            commit()
            write("b.lean", "uncommitted\n")
            write("c.lean", "staged\n")
            run("add", "c.lean")
            paths = [change.path for change in SCOPE.changes("origin/main")]
            self.assertEqual(paths, ["a.lean", "b.lean", "c.lean"])

    def test_staged_work_on_a_branch_at_the_base(self) -> None:
        with repository({"a.lean": "a\n"}):
            write("new.lean", "staged\n")
            run("add", "new.lean")
            self.assertEqual([c.path for c in SCOPE.changes("origin/main")], ["new.lean"])

    def test_merge_in_progress_excludes_the_changes_of_the_base(self) -> None:
        with repository({"a.lean": "a\n", "base.lean": "base\n"}):
            write("a.lean", "topic\n")
            commit()
            run("checkout", "-q", "main")
            write("base.lean", "advanced\n")
            write("moved/README.md", "base work\n")
            commit("advance the base")
            run("update-ref", "refs/remotes/origin/main", "main")
            run("checkout", "-q", "topic")
            run("merge", "--no-commit", "--no-ff", "-q", "main")
            self.assertTrue(SCOPE.merge_in_progress())
            self.assertEqual([c.path for c in SCOPE.changes("origin/main")], ["a.lean"])

    def test_deleted_renamed_and_restored_paths(self) -> None:
        with repository({"old.lean": "o\n", "gone.lean": "g\n", "back.lean": "b\n"}):
            run("mv", "old.lean", "new.lean")
            run("rm", "-q", "gone.lean", "back.lean")
            commit()
            write("back.lean", "b\n")
            write("tmp.lean", "t\n")
            commit("restore one file and add another")
            run("rm", "-q", "tmp.lean")
            self.assertEqual(SCOPE.deleted_paths("origin/main"), ["gone.lean", "old.lean"])

    def test_generated_drift(self) -> None:
        with repository({"docs/kb/_generated/refs.json": "{}\n"}):
            write("docs/kb/_generated/refs.json", '{"a": 1}\n')
            commit()
            committed, uncommitted = SCOPE.generated_drift("origin/main")
            self.assertEqual(committed, ["docs/kb/_generated/refs.json"])
            self.assertEqual(uncommitted, [])

    def test_working_files(self) -> None:
        with repository({"README.md": "r\n"}):
            write("PLAN.md", "plan\n")
            write("docs/wiki/page.md", "page\n")
            write("NOTES.md", "notes\n")
            run("add", "docs/wiki/page.md", "NOTES.md")
            found = SCOPE.working_files("origin/main")
            self.assertEqual(found, [("NOTES.md", "added"), ("PLAN.md", "untracked")])

    def test_fork_remote_warning(self) -> None:
        with repository({"a.lean": "a\n"}):
            run("remote", "set-url", "origin", "https://github.com/someone/ArkLib.git")
            warnings = SCOPE.check_base("origin/main")
            self.assertTrue(any("someone" in warning for warning in warnings))


class StaleReferenceTests(unittest.TestCase):
    def test_module_promoted_to_a_directory(self) -> None:
        files = {"ArkLib/Foo/Gadget.lean": "def g := 1\n",
                 "ArkLib/User.lean": "import ArkLib.Foo.Gadget\n",
                 "docs/page.md": "Refer to `Gadget.lean`.\n"}
        with repository(files):
            run("rm", "-q", "ArkLib/Foo/Gadget.lean")
            write("ArkLib/Foo/Gadget/Core.lean", "def g := 1\n")
            write("ArkLib/User.lean", "import ArkLib.Foo.Gadget.Core\n")
            write("docs/other.md", "The module ArkLib.Foo.Gadget is gone.\n")
            commit()
            hits = SCOPE.stale_references("origin/main")
            lines = sorted((kind.split(",")[0], line) for _, kind, line in hits)
            self.assertEqual(lines, [("basename", "docs/page.md:1:Refer to `Gadget.lean`."),
                                     ("module",
                                      "docs/other.md:1:The module ArkLib.Foo.Gadget is gone.")])

    def test_common_basename_and_namesake(self) -> None:
        files = {"docs/a/README.md": "a\n", "docs/b/README.md": "b\n",
                 "docs/index.md": "[a](a/README.md) and [b](b/README.md)\n",
                 "ArkLib/Hachi/Escape.lean": "x\n", "ArkLib/Other/Escape.lean": "y\n",
                 "docs/escape.md": "Refer to `Escape.lean`.\n"}
        with repository(files):
            run("rm", "-q", "docs/a/README.md", "ArkLib/Hachi/Escape.lean")
            commit()
            hits = SCOPE.stale_references("origin/main")
            kinds = sorted((path, kind) for path, kind, _ in hits)
            self.assertEqual(kinds, [
                ("ArkLib/Hachi/Escape.lean", "basename, also the name of ArkLib/Other/Escape.lean"),
                ("docs/a/README.md", "parent and basename")])


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Tests for the pull request title check and the writing check."""

from __future__ import annotations

import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent


def load(name: str, filename: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


TITLE = load("check_pr_title", "check-pr-title.py")
WRITING = load("check_writing", "check-writing.py")


class TitleTests(unittest.TestCase):
    types = ["feat", "fix", "doc", "chore", "refactor"]

    def assertValid(self, title: str) -> None:
        self.assertEqual(TITLE.problems(title, self.types), [], title)

    def assertInvalid(self, title: str) -> None:
        self.assertNotEqual(TITLE.problems(title, self.types), [], title)

    def test_types_come_from_contributing(self) -> None:
        types = TITLE.allowed_types()
        self.assertIn("feat", types)
        self.assertIn("doc", types)
        self.assertNotIn("docs", types)

    def test_valid_titles(self) -> None:
        self.assertValid("feat: add the Johnson bound")
        self.assertValid("fix(hash): Poseidon2 round constants in the right order")
        self.assertValid("refactor(binius)!: remove the legacy folding API")
        self.assertValid("doc(contributing): describe `#print axioms` evidence")

    def test_invalid_titles(self) -> None:
        self.assertInvalid("Prove the subspace-design MCA bound")
        self.assertInvalid("docs: refresh the roadmap")
        self.assertInvalid("feat(proximityGens) : lemmas 6.2 to 6.6")
        self.assertInvalid("feat: add the Johnson bound.")
        self.assertInvalid("feat:add the Johnson bound")
        self.assertInvalid("feat: ")
        self.assertInvalid("feat():  add a bound")

    def test_capitalized_subject_is_a_warning(self) -> None:
        self.assertValid("feat(proximityGens): Proof of Theorem 6.1")
        self.assertTrue(TITLE.warnings("feat(proximityGens): Proof of Theorem 6.1"))
        self.assertFalse(TITLE.warnings("feat(fri): FRI query soundness"))
        self.assertFalse(TITLE.warnings("fix(hash): Poseidon2 round constants"))

    def test_github_output_escapes_data(self) -> None:
        output = io.StringIO()
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true", "PR_TITLE": "bad %0A"}):
            with mock.patch("sys.stdout", output):
                self.assertEqual(TITLE.main(["check-pr-title.py"]), 1)
        self.assertIn("::error title=Pull request title::", output.getvalue())
        self.assertIn("%250A", output.getvalue())


def findings(text: str, path: str = "doc.md") -> list[str]:
    blocks = WRITING.file_blocks(path, text)
    return sorted({item.rule for item in WRITING.check_blocks(blocks)})


class WritingRuleTests(unittest.TestCase):
    def test_vocabulary_is_parsed(self) -> None:
        general, history = WRITING.avoid_words()
        self.assertIn("utilize", general)
        self.assertIn("e.g.", general)
        self.assertIn("no longer", history)
        self.assertNotIn("now", history)
        self.assertNotIn("new", history)

    def test_sentence_length(self) -> None:
        long_sentence = " ".join(["word"] * 26) + "."
        self.assertEqual(findings(long_sentence), ["S1"])
        self.assertEqual(findings(" ".join(["word"] * 25) + "."), [])
        self.assertEqual(findings("1. " + " ".join(["word"] * 21) + "."), ["S1"])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + "."), [])

    def test_text_in_parentheses_is_a_separate_sentence(self) -> None:
        inner = " ".join(["word"] * 40)
        self.assertEqual(findings(f"The bound holds ({inner})."), ["S1"])
        self.assertEqual(findings(f"The bound holds (see ({inner}))."), ["S1"])
        self.assertEqual(findings("The bound holds (for each code)."), [])

    def test_one_word_elements(self) -> None:
        sentence = ("The bound `Code.dist_le_of_mem (h : x ∈ C)` and $\\delta \\le 1 - \\sqrt{\\rho}$ "
                    "from [BCIKS20, Theorem 1.2] and [the page](https://example.org/a.b) hold "
                    "(for every code that this page lists) here.")
        self.assertEqual(findings(sentence), [])
        counted = WRITING.mask(sentence, collapse_parentheses=True)
        self.assertEqual(WRITING.word_count(counted), 13)

    def test_paragraph_length(self) -> None:
        self.assertEqual(findings(" ".join(["One sentence."] * 7)), ["P2"])
        self.assertEqual(findings(" ".join(["One sentence."] * 6)), [])

    def test_punctuation(self) -> None:
        self.assertEqual(findings("The code is linear; it is also cyclic."), ["U1"])
        self.assertEqual(findings("The code is linear — it is also cyclic."), ["U2"])
        self.assertEqual(findings("The Reed–Solomon code has rate 1–2 in this range."), [])
        self.assertEqual(findings("Write `a; b` in Lean."), [])

    def test_words(self) -> None:
        self.assertEqual(findings("Use a ring, e.g. the integers."), ["W1", "W7"])
        self.assertEqual(findings("We utilize the lemma."), ["W1"])
        self.assertEqual(findings("Set up the build."), ["W6"])
        self.assertEqual(findings("The word ends in a vowel."), [])
        self.assertEqual(findings("Don't run the build."), ["S5"])
        self.assertEqual(findings("The prover's message is short."), [])

    def test_verbs(self) -> None:
        self.assertEqual(findings("The lemma has changed."), ["V1"])
        self.assertEqual(findings("The verifier is rejecting the proof string."), ["V1"])
        self.assertEqual(findings("The polynomials have bounded degree."), [])
        self.assertEqual(findings("The witness is missing."), [])
        self.assertEqual(findings("Using the lemma, we bound the error."), ["V2"])
        self.assertEqual(findings("Folding halves the length of the word."), [])
        self.assertEqual(findings("During a merge, the base is the merge base."), [])
        self.assertEqual(findings("The request may have failed."), [])

    def test_bare_this(self) -> None:
        self.assertEqual(findings("The bound is tight. This is the main result."), ["S7"])
        self.assertEqual(findings("The bound is tight. This lemma is the main result."), [])

    def test_history_words_apply_to_library_text_only(self) -> None:
        self.assertEqual(findings("The lemma is no longer needed.", "docs/wiki/page.md"), ["C3"])
        self.assertEqual(findings("The lemma is no longer needed.", "body.md"), [])
        self.assertEqual(findings("The new code is now linear.", "docs/wiki/page.md"), [])

    def test_exempt_text(self) -> None:
        text = ("Avoid \"e.g.; it's robust\" in prose.\n\n# Heading; with e.g. a dash — here\n\n"
                "```\nlet x := 1; e.g.\n```\n\n<!-- e.g.; utilize -->\n")
        self.assertEqual(findings(text), [])

    def test_table_cells_and_header(self) -> None:
        text = "| Rule; header | Use |\n|---|---|\n| One cell; two | Fine. |\n"
        self.assertEqual(findings(text), ["U1"])


class LeanExtractionTests(unittest.TestCase):
    def test_doc_comments_and_line_numbers(self) -> None:
        source = ('/-! # Title\n\nThe module; with a problem. -/\n'
                  'def f : Nat := 1 -- a trailing comment; also a problem\n'
                  'def s : String := "-- not a comment; ok"\n'
                  '/-- The definition utilizes `x; y`. -/\n'
                  'theorem t : True := trivial\n')
        blocks = WRITING.lean_blocks("A.lean", source)
        lines = {block.line: block.text for block in blocks}
        self.assertIn(3, lines)
        self.assertIn(4, lines)
        self.assertIn(6, lines)
        self.assertNotIn(5, lines)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(3, "U1"), (4, "U1"), (6, "W1")})

    def test_character_literals_do_not_start_strings(self) -> None:
        source = ("def quote : Char := '\"'\n"
                  "def escaped : Char := '\\''\n"
                  "def x' : Nat := 1\n"
                  "/-- The definition utilizes a quote. -/\n"
                  "def y : Nat := 2\n")
        blocks = WRITING.lean_blocks("A.lean", source)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(4, "W1")})


class ChangedLineTests(unittest.TestCase):
    def test_only_changed_blocks_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def run(*args: str) -> None:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)

            run("init", "-q", "-b", "main")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            (root / "page.md").write_text("Old text; with a semicolon.\n\nA clean line.\n")
            run("add", "page.md")
            run("commit", "-q", "-m", "base")
            run("checkout", "-q", "-b", "topic")
            (root / "page.md").write_text(
                "Old text; with a semicolon.\n\nA clean line.\n\nNew text; also bad.\n")
            (root / "untracked.md").write_text("Untracked; ignored.\n")
            with mock.patch.object(WRITING, "ROOT", root):
                blocks = WRITING.changed_blocks("main")
            self.assertEqual([block.line for block in blocks], [5])


class RepositoryTests(unittest.TestCase):
    def test_writing_pages_follow_the_standard(self) -> None:
        paths = ["docs/wiki/writing.md", "docs/wiki/writing-vocabulary.md",
                 ".github/pull_request_template.md"]
        blocks = []
        for path in paths:
            blocks.extend(WRITING.file_blocks(path, (ROOT / path).read_text(encoding="utf-8")))
        problems = [f"{item.path}:{item.line} {item.rule} {item.excerpt}"
                    for item in WRITING.check_blocks(blocks)]
        self.assertEqual(problems, [])


if __name__ == "__main__":
    unittest.main()

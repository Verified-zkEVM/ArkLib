#!/usr/bin/env -S uv run --no-project --python 3.12 python
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
    types = ["feat", "fix", "doc", "docs", "chore", "refactor"]

    def assertValid(self, title: str) -> None:
        self.assertEqual(TITLE.problems(title, self.types), [], title)

    def assertInvalid(self, title: str) -> None:
        self.assertNotEqual(TITLE.problems(title, self.types), [], title)

    def test_types_come_from_contributing(self) -> None:
        types = TITLE.allowed_types()
        self.assertIn("feat", types)
        self.assertIn("doc", types)
        self.assertIn("docs", types)

    def test_valid_titles(self) -> None:
        self.assertValid("feat: add the Johnson bound")
        self.assertValid("fix(hash): Poseidon2 round constants in the right order")
        self.assertValid("refactor(binius)!: remove the legacy folding API")
        self.assertValid("doc(contributing): describe `#print axioms` evidence")
        self.assertValid("docs: refresh the roadmap")

    def test_invalid_titles(self) -> None:
        self.assertInvalid("Prove the subspace-design MCA bound")
        self.assertInvalid("unknown: refresh the roadmap")
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
                self.assertEqual(TITLE.main(["check-pr-title.py"]), 0)
        self.assertIn("::warning title=Pull request title::", output.getvalue())
        self.assertNotIn("::error", output.getvalue())
        self.assertIn("%250A", output.getvalue())

    def test_invalid_title_is_advisory_by_default(self) -> None:
        with mock.patch("sys.stdout", io.StringIO()) as output:
            self.assertEqual(TITLE.main(["check-pr-title.py",
                                         "Prove native state-restoration knowledge soundness"]), 0)
        self.assertIn("Invalid pull request title", output.getvalue())

    def test_strict_title_check_fails_on_invalid_format(self) -> None:
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}):
            with mock.patch("sys.stdout", io.StringIO()) as output:
                self.assertEqual(TITLE.main(["check-pr-title.py", "--strict", "bad title"]), 1)
        self.assertIn("::error title=Pull request title::", output.getvalue())

    def test_strict_title_check_accepts_valid_format(self) -> None:
        with mock.patch("sys.stdout", io.StringIO()):
            self.assertEqual(TITLE.main(["check-pr-title.py", "--strict", "docs: explain the bounds"]), 0)


def findings(text: str, path: str = "doc.md") -> list[str]:
    blocks = WRITING.file_blocks(path, text)
    return sorted({item.rule for item in WRITING.check_blocks(blocks)})


class WritingRuleTests(unittest.TestCase):
    def test_semicolon_excerpt_starts_before_the_semicolon(self) -> None:
        for text in ["This works; it is fine.", "; The lemma holds."]:
            with self.subTest(text=text):
                blocks = WRITING.file_blocks("page.md", text + "\n")
                excerpts = [item.excerpt for item in WRITING.check_blocks(blocks) if item.rule == "U1"]
                self.assertEqual(excerpts, [text])

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

    def test_sentence_can_start_with_a_lowercase_filename(self) -> None:
        text = " ".join(["word"] * 20) + ". pr-scope.py " + " ".join(["word"] * 20) + "."
        self.assertEqual(findings(text), [])
        self.assertEqual(len(WRITING.sentences(text)), 2)

    def test_license_text_is_exempt_but_later_prose_is_checked(self) -> None:
        legal = "## Licensing\n\nEnsure these terms; do not change them.\n"
        self.assertEqual(findings(legal, "CONTRIBUTING.md"), [])
        nested = legal + "\n### Conditions\n\nWe utilize these terms.\n"
        self.assertEqual(findings(nested, "CONTRIBUTING.md"), [])
        resumed = nested + "\n## Next steps\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(resumed, "CONTRIBUTING.md"), ["W1"])
        self.assertEqual(findings("Ensure these terms; do not change them.", "LICENSE.md"), [])
        fenced = "```md\n## License\n```\n\nWe utilize the lemma.\n"
        self.assertEqual(findings(fenced), ["W1"])

    def test_mathematical_terms_are_not_blanket_vocabulary_bans(self) -> None:
        for text in ["The following are equivalent.", "Every valid transcript has a witness.",
                     "The space is simply connected.", "This functor is essentially surjective.",
                     "Complete the pull request template."]:
            self.assertNotIn("W1", findings(text), text)

    def test_paragraph_length(self) -> None:
        self.assertEqual(findings(" ".join(["One sentence."] * 7)), ["P2"])
        self.assertEqual(findings(" ".join(["One sentence."] * 6)), [])

    def test_punctuation(self) -> None:
        self.assertEqual(findings("The code is linear; it is also cyclic."), ["U1"])
        self.assertEqual(findings("The code is linear — it is also cyclic."), ["U2"])
        self.assertEqual(findings("The Reed–Solomon code has rate 1–2 in this range."), [])
        self.assertEqual(findings("Write `a; b` in Lean."), [])

    def test_definition_separator_is_not_a_clause_join(self) -> None:
        for dash in ["—", "–", "--"]:
            for term in ["`Δ₀(u, v)`", "``Δ₀(u, v)``", "$\\delta$", "**Relative distance**"]:
                with self.subTest(dash=dash, term=term):
                    self.assertEqual(findings(f"- {term} {dash} `hammingDist u v`."), [])
        self.assertNotIn("U2", findings("- `Λ(C, δ, f)` and `Λ(C, δ)` — write `Code.Lambda C δ`."))
        self.assertEqual(findings("- `Gadget/` (§2.1) — the gadget matrix."), [])
        self.assertEqual(findings("- `EvalSplit.lean` (§4, Eq. (12)) — the matrix split."), [])

    def test_definition_description_is_still_checked(self) -> None:
        self.assertEqual(findings("- `δ` — We utilize the lemma."), ["W1"])
        self.assertEqual(findings("- `δ` — relative distance — it is bounded."), ["U2"])
        self.assertEqual(findings("- `δ` — relative distance.\n  The code is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("- `C` (§2.1) is linear — it is cyclic."), ["U2"])
        self.assertEqual(findings("| Term | Description |\n|---|---|\n| `C` is linear — it is cyclic. | Bound |"), ["U2"])

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
        environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.dict(os.environ, environment, clear=True):
            root = Path(directory)

            def run(*args: str) -> None:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)

            run("init", "-q", "-b", "main", "--template=")
            run("config", "user.email", "test@example.org")
            run("config", "user.name", "Test")
            run("config", "commit.gpgsign", "false")
            run("config", "core.hooksPath", os.devnull)
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
                 ".github/pull_request_template.md", "CONTRIBUTING.md",
                 "docs/skills/write-technical-prose.md", "AGENTS.md"]
        blocks = []
        for path in paths:
            blocks.extend(WRITING.file_blocks(path, (ROOT / path).read_text(encoding="utf-8")))
        problems = [f"{item.path}:{item.line} {item.rule} {item.excerpt}"
                    for item in WRITING.check_blocks(blocks)]
        self.assertEqual(problems, [])


if __name__ == "__main__":
    unittest.main()

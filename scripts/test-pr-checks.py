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

    def test_nonimperative_verbs_receive_advisory_feedback(self) -> None:
        for title in ["feat: added the FRI round", "feat(fri): adds the FRI round",
                      "fix: fixed a typo"]:
            with self.subTest(title=title):
                self.assertTrue(TITLE.warnings(title))
                with mock.patch("sys.stdout", io.StringIO()) as output:
                    self.assertEqual(TITLE.main(["check-pr-title.py", title]), 0)
                self.assertIn("imperative phrase or a noun phrase", output.getvalue())
                self.assertNotIn("has the correct format", output.getvalue())
        self.assertFalse(TITLE.warnings("feat: the FRI soundness theorem"))
        self.assertFalse(TITLE.warnings("docs: changes to the guide"))

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
        self.assertEqual(findings("1. " + " ".join(["word"] * 21) + "."), [])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + "."), [])
        self.assertEqual(findings("- " + " ".join(["word"] * 21) + ".", 'AGENTS.md'), ['S1'])
        self.assertEqual(findings(" ".join(["word"] * 21) + ".", 'docs/skills/task.md'), ['S1'])
        self.assertEqual(findings("- [ ] " + " ".join(["word"] * 21) + "."), ['S1'])
        self.assertNotIn('S1', findings('/-!\n1. ' + ' '.join(['word'] * 21) + '.\n-/', 'M.lean'))

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


    def test_definition_description_is_still_checked(self) -> None:
        self.assertEqual(findings("- `δ` — We utilize the lemma."), ["W1"])

    def test_grammar_and_structure_are_left_to_review(self) -> None:
        for text in ["The verifier is rejecting the message.", "The lemma has changed.",
                     "Leading coefficients aside, the lemma holds.", "Constructing a proof, the budget changes.",
                     "The bound holds. This is the main result.", "The code is linear; it is cyclic.",
                     "The code is linear — it is cyclic.", "Before making a change, run the tests.",
                     " ".join(["One sentence."] * 7)]:
            with self.subTest(text=text):
                self.assertEqual(findings(text), [])

    def test_word_suggestions_are_optional(self) -> None:
        with mock.patch("sys.stdin", io.StringIO("We utilize this lemma.")):
            with mock.patch("sys.stdout", io.StringIO()) as output:
                self.assertEqual(WRITING.main(["check-writing.py", "--stdin", "body"]), 0)
        self.assertIn("1 writing suggestion(s)", output.getvalue())
        self.assertIn("leave clear, correct text alone", output.getvalue())

    def test_words(self) -> None:
        self.assertEqual(findings("Use a ring, e.g. the integers."), ["W7"])
        self.assertEqual(findings("We utilize the lemma."), ["W1"])
        self.assertEqual(findings("Set up the build."), ["W6"])
        self.assertEqual(findings("The word ends in a vowel."), [])
        self.assertEqual(findings("Don't run the build."), ["S5"])
        self.assertEqual(findings("The prover's message is short."), [])


    def test_history_words_apply_to_library_text_only(self) -> None:
        self.assertEqual(findings("The lemma is no longer needed.", "docs/wiki/page.md"), ["C3"])
        self.assertEqual(findings("The lemma is no longer needed.", "body.md"), [])
        self.assertEqual(findings("The new code is now linear.", "docs/wiki/page.md"), [])

    def test_exempt_text(self) -> None:
        text = ("Avoid \"e.g.; it's robust\" in prose.\n\n# Heading; with e.g. a dash — here\n\n"
                "```\nlet x := 1; e.g.\n```\n\n<!-- e.g.; utilize -->\n")
        self.assertEqual(findings(text), [])

    def test_table_cells_and_header(self) -> None:
        text = "| Utilize this header | Use |\n|---|---|\n| We utilize this cell. | Fine. |\n"
        self.assertEqual(findings(text), ["W1"])


class LeanExtractionTests(unittest.TestCase):
    def test_doc_comments_and_line_numbers(self) -> None:
        source = ('/-! # Title\n\nWe utilize this module. -/\n'
                  'def f : Nat := 1 -- We utilize this value.\n'
                  'def s : String := "-- utilize is not a comment"\n'
                  '/-- The definition utilizes `x; y`. -/\n'
                  'theorem t : True := trivial\n')
        blocks = WRITING.lean_blocks("A.lean", source)
        lines = {block.line: block.text for block in blocks}
        self.assertIn(3, lines)
        self.assertIn(4, lines)
        self.assertIn(6, lines)
        self.assertNotIn(5, lines)
        rules = {(item.line, item.rule) for item in WRITING.check_blocks(blocks)}
        self.assertEqual(rules, {(3, "W1"), (4, "W1"), (6, "W1")})

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


class WritingRegressionTests(unittest.TestCase):
    def test_findings_point_to_the_source_line(self) -> None:
        text = ('The [reference](https://example.org/a(b)) and `x` agree.\n'
                'The quoted "a; b" is code here.\n'
                'We utilize the last line.\n')
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        item = next(f for f in found if f.rule == 'W1')
        self.assertEqual(item.line, 3)
        self.assertEqual(item.excerpt, 'utilize')
        self.assertNotIn('Code', item.excerpt)

    def test_line_numbers_in_lists_and_lean_comments(self) -> None:
        cases = [('- First line.\n  We utilize the second line.\n', 'page.md', 2),
                 ('/-! First line.\nWe utilize the second line.\n-/', 'A.lean', 2),
                 ('-- First line.\n-- We utilize the second line.\n', 'A.lean', 2)]
        for text, path, line in cases:
            with self.subTest(path=path, text=text):
                found = WRITING.check_blocks(WRITING.file_blocks(path, text))
                self.assertEqual([f.line for f in found if f.rule == 'W1'], [line])

    def test_word_findings_keep_source_spelling_and_line(self) -> None:
        text = 'A clean line with `code`.\nWe utilize the lemma.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([(f.line, f.excerpt) for f in found if f.rule == 'W1'], [(2, 'utilize')])

    def test_parenthetical_length_finding_points_inside_the_parenthesis(self) -> None:
        text = 'A short sentence (\n' + ' '.join(['word'] * 30) + ').'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'S1'], [2])


    def test_latin_abbreviations_have_one_finding(self) -> None:
        for word in ['e.g.', 'i.e.', 'etc.', 'cf.', 'resp.']:
            pattern = WRITING.word_pattern([word])
            blocks = WRITING.file_blocks('page.md', f'Use {word} here.')
            found = [f for b in blocks for f in WRITING.check_block(b, pattern, None)]
            self.assertEqual([f.rule for f in found], ['W7'])

    def test_final_e_verbs_keep_ing_inflections(self) -> None:
        pattern = WRITING.word_pattern(['ensure', 'utilize', 'leverage'])
        for word in ['ensure', 'ensures', 'ensured', 'ensuring', 'utilizing', 'leveraging']:
            self.assertIsNotNone(pattern.fullmatch(word), word)
        self.assertIsNone(pattern.fullmatch('reassuring'))

    def test_fences_use_their_opening_character_and_length(self) -> None:
        for opening, inner in [('~~~~', '```'), ('````', '```'), ('~~~', '```')]:
            text = f'{opening}\n{inner}\nUtilize ignored code.\n{opening}\n\nWe utilize prose.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(6, 'W1')])

    def test_visible_prose_after_comments_and_thematic_breaks(self) -> None:
        for text in ['<!-- comment --> We utilize prose.',
                     '---\nWe utilize prose.\n---', '#1431 utilizes prose.']:
            self.assertIn('W1', findings(text), text)
        self.assertEqual(findings('    Utilize example code.\n'), [])
        self.assertEqual(findings('---\nstatus: utilize metadata\n---\nClean prose.'), [])

    def test_literal_comment_markers_do_not_hide_prose(self) -> None:
        for text in ['The token `<!--` opens a comment.\nWe utilize prose.\n',
                     '```\n<!--\n```\nWe utilize prose.\n',
                     'The token `<!--` is code, as is `-->`.\nWe utilize prose.\n',
                     'The token `some\n<!--\ntext` is literal.\nWe utilize prose.\n',
                     'The text \\<!-- is literal.\nWe utilize prose.\n',
                     'The text \\<!-- utilizes a literal; --> stays visible.']:
            with self.subTest(text=text):
                self.assertIn('W1', findings(text))
        text = 'A clean line.\n    We utilize this paragraph continuation.\n'
        self.assertIn('W1', findings(text))

    def test_indented_list_continuations_remain_prose(self) -> None:
        for text in ['- Outer item.\n\n    - We utilize prose.\n',
                     '1. Outer item.\n\n    1. We utilize prose.\n',
                     '- Outer item.\n\n    We utilize prose.\n']:
            with self.subTest(text=text):
                self.assertIn('W1', findings(text))

    def test_raw_lean_strings_do_not_create_comments(self) -> None:
        for value in ['r#"a " -- utilize fake comment"#', 'r"a\\"']:
            text = f'def s := {value}\n-- We utilize prose.\n'
            found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
            self.assertEqual([(f.line, f.rule) for f in found], [(2, 'W1')])

    def test_escaped_newlines_in_lean_strings_keep_comment_locations(self) -> None:
        text = 'def s := "a\\\nb"\n-- We utilize prose.\n'
        found = WRITING.check_blocks(WRITING.file_blocks('A.lean', text))
        self.assertEqual([(f.line, f.rule) for f in found], [(3, 'W1')])


    def test_wrapped_phrasal_and_history_terms_remain_visible(self) -> None:
        self.assertIn('W6', findings('Carry\nout the test.'))
        self.assertIn('C3', findings('The lemma is no\nlonger needed.', 'docs/wiki/page.md'))

    def test_wrapped_straight_quotes_are_one_exempt_element(self) -> None:
        text = ('"essentially\nsurjective". Review their meaning. Do not delete them as '
                'isolated words. "Negligible" retains its technical meaning.')
        self.assertEqual(findings(text), [])
        text = 'The text "utilize quoted\nwords; ignored" is literal.\nWe utilize prose.'
        found = WRITING.check_blocks(WRITING.file_blocks('page.md', text))
        self.assertEqual([f.line for f in found if f.rule == 'W1'], [3])

    def test_annotation_properties_are_escaped(self) -> None:
        item = WRITING.Finding('a%,line=9::b.md', 2, 'W1', 'message', 'excerpt')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            WRITING.report([item], True, True)
        self.assertIn('file=a%25%2Cline=9%3A%3Ab.md,line=2,', output.getvalue())


class ChangedFileRegressionTests(unittest.TestCase):
    def setUp(self) -> None:
        super().setUp()
        environment = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
        environment.update(GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                           GIT_CONFIG_SYSTEM=os.devnull)
        patcher = mock.patch.dict(os.environ, environment, clear=True)
        patcher.start(); self.addCleanup(patcher.stop)
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        patcher = mock.patch.object(WRITING, 'ROOT', self.root)
        patcher.start(); self.addCleanup(patcher.stop)
        self.git('init', '-q', '-b', 'main', '--template=')
        self.git('config', 'user.email', 'test@example.org')
        self.git('config', 'user.name', 'Test')
        self.git('config', 'commit.gpgsign', 'false')
        self.git('config', 'core.hooksPath', os.devnull)
        self.git('commit', '-q', '--allow-empty', '-m', 'base')
        self.git('checkout', '-q', '-b', 'topic')

    def git(self, *args: str) -> None:
        subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True)

    def test_git_settings_and_quoted_paths_do_not_hide_changes(self) -> None:
        names = ['page.md', 'space name.md', 'café.md', 'quote"name.md', 'back\\slash.md',
                 'line\nbreak.md', ':(glob)nothing.md', ':(literal)foo.md', 'a[1].md', 'a*.md']
        for name in names:
            (self.root / name).write_text('Good line.\nWe utilize the second line.\n')
        self.git('add', '.')
        for option in ['diff.noprefix', 'diff.mnemonicPrefix', 'core.quotePath']:
            for value in ['true', 'false']:
                with self.subTest(option=option, value=value):
                    self.git('config', option, value)
                    found = WRITING.check_blocks(WRITING.changed_blocks('main'))
                    self.assertEqual({f.path for f in found if f.rule == 'W1'}, set(names))
                    self.assertEqual({f.line for f in found if f.rule == 'W1'}, {2})

    def test_renames_check_only_edited_prose(self) -> None:
        old, new = 'old café.md', 'new name.md'
        text = 'We utilize unchanged prose.\n\nA clean line.\n'
        (self.root/old).write_text(text)
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'main', 'HEAD')
        self.git('mv', old, new)
        (self.root/new).write_text(text + '\nWe utilize changed prose.\n')
        self.git('add', '.')
        found = WRITING.check_blocks(WRITING.changed_blocks('main'))
        self.assertEqual([(f.path, f.line) for f in found if f.rule == 'W1'], [(new, 5)])

    def test_interhunk_context_does_not_add_unchanged_paragraphs(self) -> None:
        path = self.root / 'page.md'
        path.write_text('First paragraph.\n\nWe utilize unchanged prose.\n\nLast paragraph.\n')
        self.git('add', '.')
        self.git('commit', '-q', '-m', 'base prose')
        self.git('branch', '-f', 'main', 'HEAD')
        path.write_text('Changed first paragraph.\n\nWe utilize unchanged prose.\n\nChanged last paragraph.\n')
        self.git('config', 'diff.interHunkContext', '100')
        found = WRITING.check_blocks(WRITING.changed_blocks('main'))
        self.assertFalse([item for item in found if item.rule == 'W1'])

    def test_directory_and_loop_symlinks_are_advisory(self) -> None:
        (self.root / 'directory').mkdir()
        (self.root / 'directory.md').symlink_to('directory', target_is_directory=True)
        (self.root / 'loop.md').symlink_to('loop.md')
        self.git('add', '.')
        diagnostics = []
        self.assertEqual(WRITING.changed_blocks('main', diagnostics), [])
        self.assertEqual({item.path for item in diagnostics}, {'directory.md', 'loop.md'})
        self.assertEqual({item.rule for item in diagnostics}, {'Input'})
        with mock.patch('sys.stdout', io.StringIO()):
            self.assertEqual(WRITING.main(['check-writing.py', '--base', 'main']), 0)

    def test_symlink_diff_lines_do_not_describe_target_prose(self) -> None:
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / 'target.md'
            target.write_text('First line.\n\nWe utilize later prose.\n')
            (self.root / 'link.md').symlink_to(target)
            self.git('add', '.')
            diagnostics = []
            self.assertEqual(WRITING.changed_blocks('main', diagnostics), [])
            self.assertEqual([(item.path, item.rule) for item in diagnostics], [('link.md', 'Input')])
            self.assertNotIn('utilize', diagnostics[0].excerpt)

    def test_non_utf8_and_dangling_symlinks_are_advisory(self) -> None:
        (self.root / 'invalid.md').write_bytes(b'Caf\xe9; text.\n')
        (self.root / 'dangling.md').symlink_to('missing-target')
        (self.root / 'good.md').write_text('We utilize prose.\n')
        self.git('add', '.')
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', '--base', 'main']), 0)
        self.assertIn('not UTF-8', output.getvalue())
        self.assertIn('symlink', output.getvalue())
        self.assertIn('W1', output.getvalue())
        self.assertNotIn('No writing suggestions', output.getvalue())
        with mock.patch('sys.stdout', io.StringIO()) as output:
            self.assertEqual(WRITING.main(['check-writing.py', str(self.root/'invalid.md')]), 0)
        self.assertIn('not UTF-8', output.getvalue())

    def test_invalid_byte_stdin_has_an_input_diagnostic(self) -> None:
        environment = dict(os.environ, PYTHONIOENCODING='utf-8:surrogateescape')
        result = subprocess.run([sys.executable, WRITING.__file__, '--stdin', 'body'],
                                input=b'\xff\n', capture_output=True, env=environment)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b'not UTF-8', result.stdout)
        self.assertNotIn(b'No writing suggestions', result.stdout)

    def test_missing_base_and_broken_configuration_are_errors(self) -> None:
        with mock.patch('sys.stderr', io.StringIO()) as error:
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check-writing.py', '--base', 'missing-base'])
        self.assertEqual(result.exception.code, 2)
        self.assertIn('git failed', error.getvalue())
        with mock.patch('sys.stderr', io.StringIO()), mock.patch('sys.stdin', io.StringIO('')):
            with self.assertRaises(SystemExit) as result:
                WRITING.main(['check-writing.py', '--stdin', 'body', '--vocabulary',
                              str(self.root/'missing-vocabulary')])
        self.assertEqual(result.exception.code, 2)


class RecoveryRegressionTests(unittest.TestCase):
    def test_indented_lean_prose_is_checked_but_markdown_code_is_not(self) -> None:
        examples = [('/-!\n    We utilize indented prose.\n-/', 2),
                    ('/-- First line.\n\n        We utilize the second paragraph.\n-/', 3)]
        for text, line in examples:
            with self.subTest(text=text):
                found = WRITING.check_blocks(WRITING.file_blocks('Module.lean', text))
                self.assertEqual([item.line for item in found if item.rule == 'W1'], [line])
        self.assertNotIn('W1', findings('    Utilize exempt code.', 'page.md'))
        self.assertNotIn('W1', findings('/-!\n```lean\nutilize exempt code\n```\n-/', 'Module.lean'))

    def test_github_summary_contains_all_findings_as_escaped_text(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            summary = Path(directory) / 'summary.md'
            items = [WRITING.Finding('<tag>.md', index, 'W1', 'Review <text>.', 'utilize')
                     for index in range(1, 13)]
            with mock.patch.dict(os.environ, GITHUB_STEP_SUMMARY=str(summary)):
                with mock.patch('sys.stdout', io.StringIO()):
                    WRITING.report(items, True, True)
            text = summary.read_text()
            self.assertIn('12 writing suggestion(s)', text)
            self.assertIn('&lt;tag&gt;.md:12:', text)
            self.assertNotIn('<tag>', text)


if __name__ == "__main__":
    unittest.main()

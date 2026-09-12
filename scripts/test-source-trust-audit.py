#!/usr/bin/env python3
"""Focused tests for source-trust-audit's distinct blind-spot mutations."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("source-trust-audit.py")
SPEC = importlib.util.spec_from_file_location("source_trust_audit", SCRIPT)
assert SPEC and SPEC.loader
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


class SourceTrustAuditTests(unittest.TestCase):
    def test_production_and_acceptance_sources_are_inventoried(self) -> None:
        previous = Path.cwd()
        with tempfile.TemporaryDirectory() as directory:
            try:
                os.chdir(directory)
                subprocess.run(["git", "init", "-q"], check=True)
                for path in ["ArkLib/Production.lean", "ArkLibTest/Acceptance.lean",
                             "scripts/DeliberatelyInvalid.lean"]:
                    source = Path(path)
                    source.parent.mkdir(parents=True, exist_ok=True)
                    source.write_text("example : True := by sorry\n", encoding="utf-8")
                subprocess.run(["git", "add", "."], check=True)
                tree = subprocess.check_output(["git", "write-tree"], text=True).strip()
                expected = {"ArkLib/Production.lean", "ArkLibTest/Acceptance.lean"}
                for ref in [None, tree]:
                    self.assertEqual({path for path, _ in AUDIT.tracked_sources(ref)}, expected)
                    self.assertEqual(AUDIT.counts(AUDIT.scan_tree(ref))["admission"], 2)
            finally:
                os.chdir(previous)

    def tokens(self, source: str) -> list[tuple[str, str]]:
        return [(item.kind, item.token) for item in AUDIT.scan_source("Fixture.lean", source)]

    def test_source_only_admissions_are_visible(self) -> None:
        source = """
example : True := by sorry
structure Defaults where
  value : Nat := by sorry
def withAutoparam (n : Nat := by admit) := n
"""
        tokens = self.tokens(source)
        self.assertEqual(tokens.count(("example", "example")), 1)
        self.assertEqual(tokens.count(("admission", "sorry")), 2)
        self.assertEqual(tokens.count(("admission", "admit")), 1)

    def test_comments_strings_and_quoted_identifiers_do_not_create_noise(self) -> None:
        source = '''
-- sorry native_decide example axiom
/- outer sorry /- nested admit -/ Lean.trustCompiler -/
def message := "sorry native_decide"
def rawMessage := r##"quoted " sorry native_decide example axiom"##
def «sorry» := 1
def quoted := `sorry
def quotedNative := `native_decide
'''
        self.assertEqual(self.tokens(source), [])

    def test_nonallowlistable_native_trust_spellings_are_visible(self) -> None:
        source = """
example : True := by native_decide
#check Lean.ofReduceBool
#check Lean.trustCompiler
"""
        native = [token for kind, token in self.tokens(source) if kind == "native_trust"]
        self.assertEqual(native, ["native_decide", "Lean.ofReduceBool", "Lean.trustCompiler"])

    def test_diff_is_stable_across_line_moves_and_counts_duplicates(self) -> None:
        old = AUDIT.scan_source("Fixture.lean", "example : True := by sorry\n")
        moved = AUDIT.scan_source("Fixture.lean", "\n\nexample : True := by sorry\n")
        doubled = AUDIT.scan_source(
            "Fixture.lean", "example : True := by sorry\nexample : True := by sorry\n"
        )
        self.assertEqual(AUDIT.multiset_difference(moved, old), [])
        added = AUDIT.multiset_difference(doubled, old)
        self.assertEqual([(item.kind, item.token) for item in added], [
            ("example", "example"),
            ("admission", "sorry"),
        ])


if __name__ == "__main__":
    unittest.main()

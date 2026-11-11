/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-! Allowed prose and literal fixtures for the commented-declaration check. -/

-- instance search is slow here
-- theorem names should describe the conclusion
-- definition examples follow below
-- lemmafoo : True := trivial
-- @[simp theorem incomplete : True
/- -- theorem blockComment : True := trivial -/
/- Outer block comment.
/- Nested block comment. -/
-- def nestedComment := 1
-/
/-- The documentation contains a line-comment example.
-- theorem documented : True := trivial
-/
def ordinaryString := "-- theorem stringContent : True := trivial"
def rawString := r###"-- def rawContent := 1"###
def multilineRawString := r#"
-- instance : Inhabited Nat := ⟨0⟩
"#
def «-- lemma quotedIdentifier : True» := 1
def interpolatedString := s!"{"-- theorem hidden : True"}"
def nestedInterpolatedString := s!"{s!"{"-- lemma nested : True"}"}"
def interpolatedRecord := s!"{({ val := "-- def nested := 1", property := trivial } :
  {s : String // True}).val}"
def interpolatedRawString := s!"{r#"-- theorem rawNested : True"#}"

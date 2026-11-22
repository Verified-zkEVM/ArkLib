/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-! Rejected line-comment fixtures for the commented-declaration check. -/

-- theorem commented : True := trivial
-- @[simp] private lemma attributed : True := trivial
-- noncomputable def value : Nat := 0
-- instance : Inhabited Nat := ⟨0⟩
-- example (n : Nat) : n = n := rfl
-- structure Continued
-- class Dictionary where
-- inductive Choice where
-- abbrev synonym := Nat
-- axiom assumption : True
-- opaque hidden : Nat
-- @[name [nested], label "]"] protected theorem nestedAttribute : True := trivial
-- unsafe partial nonrec scoped local def modified := 0
example : True := trivial -- lemma trailing : True := trivial
-- @[simp] public meta def moduleModified := 1
def interpolatedTrailing := s!"{"-- theorem literal : True"}" -- theorem trailing : True

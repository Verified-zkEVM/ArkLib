/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Interaction.Config
public import Mathlib.Algebra.CharP.Defs

/-!
# Checked scalar lookup parameters

A lookup configuration retains the existing weighted grouping for all query columns and declared
table pieces, and an explicit characteristic certificate. The executable constructor checks only
the supplied numeric query budget and the existing grouping constructor. It never searches for a
field characteristic. Empty query or table collections are permitted separately; zero total columns
are rejected by the existing weighted configuration.
-/

@[expose] public section

namespace Logup.Lookup

/-- Fixed grouping and a certified query-count budget below the explicit characteristic. -/
structure Config (B : Type) [CommRing B] (n M P ell : ℕ) where
  /-- Checked weighted grouping of all query columns and physical table pieces. -/
  weighted : Logup.Interaction.Config n (M + P) ell
  /-- Explicit numeric characteristic, supplied rather than discovered at runtime. -/
  characteristic : ℕ
  /-- The supplied natural number is the actual coefficient-ring characteristic. -/
  charP : CharP B characteristic
  /-- Every possible positive query count stays nonzero after casting. -/
  queryBudget : M * 2 ^ n < characteristic

/-- Check the numeric query budget and existing consecutive grouping once. -/
def Config.create? (B : Type) [CommRing B] (n M P ell p : ℕ) [CharP B p] :
    Option (Config B n M P ell) :=
  if hbudget : M * 2 ^ n < p then
    (Logup.Interaction.Config.create? n (M + P) ell).map fun weighted =>
      ⟨weighted, p, inferInstance, hbudget⟩
  else none

/-- The constructor accepts exactly a nonempty collection, valid grouping and query budget. -/
theorem Config.isSome_create? (B : Type) [CommRing B] (n M P ell p : ℕ) [CharP B p] :
    (Config.create? B n M P ell p).isSome ↔
      0 < M + P ∧ 1 ≤ ell ∧ ell ≤ M + P ∧ M * 2 ^ n < p := by
  unfold Config.create?
  split
  · simpa only [Option.isSome_map, Logup.Interaction.Config.isSome_create?, and_true] using
      (show (0 < M + P ∧ 1 ≤ ell ∧ ell ≤ M + P) ↔
        0 < M + P ∧ 1 ≤ ell ∧ ell ≤ M + P ∧ M * 2 ^ n < p by omega)
  · simp_all

end Logup.Lookup

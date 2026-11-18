/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Separation
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for the Reed–Muller combiner lower bound -/

open ReedSolomon

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private noncomputable instance : Fintype (GaloisField 5 2) := Fintype.ofFinite _

private theorem field_card : Fintype.card (GaloisField 5 2) = 25 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 5 2 (by norm_num)]
  norm_num

-- On the grid `F₅²` inside `F₂₅`, with `d = 1`, `A = n = 25` and loss `n / q₀ = 5`,
-- the error is at least `1 / q² = 1 / 625`.
open Classical in
example : (1 : ENNReal) / 625 ≤ reedMullerMcaError (ZMod 5) (GaloisField 5 2) 2 1 25 5 := by
  have h := le_reedMullerMcaError_of_add_two_le (K₀ := ZMod 5) (F := GaloisField 5 2)
    (k := 2) (d := 1) (A := 25) (by norm_num) (by simp [ZMod.card]) (by simp [ZMod.card])
  rw [field_card, ZMod.card] at h
  norm_num at h
  rwa [one_div]

-- With `K₀ = F = F₅`, `k = 2`, `d = 3 = q₀ - 2`, the bound is `1 / 25`.
example : (1 : ENNReal) / 25 ≤ reedMullerMcaError (ZMod 5) (ZMod 5) 2 3 10 5 := by
  have h := le_reedMullerMcaError_of_add_two_le (K₀ := ZMod 5) (F := ZMod 5)
    (k := 2) (d := 3) (A := 10) (by norm_num) (by simp [ZMod.card]) (by simp [ZMod.card])
  rw [ZMod.card] at h
  norm_num at h
  rwa [one_div]

/-- info: 'ReedSolomon.le_reedMullerMcaError_of_add_two_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_reedMullerMcaError_of_add_two_le

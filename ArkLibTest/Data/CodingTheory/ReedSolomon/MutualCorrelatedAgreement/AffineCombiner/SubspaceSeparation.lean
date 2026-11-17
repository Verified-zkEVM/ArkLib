/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.SubspaceSeparation
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance case for the scalar lower bound on additive domains -/

open ReedSolomon

private noncomputable instance : Fintype (GaloisField 2 4) := Fintype.ofFinite _

open Classical in
/-- On the whole field `F₁₆`, the scalar error at `d = 4`, `A = 9`, `s = 2` is at least `1 / 2`. -/
example : (1 : ENNReal) / 2 ≤
    scalarMcaError (Function.Embedding.refl (GaloisField 2 4)) 4 9 2 := by
  have hq : Fintype.card (GaloisField 2 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 4 (by norm_num)]
    norm_num
  have h := le_scalarMcaError_of_addSubgroup (⊤ : AddSubgroup (GaloisField 2 4))
    (Function.Embedding.refl _) (fun x ↦ by simp) (by rw [hq])
    (A := 9) (s := 2) (by rw [hq]) (by rw [hq]; norm_num)
  rw [hq] at h
  norm_num [ENNReal.ofReal_div_of_pos] at h
  simpa only [one_div] using h

#print axioms ReedSolomon.le_scalarMcaError_of_addSubgroup

private noncomputable instance : Fintype (GaloisField 2 5) := Fintype.ofFinite _

-- A subgroup with 16 points in F32 exercises a domain smaller than the field.
open Classical in
example (V : AddSubgroup (GaloisField 2 5)) (hV : Fintype.card V = 16) :
    (1 : ENNReal) / 4 ≤ scalarMcaError (Function.Embedding.subtype (· ∈ V)) 4 9 2 := by
  have hq : Fintype.card (GaloisField 2 5) = 32 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 5 (by norm_num)]
    norm_num
  have h := le_scalarMcaError_of_addSubgroup V (Function.Embedding.subtype (· ∈ V))
    (fun x ↦ by simp) (by rw [hV]) (A := 9) (s := 2) (by rw [hV]) (by rw [hV]; norm_num)
  rw [hV, hq] at h
  norm_num [ENNReal.ofReal_div_of_pos] at h
  simpa only [one_div] using h

-- The proper-subgroup premise above is inhabited.
example : Nonempty {V : AddSubgroup (GaloisField 2 5) // Nat.card V = 16} := by
  have hq : Fintype.card (GaloisField 2 5) = 2 ^ 5 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 5 (by norm_num)]
  have h := FiniteField.two_pow_le_card_addSubgroup (F := GaloisField 2 5) hq
    (v := 4) (by norm_num)
  exact (Nat.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) h)).1

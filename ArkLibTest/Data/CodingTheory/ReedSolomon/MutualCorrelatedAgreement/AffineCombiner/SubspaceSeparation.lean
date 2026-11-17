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
    (Function.Embedding.refl _) (fun x ↦ by simp) (by rw [hq]) ⟨4, by rw [hq]; norm_num⟩
    (A := 9) (s := 2) (by rw [hq]) (by rw [hq]; norm_num)
  rw [hq] at h
  norm_num [ENNReal.ofReal_div_of_pos] at h
  simpa only [one_div] using h

#print axioms ReedSolomon.le_scalarMcaError_of_addSubgroup

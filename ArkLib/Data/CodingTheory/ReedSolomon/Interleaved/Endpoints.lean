/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreementArbitrary
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ConstantCode
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullDimension

/-!
# Interleaved constant-code and full-code endpoints

The arbitrary-field scalar projection argument preserves the sharp constant-code collision count.
The full-code endpoint is direct, over arbitrary fields, including zero block length and width.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

noncomputable section

set_option autoImplicit false

open Classical in
/-- Arbitrary-field interleaving preserves the scalar constant-code exceptional count without
a width factor, including the separate agreement-one fallback. -/
theorem uniformExactInterleavedPowerAgreement_constantCode
    {F : Type} [Field F] {n ell width A : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → Fin width → F)
    (hwidth : 0 < width) (hA : 0 < A) :
    UniformExactInterleavedPowerAgreement domain values 1 A
      (if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1)) := by
  exact uniformExactInterleavedPowerAgreement_of_scalar_arbitrary domain
    (fun scalarValues ↦ uniformExactPowerAgreement_constantCode domain scalarValues A hA)
    hwidth hA values

open Classical in
/-- Full-code interleaving has no exceptional challenges over any field, even for empty
evaluation domains or empty row tuples. -/
theorem uniformExactInterleavedPowerAgreement_fullDimension
    {F : Type} [Field F] {n ell width : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → Fin width → F) :
    UniformExactInterleavedPowerAgreement domain values n n 0 := by
  classical
  refine ⟨∅, by simp, ?_⟩
  intro z _ Q hQ hagree
  have hfull : interleavedPolynomialAgreementSet domain
      (interleavedPowerBatchedWord values z) Q = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hupper := (interleavedPolynomialAgreementSet domain
      (interleavedPowerBatchedWord values z) Q).card_le_univ
    exact Nat.le_antisymm hupper (by simpa using hagree)
  have hrow (j : Fin width) :
      HasExactPowerAgreement domain (fun t i ↦ values t i j) (RingHom.id F) n z (Q j) := by
    obtain ⟨_, _, hgood⟩ := exists_exactPower_fullDimension n ell domain
      (fun t i ↦ values t i j)
    apply hgood z (Q j) (hQ j)
    have hset : polynomialAgreementSet domain
        (powerBatchedWord (fun t i ↦ values t i j) z) (Q j) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      have hi : i ∈ interleavedPolynomialAgreementSet domain
          (interleavedPowerBatchedWord values z) Q := by simp [hfull]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2 j⟩
    simp [hset]
  let P := fun t j ↦ (Classical.choose (hrow j)) t
  refine ⟨P, fun t j ↦ (Classical.choose_spec (hrow j)).1 t, ?_, ?_⟩
  · intro j
    simpa only [P, Polynomial.map_id, RingHom.id_apply] using
      (Classical.choose_spec (hrow j)).2.1
  · rw [hfull]
    symm
    apply Finset.eq_univ_of_forall
    intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    intro t j
    have hi : i ∈ interleavedPolynomialAgreementSet domain
        (interleavedPowerBatchedWord values z) Q := by simp [hfull]
    have hrowMem : i ∈ polynomialAgreementSet
        (mappedDomain domain (RingHom.id F))
        (powerBatchedWord (fun t i ↦ (RingHom.id F) (values t i j)) z) (Q j) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2 j⟩
    rw [(Classical.choose_spec (hrow j)).2.2] at hrowMem
    exact (Finset.mem_filter.mp hrowMem).2 t

end

end ReedSolomon

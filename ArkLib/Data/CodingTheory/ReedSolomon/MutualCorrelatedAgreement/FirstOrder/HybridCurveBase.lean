/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveRecovery
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullDimension

/-!
# Base-field optimized first-order curve recovery

The algebraic closure is internal. The full-code branch is dispatched before imposing the
characteristic guard and has no exceptional challenges.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

open Classical in
/-- Arbitrary-field form of optimized first-order curve recovery. The exceptional set lies
in the original field; so do every recovered constituent and the candidate polynomial. -/
theorem exists_exceptional_firstOrder_hybridCurve_base_optimized
    {F : Type*} [Field F] {n D A h mu M ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 1)
    (hQ : Q ≠ 0) (hweight : jetWeight Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hheight : ChallengeHeightLE Q h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDn : D + 2 ≤ n)
    (hDA : D < A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D (jetDegree Q (1 : Fin 2)) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ hybridCurveOptimized n D ell A h mu M ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  let E := AlgebraicClosure F
  let iota := algebraMap F E
  let phi := Polynomial.mapRingHom iota
  let QE := MvPolynomial.map phi Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective phi (Polynomial.map_injective iota iota.injective)
    simpa only [map_zero] using hz
  have hweightE : jetWeight QE ≤ mu := by
    apply le_trans _ hweight
    unfold jetWeight
    rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
      MvPolynomial.mem_restrictWeightedDegree]
    intro u hu
    exact MvPolynomial.le_weightedTotalDegree _ (MvPolynomial.support_map_subset phi Q hu)
  have hdegreeE : jetDegree QE (1 : Fin 2) ≤ jetDegree Q (1 : Fin 2) := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    exact MvPolynomial.monomial_le_degreeOf _ (MvPolynomial.support_map_subset phi Q hu)
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_firstOrder_hybridCurve_optimized domain values iota QE
      hQE hweightE (hdegreeE.trans hdegree) (hheight.map_coefficients iota)
      hell hD hDn hDA hAn
      (hchar.imp_right (fun hc ↦ (max_le_max_left D hdegreeE).trans_lt hc))
  let baseExceptional := exceptional.preimage iota iota.injective.injOn
  refine ⟨baseExceptional, ?_, ?_⟩
  · apply (show (baseExceptional.card : ℝ) ≤ exceptional.card by
      exact_mod_cast Finset.card_le_card_of_injOn iota
        (fun _ hz ↦ Finset.mem_preimage.mp hz) iota.injective.injOn).trans hcard
  · intro z hz P hP hagree hroot
    apply HasExactPowerAgreement.descend domain values iota (D + 1) z P
    apply hgood (iota z)
    · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
    · exact Polynomial.degree_map_le.trans_lt hP
    · have hword :
          powerBatchedWord (fun t i ↦ iota (values t i)) (iota z) =
            fun i ↦ iota (powerBatchedWord values z i) := by
        funext i
        simp only [powerBatchedWord, map_sum, map_mul, map_pow]
      rw [hword, polynomialAgreementSet_map]
      exact hagree
    · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]

open Classical in
/-- The full-code endpoint is characteristic-free and has bound zero. Away from it, the
same statement exposes the optimized actual-degree bound with independent retention minima. -/
theorem exists_exceptional_firstOrder_hybridCurve_base_including_fullDimension
    {F : Type*} [Field F] {n D A h mu M ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 1)
    (hQ : Q ≠ 0) (hweight : jetWeight Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M)
    (hheight : ChallengeHeightLE Q h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hchar : D + 1 = n ∨ ringChar F = 0 ∨
      max D (jetDegree Q (1 : Fin 2)) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        (if D + 1 = n then 0 else hybridCurveOptimized n D ell A h mu M) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  by_cases hfull : D + 1 = n
  · have hA : A = n := by omega
    obtain ⟨tuple, htuple, hgood⟩ := exists_exactPower_fullDimension n ell domain values
    refine ⟨∅, by simp [hfull], ?_⟩
    intro z _ P hP hagree _
    rw [hfull]
    exact hgood z P (by simpa only [← Nat.cast_add_one, hfull] using hP)
      (by simpa only [hA] using hagree)
  · simpa only [if_neg hfull] using
      exists_exceptional_firstOrder_hybridCurve_base_optimized domain values Q
        hQ hweight hdegree hheight hell hD (by omega) hDA hAn (hchar.resolve_left hfull)

end

end ReedSolomon

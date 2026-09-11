/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Equation
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-! # Base-field polynomial-curve ordinary equation transfer -/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

open Classical in
/-- The polynomial-curve ordinary equation transfer over an arbitrary field. Algebraic closure
and Frobenius choices are internal, and full agreement sets descend to the base field. -/
theorem exists_exceptional_ordinaryPowerEquation_base
    {F : Type*} [Field F] {n ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hℓ : 0 < ℓ) (hmu : 1 ≤ mu)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ordinaryPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ mu h ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  let E := AlgebraicClosure F
  let ι := algebraMap F E
  let QE := MvPolynomial.map (Polynomial.mapRingHom ι) Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective (Polynomial.mapRingHom ι)
      (Polynomial.map_injective ι ι.injective)
    simpa only [map_zero] using hz
  have hQheight : ChallengeHeightLE QE h := hheight.map_coefficients ι
  have hQdegree : QE.degreeOf (some 0) ≤ mu := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    exact (MvPolynomial.monomial_le_degreeOf (some 0)
      (MvPolynomial.support_map_subset _ _ hu)).trans hdegree
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_ordinaryPowerEquation
    domain values ι QE D h mu A hQE hD hℓ hmu hDA hAn hQheight hQdegree
  let baseEx := ex.preimage ι ι.injective.injOn
  refine ⟨baseEx, ?_, ?_⟩
  · apply (show (baseEx.card : ℚ) ≤ ex.card by
      exact_mod_cast Finset.card_le_card_of_injOn ι
        (fun _ hz ↦ Finset.mem_preimage.mp hz) ι.injective.injOn).trans
    exact hexCard
  · intro z hz P hP hroot hagree
    apply HasExactPowerAgreement.descend domain values ι (D + 1) z P
    apply hex (ι z)
    · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
    · exact Polynomial.degree_map_le.trans_lt hP
    · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]
    · have hword :
          powerBatchedWord (fun t i ↦ ι (values t i)) (ι z) =
            fun i ↦ ι (powerBatchedWord values z i) := by
          funext i
          simp only [powerBatchedWord, map_sum, map_mul, map_pow]
      rw [hword, polynomialAgreementSet_map]
      exact hagree

end ReedSolomon

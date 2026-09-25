/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Exceptional challenges for ordinary equations over an arbitrary field

Every nonzero ordinary differential equation over an arbitrary field has one bounded exceptional
set of challenges outside which every accepted close root has an exact correlated-pair witness.
The algebraic closure is an internal construction: both polynomial identities and full agreement
sets descend along the injective scalar map, with no characteristic hypothesis.

## Main statements

* `ReedSolomon.exists_exceptional_ordinaryEquation_base` gives the exceptional-set bound for
  nonzero ordinary equations with coefficients and roots over the base field.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

/-- Every nonzero ordinary equation over an arbitrary field has one finite exceptional set for
all accepted base-field roots, with the stated root-degree and challenge-height budgets. -/
theorem exists_exceptional_ordinaryEquation_base
    {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hmu : 1 ≤ mu) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : CoeffNatDegreeLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ordinaryFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
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
  have hQheight : CoeffNatDegreeLE QE h := hheight.map_coefficients ι
  have hQdegree : QE.degreeOf (some 0) ≤ mu := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    exact (MvPolynomial.monomial_le_degreeOf (some 0)
      (MvPolynomial.support_map_subset _ _ hu)).trans hdegree
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_ordinaryEquation
    domain f g ι QE D h mu A hQE hD hmu hDA hAn hQheight hQdegree
  obtain ⟨baseEx, hbaseCard, hbase⟩ := exists_exceptional_equation_correlatedAgreement_descend
    domain f g ι Q (D + 1) A ex (fun z hz P hP hagree hroot => by
      convert hex z hz P hP hroot hagree)
  refine ⟨baseEx, le_trans (by exact_mod_cast hbaseCard) hexCard, ?_⟩
  intro z hz P hP hroot hagree
  exact hbase z hz P hP hagree hroot

end ReedSolomon

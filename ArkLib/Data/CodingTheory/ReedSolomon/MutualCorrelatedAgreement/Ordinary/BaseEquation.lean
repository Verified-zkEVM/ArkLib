/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine

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
  obtain ⟨exceptional, hcard, hgood⟩ := exists_baseExceptional_ordinaryPowerEquation
    (ℓ := 1) domain ![f, g] Q D h mu (D + 1) A hQ hD (by omega) (by omega) hDA hheight hdegree
  rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos n D 1 mu h A (D + 1) hmu,
    ordinaryUnifiedPowerFactorAt_succ_eq n D 1 mu h A hDA hAn] at hcard
  have hcharge : ordinaryCurveFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D 1 mu h =
      ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h := by
    simp [ordinaryCurveFactorRaw, ordinaryFactorRaw]
  have hword (z : F) : powerBatchedWord ![f, g] z = fun i ↦ f i + z * g i := by
    exact powerBatchedWord_pair_eq f g (RingHom.id F) z
  refine ⟨exceptional, hcard.trans ((ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw
    n 1 mu h (by positivity) hD).trans_eq hcharge), ?_⟩
  intro z hz P hP hroot hagree
  exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
    (hgood z hz P hP hroot (by rwa [hword]))

end ReedSolomon

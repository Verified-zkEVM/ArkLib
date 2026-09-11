/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Irreducible
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Assembly
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.ContentExceptions
/-! # Ordinary equations along a polynomial challenge curve -/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

open Classical in
/-- Every nonzero ordinary equation has one finite exceptional set for every accepted
polynomial-curve root, with loss linear in the curve degree in arbitrary characteristic. -/
theorem exists_exceptional_ordinaryPowerEquation
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hℓ : 0 < ℓ) (hmu : 1 ≤ mu)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ mu h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
          (powerBatchedWord (fun t i ↦ ι (values t i)) z) P).card →
        HasExactPowerAgreement domain values ι (D + 1) z P := by
  classical
  let flat := ordinaryFlatten E Q
  let height (R : MvPolynomial (Option (Fin 2)) E) := R.degreeOf (some 1)
  let ev (z : E) (P : E[X]) :=
    ((differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (σ := JetVariable 0) (Polynomial.aeval z).toRingHom)).comp
        (ordinaryUnflatten E).toRingHom
  let Good (z : E) (P : E[X]) := P.degree < D + 1 →
    A ≤ (polynomialAgreementSet (mappedDomain domain ι)
      (powerBatchedWord (fun t i ↦ ι (values t i)) z) P).card →
    HasExactPowerAgreement domain values ι (D + 1) z P
  have hflat : flat ≠ 0 := (ordinaryFlatten E).map_ne_zero_iff.mpr hQ
  have hdegUnflat (R : MvPolynomial (Option (Fin 2)) E) :
      (ordinaryUnflatten E R).degreeOf (some 0) = R.degreeOf none := by
    rw [← degreeOf_none_ordinaryFlatten]
    simp [ordinaryUnflatten]
  have hev (z : E) (P : E[X]) (R : MvPolynomial (Option (Fin 2)) E) :
      ev z P R = differentialSpecialization
        (challengeSpecialization (ordinaryUnflatten E R) z) P := rfl
  have hc : ∃ ex : Finset E, ex.card ≤ height (ordinaryContent flat) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryContent flat) ≠ 0 := by
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryContent
      (ordinaryUnflatten E (ordinaryContent flat))
      ((ordinaryUnflatten E).map_ne_zero_iff.mpr (ordinaryContent_ne_zero flat))
      (by rw [hdegUnflat, degreeOf_ordinaryContent_none])
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
    exact ⟨ex, hcard, hgood⟩
  have hf : ∀ a ∈ ordinaryRootFactorClasses flat, ∃ ex : Finset E,
      (ex.card : ℚ) ≤ ordinaryPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ℓ
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryFactorRepresentative a) = 0 → Good z P := by
    intro a ha
    obtain ⟨hirr, hpos⟩ := ordinaryRootFactorClasses_spec flat ha
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryPowerEquation
      domain values ι (ordinaryUnflatten E (ordinaryFactorRepresentative a)) D
      (height (ordinaryFactorRepresentative a)) A hD hℓ hDA hAn
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
      (hirr.map (ordinaryUnflatten E)) (by simpa only [hdegUnflat] using hpos)
    refine ⟨ex, ?_, ?_⟩
    · simpa only [hdegUnflat] using hcard
    · intro z hz P hroot hP hagree
      exact hgood z hz P hP hroot hagree
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryPowerFactorAssembly
    flat hflat ev Good height (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ))
    n D ℓ mu h (by positivity) hℓ hmu
    (by simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree)
    ((ordinary_degree_sum_le flat hflat (some 1)).trans
      (degreeOf_challenge_ordinaryFlatten_le Q hheight)) hc hf
  refine ⟨ex, hcard, ?_⟩
  intro z hz P hP hroot hagree
  apply hgood z hz P _ hP hagree
  rw [hev]
  simpa only [flat, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using hroot

end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorAssembly
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.IrreducibleEquation
public import ArkLib.Data.Polynomial.Differential.ContentExceptions

/-!
# Exceptional challenges for ordinary equations

Every nonzero ordinary differential equation has one bounded exceptional set controlling all
accepted roots with the stated root-degree and challenge-height budgets in every characteristic.

## Main statements

* `ReedSolomon.exists_exceptional_ordinaryEquation` gives the bound for arbitrary nonzero
  ordinary equations.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

open Classical in
/-- Every nonzero ordinary equation has one finite exceptional set for all accepted roots,
with the stated root-degree and challenge-height budgets in arbitrary characteristic. -/
theorem exists_exceptional_ordinaryEquation
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hmu : 1 ≤ mu) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : CoeffNatDegreeLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (fun i ↦ ι (f i) + z * ι (g i)) P).card →
        HasExactCorrelatedPair domain f g ι (D + 1) z P := by
  classical
  let flat := ordinaryFlatten E Q
  let height (R : MvPolynomial (Option (Fin 2)) E) := R.degreeOf (some 1)
  let ev (z : E) (P : E[X]) :=
    ((differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (σ := JetVariable 0) (Polynomial.aeval z).toRingHom)).comp
        (ordinaryUnflatten E).toRingHom
  let Good (z : E) (P : E[X]) := P.degree < D + 1 →
    A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
      (fun i ↦ ι (f i) + z * ι (g i)) P).card →
    HasExactCorrelatedPair domain f g ι (D + 1) z P
  have hflat : flat ≠ 0 := (ordinaryFlatten E).map_ne_zero_iff.mpr hQ
  have hflatHeight : flat.degreeOf (some 1) ≤ h :=
    degreeOf_challenge_ordinaryFlatten_le Q hheight
  have hdegUnflat (R : MvPolynomial (Option (Fin 2)) E) :
      (ordinaryUnflatten E R).degreeOf (some 0) = R.degreeOf none := by
    rw [← degreeOf_none_ordinaryFlatten]
    simp [ordinaryUnflatten]
  have hev (z : E) (P : E[X]) (R : MvPolynomial (Option (Fin 2)) E) :
      ev z P R = differentialSpecialization
        (challengeSpecialization (ordinaryUnflatten E R) z) P := rfl
  have hcontentHeight :
      (radicalContent none flat).degreeOf (some 1) ≤ h := by
    calc
      _ ≤ (radicalContent none flat).degreeOf (some 1) +
          ∑ c ∈ positiveDegreeFactorClasses none flat, c.rep.degreeOf (some 1) :=
        Nat.le_add_right _ _
      _ ≤ flat.degreeOf (some 1) :=
        add_sum_degreeOf_positiveDegreeFactorClasses_le none (some 1) flat
      _ ≤ h := hflatHeight
  have hc : ∃ ex : Finset E, ex.card ≤ height (radicalContent none flat) ∧
      ∀ z ∉ ex, ∀ P, ev z P (radicalContent none flat) ≠ 0 := by
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_jet_independent_content
      (ordinaryUnflatten E (radicalContent none flat))
      ((ordinaryUnflatten E).map_ne_zero_iff.mpr (radicalContent_ne_zero none flat))
      (by rw [hdegUnflat, degreeOf_radicalContent])
      (coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
    exact ⟨ex, hcard, hgood⟩
  have hf : ∀ c ∈ positiveDegreeFactorClasses none flat, ∃ ex : Finset E,
      (ex.card : ℚ) ≤ ordinaryFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
        (c.rep.degreeOf none) (height c.rep) ∧
      ∀ z ∉ ex, ∀ P, ev z P c.rep = 0 → Good z P := by
    intro c hc
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryEquation
      domain f g ι (ordinaryUnflatten E c.rep) D (height c.rep) A hD hDA hAn
      (coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
      (irreducible_rep_of_mem_positiveDegreeFactorClasses hc |>.map (ordinaryUnflatten E))
      (by simpa only [hdegUnflat] using (mem_positiveDegreeFactorClasses.mp hc).2)
    refine ⟨ex, ?_, ?_⟩
    · simpa only [hdegUnflat] using hcard
    · intro z hz P hzero hP hagree
      exact hgood z hz P hP (by simpa only [hev] using hzero) hagree
  have hroot : flat.degreeOf none ≤ mu := by
    simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree
  have hbudgetHeight : height (radicalContent none flat) +
      ∑ c ∈ positiveDegreeFactorClasses none flat, height c.rep ≤ h := by
    simpa only [height] using (add_sum_degreeOf_positiveDegreeFactorClasses_le
      none (some 1) flat).trans hflatHeight
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryFactorAssembly
    (i := none) (Q := flat) hflat ev Good height
    (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h (by positivity) hmu hroot
    hbudgetHeight hc hf
  refine ⟨ex, hcard, ?_⟩
  intro z hz P hP hroot hagree
  exact hgood z hz P (by
    rw [hev]
    simpa only [flat, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using hroot) hP hagree

end ReedSolomon

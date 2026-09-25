/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleSeparableBound
public import ArkLib.Data.Polynomial.Differential.FrobeniusEquation
import ArkLib.Data.Polynomial.Differential.OrderZeroPresentation
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine

/-!
# Irreducible ordinary equations

An irreducible ordinary equation with positive root degree admits a finite exceptional set
controlling all sufficiently agreeing polynomial solutions in every characteristic.

## Main statements

* `ReedSolomon.exists_exceptional_irreducibleOrdinaryEquation` gives the ordinary factor bound
  without specifying a Frobenius exponent or a pulled equation.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

open Classical in
/-- Every irreducible ordinary equation of positive root degree has a bounded exceptional set in
all characteristics. Outside this set, each degree-`< D + 1` solution of the specialized equation
with at least `A` agreements is an exact correlated pair. -/
theorem exists_exceptional_irreducibleOrdinaryEquation
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h A : ℕ)
    (hD : 0 < D) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : CoeffNatDegreeLE Q h)
    (hirr : Irreducible Q) (hpos : 0 < Q.degreeOf (some 0)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D (Q.degreeOf (some 0)) h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (fun i ↦ ι (f i) + z * ι (g i)) P).card →
        HasExactCorrelatedPair domain f g ι (D + 1) z P := by
  classical
  let p := ringExpChar E
  obtain ⟨e, H, hHirr, hHder, hHdegree, _, hHheight, htransport⟩ :=
    exists_frobeniusEquation p hpos hirr hheight
  have hHpos : 0 < H.degreeOf (some 0) := by
    by_contra! hz
    have hz' := Nat.eq_zero_of_le_zero hz
    rw [hz', zero_mul] at hHdegree
    omega
  have hHjet : jetTotalDegree H ≤ H.degreeOf (some 0) := by
    rw [jetTotalDegree_eq_jetDegree_zero, jetDegree]
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusPowerFactorSolutions
    domain ![f, g] ι H p e D h (H.degreeOf (some 0)) A hD (by omega) hHpos hDA hAn
    hHheight hHjet hHirr hHder rfl
  have heq : p ^ e * H.degreeOf (some 0) = Q.degreeOf (some 0) := by
    simpa only [Nat.mul_comm] using hHdegree
  have hEval (x : E) : (Polynomial.aeval x).toRingHom = Polynomial.evalRingHom x := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  refine ⟨ex, ?_, ?_⟩
  · simpa [ordinaryCurveFactorRaw, ordinaryFactorRaw, heq] using hexCard
  · intro z hz P hdegree hroot hagree
    let w := (iterateFrobeniusEquiv E p e).symm z
    have hw : w ^ (p ^ e) = z :=
      (iterateFrobeniusEquiv E p e).apply_symm_apply z
    have hHroot : differentialSpecialization (challengeSpecialization H w)
        (expand E (p ^ e) P) = 0 := by
      rw [challengeSpecialization, hEval]
      apply htransport P w
      rw [hw]
      simpa only [challengeSpecialization, hEval] using hroot
    have hpowerAgreement : A ≤
        (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
          (powerBatchedWord (fun t i ↦ ι (![f, g] t i)) (w ^ (p ^ e))) P).card := by
      rw [powerBatchedWord_pair_eq]
      simpa only [hw] using hagree
    have hout := hex w (by simpa only [hw] using hz) P hdegree hHroot hpowerAgreement
    have hout' := exactCorrelatedPair_of_powerAgreement_one domain ![f, g] ι
      (w ^ (p ^ e)) P hout
    simpa [hw] using hout'

end ReedSolomon

end

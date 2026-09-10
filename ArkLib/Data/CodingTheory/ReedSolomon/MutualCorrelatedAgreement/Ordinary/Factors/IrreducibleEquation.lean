/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.Equation
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.FactorSolutions
/-!
# Irreducible ordinary equations in every characteristic

The Frobenius exponent, separable pulled equation, and coordinate roots are constructed
internally. Their finite exception bound is charged in the original root degree.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative
open MvPolynomial PolynomialDifferential

theorem ordinary_jetWeight_eq_degreeOf {R : Type*} [CommSemiring R]
    (Q : DifferentialPolynomial R 0) :
    Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) = Q.degreeOf (some 0) := by
  classical
  rw [← weightedTotalDegree_piSingle (some (0 : Fin 1))]
  congr 1
  funext i
  cases i with
  | none => simp
  | some j =>
    have hj : j = 0 := by omega
    subst j
    simp

end ReedSolomon.HiddenDerivative

namespace ReedSolomon
open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

open Classical in
/-- Every positive-root-degree irreducible ordinary equation has the ordinary exception bound
in all characteristics. The Frobenius exponent and pulled equation are chosen internally. -/
theorem exists_exceptional_irreducibleOrdinaryEquation
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h A : ℕ)
    (hD : 0 < D) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hirr : Irreducible Q) (hpos : 0 < Q.degreeOf (some 0)) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D (Q.degreeOf (some 0)) h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain ι)
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
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusFactorSolutions
    domain f g ι H p e D h (H.degreeOf (some 0)) A hD hHpos hDA hAn hHheight
    (by rw [ordinary_jetWeight_eq_degreeOf]) hHirr hHder rfl
  have heq : p ^ e * H.degreeOf (some 0) = Q.degreeOf (some 0) := by
    simpa only [Nat.mul_comm] using hHdegree
  refine ⟨ex, ?_, ?_⟩
  · simpa only [heq] using hexCard
  · intro z hz P hdegree hroot hagree
    let w := (iterateFrobeniusEquiv E p e).symm z
    have hw : w ^ (p ^ e) = z :=
      (iterateFrobeniusEquiv E p e).apply_symm_apply z
    have hEval (x : E) : (Polynomial.aeval x).toRingHom = Polynomial.evalRingHom x := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    have hHroot : differentialSpecialization (challengeSpecialization H w)
        (expand E (p ^ e) P) = 0 := by
      rw [challengeSpecialization, hEval]
      apply htransport P w
      rw [hw]
      simpa only [challengeSpecialization, hEval] using hroot
    have hout := hex w (by simpa only [hw] using hz) P hdegree hHroot
      (by simpa only [hw] using hagree)
    simpa only [hw] using hout

end ReedSolomon

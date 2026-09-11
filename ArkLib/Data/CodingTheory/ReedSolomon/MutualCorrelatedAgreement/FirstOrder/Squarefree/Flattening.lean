/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorBidegree
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorDerivativeDegree
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.SeparantChain

/-!
# Flattening the challenge coefficient of a first-order equation

The polynomial coefficient variable is retained as a literal multivariate coordinate before
factorization.  The equivalence is injective, preserves the first-derivative-variable cap, and
preserves arbitrary weighted source-degree caps.  In particular it keeps total jet degree
separate from challenge degree and from the independent coordinate.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicSeparantChain

noncomputable section

variable {F σ : Type*} [Field F]

/-- Lift a source-variable weight across challenge flattening, assigning weight zero to the
new challenge coordinate. -/
def liftedSourceWeight (w : σ → ℕ) : Option σ → ℕ
  | none => 0
  | some i => w i

private theorem weightedTotalDegree_finsetSum_le
    (w : σ → ℕ) {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (P : ι → MvPolynomial σ R) (d : ℕ)
    (hP : ∀ i ∈ s, (P i).weightedTotalDegree w ≤ d) :
    (∑ i ∈ s, P i).weightedTotalDegree w ≤ d := by
  unfold MvPolynomial.weightedTotalDegree
  exact AddMonoidAlgebra.supDegree_sum_le.trans (Finset.sup_le fun i hi ↦ hP i hi)

private theorem weightedTotalDegree_X_eq
    {R : Type*} [CommSemiring R] [Nontrivial R] (w : σ → ℕ) (i : σ) :
    (X i : MvPolynomial σ R).weightedTotalDegree w = w i := by
  classical
  rw [show (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 by rfl]
  rw [weightedTotalDegree_monomial _ _ _ one_ne_zero, Finsupp.weight_single]
  simp

private theorem flattenChallenge_C_liftedWeight_zero (w : σ → ℕ) (p : F[X]) :
    (flattenChallenge (C p : MvPolynomial σ F[X])).weightedTotalDegree
      (liftedSourceWeight w) = 0 := by
  classical
  rw [flattenChallenge_C]
  have he : Polynomial.aeval (X none : MvPolynomial (Option σ) F) p =
      ∑ n ∈ p.support, MvPolynomial.C (p.coeff n) * X none ^ n := by
    simpa [Polynomial.sum_def] using congrArg
      (Polynomial.aeval (X none : MvPolynomial (Option σ) F)) p.sum_monomial_eq.symm
  rw [he]
  apply Nat.eq_zero_of_le_zero
  apply weightedTotalDegree_finsetSum_le
  intro n _
  apply (weightedTotalDegree_mul_le _ _ _).trans
  simp only [weightedTotalDegree_C, zero_add]
  apply (weightedTotalDegree_pow_le _ _ _).trans
  rw [weightedTotalDegree_X_eq]
  simp [liftedSourceWeight]

/-- Flattening the coefficient challenge preserves every weighted source-degree cap. -/
theorem flattenChallenge_weightedTotalDegree_le
    (P : MvPolynomial σ F[X]) (w : σ → ℕ) :
    (flattenChallenge P).weightedTotalDegree (liftedSourceWeight w) ≤
      P.weightedTotalDegree w := by
  classical
  have he : flattenChallenge P =
      ∑ m ∈ P.support, flattenChallenge (C (coeff m P)) *
        ∏ i ∈ m.support, (X (some i) : MvPolynomial (Option σ) F) ^ m i := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
      flattenChallenge_X]
  rw [he]
  apply weightedTotalDegree_finsetSum_le
  intro m hm
  apply (weightedTotalDegree_mul_le _ _ _).trans
  rw [flattenChallenge_C_liftedWeight_zero, zero_add]
  apply (AddMonoidAlgebra.supDegree_prod_le (R := F)
    (A := Option σ →₀ ℕ) (B := ℕ) (D := Finsupp.weight (liftedSourceWeight w))
    (map_zero _) (fun a b ↦ map_add _ a b)).trans
  calc
    ∑ i ∈ m.support,
        ((X (some i) : MvPolynomial (Option σ) F) ^ m i).weightedTotalDegree
          (liftedSourceWeight w) ≤ ∑ i ∈ m.support, m i * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact (weightedTotalDegree_pow_le _ _ _).trans (by
        rw [weightedTotalDegree_X_eq]
        simp [liftedSourceWeight])
    _ = Finsupp.weight w m := by simp [Finsupp.weight_apply, Finsupp.sum]
    _ ≤ P.weightedTotalDegree w := le_weightedTotalDegree w hm

/-- A first-order equation with its coefficient challenge retained as coordinate `none`. -/
def flattenFirstOrderChallenge (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (Option (JetVariable 1)) F :=
  flattenChallenge Q

@[simp]
theorem flattenFirstOrderChallenge_ne_zero_iff (Q : DifferentialPolynomial F[X] 1) :
    flattenFirstOrderChallenge Q ≠ 0 ↔ Q ≠ 0 := by
  change flattenChallenge Q ≠ flattenChallenge 0 ↔ Q ≠ 0
  exact flattenChallenge.injective.ne_iff

/-- The `Y₁` cap survives coefficient flattening. -/
theorem flattenFirstOrderChallenge_yOneDegree_le (Q : DifferentialPolynomial F[X] 1) :
    degreeOf (some (some (1 : Fin 2))) (flattenFirstOrderChallenge Q) ≤
      degreeOf (some (1 : Fin 2)) Q :=
  flattenChallenge_degreeOf_le Q (some (1 : Fin 2))

/-- The challenge-height cap becomes the degree of the literal challenge coordinate. -/
theorem flattenFirstOrderChallenge_challengeDegree_le
    (Q : DifferentialPolynomial F[X] 1) {H : ℕ} (hQ : ChallengeHeightLE Q H) :
    degreeOf none (flattenFirstOrderChallenge Q) ≤ H := by
  rw [← weightedTotalDegree_piSingle]
  have h := flattenChallenge_challengeDegree_le hQ
  have hw : AffineHilbert.challengeWeight (σ := JetVariable 1) =
      Pi.single none 1 := by
    funext i
    cases i <;> simp [AffineHilbert.challengeWeight]
  change (flattenChallenge Q).weightedTotalDegree (Pi.single none 1) ≤ H
  rw [← hw]
  exact h

/-- Total jet degree survives flattening while both the challenge and independent coordinate
retain weight zero. -/
theorem flattenFirstOrderChallenge_jetWeight_le (Q : DifferentialPolynomial F[X] 1) :
    (flattenFirstOrderChallenge Q).weightedTotalDegree
        (liftedSourceWeight (fun v : JetVariable 1 ↦ v.elim 0 fun _ ↦ 1)) ≤
      jetWeight Q := by
  exact flattenChallenge_weightedTotalDegree_le Q _

end

end ReedSolomon.FirstOrder.Squarefree

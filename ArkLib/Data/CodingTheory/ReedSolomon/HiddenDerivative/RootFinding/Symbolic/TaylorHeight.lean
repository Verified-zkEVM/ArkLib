/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorNumerator


/-!
# Challenge heights under Taylor substitution

Taylor substitution at a constant center does not increase the degree of the symbolic
challenge in any coefficient. This separates challenge height from Taylor and jet degrees.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Polynomial
open scoped BigOperators

variable {F σ τ : Type*} [Field F]

/-- Every coefficient has challenge degree at most `h`. -/
def ChallengeHeightLE (P : MvPolynomial σ F[X]) (h : ℕ) : Prop :=
  ∀ m, (MvPolynomial.coeff m P).natDegree ≤ h

private theorem height_C {p : F[X]} {h : ℕ} (hp : p.natDegree ≤ h) :
    ChallengeHeightLE (MvPolynomial.C p : MvPolynomial σ F[X]) h := by
  classical
  intro m
  by_cases hm : m = 0
  · subst m; simpa using hp
  · simp [MvPolynomial.coeff_C, Ne.symm hm]

private theorem height_X (i : σ) :
    ChallengeHeightLE (MvPolynomial.X i : MvPolynomial σ F[X]) 0 := by
  classical
  intro m
  by_cases hm : m = Finsupp.single i 1
  · subst m; simp
  · simp [MvPolynomial.coeff_X, Ne.symm hm]

private theorem ChallengeHeightLE.add {P Q : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) (hQ : ChallengeHeightLE Q h) :
    ChallengeHeightLE (P + Q) h := by
  intro m
  rw [MvPolynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP m) (hQ m))

private theorem ChallengeHeightLE.mul {P Q : MvPolynomial σ F[X]} {a b : ℕ}
    (hP : ChallengeHeightLE P a) (hQ : ChallengeHeightLE Q b) :
    ChallengeHeightLE (P * Q) (a + b) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro pair _
  exact Polynomial.natDegree_mul_le_of_le (hP pair.1) (hQ pair.2)

private theorem ChallengeHeightLE.pow_zero {P : MvPolynomial σ F[X]}
    (hP : ChallengeHeightLE P 0) (n : ℕ) : ChallengeHeightLE (P ^ n) 0 := by
  induction n with
  | zero => simpa using height_C (σ := σ) (p := (1 : F[X])) (h := 0) (by simp)
  | succ n ih => simpa [pow_succ] using ih.mul hP

private theorem height_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ F[X]) {h : ℕ}
    (hP : ∀ i ∈ s, ChallengeHeightLE (P i) h) : ChallengeHeightLE (∑ i ∈ s, P i) h := by
  intro m
  rw [MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  exact fun i hi ↦ hP i hi m

private theorem height_prod_zero {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ F[X])
    (hP : ∀ i ∈ s, ChallengeHeightLE (P i) 0) : ChallengeHeightLE (∏ i ∈ s, P i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using height_C (σ := σ) (p := (1 : F[X])) (h := 0) (by simp)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    simpa using (hP i (Finset.mem_insert_self i s)).mul
      (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

/-- Substitution by challenge-independent polynomials preserves coefficient height. -/
theorem ChallengeHeightLE.aeval {P : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) (f : σ → MvPolynomial τ F[X])
    (hf : ∀ i, ChallengeHeightLE (f i) 0) : ChallengeHeightLE (aeval f P) h := by
  classical
  rw [P.as_sum, map_sum]
  apply height_sum
  intro m _
  rw [MvPolynomial.aeval_monomial]
  have hp : ChallengeHeightLE (m.prod fun i k ↦ f i ^ k) 0 := by
    apply height_prod_zero
    intro i _
    exact (hf i).pow_zero _
  simpa using (height_C (σ := τ) (hP m)).mul hp

/-- Formal differentiation cannot increase challenge height. -/
theorem ChallengeHeightLE.pderiv {P : MvPolynomial σ F[X]} {h : ℕ}
    (hP : ChallengeHeightLE P h) (i : σ) : ChallengeHeightLE (pderiv i P) h := by
  intro m
  rw [coeff_pderiv]
  simpa using Polynomial.natDegree_mul_le_of_le (hP (m + Finsupp.single i 1))
    (show ((m i + 1 : ℕ) : F[X]).natDegree ≤ 0 by
      have he : ((m i + 1 : ℕ) : F[X]) = Polynomial.C ((m i + 1 : ℕ) : F) :=
        (map_natCast Polynomial.C _).symm
      rw [he, Polynomial.natDegree_C])

/-- Taking the initial separant at a constant center preserves challenge height. -/
theorem challengeHeightLE_initialJetSeparantOver {r h : ℕ}
    (Q : DifferentialPolynomial F[X] r) (c : F) (hQ : ChallengeHeightLE Q h) :
    ChallengeHeightLE (initialJetSeparantOver (Polynomial.C c) Q) h := by
  apply (hQ.pderiv (some (Fin.last r))).aeval
  intro i
  cases i with
  | none => exact height_C (by simp)
  | some i => exact height_X i

/-- Universal Taylor jets have challenge-independent coefficients. -/
theorem challengeHeightLE_universalTaylorJet (K j : ℕ) :
    ChallengeHeightLE (universalTaylorJet (F := F[X]) K j) 0 := by
  rw [← map_universalTaylorJet (Polynomial.C : F →+* F[X])]
  intro m
  rw [MvPolynomial.coeff_map, Polynomial.natDegree_C]

/-- Every coefficient of the universal residual retains the source challenge-height bound. -/
theorem challengeHeightLE_universalTaylorResidual {r h : ℕ}
    (Q : DifferentialPolynomial F[X] r) (c : F) (hQ : ChallengeHeightLE Q h)
    (K : ℕ) :
    ChallengeHeightLE (universalTaylorResidual K (Polynomial.C c) Q) h := by
  apply hQ.aeval
  intro i
  cases i with
  | none => exact (height_C (by simp)).add (height_X none)
  | some j => exact challengeHeightLE_universalTaylorJet K j.val

/-- Separating out the Taylor power also preserves the challenge-height bound. -/
theorem universalTaylorResidual_coeff_natDegree_le {r h : ℕ}
    (Q : DifferentialPolynomial F[X] r) (c : F) (hQ : ChallengeHeightLE Q h)
    (K t : ℕ) (m : Fin K →₀ ℕ) :
    (MvPolynomial.coeff m ((optionEquivLeft F[X] (Fin K)
      (universalTaylorResidual K (Polynomial.C c) Q)).coeff t)).natDegree ≤ h := by
  rw [optionEquivLeft_coeff_coeff]
  exact challengeHeightLE_universalTaylorResidual Q c hQ K _

end ReedSolomon.HiddenDerivative

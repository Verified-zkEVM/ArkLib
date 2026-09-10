/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorCuts
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorDegree


/-!
# Joint degree of symbolic Taylor cuts

The affine received symbol contributes one challenge degree. It fits the same uniform
degree bound as the common Taylor numerators.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {r : ℕ}

/-- Specializing the independent variable preserves the initial equation's jet-degree bound. -/
theorem totalDegree_initialJetEquationOver_le (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) :
    (initialJetEquationOver center Q).totalDegree ≤
      Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  rw [← weightedTotalDegree_one]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none => simp
  | some j => simp only [Option.elim_some, weightedTotalDegree_one,
      totalDegree_X, le_refl]

/-- Coefficient height and jet degree bound the joint initial hypersurface degree. -/
theorem jointTotalDegree_initialJetEquationOver_le (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hh : ∀ m ∈ (initialJetEquationOver center Q).support,
      (coeff m (initialJetEquationOver center Q)).natDegree ≤ h) :
    jointTotalDegree (initialJetEquationOver center Q) ≤ v + h := by
  have hd := jointTotalDegree_le_coeff_degree_add (initialJetEquationOver center Q) h hh
  have hj := (totalDegree_initialJetEquationOver_le center Q).trans hv
  omega

/-- An affine challenge-dependent agreement cut has the uniform common-numerator degree. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_exponent
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (K τ B : ℕ)
    (hS : jointTotalDegree (initialJetSeparantOver (Polynomial.C center) Q) ≤ B)
    (hN : ∀ l : Fin K,
      jointTotalDegree
          (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ)) ≤
        1 + τ * B) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b) (τ := τ)) ≤
        1 + τ * B := by
  unfold taylorAgreementEquationOver
  apply (jointTotalDegree_sub_le _ _).trans
  apply max_le
  · apply jointTotalDegree_finsetSum_le
    intro l _
    apply (jointTotalDegree_mul_le _ _).trans
    simpa only [← Polynomial.C_sub, ← Polynomial.C_pow, jointTotalDegree_scalar,
      zero_add] using hN l
  · apply (jointTotalDegree_mul_le _ _).trans
    exact Nat.add_le_add (jointTotalDegree_affine_le a b)
      ((jointTotalDegree_pow_le _ _).trans (Nat.mul_le_mul_left _ hS))

/-- The default affine challenge-dependent agreement cut has the coarse degree bound. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (K B : ℕ)
    (hS : jointTotalDegree (initialJetSeparantOver (Polynomial.C center) Q) ≤ B)
    (hN : ∀ l : Fin K,
      jointTotalDegree (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l) ≤
        1 + 2 * K * B) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b)) ≤
        1 + 2 * K * B := by
  exact jointTotalDegree_taylorAgreementEquationOver_le_of_exponent
    center x a b Q K (2 * K) B hS hN

/-- Initial specialization at a constant center does not increase challenge height. -/
theorem challengeHeightLE_initialJetEquationOver (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) {h : ℕ}
    (hQ : ChallengeHeightLE Q h) :
    ChallengeHeightLE (initialJetEquationOver (Polynomial.C center) Q) h := by
  classical
  apply hQ.aeval
  intro i
  cases i with
  | none =>
    intro m
    simp only [Option.elim_none, coeff_C]
    split_ifs <;> simp
  | some i =>
    intro m
    simp only [Option.elim_some, coeff_X]
    split_ifs <;> simp

/-- Source degree and height bound the actual initial symbolic hypersurface. -/
theorem jointTotalDegree_initialJetEquationOver_le_of_source (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h) :
    jointTotalDegree (initialJetEquationOver (Polynomial.C center) Q) ≤ v + h := by
  apply jointTotalDegree_initialJetEquationOver_le _ Q v h hjet
  intro m _
  exact challengeHeightLE_initialJetEquationOver center Q hheight m

/-- The affine received-word cut padded to a sufficient exponent satisfies the source-derived
degree bound. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_source_and_exponent
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b) (τ := τ)) ≤
        1 + τ * (v - 1 + h) := by
  apply jointTotalDegree_taylorAgreementEquationOver_le_of_exponent
    center x a b Q K τ (v - 1 + h)
  · apply jointTotalDegree_initialJetSeparantOver_le _ Q v h hjet
    intro m _
    exact challengeHeightLE_initialJetSeparantOver Q center hheight m
  · exact jointTotalDegree_commonTaylorNumeratorOver_le_of_source_and_exponent
      center Q v h K τ hτ hv hjet hheight

/-- The default affine received-word cut satisfies the coarse source-derived bound. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_source
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h K : ℕ)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b)) ≤
        1 + 2 * K * (v - 1 + h) := by
  exact jointTotalDegree_taylorAgreementEquationOver_le_of_source_and_exponent
    center x a b Q v h K (2 * K) (taylorExponentSufficient_two_mul r K)
      hv hjet hheight

end

end ReedSolomon.HiddenDerivative

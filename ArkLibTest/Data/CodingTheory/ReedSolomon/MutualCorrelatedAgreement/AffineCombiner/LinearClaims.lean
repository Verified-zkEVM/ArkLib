/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LinearClaimsExact
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the equal-degree combiner with linear claims -/

open ReedSolomon Polynomial
open scoped Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The whole field `F₂` as the evaluation domain. -/
private def binaryDomain : ZMod 2 ↪ ZMod 2 := Function.Embedding.refl _

-- At degree zero, the combined word must be constant. For nonzero input words, at least one
-- value of `θ` leaves a nontrivial equality in `(α, β)` for the two values to agree.
-- For zero words, a false claim can be exceptional for at most two pairs per `θ`.
-- The bound is attained at six exceptional triples with constant words `f = 0` and `g = 1`,
-- weight and initial claims zero, and message `c(θ) = θ`.
/-- info: true -/
#guard_msgs in
#eval linearClaimMcaErrorRat binaryDomain 0 2 1 == 3 / 4

-- A threshold greater than the domain size excludes all candidates.
/-- info: true -/
#guard_msgs in
#eval linearClaimMcaErrorRat binaryDomain 0 3 1 == 0

-- Honest claims on `F₅` with `v = (1, 2)`, `F = 1`, `G = 2`, `θ = 1`:
-- `⟨coef(G), v⟩ = 2`, `⟨coef(F), v⟩ = 1`, and `⟨coef(X(F + θ G)), v⟩ = 3 · 2 = 1`.
example (α β : ZMod 5) :
    linearClaim ![1, 2] (C 2 + affineMultiplier α β * (C 1 + C 1 * C 2)) =
      2 + α * (1 + 1 * 2) + β * 1 := by
  rw [linearClaim_add_affineMultiplier_mul]
  simp [linearClaim, Fin.sum_univ_two, coeff_C, coeff_X_mul, coeff_one]
  have h6 : (6 : ZMod 5) = 1 := by decide
  linear_combination β * h6

-- At `d = 1`, `A = 4` on `F₅`, the Johnson quotient is `5 · 2 / (9 - 5) = 5 / 2`.
-- So `ℓ₀ = 2`, and the additive term `ℓ₀/q` is `2 / 5`. The paper's `2ℓ₀/q` is `4 / 5`.
example :
    linearClaimMcaError fullDomain 1 4 1 ≤ affineMcaError fullDomain 1 4 1 + 2 / 5 := by
  have h := linearClaimMcaError_le_affineMcaError_add fullDomain (d := 1) (A := 4)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

-- With honest announcements `c_F = ⟨coef(X F), v⟩`, `c_G = ⟨coef(X G), v⟩`, the derived message
-- is the honest claim `⟨coef(X(F + θ G)), v⟩`.
example {F : Type*} [Field F] {d : ℕ} (v : Fin (d + 1) → F) (F₀ G₀ : F[X]) (θ : F) :
    linearClaim v (X * F₀) + θ * linearClaim v (X * G₀) = linearClaim v (X * (F₀ + C θ * G₀)) := by
  rw [mul_add, mul_left_comm, linearClaim_add, linearClaim_C_mul]

-- Non-vacuity: on `F₅` with `f = g = 0`, `v = (1, 0)`, false claims `γ₀ = γ₁ = 1`, message `0`,
-- and `(θ, α, β) = (0, -1, 0)`, the zero polynomial is exceptional at `d = 1`, `A = 5`, `s = 1`.
-- It meets the combined claim `0 = 1 - 1`, but any witness `G₀` claiming `1` is the constant `1`,
-- which misses `g = 0` at all five points.
example : ∃ P, IsLinearClaimExceptional fullDomain 0 0 1 5 1 ![1, 0] 1 1 0 0 (-1) 0 P := by
  refine ⟨0, by simp, ?_, by simp [linearClaim], ?_⟩
  · have : polynomialAgreementSet fullDomain (equalDegreeWord fullDomain 0 0 0 (-1) 0) 0 =
        Finset.univ := by
      ext i
      simp [equalDegreeWord]
    rw [this, Finset.card_univ, ZMod.card]
  · intro F₀ G₀ _ hG _ ⟨_, h₁, _⟩
    have hG0 : G₀ = C (G₀.coeff 0) := eq_C_of_degree_le_zero (Order.le_of_lt_succ hG)
    have hc : G₀.coeff 0 = 1 := by simpa [linearClaim, Fin.sum_univ_two] using h₁
    have : {i ∈ polynomialAgreementSet fullDomain (equalDegreeWord fullDomain 0 0 0 (-1) 0) 0 |
        F₀.eval (fullDomain i) ≠ (0 : ZMod 5 → ZMod 5) i ∨
          G₀.eval (fullDomain i) ≠ (0 : ZMod 5 → ZMod 5) i} = Finset.univ := by
      ext i
      rw [hG0, hc]
      simp [equalDegreeWord]
    rw [this, Finset.card_univ, ZMod.card]
    norm_num

-- Honest instance: with `f = g = 0` and correct claims `γ₀ = γ₁ = c = 0`, no challenge triple
-- is exceptional at `d = 1`, `A = 4`, `s = 1`.
-- A candidate of degree at most one with four roots is zero, and `F₀ = G₀ = 0` explain it.
example (v : Fin 2 → ZMod 5) (θ α β : ZMod 5) :
    ¬ ∃ P, IsLinearClaimExceptional fullDomain 0 0 1 4 1 v 0 0 0 θ α β P := by
  rintro ⟨P, hdeg, hA, -, hexc⟩
  have hP : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P
      (polynomialAgreementSet fullDomain (equalDegreeWord fullDomain 0 0 θ α β) P)
      (fun i hi ↦ by simpa [equalDegreeWord, fullDomain] using hi) ?_
    have := natDegree_le_of_degree_le hdeg
    omega
  subst hP
  have := hexc 0 0 (by simp) (by simp) (by simp)
    ⟨by simp [linearClaim], by simp [linearClaim], by simp [linearClaim]⟩
  simp at this

-- The paper's worked case: `n = 2²⁰`, `d = 2¹⁸`, `A = 576717` gives `ℓ₀ = ⌊5.714…⌋ = 5`.
private theorem paper_johnson_floor :
    ⌊((2 ^ 20 : ℕ) : ℝ) * (((576717 : ℕ) : ℝ) - 1 - (2 ^ 18 : ℕ)) /
      ((((576717 : ℕ) : ℝ) - 1) ^ 2 - (2 ^ 20 : ℕ) * (2 ^ 18 : ℕ))⌋₊ = 5 := by
  rw [Nat.floor_eq_iff (by norm_num)]
  norm_num

-- At the paper's parameters `n = 2²⁰`, `d = 2¹⁸`, `A = 576717`, and `q = 2¹²⁸`:
-- linear claims add `ℓ₀/q = 5 · 2⁻¹²⁸` to the affine error, as the equal-degree combiner does.
-- The paper's term `2ℓ₀/q` is `10 · 2⁻¹²⁸`.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype F] [Fintype ι] (domain : ι ↪ F)
    (hn : Fintype.card ι = 2 ^ 20) (hq : Fintype.card F = 2 ^ 128) :
    linearClaimMcaError domain (2 ^ 18) 576717 1 ≤
      affineMcaError domain (2 ^ 18) 576717 1 + ENNReal.ofReal (5 / 2 ^ 128) := by
  have hJ : Fintype.card ι * 2 ^ 18 < (576717 - 1) ^ 2 := by
    rw [hn]
    norm_num
  have h := linearClaimMcaError_le_affineMcaError_add domain hJ
  rw [hn, hq, paper_johnson_floor] at h
  convert h using 4
  norm_num

-- The Johnson list bound accepts the caller's decidable equality instance.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι] (domain : ι ↪ F)
    (f g : ι → F) {d L : ℕ} (T : Finset (F[X] × F[X]))
    (hdeg : ∀ p ∈ T, p.1.degree ≤ d ∧ p.2.degree ≤ d)
    (hL : ∀ p ∈ T, L ≤ #(commonPolynomialAgreementSet domain f g p.1 p.2)) :
    #T * (L * L - Fintype.card ι * d) ≤ Fintype.card ι * (L - d) :=
  card_mul_sq_sub_card_mul_le_of_commonPolynomialAgreementSet domain f g T hdeg hL

/-- info: 'ReedSolomon.linearClaimMcaError_le_affineMcaError_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.linearClaimMcaError_le_affineMcaError_add

/-- info: 'ReedSolomon.card_filter_linearClaimResidual_eq_zero_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_filter_linearClaimResidual_eq_zero_le

/-- info: 'ReedSolomon.card_mul_sq_sub_card_mul_le_of_commonPolynomialAgreementSet' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_mul_sq_sub_card_mul_le_of_commonPolynomialAgreementSet

/-- info: 'ReedSolomon.le_floor_johnson_of_mul_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_floor_johnson_of_mul_le

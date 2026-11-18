/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LinearClaimsSampling
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the equal-degree combiner with linear claims -/

open ReedSolomon Polynomial
open scoped Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

-- Honest claims on `F₅` with `v = (1, 2)`, `F = 1`, `G = 2`, `θ = 1`:
-- `⟨coef(G), v⟩ = 2`, `⟨coef(F), v⟩ = 1`, and `⟨coef(X(F + θ G)), v⟩ = 3 · 2 = 1`.
example (α β : ZMod 5) :
    linearClaim ![1, 2] (C 2 + affineMultiplier α β * (C 1 + C 1 * C 2)) =
      2 + α * (1 + 1 * 2) + β * 1 := by
  rw [linearClaim_equalDegree_combination]
  simp [linearClaim, Fin.sum_univ_two, coeff_C, coeff_X_mul, coeff_one]
  have h6 : (6 : ZMod 5) = 1 := by decide
  linear_combination β * h6

-- The honest combination identity holds with no degree bound on the witnesses.
example {F : Type*} [Field F] (v : Fin 3 → F) (F₀ G₀ : F[X]) (θ α β : F) :
    linearClaim v (G₀ + affineMultiplier α β * (F₀ + C θ * G₀)) =
      linearClaim v G₀ + α * (linearClaim v F₀ + θ * linearClaim v G₀) +
        β * linearClaim v (X * (F₀ + C θ * G₀)) :=
  linearClaim_equalDegree_combination v F₀ G₀ θ α β

-- At `d = 1`, `A = 4` on `F₅`, the Johnson quotient is `5 · 2 / (9 - 5) = 5 / 2`.
-- So `ℓ₀ = 2`, and the paper's additive term `2ℓ₀/q` is `4 / 5`.
example :
    linearClaimMcaError fullDomain 1 4 1 ≤ affineMcaError fullDomain 1 4 1 + 4 / 5 := by
  have h := linearClaimMcaError_le_affineMcaError_add fullDomain (d := 1) (A := 4)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

/-- The round-saving prover announces `c_F, c_G` up front and answers `θ` with `c_F + θ c_G`. -/
private def roundSaving {ι F : Type*} [Field F] {d : ℕ} (f g : ι → F) (v : Fin (d + 1) → F)
    (γ₀ γ₁ cF cG : F) : LinearClaimInstance ι F d :=
  ⟨f, g, v, γ₀, γ₁, fun θ ↦ cF + θ * cG⟩

-- With honest announcements `c_F = ⟨coef(X F), v⟩`, `c_G = ⟨coef(X G), v⟩`, the derived message
-- is the honest claim `⟨coef(X(F + θ G)), v⟩`.
example {F : Type*} [Field F] {d : ℕ} (v : Fin (d + 1) → F) (F₀ G₀ : F[X]) (θ : F) :
    linearClaim v (X * F₀) + θ * linearClaim v (X * G₀) = linearClaim v (X * (F₀ + C θ * G₀)) := by
  rw [mul_add, mul_left_comm, linearClaim_add, linearClaim_C_mul]

open scoped ProbabilityTheory

-- The round-saving prover is covered: its exceptional probability on `F₅` is at most
-- the affine error plus `4 / 5`.
example (f g : ZMod 5 → ZMod 5) (v : Fin 2 → ZMod 5) (γ₀ γ₁ cF cG : ZMod 5) :
    Pr{let c ← $ᵗ (ZMod 5 × ZMod 5 × ZMod 5)}[∃ P,
      IsLinearClaimExceptional fullDomain f g 1 4 1 v γ₀ γ₁ (cF + c.1 * cG) c.1 c.2.1 c.2.2 P] ≤
        affineMcaError fullDomain 1 4 1 + 4 / 5 := by
  refine (prob_isLinearClaimExceptional_le fullDomain 1 4 1
    (roundSaving f g v γ₀ γ₁ cF cG)).trans ?_
  have h := linearClaimMcaError_le_affineMcaError_add fullDomain (d := 1) (A := 4)
    (by simp [ZMod.card])
  norm_num [ZMod.card, ENNReal.ofReal_div_of_pos] at h
  exact h

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

/-- info: 'ReedSolomon.linearClaimMcaError_eq_iSup_prob' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.linearClaimMcaError_eq_iSup_prob

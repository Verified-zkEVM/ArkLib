/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LinearClaimsSampling
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for uniform probabilities of linear-claim combiners -/

open ReedSolomon
open scoped ProbabilityTheory

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

/-- The round-saving prover announces `c_F, c_G` up front and answers `θ` with `c_F + θ c_G`. -/
private def roundSaving {ι F : Type*} [Field F] {d : ℕ} (f g : ι → F) (v : Fin (d + 1) → F)
    (γ₀ γ₁ cF cG : F) : LinearClaimInstance ι F d :=
  ⟨f, g, v, γ₀, γ₁, fun θ ↦ cF + θ * cG⟩

-- The round-saving prover is covered: for uniform `(θ, α, β)` on `F₅`, its exceptional
-- probability is at most the affine error plus `2ℓ₀/q = 4/5`.
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

/-- info: 'ReedSolomon.linearClaimMcaError_eq_iSup_prob' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.linearClaimMcaError_eq_iSup_prob

/-- info: 'ReedSolomon.prob_isLinearClaimExceptional_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.prob_isLinearClaimExceptional_le

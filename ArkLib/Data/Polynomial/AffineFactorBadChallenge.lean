/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Probability.Uniform
public import VCVio.EvalDist.ProbabilityBounds
public import Mathlib.Algebra.Field.Basic

/-! # Bad challenges for affine factors

Each factor has exactly one zero as a function of its additive challenge. A union bound over
the factors controls the probability that a denominator vanishes.
-/

@[expose] public section

namespace AffineFactorBadChallenge

variable {U F : Type} [Field F]

/-- A challenge is bad when one of the affine factors vanishes. -/
def BadChallenge (W label : U → F) (β γ : F) : Prop :=
  ∃ u, W u + β * label u + γ = 0

/-- The only bad additive challenge is the negative of the other two terms. -/
theorem factor_eq_zero_iff (W label : U → F) (u : U) (β γ : F) :
    W u + β * label u + γ = 0 ↔ γ = -(W u + β * label u) := by
  rw [add_comm]
  exact add_eq_zero_iff_eq_neg

/-- For every factor and multiplicative challenge there is exactly one bad additive challenge. -/
theorem existsUnique_bad_gamma (W label : U → F) (u : U) (β : F) :
    ∃! γ, W u + β * label u + γ = 0 := by
  refine ⟨-(W u + β * label u), ?_, ?_⟩
  · exact (factor_eq_zero_iff W label u β _).mpr rfl
  · intro γ hγ
    exact (factor_eq_zero_iff W label u β γ).mp hγ

section Probability

open scoped ProbabilityTheory ENNReal NNReal

variable {F : Type} [Field F] [Fintype F] [SampleableType F]

/-- For a fixed multiplicative challenge, a single affine factor vanishes with probability
exactly `1 / |F|`. -/
theorem prob_factor_eq_zero (W label : U → F) (u : U) (β : F) :
    Pr{let γ ← $ᵗ F}[W u + β * label u + γ = 0] =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [prEvent_congr ($ᵗ F) _ (fun γ => γ = -(W u + β * label u))
    (factor_eq_zero_iff W label u β)]
  exact SampleableType.prEvent_uniformSample_eq_singleton _

/-- A single factor vanishes with probability at most `1 / |F|` under joint challenges. -/
theorem prob_factor_eq_zero_le (W label : U → F) (u : U) :
    Pr{let r ← $ᵗ (F × F)}[W u + r.1 * label u + r.2 = 0] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  exact SampleableType.prEvent_uniformSample_prod_le_of_forall_fst _
    (fun β => (prob_factor_eq_zero W label u β).le)

/-- The chance of a zero factor among `|U|` factors is at most `|U| / |F|`. -/
theorem prob_badChallenge_le [Fintype U] (W label : U → F) :
    Pr{let r ← $ᵗ (F × F)}[BadChallenge W label r.1 r.2] ≤
      (((Fintype.card U : ℕ) : ℝ≥0) / Fintype.card F : ℝ≥0) := by
  rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast,
    div_eq_mul_inv]
  exact prEvent_exists_le_card_mul ($ᵗ (F × F))
    (fun (u : U) (r : F × F) => W u + r.1 * label u + r.2 = 0)
    (prob_factor_eq_zero_le W label)

end Probability
end AffineFactorBadChallenge

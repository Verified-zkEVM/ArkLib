/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Spartan.ZeroCheck.Reduction
import Mathlib.Algebra.Field.ZMod

/-! # Random-evaluation and zero-check examples over a small prime field -/

namespace Spartan.ZeroCheckTest

open MvPolynomial OracleComp OracleInterface
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable local instance : SampleableType (ZMod 5) := SampleableType.ofFintype _

/-- A false identity `X₀ = 0` passes the evaluation check at the zero point. -/
example : answer (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5)) (fun _ => (0 : ZMod 5)) =
    answer (0 : MvPolynomial (Fin 1) (ZMod 5)) (fun _ => (0 : ZMod 5)) := by
  simp only [RandomEvaluation.answer_eq_eval, eval_X, map_zero]
  rfl

/-- The same false identity fails at a nonzero point. -/
example : answer (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5)) (fun _ => (1 : ZMod 5)) ≠
    answer (0 : MvPolynomial (Fin 1) (ZMod 5)) (fun _ => (1 : ZMod 5)) := by
  simp only [RandomEvaluation.answer_eq_eval, eval_X, map_zero]
  exact (one_ne_zero : (1 : ZMod 5) ≠ 0)

/-- A nonzero linear polynomial vanishes at a uniform point with probability at most `1/5`. -/
example :
    Pr{let τ ← $ᵗ Query (MvPolynomial (Fin 1) (ZMod 5))}[
      answer (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5)) τ = answer 0 τ] ≤
      ((1 : ℝ≥0) / 5 : ℝ≥0) := by
  simpa only [ZMod.card, Nat.cast_one, Nat.cast_ofNat] using
    RandomEvaluation.prob_answer_eq_zero_le (X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5))
      (X_ne_zero _) 1 (totalDegree_X _).le

/-- A nonzero quadratic vanishes at a uniform point with probability at most `2/5`. -/
example :
    Pr{let τ ← $ᵗ Query (MvPolynomial (Fin 1) (ZMod 5))}[
      answer (X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) (ZMod 5)) τ = answer 0 τ] ≤
      ((2 : ℝ≥0) / 5 : ℝ≥0) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    RandomEvaluation.prob_answer_eq_zero_le (X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) (ZMod 5))
      (pow_ne_zero 2 (X_ne_zero _)) 2 (totalDegree_X_pow (0 : Fin 1) 2).le

/-- With no variables, a false constant identity never passes. -/
example :
    Pr{let τ ← $ᵗ Query (MvPolynomial (Fin 0) (ZMod 5))}[
      answer (C 1 : MvPolynomial (Fin 0) (ZMod 5)) τ = answer 0 τ] = 0 := by
  apply le_antisymm _ zero_le
  simpa using RandomEvaluation.prob_answer_eq_zero_le (C 1 : MvPolynomial (Fin 0) (ZMod 5))
    (by simp) 0 (totalDegree_C _).le

/-- The specialized first challenge preserves satisfaction over the small prime field. -/
example (pp : PublicParams) (x : R1CS.Statement (ZMod 5) pp.toSizeR1CS)
    (oracles : ∀ i, Realization.OracleStatement (R := ZMod 5) pp i)
    (h : Spartan.ZeroCheck.inputRelation pp x oracles) (τ : Fin pp.ℓ_m → ZMod 5) :
    Spartan.ZeroCheck.outputRelation pp (τ, x) oracles := by
  change eval τ (Spartan.ZeroCheck.polynomial pp x oracles) = 0
  rw [(Spartan.ZeroCheck.polynomial_zero_iff pp x oracles).2 h, map_zero]

end Spartan.ZeroCheckTest

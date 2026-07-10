/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import VCVio.OracleComp.ProbComp

/-!
# Additions to VCV-io's `EvalDist.Monad.Basic`

Boolean monotonicity lemmas for the outcome probability of `pure` computations, shared by the
lattice commitment binding reductions.
-/

open OracleComp

/-- Boolean monotonicity of `pure` outcome probability into a disjunction: if `win` implies
`inner ∨ outer`, then the probability of the winning outcome is bounded by the sum of the two
disjunct probabilities. -/
theorem probOutput_pure_bool_le_or (win inner outer : Bool)
    (h : win = true → inner = true ∨ outer = true) :
    Pr[= true | ((pure win) : ProbComp Bool)] ≤
      Pr[= true | ((pure inner) : ProbComp Bool)] +
        Pr[= true | ((pure outer) : ProbComp Bool)] := by
  cases win <;> cases inner <;> cases outer <;> simp_all

/-- Boolean monotonicity of `pure` outcome probability: if `b₁` implies `b₂`, then the winning
probability of `pure b₁` is bounded by that of `pure b₂`. -/
theorem probOutput_pure_bool_le (b₁ b₂ : Bool) (h : b₁ = true → b₂ = true) :
    Pr[= true | (pure b₁ : ProbComp Bool)] ≤ Pr[= true | (pure b₂ : ProbComp Bool)] := by
  simpa using probOutput_pure_bool_le_or b₁ b₂ false (fun hw => Or.inl (h hw))

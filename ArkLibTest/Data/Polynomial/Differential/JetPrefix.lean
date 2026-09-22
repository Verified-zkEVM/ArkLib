/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.JetPrefix

/-!
# Acceptance tests for active jets and jet prefixes

* In depth `2`, `Y₁ * X` depends on `Y₁` and on no other jet variable, so `Y₁` is its highest
  active jet; `highestActiveJet` computes it, and the prefix presentation is `Y₁ * X` in depth
  `1`.
* An equation in `X` alone has no highest active jet, and dependence on `X` is not counted.
* The prefix embedding sends the top variable of depth `1` to `Y₁` in depth `2`, and restricting
  a Hasse jet gives the shorter Hasse jet.
* `1` is a bounded solution of `y' = 0` of degree `0`.
* For `Y₁ - Y₀` embedded in depth `2`, regularity in `Y₁` at the jet of `1` is regularity in the
  top variable of depth `1`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- `Y₁ * X` in depth `2`. -/
private abbrev productEquation : DifferentialPolynomial ℚ 2 :=
  X (some 1) * X none

private theorem jetDegree_productEquation (j : Fin 3) :
    jetDegree productEquation j = if j = 1 then 1 else 0 := by
  classical
  rw [jetDegree, degreeOf_mul_X_of_ne _ (Option.some_ne_none j), degreeOf_X]
  simp

private theorem isHighestActiveJet_productEquation : IsHighestActiveJet productEquation 1 := by
  refine ⟨by simp [DependsOnJet, jetDegree_productEquation], fun j hj ↦ ?_⟩
  simp [DependsOnJet, jetDegree_productEquation, hj.ne']

/-- The computed highest active jet of `Y₁ * X` is `Y₁`. -/
example : highestActiveJet productEquation = some 1 := by
  have hactive : activeJets productEquation = {1} := by
    ext j
    by_cases h : j = 1 <;> simp [DependsOnJet, jetDegree_productEquation, h]
  have hne : (activeJets productEquation).Nonempty := by simp [hactive]
  rw [highestActiveJet_eq_some_max _ hne]
  simp [hactive]

/-- The prefix presentation of `Y₁ * X` is `Y₁ * X` in depth `1`, obtained from
`exists_prefixDifferentialPolynomial`. -/
example : ∃ Q' : DifferentialPolynomial ℚ 1,
    rename (jetPrefixEmbedding (1 : Fin 3)) Q' = productEquation ∧
      Q' = X (some (Fin.last 1)) * X none := by
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial _ isHighestActiveJet_productEquation
  refine ⟨Q', hQ', rename_injective _ (jetPrefixEmbedding (1 : Fin 3)).injective ?_⟩
  rw [hQ']
  simp [productEquation]

/-- An equation in `X` alone depends on no jet variable. -/
example : highestActiveJet (X none ^ 2 : DifferentialPolynomial ℚ 2) = none := by
  rw [highestActiveJet_eq_none_iff]
  intro j
  simp [DependsOnJet, jetDegree, degreeOf_X_pow_of_ne 2 (Option.some_ne_none j)]

/-- The prefix embedding sends the top variable of depth `1` to `Y₁` in depth `2`. -/
example : jetPrefixEmbedding (1 : Fin 3) (some (Fin.last 1)) = some 1 :=
  jetPrefixEmbedding_some_last 1

/-- Restricting the Hasse jet of `P` through order `2` to order `1` gives the jet through
order `1`. -/
example (P : Polynomial ℚ) (c : ℚ) :
    restrictJet (1 : Fin 3) (polynomialJet (d := 2) c P) = polynomialJet (d := 1) c P :=
  restrictJet_polynomialJet 1 c P

/-- `1` is a bounded solution of `y' = 0` of degree at most `0`. -/
example : ∃ P : BoundedSolution (X (some 1) : DifferentialPolynomial ℚ 1) 0,
    P.polynomial = 1 := by
  refine ⟨⟨⟨1, ?_⟩, ?_⟩, rfl⟩
  · rw [Polynomial.mem_degreeLT]
    simp
  · simp

/-- Regularity of `Y₁ - Y₀`, embedded in depth `2`, reduces to depth `1`. -/
example (c : ℚ) (P : Polynomial ℚ) :
    IsRegularJet (rename (jetPrefixEmbedding (1 : Fin 3))
        (X (some 1) - X (some 0) : DifferentialPolynomial ℚ 1)) 1 c (polynomialJet c P) ↔
      IsRegularJet (X (some 1) - X (some 0) : DifferentialPolynomial ℚ 1) (Fin.last 1) c
        (polynomialJet c P) :=
  isRegularJet_rename_jetPrefixEmbedding_iff 1 _ c P

end

end PolynomialDifferential

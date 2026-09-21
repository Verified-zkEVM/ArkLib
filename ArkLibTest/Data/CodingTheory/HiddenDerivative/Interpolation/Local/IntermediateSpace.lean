/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.IntermediateSpace

/-!
# Intermediate space acceptance tests

Membership of monomials at the boundary of the `U`-degree condition, a concrete dimension, and a
counterexample showing that `finrank_localIntermediateSpace` needs `0 < d`.
-/

open MvPolynomial ReedSolomon.HiddenDerivative

/-- `T U` has `U`-degree equal to its `T`-degree, so it is in the space. -/
example : (X (localT 1) * X (localU 1) : LocalPolynomial ℚ 1) ∈
    localIntermediateSpace ℚ 1 2 0 0 := by
  rw [X, X, monomial_mul_monomial, one_mul, mem_localIntermediateSpace_iff]
  intro e he
  simp only [support_monomial, one_ne_zero, ↓reduceIte, Finset.mem_singleton] at he
  subst he
  simp [LocalIntermediateExponent, localT, localU, localAux, Finsupp.weight_eq_sum,
    Fintype.sum_option, localFirstJetWeight, localHigherJetWeight]

/-- `U` alone has `U`-degree above its `T`-degree, so it is not in the space. -/
example : (X (localU 1) : LocalPolynomial ℚ 1) ∉ localIntermediateSpace ℚ 1 2 0 0 := by
  intro h
  have := (mem_localIntermediateSpace_iff.mp h) (Finsupp.single (localU 1) 1)
    (by simp [X, support_monomial])
  simp [LocalIntermediateExponent, localT, localU, localAux] at this

/-- For `d = 1, m = 2, M = 1, W = 0`: `2 + 4 = 6` monomials. -/
example : Module.finrank ℚ (localIntermediateSpace ℚ 1 2 1 0) = 6 := by
  rw [finrank_localIntermediateSpace (by norm_num)]
  decide

/-- For `d = 0` there is no `Y₁`, and with `m = 1` the only monomial is `1`. The formula of
`finrank_localIntermediateSpace` would give `Λ_0(0) (0 + 1)(1 + 1) = 2`. -/
example : Module.finrank ℚ (localIntermediateSpace ℚ 0 1 1 0) = 1 ∧
    weightedHigherJetCount 0 0 * ambientContactCount 0 1 = 2 := by
  refine ⟨?_, by decide⟩
  have hset : {e | LocalIntermediateExponent 0 1 1 0 e} =
      ↑({0} : Finset (LocalVariable 0 →₀ ℕ)) := by
    ext e
    simp only [Set.mem_ofPred_eq, Finset.coe_singleton, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, -, -⟩
      ext v
      rcases v with _ | _ | j
      · simp only [localT] at h1; simp; omega
      · simp only [localT, localU, localAux] at h1 h2; simp; omega
      · exact j.elim0
    · rintro rfl
      simp [LocalIntermediateExponent]
  rw [localIntermediateSpace, hset, finrank_restrictSupport_finset, Finset.card_singleton]

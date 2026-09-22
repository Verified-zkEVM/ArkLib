/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Combinatorics.Enumerative.MonomialCount

/-!
# Acceptance tests for exponent-vector counts

The examples compute small counts of exponent vectors of bounded degree, check that the
cone-count formula needs its degree hypothesis, and evaluate the cone-avoidance count for the
single forbidden exponent `X₀` in two variables, where the surviving exponents are the powers of
`X₁`.
-/

open Finset Finsupp

/-- There are six exponent vectors of degree at most two in two variables:
`1, X₀, X₁, X₀², X₀X₁, X₁²`. -/
example : #(degreeLEFinset (Fin 2) 2) = 6 := by
  rw [card_degreeLEFinset]
  decide

/-- The same count through the `Set.ncard` form, which needs only `Finite σ`. -/
example : {e : Fin 3 →₀ ℕ | e.degree ≤ 1}.ncard = 4 := by
  rw [ncard_setOf_degree_le]
  simp

/-- The cone count needs `b.degree ≤ N`. For `b = X₀²` in one variable and `N = 1` no exponent of
degree at most one lies above `b`, but the formula `(N - b.degree + 1).choose 1` evaluates to `1`
because natural subtraction truncates. -/
example :
    #{e ∈ degreeLEFinset (Fin 1) 1 | single 0 2 ≤ e} = 0 ∧
      (1 - (single (0 : Fin 1) 2).degree + Fintype.card (Fin 1)).choose (Fintype.card (Fin 1)) =
        1 := by
  refine ⟨card_eq_zero.mpr (filter_eq_empty_iff.mpr fun e he hle ↦ ?_), by simp⟩
  have h1 := mem_degreeLEFinset.mp he
  have h2 := degree_mono hle
  simp at h2
  omega

/-- Inside the degree range the cone count holds: in two variables, `3` of the `10` exponents of
degree at most three are divisible by `X₀X₁`, namely `X₀X₁`, `X₀²X₁` and `X₀X₁²`. -/
example : #{e ∈ degreeLEFinset (Fin 2) 3 | single 0 1 + single 1 1 ≤ e} = 3 := by
  rw [card_filter_le_degreeLEFinset _ (by simp)]
  simp

/-- Avoiding the cone above `X₀` in two variables leaves the powers of `X₁`, so the count at
degree bound `N = 3` is `4`, and the counting polynomial evaluates to it. -/
example :
    (coneAvoidancePoly ℚ (Fintype.card (Fin 2))
      ({single 0 1} : Finset (Fin 2 →₀ ℕ))).eval (3 : ℚ) = 4 := by
  have heval := eval_coneAvoidancePoly (σ := Fin 2) ℚ {single 0 1} (N := 3) (by simp)
  have hsplit := card_filter_add_card_filter_not (fun e : Fin 2 →₀ ℕ ↦ single 0 1 ≤ e)
    (s := degreeLEFinset (Fin 2) 3)
  rw [card_filter_le_degreeLEFinset _ (by simp), card_degreeLEFinset] at hsplit
  have hcount : #{e ∈ degreeLEFinset (Fin 2) 3 | ¬single 0 1 ≤ e} = 4 := by
    simp only [degree_single, Fintype.card_fin] at hsplit
    rw [show Nat.choose (3 - 1 + 2) 2 = 6 by decide, show Nat.choose (3 + 2) 2 = 10 by decide]
      at hsplit
    omega
  simp only [mem_singleton, forall_eq] at heval
  rw [hcount] at heval
  exact_mod_cast heval

/-- The polynomial count exists for every finite forbidden set, with degree at most the number of
variables. -/
example (B : Finset (Fin 3 →₀ ℕ)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ 3 ∧ ∀ N ≥ (B.sup id).degree,
      P.eval (N : ℚ) = {e : Fin 3 →₀ ℕ | e.degree ≤ N ∧ ∀ b ∈ B, ¬b ≤ e}.ncard := by
  simpa using exists_eval_eq_ncard_forall_not_le ℚ B

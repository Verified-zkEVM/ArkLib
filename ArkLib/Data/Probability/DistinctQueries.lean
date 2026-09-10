/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Probability.UniformQueryBoundary

/-!
# Distinct positions among independent uniform queries

Repeated queries need only one response per distinct position. The query draws themselves
remain unchanged. This expectation counts responses after deduplication without replacing
sampling with replacement by a different query distribution.
-/

@[expose] public section
namespace ArkLib.UniformQueryBoundary
noncomputable section

/-- Number of positions visited by a query tuple. -/
def distinctQueryCount {α : Type*} [DecidableEq α] {t : ℕ}
    (queries : Fin t → α) : ℕ := (Finset.univ.image queries).card

/-- The expected number of distinct positions in `t` independent uniform draws from `n`
positions is `n * (1 - ((n-1)/n)^t)`. -/
theorem uniformQueryExpectation_distinctQueryCount
    {α : Type*} [Fintype α] [DecidableEq α] (t : ℕ)
    (hn : 0 < Fintype.card α) :
    uniformQueryExpectation t (distinctQueryCount (α := α)) =
      (Fintype.card α : ℚ) *
        (1 - (((Fintype.card α - 1 : ℕ) : ℚ) / Fintype.card α) ^ t) := by
  classical
  have hstat : distinctQueryCount (α := α) (t := t) =
      authenticationHashCount (fun _ : α ↦ ∅) (fun a ↦ {a}) := by
    funext queries
    unfold distinctQueryCount authenticationHashCount
    congr 1
    ext a
    simp [IsAuthenticationBoundary, QueriesAvoid, eq_comm]
  rw [hstat, uniformQueryExpectation_authenticationHashCount]
  simp only [Finset.card_empty, Nat.sub_zero, Finset.empty_union, Finset.card_singleton]
  have hp : (Fintype.card α - 1) ^ t ≤ Fintype.card α ^ t :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) _
  rw [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_pow]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hq : (Fintype.card α : ℚ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp

end
end ArkLib.UniformQueryBoundary

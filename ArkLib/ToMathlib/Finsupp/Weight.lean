/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finsupp.Weight

/-!
# Comparisons for `Finsupp.weight`

`Finsupp.weight_le_weight` states that a pointwise larger weight function gives every finitely
supported exponent a larger weight. Mathlib has monotonicity of `Finsupp.weight w` in the exponent
(for canonically ordered codomains) but not in `w`. `Finsupp.apply_smul_le_weight` bounds a single
term `f s • w s` by the weight; Mathlib's `Finsupp.le_weight` bounds `f s` alone for natural-number
weights.
-/

@[expose] public section

namespace Finsupp

variable {σ M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- If `w i ≤ w' i` for every `i`, then `f.weight w ≤ f.weight w'` for every exponent `f`. The
comparison is only needed on the support of `f`, but the pointwise form is what callers have. -/
theorem weight_le_weight {w w' : σ → M} (h : ∀ i, w i ≤ w' i) (f : σ →₀ ℕ) :
    f.weight w ≤ f.weight w' := by
  simp only [weight_apply]
  exact Finset.sum_le_sum fun i _ => nsmul_le_nsmul_right (h i) _

/-- In a canonically ordered monoid, a single term `f s • w s` of the weight is at most the
weight. For `M = ℕ` this bounds the exponent `f s` by `f.weight w / w s` when `0 < w s`. -/
theorem apply_smul_le_weight [CanonicallyOrderedAdd M] (w : σ → M) (f : σ →₀ ℕ) (s : σ) :
    f s • w s ≤ f.weight w := by
  classical
  rw [weight_apply, Finsupp.sum]
  by_cases hs : s ∈ f.support
  · exact Finset.single_le_sum (f := fun i => f i • w i) (fun _ _ => zero_le) hs
  · rw [Finsupp.notMem_support_iff.mp hs, zero_smul]
    exact zero_le

end Finsupp

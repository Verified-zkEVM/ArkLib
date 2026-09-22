/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finsupp.Weight

/-!
# Monotonicity of `Finsupp.weight` in the weight

`Finsupp.weight_le_weight` states that a pointwise larger weight function gives every finitely
supported exponent a larger weight. Mathlib has monotonicity of `Finsupp.weight w` in the exponent
(for canonically ordered codomains) but not in `w`.
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

end Finsupp

/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma, Chung Thai Nguyen
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# More lemmas about `Fin` and big operators
-/

@[expose] public section

namespace Fin

/-- The sums of `f` over the even and over the odd naturals below `2 * m` add up to its sum
over `Fin (m * 2)`. This is the finite analogue of `tsum_even_add_odd`. -/
theorem sum_even_add_odd {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ∑ x : Fin m, f (2 * x) + ∑ x : Fin m, f (2 * x + 1) = ∑ x : Fin (m * 2), f x := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Fin.sum_univ_two, finProdFinEquiv, mul_comm, add_comm]

end Fin

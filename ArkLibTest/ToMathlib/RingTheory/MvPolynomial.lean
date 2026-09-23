/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree

/-!
# Acceptance tests for bidegree bounds

The example checks that a bidegree bound with positive degree in both coordinates remains valid
after enlarging both bounds.
-/

open MvPolynomial

namespace BidegreeAcceptance

/-- A bidegree bound with positive degree in both coordinates remains valid after enlargement. -/
example : (X none * X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈
    restrictBidegree (Fin 1) ℚ 2 3 := by
  have hnone : (X none : MvPolynomial (Option (Fin 1)) ℚ) ∈
      restrictBidegree (Fin 1) ℚ 1 0 := by
    rw [mem_restrictBidegree, support_X]
    simp
  have hsome : (X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈
      restrictBidegree (Fin 1) ℚ 0 1 := by
    rw [mem_restrictBidegree, support_X]
    simp
  exact mem_restrictBidegree_mono (mul_mem_restrictBidegree hnone hsome)
    (by omega) (by omega)

end BidegreeAcceptance

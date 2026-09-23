/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree

/-!
# Acceptance tests for polynomials of bounded bidegree

The examples count exponents and compute dimensions of spaces of bounded bidegree, check
membership of small monomials, multiply bidegree bounds, lift a polynomial along the monomial map,
and show that `bidegreeMap_surjective` needs `0 < a`.
-/

open MvPolynomial

namespace BidegreeTest

/-- In one variable there are `2 * 2 = 4` exponents of bidegree at most `(1, 1)`. -/
example : (bidegreeExponents (Fin 1) 1 1).ncard = 4 := by
  rw [ncard_bidegreeExponents, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

/-- In two variables the polynomials of bidegree at most `(2, 3)` form a space of dimension
`3 * (5).choose 2 = 30`. -/
example : Module.finrank ℚ (restrictBidegree (Fin 2) ℚ 2 3) = 30 := by
  rw [finrank_restrictBidegree, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

/-- The distinguished variable has bidegree `(1, 0)`. -/
theorem X_none_mem_restrictBidegree : (X none : MvPolynomial (Option (Fin 1)) ℚ) ∈
    restrictBidegree (Fin 1) ℚ 1 0 := by
  rw [mem_restrictBidegree, support_X]
  simp

/-- A variable `some i` has bidegree `(0, 1)`. -/
theorem X_some_mem_restrictBidegree : (X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈
    restrictBidegree (Fin 1) ℚ 0 1 := by
  rw [mem_restrictBidegree, support_X]
  simp

/-- The product `X none * X (some 0)` has bidegree `(1, 1)`. -/
example : (X none * X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈
    restrictBidegree (Fin 1) ℚ 1 1 :=
  mul_mem_restrictBidegree X_none_mem_restrictBidegree X_some_mem_restrictBidegree

/-- A bidegree bound with positive degree in both coordinates remains valid after enlargement. -/
example : (X none * X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈
    restrictBidegree (Fin 1) ℚ 2 3 :=
  mem_restrictBidegree_mono
    (mul_mem_restrictBidegree X_none_mem_restrictBidegree X_some_mem_restrictBidegree)
    (by omega) (by omega)

/-- The square of the distinguished variable does not have bidegree at most `(1, b)`. -/
example (b : ℕ) : (X none ^ 2 : MvPolynomial (Option (Fin 1)) ℚ) ∉
    restrictBidegree (Fin 1) ℚ 1 b := by
  rw [mem_restrictBidegree, X_pow_eq_monomial, support_monomial]
  simp

/-- A polynomial of bidegree at most `(1, 1)` lifts to a polynomial of total degree at most `1` on
the exponents, which `bidegreeMap` sends back to it. -/
example :
    let P : MvPolynomial (Option (Fin 1)) ℚ := X none * X (some 0)
    ∃ Q : MvPolynomial (bidegreeExponents (Fin 1) 1 1) ℚ,
      Q.totalDegree ≤ 1 ∧ bidegreeMap (Fin 1) ℚ 1 1 Q = P :=
  have hP := mul_mem_restrictBidegree X_none_mem_restrictBidegree X_some_mem_restrictBidegree
  ⟨bidegreeLift _ hP, totalDegree_bidegreeLift_le_one _ hP, bidegreeMap_bidegreeLift _ hP⟩

/-- The hypothesis `0 < a` of `bidegreeMap_surjective` is needed: for `a = 0` every exponent has
`none`-component `0`, so the distinguished variable `X none` is not in the image. -/
example (b : ℕ) : ¬Function.Surjective (bidegreeMap (Fin 1) ℚ 0 b) := by
  intro hsurj
  obtain ⟨P, hP⟩ := hsurj (X none)
  have hmem := bidegreeMap_mem_restrictBidegree (N := P.totalDegree) (le_refl P.totalDegree)
  rw [hP, mem_restrictBidegree, support_X] at hmem
  simpa using hmem _ (Finset.mem_singleton_self _)

end BidegreeTest

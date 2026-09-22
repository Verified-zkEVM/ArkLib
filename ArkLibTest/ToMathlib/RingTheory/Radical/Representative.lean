/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Radical.Representative
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Acceptance tests for radical representatives

For a prime `p` and `n ≠ 0`, the only prime factor class of `p ^ n` is that of `p`, so
`radicalRep (p ^ n)` is associated to `p`. For `X ^ 2` over `ℚ` this makes the degree sum of
`sum_primeFactors_le` equal to `1`, strictly below `natDegree (X ^ 2) = 2`. The zero element shows
that `map_radicalRep_eq_zero_iff` needs `a ≠ 0`.
-/

open Polynomial UniqueFactorizationMonoid

namespace RadicalRepTest

/-! ### The square of `X` over `ℚ` -/

example : Associated (radicalRep (X ^ 2 : ℚ[X])) X :=
  associated_radicalRep_pow_of_prime prime_X two_ne_zero

/-- `natDegree` is additive on nonzero products over a domain. -/
theorem natDegree_additive : ∀ x y : ℚ[X], x ≠ 0 → y ≠ 0 →
    (x * y).natDegree = x.natDegree + y.natDegree :=
  fun _ _ hx hy ↦ natDegree_mul hx hy

/-- The distinct factor of `X ^ 2` has degree `1`, although `X ^ 2` has degree `2`: the bound of
`sum_primeFactors_le` is strict here. -/
example : ∑ c ∈ primeFactors (Associates.mk (X ^ 2 : ℚ[X])), c.rep.natDegree = 1 := by
  have h := associated_radicalRep_pow_of_prime (prime_X (R := ℚ)) two_ne_zero
  rw [← map_radicalRep_eq_sum natDegree_additive]
  simpa using map_eq_of_associated natDegree_additive X_ne_zero h

example : (X ^ 2 : ℚ[X]).natDegree = 2 := natDegree_X_pow 2

/-- `primeFactors_mk_pow_of_prime` needs `n ≠ 0`: `X ^ 0 = 1` has no prime factor classes. -/
example : primeFactors (Associates.mk ((X : ℚ[X]) ^ 0)) = ∅ := by
  simp [primeFactors_of_isUnit]

/-! ### Zeros -/

/-- Evaluation at `0` kills `X ^ 2`, hence the representative of its prime factor class. -/
example : ∃ c ∈ primeFactors (Associates.mk (X ^ 2 : ℚ[X])),
    eval₂RingHom (RingHom.id ℚ) 0 c.rep = 0 :=
  (map_eq_zero_iff_exists_primeFactors (eval₂RingHom (RingHom.id ℚ) 0)
    (pow_ne_zero 2 X_ne_zero)).mp (by simp)

/-- `map_radicalRep_eq_zero_iff` fails at `a = 0`, since `radicalRep 0 = 1`. -/
example : ¬ (RingHom.id ℚ[X] (radicalRep 0) = 0 ↔ RingHom.id ℚ[X] 0 = 0) := by
  simp [radicalRep_zero]

end RadicalRepTest

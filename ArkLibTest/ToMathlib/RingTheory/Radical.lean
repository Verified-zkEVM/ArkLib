/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Radical.Representative
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Radical-representative acceptance examples
-/

open Polynomial UniqueFactorizationMonoid

example : Associated (radicalRep (X ^ 2 : ℚ[X])) X :=
  associated_radicalRep_pow_of_prime prime_X two_ne_zero

example : ∃ c ∈ primeFactors (Associates.mk (X ^ 2 : ℚ[X])),
    eval₂RingHom (RingHom.id ℚ) 0 c.rep = 0 :=
  (map_eq_zero_iff_exists_primeFactors (eval₂RingHom (RingHom.id ℚ) 0)
    (pow_ne_zero 2 X_ne_zero)).mp (by simp)

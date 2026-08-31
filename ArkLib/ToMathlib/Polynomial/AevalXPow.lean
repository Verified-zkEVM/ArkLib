/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Substituting `X ↦ X^i` in `Polynomial R`

Small facts about the `R`-algebra endomorphism `aeval (X^i) : R[X] →ₐ[R] R[X]` (substitution
`p ↦ p(X^i)`): its action on monomials, and that iterating substitutions multiplies exponents.
These are generic `Polynomial` lemmas (no cyclotomic content) used by the Galois-automorphism
layer of `Data/Lattices/CyclotomicRing/`, and are reasonable upstreaming candidates.
-/

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- `aeval (X^i)` sends a monomial `c·X^k` to `c·X^{ki}`. -/
theorem aeval_X_pow_monomial (i k : ℕ) (c : R) :
    (aeval (X ^ i : R[X])) (monomial k c) = monomial (k * i) c := by
  rw [aeval_monomial, algebraMap_eq, ← pow_mul, C_mul_X_pow_eq_monomial, Nat.mul_comm]

/-- Substituting `X ↦ X^j` then `X ↦ X^i` is substituting `X ↦ X^{ij}`. -/
theorem aeval_X_pow_aeval_X_pow (i j : ℕ) (p : R[X]) :
    (aeval (X ^ i : R[X])) ((aeval (X ^ j : R[X])) p) = (aeval (X ^ (i * j) : R[X])) p := by
  have h : (aeval (X ^ i : R[X])).comp (aeval (X ^ j : R[X])) = aeval (X ^ (i * j) : R[X]) := by
    rw [← aeval_algHom, map_pow, aeval_X, ← pow_mul]
  exact AlgHom.congr_fun h p

end Polynomial

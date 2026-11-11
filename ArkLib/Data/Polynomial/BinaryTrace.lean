/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Binary Frobenius-sum polynomials

`binaryTracePoly m` is the polynomial `X + X² + ⋯ + X^(2^(m-1))`. For positive `m`
its degree is `2^(m-1)`. Its evaluation as a field trace is established in
`ArkLib.Data.FieldTheory.BinaryTrace`.
-/

@[expose] public section

open scoped BigOperators

namespace Polynomial

/-- The Frobenius-sum polynomial `X + X² + ⋯ + X^(2^(m-1))`. -/
noncomputable def binaryTracePoly {R : Type*} [Semiring R] (m : ℕ) : R[X] :=
  ∑ i ∈ Finset.range m, X ^ (2 ^ i)

@[simp]
lemma binaryTracePoly_zero {R : Type*} [Semiring R] : binaryTracePoly (R := R) 0 = 0 := by
  simp [binaryTracePoly]

lemma binaryTracePoly_succ {R : Type*} [Semiring R] (m : ℕ) :
    binaryTracePoly (R := R) (m + 1) = binaryTracePoly m + X ^ (2 ^ m) := by
  simp [binaryTracePoly, Finset.sum_range_succ]

variable {F : Type*} [Field F]

/-- A nonempty binary trace polynomial has leading exponent `2^(m-1)`. -/
lemma natDegree_binaryTracePoly {m : ℕ} (hm : 0 < m) :
    (binaryTracePoly (R := F) m).natDegree = 2 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  induction n with
  | zero => simp [binaryTracePoly_succ]
  | succ n ih =>
      rw [binaryTracePoly_succ]
      have hlt : (binaryTracePoly (R := F) (n + 1)).natDegree <
          (X ^ (2 ^ (n + 1)) : F[X]).natDegree := by
        rw [ih (by omega), natDegree_X_pow]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      rw [natDegree_add_eq_right_of_natDegree_lt hlt, natDegree_X_pow]
      simp

lemma binaryTracePoly_ne_zero {m : ℕ} (hm : 0 < m) :
    binaryTracePoly (R := F) m ≠ 0 := by
  intro h
  have := natDegree_binaryTracePoly (F := F) hm
  rw [h, natDegree_zero] at this
  have : 0 < 2 ^ (m - 1) := pow_pos (by omega) _
  omega

end Polynomial

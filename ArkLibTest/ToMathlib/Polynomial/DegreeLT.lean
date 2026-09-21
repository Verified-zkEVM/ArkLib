/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.Polynomial.DegreeLT

/-!
# Acceptance client for `Polynomial.degreeLT` facts

The examples check the two boundary budgets. A polynomial in `degreeLT R 1` is a constant, and a
nonzero multiple `g * q` in `degreeLT R 0` forces `q = 0`.
-/

open Polynomial

/-- The budget `degreeLT R 1` contains only constants. -/
example {R : Type*} [Semiring R] {p : R[X]} (hp : p ∈ degreeLT R 1) : p = C (p.coeff 0) :=
  eq_C_of_natDegree_le_zero (natDegree_le_of_mem_degreeLT_succ hp)

/-- With the budget `n = 0`, removing a nonzero factor leaves the zero polynomial. -/
example {R : Type*} [Semiring R] [NoZeroDivisors R] {g q : R[X]} (hg : g ≠ 0)
    (h : g * q ∈ degreeLT R 0) : q = 0 := by
  have hq := mem_degreeLT_of_mul_left hg h
  rwa [degreeLT_zero, Submodule.mem_bot] at hq

/--
info: 'Polynomial.natDegree_le_of_mem_degreeLT_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.natDegree_le_of_mem_degreeLT_succ

/--
info: 'Polynomial.mem_degreeLT_of_mul_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.mem_degreeLT_of_mul_left

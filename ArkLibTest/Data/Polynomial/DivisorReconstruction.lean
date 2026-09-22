/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.DivisorReconstruction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Divisor-reconstruction clients

These clients use the nodal instance with repeated anchors and with an empty anchor set, apply
the quotient equation at an anchor in `ZMod 4`, which has zero divisors, and show that the degree
bound on the correction polynomial cannot be dropped.
-/

namespace Polynomial

noncomputable section

-- Repeated anchors: the nodal divisor of `(2, 2)` is `(X - 2) ^ 2`, and a linear quotient gives
-- degree below `2 + 2`.
example {q I : ℚ[X]} (hq : q.degree < 2) (hI : I.degree < 2) :
    (Lagrange.nodal Finset.univ ![(2 : ℚ), 2] * q + I).degree < (2 + 2 : ℕ) := by
  simpa using degree_nodal_mul_add_lt Finset.univ ![(2 : ℚ), 2] hq (I := I) (by simpa using hI)

-- Empty anchor set: the divisor is `1`, the correction must be `0`, and the bound is `k`.
example {q : ℚ[X]} {k : ℕ} (hq : q.degree < k) :
    (Lagrange.nodal (∅ : Finset (Fin 0)) Fin.elim0 * q + 0).degree < ((k + 0 : ℕ) : WithBot ℕ) :=
  degree_nodal_mul_add_lt ∅ Fin.elim0 hq (I := 0) (by simp)

-- At an anchor the reconstruction takes the correction's value.
example (q I : ℚ[X]) :
    (Lagrange.nodal Finset.univ ![(1 : ℚ), 5] * q + I).eval 5 = I.eval 5 := by
  simpa using eval_nodal_mul_add_at_node (s := Finset.univ) (v := ![(1 : ℚ), 5])
    (Finset.mem_univ 1) q I

-- Over `ZMod 4` the quotient equation at `x = 2` holds with `D(2) = 2` and `q(2) = 2`, whose
-- product is `0`; no division is involved.
example : ((X - C 0 : (ZMod 4)[X]) * C 2 + C 3).eval 2 = 3 :=
  eval_mul_add_of_eval_mul_eq_sub (by
    simp only [map_zero, sub_zero, eval_X, eval_C, sub_self]
    decide)

-- The degree bound on the correction is needed: `D = 1`, `d = 0`, `q = 0`, `I = 1`.
example : ¬ ((1 : ℚ[X]) * 0 + 1).degree < (0 + 0 : ℕ) := by
  simp

end

end Polynomial

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Reconstructing a polynomial from a quotient by a divisor

Let `D` be a polynomial of degree at most `d`, let `q` be a quotient of degree below `k`, and let
`I` be a correction polynomial of degree below `d`, for instance an interpolant of prescribed
values at the roots of `D`. The polynomial `D * q + I` has degree below `k + d`, takes the values
of `I` at every root of `D`, and at any point `x` where the quotient equation
`D(x) * q(x) = y - I(x)` holds it takes the value `y`. The last statement involves no division, so
it applies at roots of `D` and in rings with zero divisors.

The main instance is a nodal divisor `∏ i ∈ s, (X - v i)` (`Lagrange.nodal`). Its degree is
`#s`, so reconstruction from a quotient of degree below `k` has degree below `k + #s`. The anchor
values `v i` need not be distinct. The cubic divisor `(X - s₁) (X - s₂) (X - z)` is treated in
`ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredReconstruction`.

## Main statements

* `Polynomial.degree_mul_add_lt`: the degree bound `k + d`.
* `Polynomial.eval_mul_add_of_eval_eq_zero`: values at roots of the divisor.
* `Polynomial.eval_mul_add_of_eval_mul_eq_sub`: values where the quotient equation holds.
* `Polynomial.degree_nodal_mul_add_lt` and `Polynomial.eval_nodal_mul_add_at_node`: the nodal
  instances.
-/

@[expose] public section

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R]

/-- **Degree of a reconstruction.** If `D` has degree at most `d`, `q` has degree below `k` and
`I` has degree below `d`, then `D * q + I` has degree below `k + d`.

No hypothesis on `k` is needed: for `k = 0` the quotient is `0` and the reconstruction is `I`.
The bound on `I` is needed: for `D = 1`, `d = 0`, `q = 0` and `I = 1`, the reconstruction has
degree `0`, which is not below `k + d = 0`. -/
theorem degree_mul_add_lt {D q I : R[X]} {d k : ℕ} (hD : D.natDegree ≤ d) (hq : q.degree < k)
    (hI : I.degree < d) : (D * q + I).degree < (k + d : ℕ) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simpa using hI.trans_le (by exact_mod_cast Nat.le_add_left d k)
  have hqn : q.natDegree < k := (natDegree_lt_iff_degree_lt hq0).mpr hq
  have hnat : (D * q).natDegree < k + d :=
    (natDegree_mul_le (p := D) (q := q)).trans_lt (by omega)
  have hprod : (D * q).degree < (k + d : ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast hnat)
  exact (degree_add_le _ _).trans_lt
    (max_lt hprod (hI.trans_le (by exact_mod_cast Nat.le_add_left d k)))

end Semiring

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- **Values at roots of the divisor.** At a root `x` of `D`, the reconstruction `D * q + I` takes
the value of `I`, whatever the quotient `q`. -/
theorem eval_mul_add_of_eval_eq_zero {D q I : R[X]} {x : R} (hx : D.eval x = 0) :
    (D * q + I).eval x = I.eval x := by
  simp [hx]

end CommSemiring

section Ring

variable {R : Type*} [CommRing R]

/-- **Values from the quotient equation.** If `D(x) * q(x) = y - I(x)` at a point `x`, the
reconstruction `D * q + I` takes the value `y` at `x`. The equation is used as stated, without
dividing by `D(x)`. -/
theorem eval_mul_add_of_eval_mul_eq_sub {D q I : R[X]} {x y : R}
    (h : D.eval x * q.eval x = y - I.eval x) : (D * q + I).eval x = y := by
  simp [h]

/-- **Degree of a nodal reconstruction.** For the nodal divisor of the anchors `v i`, `i ∈ s`,
a quotient of degree below `k` and a correction of degree below `#s` give a reconstruction of
degree below `k + #s`. The anchors need not be distinct. -/
theorem degree_nodal_mul_add_lt {ι : Type*} [Nontrivial R] (s : Finset ι) (v : ι → R)
    {q I : R[X]} {k : ℕ} (hq : q.degree < k) (hI : I.degree < s.card) :
    (Lagrange.nodal s v * q + I).degree < (k + s.card : ℕ) :=
  degree_mul_add_lt Lagrange.natDegree_nodal.le hq hI

/-- **Values of a nodal reconstruction at the anchors.** At every anchor `v i` with `i ∈ s`, the
reconstruction `nodal s v * q + I` takes the value of `I`. -/
theorem eval_nodal_mul_add_at_node {ι : Type*} {s : Finset ι} {v : ι → R} {i : ι} (hi : i ∈ s)
    (q I : R[X]) : (Lagrange.nodal s v * q + I).eval (v i) = I.eval (v i) :=
  eval_mul_add_of_eval_eq_zero (Lagrange.eval_nodal_at_node hi)

end Ring

end Polynomial

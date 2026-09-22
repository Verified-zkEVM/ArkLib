/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Division by `X ^ d + 1` in the low-degree range

Dividing a polynomial of degree `< 2 d` by `X ^ d + 1` needs no algorithm: writing
`p = A + X ^ d · B` with `deg A, deg B < d`, the identity `p = (X ^ d + 1) · B + (A - B)` already
exhibits quotient and remainder, because `deg (A - B) < d = deg (X ^ d + 1)`. Hence the quotient is
just the **upper half of the coefficients**, shifted down by `d`:

`(p /ₘ (X ^ d + 1)).coeff k = p.coeff (d + k)`.

This is the concrete replacement for a general theory of coefficient growth under polynomial
division: in the power-of-two cyclotomic setting (`φ = X ^ d + 1`, `d = 2 ^ α`) every quotient of a
degree-`< 2 d` polynomial is *coefficientwise a subsequence of the dividend*, so any coefficient
bound on the dividend transfers verbatim to the quotient.

## Main results

* `Polynomial.divByMonic_X_pow_add_one`: the quotient in closed form, as the shifted upper half.
* `Polynomial.coeff_divByMonic_X_pow_add_one`: its coefficientwise form, the one consumers use.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Coefficients of a `Finset.range`-indexed sum of monomials: the truncation of `f` at `d`. -/
private theorem coeff_sum_range_monomial (d : ℕ) (f : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range d, (monomial k) (f k) : R[X]).coeff n = if n < d then f n else 0 := by
  rw [finsetSum_coeff]
  by_cases hn : n < d
  · rw [ite_eq_left hn, Finset.sum_eq_single n (fun b _ hb => by
      rw [coeff_monomial, ite_eq_right hb])
      (fun h => absurd (Finset.mem_range.mpr hn) h), coeff_monomial, ite_eq_left rfl]
  · rw [ite_eq_right hn]
    exact Finset.sum_eq_zero fun k hk => by
      rw [coeff_monomial, ite_eq_right (by have := Finset.mem_range.mp hk; omega)]

/-- **Degree-`< 2d` division by `X ^ d + 1` in closed form**: the quotient is the upper half of the
dividend's coefficients, shifted down by `d`.

The hypothesis is on `natDegree`, so `p = 0` is allowed (`natDegree 0 = 0 < 2 d`). -/
theorem divByMonic_X_pow_add_one [Nontrivial R] {d : ℕ} (hd : 0 < d) {p : R[X]}
    (hp : p.natDegree < 2 * d) :
    p /ₘ (X ^ d + 1) = ∑ k ∈ Finset.range d, (monomial k) (p.coeff (d + k)) := by
  set A : R[X] := ∑ k ∈ Finset.range d, (monomial k) (p.coeff k) with hA
  set B : R[X] := ∑ k ∈ Finset.range d, (monomial k) (p.coeff (d + k)) with hB
  have hmonic : (X ^ d + 1 : R[X]).Monic := by
    rw [← C_1]; exact monic_X_pow_add_C (1 : R) (by omega)
  have hdeg : (X ^ d + 1 : R[X]).degree = (d : WithBot ℕ) := by
    rw [← C_1, degree_X_pow_add_C hd]
  -- The dividend splits as `A + X ^ d · B`.
  have hsplit : p = A + X ^ d * B := by
    ext n
    rw [coeff_add, hA, coeff_sum_range_monomial, mul_comm, coeff_mul_X_pow']
    by_cases hnd : n < d
    · rw [ite_eq_left hnd, ite_eq_right (by omega), add_zero]
    · rw [ite_eq_right hnd, ite_eq_left (by omega), zero_add, hB, coeff_sum_range_monomial]
      by_cases hn2 : n - d < d
      · rw [ite_eq_left hn2]
        congr 1
        omega
      · rw [ite_eq_right hn2]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
  -- Remainder `A - B` has degree `< d`, so quotient/remainder are forced.
  refine (div_modByMonic_unique B (A - B) hmonic ⟨?_, ?_⟩).1
  · rw [hsplit]; ring
  · rw [hdeg, degree_lt_iff_coeff_zero]
    intro n hn
    rw [coeff_sub, hA, hB, coeff_sum_range_monomial, coeff_sum_range_monomial,
      ite_eq_right (by exact_mod_cast (not_lt.mpr (by exact_mod_cast hn))),
      ite_eq_right (by exact_mod_cast (not_lt.mpr (by exact_mod_cast hn))), sub_zero]

/-- **Coefficientwise form**: the `k`-th quotient coefficient is the dividend's `(d + k)`-th. Every
coefficient bound on `p` therefore transfers to `p /ₘ (X ^ d + 1)` with no growth at all. -/
theorem coeff_divByMonic_X_pow_add_one [Nontrivial R] {d : ℕ} (hd : 0 < d) {p : R[X]}
    (hp : p.natDegree < 2 * d) (k : ℕ) :
    (p /ₘ (X ^ d + 1)).coeff k = p.coeff (d + k) := by
  rw [divByMonic_X_pow_add_one hd hp, coeff_sum_range_monomial]
  by_cases hk : k < d
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

end Polynomial

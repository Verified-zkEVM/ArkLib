/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Individual degree under formal partial differentiation

This file proves how the formal partial derivative `MvPolynomial.pderiv i` and its iterates
`(pderiv i)^[a]` change the individual degree `degreeOf`.

The upper bounds hold over every commutative semiring. The exact-degree and nonvanishing results
need two further inputs: the coefficient ring has no zero divisors, and the natural number that
multiplies the leading coefficient in variable `i` is nonzero in the ring. The second input is
stated as an explicit cast hypothesis `(n : R) ≠ 0`. This covers characteristic zero, where every
positive cast is nonzero, and positive characteristic `p` whenever `p` does not divide `n`, in
particular when `0 < n < p`. A hypothesis of the form
`n < ringChar R` alone would exclude characteristic zero, since then `ringChar R = 0`. The lemma
`natCast_ne_zero_of_ringChar_eq_zero_or_lt` converts the usual characteristic guard into the cast
hypothesis.

Both extra inputs are necessary. In characteristic `p`, `pderiv i (X i ^ p) = p • X i ^ (p - 1)`
is zero although `X i ^ p` has degree `p` in `X i`. Over `ZMod 4`, the polynomial `2 * X i ^ 2`
has degree `2` and `(2 : ZMod 4) ≠ 0`, yet its derivative `4 * X i` is zero.

The weighted-degree bounds for `pderiv` are in `ArkLib.Data.MvPolynomial.WeightedDegree`.

## Main statements

* `MvPolynomial.degreeOf_pderiv_le_sub_one` and `MvPolynomial.degreeOf_pderiv_le`: one partial
  derivative lowers the degree in its own variable by at least one and does not raise any
  individual degree.
* `MvPolynomial.coeff_pderiv_sub_single_one`: the coefficient identity behind the exact results.
* `MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero` and
  `MvPolynomial.degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero`: nonvanishing and exact degree loss
  under the cast hypothesis `(degreeOf i p : R) ≠ 0`.
* `MvPolynomial.degreeOf_iterate_pderiv_le_sub`, `MvPolynomial.degreeOf_iterate_pderiv_le`, and
  `MvPolynomial.iterate_pderiv_eq_zero_of_degreeOf_lt`: characteristic-free bounds for iterates.
* `MvPolynomial.degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero` and
  `MvPolynomial.iterate_pderiv_ne_zero_of_natCast_ne_zero`: exact degree and nonvanishing along
  the first `a` steps of the derivative chain.
* `natCast_ne_zero_of_ringChar_eq_zero_or_lt`: the characteristic guard as a cast hypothesis.

## Proof outline

Mathlib's `MvPolynomial.coeff_pderiv` states that the coefficient of `m` in `pderiv i p` is the
coefficient of `m + single i 1` in `p` times `m i + 1`. Every monomial of the derivative therefore
comes from a monomial of `p` with one more power of `X i`, which gives the upper bounds. For the
exact results, take a monomial `m` of `p` whose exponent of `X i` equals `degreeOf i p`. The
coefficient of `m - single i 1` in the derivative is `coeff m p * (m i : R)`, which is nonzero
under the two extra inputs. The iterated statements follow by induction on the number of
derivatives; the cast hypothesis for step `k` concerns `degreeOf i p - k`, the degree reached after
`k` steps.
-/

@[expose] public section

/-- If `ringChar R` is zero or exceeds `n`, then every natural number `k` with `0 < k ≤ n` has a
nonzero image in `R`.

This turns the usual characteristic guard into the cast hypotheses used below. The disjunct
`ringChar R = 0` is what covers characteristic zero; the strict inequality alone would force
`n = 0` there. The hypothesis `0 < k` is needed because `(0 : R) = 0`. -/
theorem natCast_ne_zero_of_ringChar_eq_zero_or_lt {R : Type*} [NonAssocSemiring R] {n k : ℕ}
    (hchar : ringChar R = 0 ∨ n < ringChar R) (hk : 0 < k) (hkn : k ≤ n) : (k : R) ≠ 0 := by
  intro hzero
  have hdvd : ringChar R ∣ k := (ringChar.spec R k).mp hzero
  rcases hchar with hchar | hchar
  · rw [hchar, Nat.zero_dvd] at hdvd
    omega
  · have := Nat.le_of_dvd hk hdvd
    omega

namespace MvPolynomial

open Finsupp

variable {R σ : Type*} [CommSemiring R]

/-- Every monomial of `pderiv i p` comes from a monomial of `p` with one more factor `X i`. -/
private theorem add_single_one_mem_support_of_mem_support_pderiv {i : σ}
    {p : MvPolynomial σ R} {m : σ →₀ ℕ} (hm : m ∈ (pderiv i p).support) :
    m + single i 1 ∈ p.support := by
  rw [mem_support_iff] at hm ⊢
  intro hzero
  rw [coeff_pderiv, hzero, zero_mul] at hm
  exact hm rfl

/-- A partial derivative lowers the degree in its differentiation variable by at least one.

This holds in every characteristic, and truncated subtraction makes it hold for polynomials
constant in `X i`. Equality can fail: in characteristic `p`, `pderiv i (X i ^ p) = 0`. -/
theorem degreeOf_pderiv_le_sub_one (i : σ) (p : MvPolynomial σ R) :
    degreeOf i (pderiv i p) ≤ degreeOf i p - 1 := by
  rw [degreeOf_le_iff]
  intro m hm
  have hle := monomial_le_degreeOf i (add_single_one_mem_support_of_mem_support_pderiv hm)
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hle
  omega

/-- Partial differentiation in any variable does not increase the degree in any variable `j`,
including `j = i`. -/
theorem degreeOf_pderiv_le (i j : σ) (p : MvPolynomial σ R) :
    degreeOf j (pderiv i p) ≤ degreeOf j p := by
  rw [degreeOf_le_iff]
  intro m hm
  refine le_trans ?_
    (monomial_le_degreeOf j (add_single_one_mem_support_of_mem_support_pderiv hm))
  simp only [Finsupp.add_apply]
  omega

/-- The coefficient of `m - single i 1` in `pderiv i p` is the coefficient of `m` in `p` times the
exponent `m i`, provided `m i ≠ 0`.

Without `m i ≠ 0` the identity fails: for `m = 0` the left side is the coefficient of `X i` in
`p`, while the right side is zero. -/
theorem coeff_pderiv_sub_single_one (i : σ) (p : MvPolynomial σ R) {m : σ →₀ ℕ}
    (hm : m i ≠ 0) :
    (pderiv i p).coeff (m - single i 1) = p.coeff m * (m i : R) := by
  rw [coeff_pderiv, sub_add_single_one_cancel hm]
  congr 1
  rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]

/-- Under the cast hypothesis, `pderiv i p` has a nonzero coefficient at the exponent obtained
from a top-degree monomial in `X i` by lowering that exponent by one. -/
private theorem exists_mem_support_pderiv_of_natCast_ne_zero [NoZeroDivisors R] (i : σ)
    (p : MvPolynomial σ R) (hcast : (degreeOf i p : R) ≠ 0) :
    ∃ m : σ →₀ ℕ, m ∈ (pderiv i p).support ∧ m i = degreeOf i p - 1 := by
  classical
  have hdeg : degreeOf i p ≠ 0 := fun h => hcast (by rw [h, Nat.cast_zero])
  obtain ⟨m, hm, heq⟩ := Finset.exists_mem_eq_sup p.support
    (support_nonempty.mpr (ne_zero_of_degreeOf_ne_zero hdeg)) fun m => m i
  rw [← degreeOf_eq_sup i p] at heq
  have hmi : m i ≠ 0 := heq ▸ hdeg
  refine ⟨m - single i 1, ?_, ?_⟩
  · rw [mem_support_iff, coeff_pderiv_sub_single_one i p hmi]
    exact mul_ne_zero (mem_support_iff.mp hm) (heq ▸ hcast)
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_same, heq]

/-- If `R` has no zero divisors and the degree of `p` in `X i` is nonzero in `R`, then
`pderiv i p ≠ 0`.

The cast hypothesis implies that the degree is positive and that `R` is nontrivial. It holds in
characteristic zero whenever `p` depends on `X i`, and in characteristic `q > 0` when the degree
is not divisible by `q`. Both hypotheses are needed: `pderiv i (X i ^ q) = 0` in characteristic
`q`, and `pderiv i (2 * X i ^ 2) = 0` over `ZMod 4` although `(2 : ZMod 4) ≠ 0`. -/
theorem pderiv_ne_zero_of_natCast_ne_zero [NoZeroDivisors R] (i : σ) (p : MvPolynomial σ R)
    (hcast : (degreeOf i p : R) ≠ 0) : pderiv i p ≠ 0 := by
  obtain ⟨m, hm, -⟩ := exists_mem_support_pderiv_of_natCast_ne_zero i p hcast
  exact support_nonempty.mp ⟨m, hm⟩

/-- If `R` has no zero divisors and the degree of `p` in `X i` is nonzero in `R`, then
`pderiv i p` has degree exactly one less in `X i`.

The hypotheses are those of `pderiv_ne_zero_of_natCast_ne_zero`, and the same counterexamples
show that they are needed. -/
theorem degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero [NoZeroDivisors R] (i : σ)
    (p : MvPolynomial σ R) (hcast : (degreeOf i p : R) ≠ 0) :
    degreeOf i (pderiv i p) = degreeOf i p - 1 := by
  obtain ⟨m, hm, hmi⟩ := exists_mem_support_pderiv_of_natCast_ne_zero i p hcast
  exact le_antisymm (degreeOf_pderiv_le_sub_one i p) (hmi ▸ monomial_le_degreeOf i hm)

/-- `a` partial derivatives in `X i` lower the degree in `X i` by at least `a`, in every
characteristic. -/
theorem degreeOf_iterate_pderiv_le_sub (i : σ) (a : ℕ) (p : MvPolynomial σ R) :
    degreeOf i ((pderiv i)^[a] p) ≤ degreeOf i p - a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply']
      refine (degreeOf_pderiv_le_sub_one i _).trans ?_
      omega

/-- Iterated partial differentiation in `X i` does not increase the degree in any variable
`X j`. -/
theorem degreeOf_iterate_pderiv_le (i j : σ) (a : ℕ) (p : MvPolynomial σ R) :
    degreeOf j ((pderiv i)^[a] p) ≤ degreeOf j p := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply']
      exact (degreeOf_pderiv_le i j _).trans ih

/-- A polynomial that does not depend on `X i` has zero partial derivative in `X i`. -/
theorem pderiv_eq_zero_of_degreeOf_eq_zero {i : σ} {p : MvPolynomial σ R}
    (h : degreeOf i p = 0) : pderiv i p = 0 :=
  pderiv_eq_zero_of_notMem_vars fun hi => mem_vars_iff_degreeOf_ne_zero.mp hi h

/-- Differentiating in `X i` more times than the degree of `p` in `X i` gives zero, in every
characteristic. -/
theorem iterate_pderiv_eq_zero_of_degreeOf_lt {i : σ} {a : ℕ} {p : MvPolynomial σ R}
    (ha : degreeOf i p < a) : (pderiv i)^[a] p = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_lt ha
  have h0 : degreeOf i ((pderiv i)^[degreeOf i p] p) = 0 := by
    have := degreeOf_iterate_pderiv_le_sub i (degreeOf i p) p
    omega
  rw [add_assoc, add_comm, Function.iterate_add_apply, Function.iterate_succ_apply,
    pderiv_eq_zero_of_degreeOf_eq_zero h0]
  exact Function.iterate_fixed (map_zero _) b

/-- If `R` has no zero divisors and each of the degrees `degreeOf i p - k` for `k < a` is nonzero
in `R`, then `a` partial derivatives in `X i` lower the degree in `X i` by exactly `a`.

The hypothesis concerns only the degrees that are actually differentiated: after `k` steps the
degree is `degreeOf i p - k`, and the next step multiplies the leading coefficient by that number.
It implies `a ≤ degreeOf i p`, since otherwise `k = degreeOf i p` gives `(0 : R) ≠ 0`. In
characteristic `q > 0` it holds when `degreeOf i p < q` and `a ≤ degreeOf i p`, but also for
larger degrees as long as none of the `a` differentiated degrees is divisible by `q`. -/
theorem degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero [NoZeroDivisors R] (i : σ) (a : ℕ)
    (p : MvPolynomial σ R) (hcast : ∀ k < a, ((degreeOf i p - k : ℕ) : R) ≠ 0) :
    degreeOf i ((pderiv i)^[a] p) = degreeOf i p - a := by
  induction a with
  | zero => simp
  | succ a ih =>
      have ih' := ih fun k hk => hcast k (Nat.lt_succ_of_lt hk)
      rw [Function.iterate_succ_apply',
        degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero i _ (ih' ▸ hcast a (Nat.lt_succ_self a)),
        ih']
      omega

/-- If `p ≠ 0`, `R` has no zero divisors, and each of the degrees `degreeOf i p - k` for `k < a`
is nonzero in `R`, then `(pderiv i)^[a] p ≠ 0`.

Taking `a = degreeOf i p` shows that differentiating exactly through the degree in `X i` leaves a
nonzero polynomial independent of `X i`. The hypothesis `p ≠ 0` is needed only for `a = 0`, where
the cast hypothesis is vacuous and `p = 0` is a counterexample; for `a > 0` the cast hypothesis at
`k = 0` already forces `p ≠ 0`. -/
theorem iterate_pderiv_ne_zero_of_natCast_ne_zero [NoZeroDivisors R] (i : σ) (a : ℕ)
    {p : MvPolynomial σ R} (hp : p ≠ 0) (hcast : ∀ k < a, ((degreeOf i p - k : ℕ) : R) ≠ 0) :
    (pderiv i)^[a] p ≠ 0 := by
  cases a with
  | zero => exact hp
  | succ a =>
      rw [Function.iterate_succ_apply']
      apply pderiv_ne_zero_of_natCast_ne_zero
      rw [degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero i a p
        fun k hk => hcast k (Nat.lt_succ_of_lt hk)]
      exact hcast a (Nat.lt_succ_self a)

end MvPolynomial

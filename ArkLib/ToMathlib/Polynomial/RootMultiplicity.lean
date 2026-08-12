/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Root multiplicities from degree and from iterated derivatives

Two bounds relating the multiplicity of roots to other data: one counting multiplicities
against the degree, and one reading a multiplicity off the vanishing of iterated derivatives.

## Main statements

* `Polynomial.sum_rootMultiplicity_le_natDegree`: multiplicities summed over a finite set of
  points are bounded by the degree.
* `Polynomial.X_sub_C_pow_dvd_of_isRoot_iterate_derivative`: if the first `s` ordinary
  derivatives vanish at `a`, then `a` is a root of multiplicity at least `s`.

## Implementation notes

`X_sub_C_pow_dvd_of_isRoot_iterate_derivative` is the positive-characteristic complement of
`lt_rootMultiplicity_iff_isRoot_iterate_derivative`, which assumes `CharZero`. Both concern
*ordinary* derivatives, which agree with Hasse derivatives only up to the factors `j !`; the
guard `ringChar R = 0 ∨ min s k ≤ ringChar R` is what keeps those nonzero over the range
where they are actually divided out. It is phrased as a disjunction so that characteristic
zero is not excluded by `ringChar R = 0` forcing the bound to be `0`, and it cannot be
dropped: in characteristic `p` with `p ≤ min s k` one has `derivative^[p] (X ^ p) = 0`.

The bound is on `min s k` rather than on `k` alone. Only the factorials `j !` with `j < s`
*and* `j < k` are ever divided out, and the two bounds are incomparable — neither `s ≤ p`
nor `k ≤ p` implies the other — so `min` is the correct common weakening. This admits, for
instance, characteristic `2` with `k = 5` and `s = 2`.

## Tags

polynomial, root multiplicity, derivative
-/

namespace Polynomial

/-- The sum of the root multiplicities of a polynomial over a finite set of points is at most
its natural degree. -/
lemma sum_rootMultiplicity_le_natDegree {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (s : Finset R) :
    ∑ a ∈ s, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  have hle : (∑ a ∈ s, Multiset.replicate (p.rootMultiplicity a) a) ≤ p.roots := by
    rw [Multiset.le_iff_count]
    intro b
    rw [Multiset.count_sum', count_roots]
    calc ∑ a ∈ s, Multiset.count b (Multiset.replicate (p.rootMultiplicity a) a)
        = ∑ a ∈ s, (if a = b then p.rootMultiplicity a else 0) :=
          Finset.sum_congr rfl fun a _ => by rw [Multiset.count_replicate]
      _ ≤ p.rootMultiplicity b := by
          rw [Finset.sum_ite_eq' s b]
          split <;> simp
  have hcard := Multiset.card_le_card hle
  rw [Multiset.card_sum] at hcard
  simp only [Multiset.card_replicate] at hcard
  exact hcard.trans (card_roots' p)

/-- If the first `s` ordinary derivatives of a polynomial of degree `< k` are all rooted at
`a`, then `a` is a root of multiplicity at least `s`, provided the ring has characteristic
zero or characteristic at least `min s k`.

Ordinary derivatives differ from the Hasse derivatives of Mathlib's multiplicity criterion by
the factors `j !`; the characteristic hypothesis is what makes those nonzero. Only the
factorials `j !` with `j < s` and `j < k` are ever inverted, which is why the bound is on
`min s k` rather than on either argument alone — the two are incomparable, and neither
implies the other. -/
lemma X_sub_C_pow_dvd_of_isRoot_iterate_derivative {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} {a : R} {s k : ℕ}
    (hp : p ∈ degreeLT R k) (hchar : ringChar R = 0 ∨ min s k ≤ ringChar R)
    (hroot : ∀ j : Fin s, (derivative^[j.val] p).IsRoot a) :
    (X - C a) ^ s ∣ p := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro d hd
  change (taylor a p).coeff d = 0
  rw [taylor_coeff]
  by_cases hdk : d < k
  · have hfac : (d.factorial : R) ≠ 0 := by
      rcases hchar with hchar0 | hcharpos
      · letI : CharZero R := (CharP.ringChar_zero_iff_CharZero R).mp hchar0
        exact Nat.cast_ne_zero.mpr d.factorial_ne_zero
      · have hdlt : d < ringChar R := (lt_min hd hdk).trans_le hcharpos
        haveI : NeZero (ringChar R) := ⟨by omega⟩
        haveI : Fact (Nat.Prime (ringChar R)) := CharP.char_is_prime_of_pos R _
        intro hzero
        have hdvd : ringChar R ∣ d.factorial :=
          (CharP.cast_eq_zero_iff R (ringChar R) _).mp hzero
        have := (Nat.Prime.dvd_factorial (Fact.out (p := (ringChar R).Prime))).mp hdvd
        omega
    have hder : (derivative^[d] p).eval a = 0 := hroot ⟨d, hd⟩
    rw [← congrFun (factorial_smul_hasseDeriv (R := R) d) p] at hder
    simp only [LinearMap.smul_apply, eval_smul] at hder
    rw [nsmul_eq_mul] at hder
    exact (mul_eq_zero.mp hder).resolve_left hfac
  · by_cases hp0 : p = 0
    · simp [hp0]
    · have hdeg : p.natDegree < k :=
        (natDegree_lt_iff_degree_lt hp0).mpr (mem_degreeLT.mp hp)
      rw [hasseDeriv_eq_zero_of_lt_natDegree p d (hdeg.trans_le (not_lt.mp hdk))]
      simp

end Polynomial

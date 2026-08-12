/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Factorial.NatCast
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
*ordinary* derivatives, which agree with Hasse derivatives only up to the units `j !`; the
guard `ringChar R = 0 ∨ k ≤ ringChar R` is what makes those factors invertible over the
relevant degree range, and is phrased as a disjunction so that characteristic zero is not
excluded by `ringChar R = 0` forcing `k = 0`. It cannot be dropped: in characteristic
`p ≤ k` one has `derivative^[p] (X ^ p) = 0`.

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
`a`, then `a` is a root of multiplicity at least `s`, provided the field has characteristic
zero or characteristic at least `k`.

Ordinary derivatives differ from the Hasse derivatives of Mathlib's multiplicity criterion by
the factors `j !`; the characteristic hypothesis is what makes those invertible. -/
lemma X_sub_C_pow_dvd_of_isRoot_iterate_derivative {F : Type*} [Field F]
    {p : F[X]} {a : F} {s k : ℕ}
    (hp : p ∈ degreeLT F k) (hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (hroot : ∀ j : Fin s, (derivative^[j.val] p).IsRoot a) :
    (X - C a) ^ s ∣ p := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro d hd
  change (taylor a p).coeff d = 0
  rw [taylor_coeff]
  by_cases hdk : d < k
  · have hfac : IsUnit (d.factorial : F) := by
      rcases hchar with hchar0 | hcharpos
      · letI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hchar0
        exact IsUnit.natCast_factorial_of_algebra F d
      · letI : NeZero (ringChar F) :=
          ⟨Nat.ne_zero_of_lt ((Nat.zero_le d).trans_lt (hdk.trans_le hcharpos))⟩
        letI : Fact (Nat.Prime (ringChar F)) := CharP.char_is_prime_of_pos F _
        exact (IsUnit.natCast_factorial_iff_of_charP (ringChar F)).2 (hdk.trans_le hcharpos)
    have hder : (derivative^[d] p).eval a = 0 := hroot ⟨d, hd⟩
    rw [← congrFun (factorial_smul_hasseDeriv (R := F) d) p] at hder
    simp only [LinearMap.smul_apply, eval_smul] at hder
    rw [nsmul_eq_mul] at hder
    exact (mul_eq_zero.mp hder).resolve_left hfac.ne_zero
  · by_cases hp0 : p = 0
    · simp [hp0]
    · have hdeg : p.natDegree < k :=
        (natDegree_lt_iff_degree_lt hp0).mpr (mem_degreeLT.mp hp)
      rw [hasseDeriv_eq_zero_of_lt_natDegree p d (hdeg.trans_le (not_lt.mp hdk))]
      simp

end Polynomial

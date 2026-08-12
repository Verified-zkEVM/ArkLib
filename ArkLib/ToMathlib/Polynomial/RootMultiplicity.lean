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
# Additional polynomial root-multiplicity lemmas

## Main statements

* `Polynomial.sum_rootMultiplicity_le_natDegree` — root multiplicities summed over a finite
  set are bounded by the degree.
* `Polynomial.pow_dvd_of_eval_iterate_derivative_eq_zero` — vanishing of the first `s`
  ordinary derivatives at a point gives a root of multiplicity `s` there. This is the
  positive-characteristic complement of Mathlib's
  `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative`, which assumes `CharZero`:
  the guard `ringChar F = 0 ∨ k ≤ ringChar F` covers both regimes.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

namespace Polynomial

/-- The sum of the root multiplicities of a polynomial over a finite set of points is at most
its natural degree. -/
lemma sum_rootMultiplicity_le_natDegree {F : Type*} [Field F]
    {W : Polynomial F} (S : Finset F) :
    ∑ a ∈ S, W.rootMultiplicity a ≤ W.natDegree := by
  classical
  have hle : (∑ a ∈ S, Multiset.replicate (W.rootMultiplicity a) a) ≤ W.roots := by
    rw [Multiset.le_iff_count]
    intro b
    rw [Multiset.count_sum', Polynomial.count_roots]
    calc ∑ a ∈ S, Multiset.count b (Multiset.replicate (W.rootMultiplicity a) a)
        = ∑ a ∈ S, (if a = b then W.rootMultiplicity a else 0) :=
          Finset.sum_congr rfl fun a _ => by rw [Multiset.count_replicate]
      _ ≤ W.rootMultiplicity b := by
          rw [Finset.sum_ite_eq' S b]
          split <;> simp
  have hcard := Multiset.card_le_card hle
  rw [Multiset.card_sum] at hcard
  simp only [Multiset.card_replicate] at hcard
  exact hcard.trans (Polynomial.card_roots' W)

/-- If the first `s` ordinary derivatives of a polynomial of degree `< k` vanish at `a`,
then `a` is a root of multiplicity at least `s`, provided `F` has characteristic zero or
characteristic at least `k`.

The characteristic hypothesis is what makes the ordinary and Hasse derivatives differ by a
unit `j !` throughout the relevant degree range; Mathlib's root-multiplicity criterion is
stated for the latter. -/
lemma pow_dvd_of_eval_iterate_derivative_eq_zero {F : Type*} [Field F]
    {p : Polynomial F} {a : F} {s k : ℕ}
    (hp : p ∈ Polynomial.degreeLT F k) (hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (hzero : ∀ j : Fin s, (Polynomial.derivative^[j.val] p).eval a = 0) :
    (Polynomial.X - Polynomial.C a) ^ s ∣ p := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  intro d hd
  change (Polynomial.taylor a p).coeff d = 0
  rw [Polynomial.taylor_coeff]
  by_cases hdk : d < k
  · have hfac : IsUnit (d.factorial : F) := by
      rcases hchar with hchar0 | hcharpos
      · letI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hchar0
        exact IsUnit.natCast_factorial_of_algebra F d
      · letI : NeZero (ringChar F) :=
          ⟨Nat.ne_zero_of_lt ((Nat.zero_le d).trans_lt (hdk.trans_le hcharpos))⟩
        letI : Fact (Nat.Prime (ringChar F)) := CharP.char_is_prime_of_pos F _
        exact (IsUnit.natCast_factorial_iff_of_charP (ringChar F)).2 (hdk.trans_le hcharpos)
    have hder := hzero ⟨d, hd⟩
    change (Polynomial.derivative^[d] p).eval a = 0 at hder
    have hscale := congrFun (Polynomial.factorial_smul_hasseDeriv (R := F) d) p
    rw [← hscale] at hder
    simp only [LinearMap.smul_apply, Polynomial.eval_smul] at hder
    rw [nsmul_eq_mul] at hder
    exact (mul_eq_zero.mp hder).resolve_left hfac.ne_zero
  · by_cases hp0 : p = 0
    · simp [hp0]
    · have hpdeg : p.degree < (k : WithBot ℕ) := Polynomial.mem_degreeLT.mp hp
      have hdeg : p.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
      rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree p d (hdeg.trans_le (not_lt.mp hdk))]
      simp

end Polynomial

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Finsupp.Fin
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Coefficient bounds for products of bounded-degree integer polynomials

The fingerprinting step of BitZ ([BGKLSW26, §4.3]) needs a bound on the largest coefficient of a
product of integer polynomials in `X₁, …, X_k` of total degree at most `D`. Each coefficient of
`p · q` is a sum over the pairs of monomials `(s, t)` with `s + t = u`, and `s` determines `t`, so
at most `T` pairs contribute, where `T` is the number of monomials of total degree `≤ D`:
`‖p · q‖∞ ≤ T · ‖p‖∞ · ‖q‖∞`.

* `MvPolynomial.monomialsLE k D` is the finset of monomials in `k` variables of total degree
  `≤ D`; `MvPolynomial.card_monomialsLE` shows that there are `(D + k).choose k = C(D + k, k)` of
  them, the quantity `T` of [BGKLSW26, §4.3].
* `MvPolynomial.natAbs_coeff_mul_le` is the product bound.

## References

* [BGKLSW26] R. Bloemen, A. Garreta, M. Kostrzewa, S. Londhe, L. Soukhanov, J. Wu.
  *BitZ: proofs and commitments in arbitrary rings through binary fields*. ePrint 2026/2141.
-/

@[expose] public section

open Finset

namespace MvPolynomial

section Monomials

/-- The monomials in `k` variables of total degree at most `D`: the monomials of exact degree `D`
in `k + 1` variables, with the last exponent forgotten. -/
noncomputable def monomialsLE (k D : ℕ) : Finset (Fin k →₀ ℕ) :=
  ((Finset.univ : Finset (Fin (k + 1))).finsuppAntidiag D).image Finsupp.tail

/-- A monomial is in `monomialsLE k D` iff its total degree is at most `D`. -/
theorem mem_monomialsLE {k D : ℕ} {s : Fin k →₀ ℕ} : s ∈ monomialsLE k D ↔ s.degree ≤ D := by
  unfold monomialsLE
  rw [mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_finsuppAntidiag] at ht
    rw [Finsupp.degree_eq_sum, ← ht.1, Fin.sum_univ_succ]
    simp [Finsupp.tail_apply]
  · intro h
    refine ⟨Finsupp.cons (D - s.degree) s, ?_, Finsupp.tail_cons _ _⟩
    rw [mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    rw [Fin.sum_univ_succ]
    simp only [Finsupp.cons_zero, Finsupp.cons_succ]
    rw [← Finsupp.degree_eq_sum]
    omega

/-- **Stars and bars.** There are `C(D + k, k)` monomials in `k` variables of total degree `≤ D`. -/
theorem card_monomialsLE (k D : ℕ) : #(monomialsLE k D) = (D + k).choose k := by
  unfold monomialsLE
  rw [card_image_of_injOn, card_finsuppAntidiag_nat_eq_choose]
  · rw [Finset.card_univ, Fintype.card_fin, Nat.choose_symm_add.symm]
    simp [add_comm]
  · intro t ht t' ht' htt
    rw [Finset.mem_coe, mem_finsuppAntidiag] at ht ht'
    have h0 : t 0 = t' 0 := by
      have h1 := ht.1
      have h2 := ht'.1
      rw [Fin.sum_univ_succ] at h1 h2
      have : ∑ i : Fin k, t i.succ = ∑ i : Fin k, t' i.succ :=
        sum_congr rfl fun i _ => by simpa [Finsupp.tail_apply] using DFunLike.congr_fun htt i
      omega
    rw [← Finsupp.cons_tail t, ← Finsupp.cons_tail t', h0, htt]

end Monomials

section Product

variable {k : ℕ}

/-- A monomial in the support of a polynomial of total degree `≤ D` has degree `≤ D`. -/
theorem degree_le_of_mem_support {p : MvPolynomial (Fin k) ℤ} {D : ℕ}
    (hp : p.totalDegree ≤ D) {s : Fin k →₀ ℕ} (hs : s ∈ p.support) : s.degree ≤ D :=
  (le_totalDegree hs).trans hp

/-- **Coefficients of a product.** If `p` and `q` have total degree `≤ D` in `k` variables and all
their coefficients are bounded in absolute value by `A` and `B`, then every coefficient of `p · q`
is bounded by `T · A · B` where `T = C(D + k, k)` is the number of monomials of degree `≤ D`
([BGKLSW26, §4.3]). -/
theorem natAbs_coeff_mul_le {p q : MvPolynomial (Fin k) ℤ} {D A B : ℕ} (hp : p.totalDegree ≤ D)
    (hA : ∀ s, (p.coeff s).natAbs ≤ A) (hB : ∀ s, (q.coeff s).natAbs ≤ B) (u : Fin k →₀ ℕ) :
    ((p * q).coeff u).natAbs ≤ (D + k).choose k * (A * B) := by
  classical
  set S := (antidiagonal u).filter fun x => x.1 ∈ monomialsLE k D with hS
  have hsum : (p * q).coeff u = ∑ x ∈ S, p.coeff x.1 * q.coeff x.2 := by
    rw [coeff_mul, hS, sum_filter_of_ne]
    intro x _ hx
    rw [mem_monomialsLE]
    refine degree_le_of_mem_support hp (s := x.1) (mem_support_iff.2 fun h0 => hx ?_)
    rw [h0, zero_mul]
  have hcard : #S ≤ (D + k).choose k := by
    rw [← card_monomialsLE]
    refine card_le_card_of_injOn Prod.fst (fun x hx => (mem_filter.1 hx).2) ?_
    intro x hx y hy hxy
    have hx' := mem_antidiagonal.1 (mem_filter.1 hx).1
    have hy' := mem_antidiagonal.1 (mem_filter.1 hy).1
    exact Prod.ext hxy (add_left_cancel (hx'.trans (hy'.symm.trans (by rw [hxy]))))
  have hterm : ∀ x ∈ S, |p.coeff x.1 * q.coeff x.2| ≤ ((A * B : ℕ) : ℤ) := by
    intro x _
    rw [abs_mul, ← Int.natCast_natAbs, ← Int.natCast_natAbs]
    exact_mod_cast Nat.mul_le_mul (hA _) (hB _)
  have : |(p * q).coeff u| ≤ (((D + k).choose k * (A * B) : ℕ) : ℤ) :=
    calc |(p * q).coeff u| = |∑ x ∈ S, p.coeff x.1 * q.coeff x.2| := by rw [hsum]
      _ ≤ ∑ x ∈ S, |p.coeff x.1 * q.coeff x.2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ S, ((A * B : ℕ) : ℤ) := sum_le_sum hterm
      _ = #S * ((A * B : ℕ) : ℤ) := by simp
      _ ≤ (((D + k).choose k * (A * B) : ℕ) : ℤ) := by
          push_cast
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
  rw [← Int.natCast_natAbs] at this
  exact_mod_cast this

end Product

end MvPolynomial

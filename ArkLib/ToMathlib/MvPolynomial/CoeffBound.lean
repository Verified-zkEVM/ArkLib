/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.ToMathlib.Combinatorics.Enumerative.MonomialCount
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Coefficient bounds for products of integer polynomials

The fingerprinting step of BitZ ([BGKLSW26, §4.3]) needs a bound on the largest coefficient of a
product of integer polynomials. Each coefficient of `p · q` is a sum over the pairs of monomials
`(s, t)` with `s + t = u` and `s` in the support of `p`, and `s` determines `t`, so at most
`#p.support` pairs contribute. If `p` has total degree `≤ D` in `n` variables, its support lies in
`Finsupp.degreeLEFinset`, which has `T = C(D + n, n)` elements, so
`‖p · q‖∞ ≤ T · ‖p‖∞ · ‖q‖∞`.

## Main statements

* `MvPolynomial.natAbs_coeff_mul_le_card_support` bounds the coefficients of `p · q` by
  `#p.support · ‖p‖∞ · ‖q‖∞`.
* `MvPolynomial.natAbs_coeff_mul_le` is the bound `C(D + n, n) · ‖p‖∞ · ‖q‖∞` for `p` of total
  degree `≤ D`; `C(D + n, n)` is the quantity `T` of [BGKLSW26, §4.3].

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ : Type*}

/-- Every coefficient of `p · q` is bounded by `#p.support · A · B`, where `A` and `B` bound the
coefficients of `p` and `q` in absolute value. -/
theorem natAbs_coeff_mul_le_card_support {p q : MvPolynomial σ ℤ} {A B : ℕ}
    (hA : ∀ s, (p.coeff s).natAbs ≤ A) (hB : ∀ s, (q.coeff s).natAbs ≤ B) (u : σ →₀ ℕ) :
    ((p * q).coeff u).natAbs ≤ #p.support * (A * B) := by
  classical
  set S := (antidiagonal u).filter fun x => x.1 ∈ p.support
  have hsum : (p * q).coeff u = ∑ x ∈ S, p.coeff x.1 * q.coeff x.2 := by
    rw [coeff_mul, sum_filter_of_ne]
    exact fun x _ hx => mem_support_iff.2 (left_ne_zero_of_mul hx)
  have hcard : #S ≤ #p.support :=
    card_le_card_of_injOn Prod.fst (fun x hx => (mem_filter.1 hx).2) fun x hx y hy hxy =>
      Prod.ext hxy (add_left_cancel ((mem_antidiagonal.1 (mem_filter.1 hx).1).trans
        ((mem_antidiagonal.1 (mem_filter.1 hy).1).symm.trans (by rw [hxy]))))
  rw [hsum]
  calc _ ≤ ∑ x ∈ S, (p.coeff x.1 * q.coeff x.2).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _x ∈ S, A * B := sum_le_sum fun x _ => by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hA _) (hB _)
    _ = #S * (A * B) := by rw [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hcard

/-- **Coefficients of a product.** If `p` has total degree `≤ D` in `n` variables and the
coefficients of `p` and `q` are bounded in absolute value by `A` and `B`, then every coefficient
of `p · q` is bounded by `T · A · B`, where `T = C(D + n, n)` is the number of monomials of degree
`≤ D`. No degree bound on `q` is needed. -/
theorem natAbs_coeff_mul_le [Fintype σ] {p q : MvPolynomial σ ℤ} {D A B : ℕ}
    (hp : p.totalDegree ≤ D) (hA : ∀ s, (p.coeff s).natAbs ≤ A)
    (hB : ∀ s, (q.coeff s).natAbs ≤ B) (u : σ →₀ ℕ) :
    ((p * q).coeff u).natAbs ≤ (D + Fintype.card σ).choose (Fintype.card σ) * (A * B) := by
  classical
  refine (natAbs_coeff_mul_le_card_support hA hB u).trans (Nat.mul_le_mul_right _ ?_)
  rw [← Finsupp.card_degreeLEFinset σ D]
  exact card_le_card fun s hs => Finsupp.mem_degreeLEFinset.2 ((le_totalDegree hs).trans hp)

end MvPolynomial

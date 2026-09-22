/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.FrobeniusTaylor

/-!
# Recovering a polynomial from sparse coefficients

A polynomial `P` is in the image of `expand R s` exactly when its coefficients vanish outside the
multiples of `s`, and then `contract s P` is the preimage. Mathlib's `Polynomial.expand_contract`
reaches the same conclusion from `derivative P = 0` in characteristic `s`; the coefficient condition
here needs no characteristic assumption. A degree bound `P.degree < s * k` descends to
`(contract s P).degree < k`, so sparse low-degree data determine a unique low-degree preimage.
Combined with `ArkLib.ToMathlib.Polynomial.FrobeniusTaylor`, sparse Taylor coefficients at one
center recover a unique preimage under the Frobenius pullback.

## Main statements

* `Polynomial.expand_contract_eq_self_iff`: `expand R s (contract s P) = P` exactly when the
  coefficients of `P` vanish outside the multiples of `s`.
* `Polynomial.degree_contract_lt_of_degree_lt`: the degree bound descends.
* `Polynomial.existsUnique_expand_of_sparse`,
  `Polynomial.existsUnique_expand_of_sparse_taylor`: unique low-degree preimages.

## References

Ported from `ToMathlib/Polynomial/SparseContraction.lean` at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, under the same names, over commutative semirings
instead of commutative rings. The source's `expand_contract_of_sparse` is the reverse direction of
the new `expand_contract_eq_self_iff`; both no longer assume `0 < s`, and neither does
`degree_contract_lt_of_degree_lt`. `existsUnique_expand_of_sparse` assumes `s ≠ 0` instead of
`0 < s`. `existsUnique_expand_of_sparse_taylor` is unchanged apart from the renamed
`taylor_expand_expChar_pow`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommSemiring R]

/-- `P` is the pullback of its contraction exactly when its coefficients vanish outside the
multiples of `s`. For `s = 0` both sides say that `P` is constant, since `expand R 0 Q` is the
constant `Q.eval 1`. -/
theorem expand_contract_eq_self_iff (s : ℕ) (P : R[X]) :
    expand R s (contract s P) = P ↔ ∀ i : ℕ, ¬s ∣ i → P.coeff i = 0 := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [zero_dvd_iff]
    constructor
    · intro h i hi
      rw [← h, expand_zero]
      simp [coeff_C, hi]
    · intro hP
      have hC : P = C (P.coeff 0) := by
        ext i
        rcases eq_or_ne i 0 with rfl | hi
        · simp
        · simp [hP i hi, coeff_C, hi]
      rw [hC, contract_C, expand_zero, eval_C]
  constructor
  · intro h i hi
    rw [← h]
    simp [coeff_expand (Nat.pos_of_ne_zero hs), hi]
  · intro hP
    ext i
    rw [coeff_expand (Nat.pos_of_ne_zero hs)]
    split_ifs with hi
    · rw [coeff_contract hs, Nat.div_mul_cancel hi]
    · exact (hP i hi).symm

/-- Sparse support is sufficient for exact contraction, without a derivative hypothesis. -/
theorem expand_contract_of_sparse (s : ℕ) (P : R[X])
    (hP : ∀ i : ℕ, ¬s ∣ i → P.coeff i = 0) : expand R s (contract s P) = P :=
  (expand_contract_eq_self_iff s P).mpr hP

/-- A degree bound `P.degree < s * k` descends to `(contract s P).degree < k`. For `s = 0` the
bound forces `P = 0`. -/
theorem degree_contract_lt_of_degree_lt {s k : ℕ} (P : R[X]) (hP : P.degree < ↑(s * k)) :
    (contract s P).degree < ↑k := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [zero_mul, degree_lt_iff_coeff_zero] at hP
    have hP0 : P = 0 := by
      ext i
      exact hP i (Nat.zero_le i)
    subst hP0
    simp [contract]
  rw [degree_lt_iff_coeff_zero] at hP ⊢
  intro i hi
  rw [coeff_contract hs]
  apply hP
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left s hi

/-- Sparse data of degree below `s * k` have a unique preimage of degree below `k` under
`expand R s`. The hypothesis `s ≠ 0` is needed: `expand R 0 Q = C (Q.eval 1)` is not injective,
so for `P = 0` and `k = 2` both `0` and `X - 1` over `ℤ` are preimages. -/
theorem existsUnique_expand_of_sparse {s k : ℕ} (hs : s ≠ 0) (P : R[X])
    (hsparse : ∀ i : ℕ, ¬s ∣ i → P.coeff i = 0) (hdegree : P.degree < ↑(s * k)) :
    ∃! Q : R[X], Q.degree < ↑k ∧ expand R s Q = P := by
  refine ⟨contract s P, ⟨degree_contract_lt_of_degree_lt P hdegree,
    expand_contract_of_sparse s P hsparse⟩, ?_⟩
  intro Q hQ
  apply expand_injective (Nat.pos_of_ne_zero hs)
  exact hQ.2.trans (expand_contract_of_sparse s P hsparse).symm

/-- In exponential characteristic `p`, if the Taylor coefficients of `P` at `t` vanish outside
the multiples of `p ^ e` and `P.degree < p ^ e * k`, then `P` has a unique preimage of degree
below `k` under `expand R (p ^ e)`. It is the contraction of `taylor t P`, translated back by
`-(t ^ (p ^ e))`, so `R` must be a ring. -/
theorem existsUnique_expand_of_sparse_taylor {R : Type*} [CommRing R] (p e k : ℕ) [ExpChar R p]
    (P : R[X]) (t : R) (hsparse : ∀ i : ℕ, ¬p ^ e ∣ i → (taylor t P).coeff i = 0)
    (hdegree : P.degree < ↑(p ^ e * k)) :
    ∃! Q : R[X], Q.degree < ↑k ∧ expand R (p ^ e) Q = P := by
  have hs : p ^ e ≠ 0 := (pow_pos (expChar_pos R p) e).ne'
  obtain ⟨Q, ⟨hQdegree, hQ⟩, _⟩ := existsUnique_expand_of_sparse hs (taylor t P)
    hsparse (by simpa only [degree_taylor] using hdegree)
  refine ⟨taylor (-(t ^ (p ^ e))) Q, ⟨?_, ?_⟩, ?_⟩
  · simpa only [degree_taylor] using hQdegree
  · apply taylor_injective t
    rw [taylor_expand_expChar_pow, taylor_taylor]
    simpa only [add_neg_cancel, taylor_zero] using hQ
  · intro Q' hQ'
    apply expand_injective (Nat.pos_of_ne_zero hs)
    apply taylor_injective t
    rw [hQ'.2, taylor_expand_expChar_pow, taylor_taylor]
    simpa only [add_neg_cancel, taylor_zero] using hQ.symm

end Polynomial

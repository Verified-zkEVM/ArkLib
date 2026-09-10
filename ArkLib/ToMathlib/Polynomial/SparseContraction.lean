/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Polynomial.FrobeniusTaylor

/-!
# Recovering a polynomial from sparse coefficients

Contraction recovers the lower-degree polynomial when all coefficients outside multiples
of a positive integer vanish. This is the coefficient-level reconstruction used after a
Frobenius pullback; it requires no characteristic assumption.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Sparse support is sufficient for exact contraction, without a derivative hypothesis. -/
theorem expand_contract_of_sparse {s : ℕ} (hs : 0 < s) (P : R[X])
    (hP : ∀ i : ℕ, ¬ s ∣ i → P.coeff i = 0) :
    expand R s (contract s P) = P := by
  ext i
  rw [coeff_expand hs]
  split_ifs with hi
  · rw [coeff_contract (Nat.ne_of_gt hs), Nat.div_mul_cancel hi]
  · exact (hP i hi).symm

/-- A cutoff at `s*k` descends to a cutoff at `k` for the contracted polynomial. -/
theorem degree_contract_lt_of_degree_lt {s k : ℕ} (hs : 0 < s) (P : R[X])
    (hP : P.degree < ↑(s * k)) : (contract s P).degree < ↑k := by
  rw [degree_lt_iff_coeff_zero] at hP ⊢
  intro i hi
  rw [coeff_contract (Nat.ne_of_gt hs)]
  apply hP
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left s hi

/-- Sparse low-degree data determine a unique polynomial before expansion. -/
theorem existsUnique_expand_of_sparse {s k : ℕ} (hs : 0 < s) (P : R[X])
    (hsparse : ∀ i : ℕ, ¬ s ∣ i → P.coeff i = 0)
    (hdegree : P.degree < ↑(s * k)) :
    ∃! Q : R[X], Q.degree < ↑k ∧ expand R s Q = P := by
  refine ⟨contract s P, ⟨degree_contract_lt_of_degree_lt hs P hdegree,
    expand_contract_of_sparse hs P hsparse⟩, ?_⟩
  intro Q hQ
  apply expand_injective hs
  exact hQ.2.trans (expand_contract_of_sparse hs P hsparse).symm

/-- Sparse Taylor coefficients at one pulled center recover a unique polynomial in the
original variable, with the original degree bound. -/
theorem existsUnique_expand_of_sparse_taylor (p e k : ℕ) [ExpChar R p]
    (P : R[X]) (t : R)
    (hsparse : ∀ i : ℕ, ¬ p ^ e ∣ i → (taylor t P).coeff i = 0)
    (hdegree : P.degree < ↑(p ^ e * k)) :
    ∃! Q : R[X], Q.degree < ↑k ∧ expand R (p ^ e) Q = P := by
  have hs : 0 < p ^ e := pow_pos (expChar_pos R p) e
  obtain ⟨Q, ⟨hQdegree, hQ⟩, _⟩ := existsUnique_expand_of_sparse hs (taylor t P)
    hsparse (by simpa only [degree_taylor] using hdegree)
  refine ⟨taylor (-(t ^ (p ^ e))) Q, ⟨?_, ?_⟩, ?_⟩
  · simpa only [degree_taylor] using hQdegree
  · apply taylor_injective t
    rw [taylor_expand_primePow, taylor_taylor]
    simpa only [add_neg_cancel, taylor_zero] using hQ
  · intro Q' hQ'
    apply expand_injective hs
    apply taylor_injective t
    rw [hQ'.2, taylor_expand_primePow, taylor_taylor]
    simpa only [add_neg_cancel, taylor_zero] using hQ.symm

end Polynomial

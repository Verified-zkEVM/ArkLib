/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality
import ArkLib.Data.Lattices.CyclotomicRing.Norms

/-!
# The Norm Bound `‖ψ(a)‖∞ ≤ 2β` (Hachi §3, Lemma 6)

Hachi [NOZ26, §3, Lemma 6]: if `a` is a vector over `R_q^H` with `‖a‖∞ ≤ β` and `ψ` is
the packing map of Theorem 2 (Eq. 8), then `‖ψ(a)‖∞ ≤ 2β`.

The paper derives this "directly from the explicit formula in Equation (9), where some
coefficients of `ψ(a)` are equal to the sum of two coefficients of `a`". Concretely: every
entry `a_j ∈ R_q^H` is supported on the coefficient positions `(d/2k)·s` (Eq. 7,
`fixedSubring_coeff_eq_zero`), the packing exponents `packExp j` of distinct summands of `ψ(a)`
are congruent to `j` modulo `d/2k` (`packExp_mod_eq`), and at most two indices `j` share a given
residue class (`eq_or_eq_of_mod_eq`). Hence each coefficient of `ψ(a)` receives contributions
(with signs, from the `X^d = -1` folding, `Xpow_mul_coeff`) from **at most two** coefficients of
the entries of `a` — one from the first half and one from the second — which gives the factor `2`
(`coeff_psi_abs_le_two_vecCInfNorm`).

Norms are the centered coefficient norms of `Norms.lean` with the balanced representative
`zmodCenteredView` (`ZMod.valMinAbs`, the paper's `mod± q` convention); `‖a‖∞` is the
entrywise maximum `vecCInfNorm`, matching the vector norm of [NOZ26, §2.1].

## Main statement

* `cInfNorm_psi_le` — **Lemma 6**.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- **Vanishing outside the matching residue classes.** If `j`'s index does not match `p`'s
residue class mod `d/2k`, the `p`-th coefficient of the `j`-th packed summand `a_j · X^{packExp j}`
is `0`. Combined with `packExp_mod_eq` and the support of fixed elements
(`fixedSubring_coeff_eq_zero`), only summands whose index agrees with `p` mod `d/2k` can
contribute to `(ψ(a)).coeff p`. -/
theorem psi_summand_coeff_eq_zero_of_ne_mod (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) (a : Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
    {p : ℕ} (hp : p < 2 ^ α) (j : Fin (2 ^ α / 2 ^ κ))
    (hne : p % 2 ^ (α - κ - 1) ≠ (j : ℕ) % 2 ^ (α - κ - 1)) :
    ((a j : Rq (powTwoCyclotomic (R := ZMod q) α))
      * Xpow (powTwoCyclotomic α) (packExp α (2 ^ κ) (j : ℕ))).1.coeff p = 0 := by
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  rw [Xpow_mul_coeff α (packExp α (2 ^ κ) (j : ℕ)) (packExp_lt α κ hk j)
    (a j : Rq (powTwoCyclotomic (R := ZMod q) α)) hp]
  split_ifs with hle
  · apply fixedSubring_coeff_eq_zero q α κ h2 hk (a j) (by omega)
    intro hdvd
    apply hne
    have hmeq : packExp α (2 ^ κ) (j : ℕ) % 2 ^ (α - κ - 1) = p % 2 ^ (α - κ - 1) :=
      (Nat.modEq_iff_dvd' hle).mpr hdvd
    rw [packExp_mod_eq α κ hk j] at hmeq; omega
  · rw [fixedSubring_coeff_eq_zero q α κ h2 hk (a j) (by omega) (by
      intro hdvd
      apply hne
      have hle2 : packExp α (2 ^ κ) (j : ℕ) ≤ p + 2 ^ α := by
        have := packExp_lt α κ hk j; omega
      have hmeq : packExp α (2 ^ κ) (j : ℕ) % 2 ^ (α - κ - 1)
          = (p + 2 ^ α) % 2 ^ (α - κ - 1) := (Nat.modEq_iff_dvd' hle2).mpr hdvd
      have h2z : (2 : ℕ) ^ α % 2 ^ (α - κ - 1) = 0 := by
        rw [show (2 : ℕ) ^ α = 2 ^ (α - κ - 1) * 2 ^ (κ + 1) from by
          rw [← pow_add]; congr 1; omega, Nat.mul_mod_right]
      rw [packExp_mod_eq α κ hk j, Nat.add_mod, h2z, Nat.add_zero, Nat.mod_mod] at hmeq
      omega),
      neg_zero]

/-- **Main combinatorial bound (at most two contributions per position).** For `p < d`, the
`p`-th coefficient of `ψ(a)` is `± c₁ ± c₂` where `c₁`, `c₂` are coefficients of the (at most two)
entries of `a` whose index matches `p`'s residue class mod `d/2k` (`j₁ := p mod d/2k` from the
first half, `j₂ := d/2k + p mod d/2k` from the second); all other summands vanish
(`psi_summand_coeff_eq_zero_of_ne_mod`). The bound then follows from the balanced-representative
triangle inequality (`ZMod.natAbs_valMinAbs_add_le` / `_neg`). -/
theorem coeff_psi_abs_le_two_vecCInfNorm (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) {β : ℕ}
    (a : Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
    (ha : (zmodCenteredView q).vecCInfNorm
      (fun i => ((a i : Rq (powTwoCyclotomic (R := ZMod q) α))).1) ≤ β)
    {p : ℕ} (hp : p < 2 ^ α) :
    (ZMod.valMinAbs ((psi α (2 ^ κ) a).1.coeff p)).natAbs ≤ 2 * β := by
  have hM0 : 0 < 2 ^ (α - κ - 1) := by positivity
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hN : 2 ^ α / 2 ^ κ = 2 * 2 ^ (α - κ - 1) := by
    have hfac : (2 : ℕ) ^ κ * (2 * 2 ^ (α - κ - 1)) = 2 ^ α := by
      rw [← Nat.mul_assoc, show (2 : ℕ) ^ κ * 2 = 2 ^ (κ + 1) from by rw [pow_succ], ← pow_add]
      congr 1; omega
    rw [← hfac, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ κ)]
  have hbound : ∀ (i : Fin (2 ^ α / 2 ^ κ)) (pos : ℕ),
      (ZMod.valMinAbs ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1.coeff pos)).natAbs ≤ β := by
    intro i pos
    have hv := ha
    rw [CenteredCoeffView.vecCInfNorm] at hv
    have hi : (Finset.range ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1).size).sup
        ((zmodCenteredView q).absCoeff (a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1) ≤ β := by
      rw [← CenteredCoeffView.cInfNorm]
      exact le_trans (Finset.le_sup (f := fun i => (zmodCenteredView q).cInfNorm
        ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1)) (Finset.mem_univ i)) hv
    by_cases hpos : pos < ((a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1).size
    · exact le_trans (Finset.le_sup (f := (zmodCenteredView q).absCoeff
        (a i : Rq (powTwoCyclotomic (R := ZMod q) α)).1) (Finset.mem_range.mpr hpos)) hi
    · rw [CompPoly.CPolynomial.coeff_eq_zero_of_size_le _ (by omega), ZMod.valMinAbs_zero]
      exact Nat.zero_le _
  have hr : p % 2 ^ (α - κ - 1) < 2 ^ (α - κ - 1) := Nat.mod_lt _ hM0
  set j₁ : Fin (2 ^ α / 2 ^ κ) := ⟨p % 2 ^ (α - κ - 1), by omega⟩ with hj1
  set j₂ : Fin (2 ^ α / 2 ^ κ) := ⟨2 ^ (α - κ - 1) + p % 2 ^ (α - κ - 1), by omega⟩ with hj2
  set t : Fin (2 ^ α / 2 ^ κ) → ZMod q := fun j =>
    ((a j : Rq (powTwoCyclotomic (R := ZMod q) α))
      * Xpow (powTwoCyclotomic α) (packExp α (2 ^ κ) (j : ℕ))).1.coeff p with ht_def
  have hsum : (psi α (2 ^ κ) a).1.coeff p = ∑ j, t j := by
    unfold psi; rw [← Rq.coeffHom_apply, map_sum]; simp only [ht_def, Rq.coeffHom_apply]
  have hjne : j₁ ≠ j₂ := by simp only [hj1, hj2, Ne, Fin.mk.injEq]; omega
  have hwit : ∀ j : Fin (2 ^ α / 2 ^ κ),
      p % 2 ^ (α - κ - 1) = (j : ℕ) % 2 ^ (α - κ - 1) → j = j₁ ∨ j = j₂ := by
    intro j heq
    rcases eq_or_eq_of_mod_eq α κ hk j heq.symm with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  have hzero : ∀ j : Fin (2 ^ α / 2 ^ κ), j ∉ ({j₁, j₂} : Finset _) → t j = 0 := by
    intro j hj
    have hnotwit : p % 2 ^ (α - κ - 1) ≠ (j : ℕ) % 2 ^ (α - κ - 1) := by
      intro heq
      rcases hwit j heq with h | h <;> exact hj (by rw [h]; simp)
    simp only [ht_def]
    exact psi_summand_coeff_eq_zero_of_ne_mod q α κ h2 hk a hp j hnotwit
  have ht_bound : ∀ j, (ZMod.valMinAbs (t j)).natAbs ≤ β := by
    intro j
    simp only [ht_def]
    rw [Xpow_mul_coeff α (packExp α (2 ^ κ) (j : ℕ)) (packExp_lt α κ hk j)
      (a j : Rq (powTwoCyclotomic (R := ZMod q) α)) hp]
    split_ifs
    · exact hbound j _
    · rw [ZMod.natAbs_valMinAbs_neg]; exact hbound j _
  have hpair : (psi α (2 ^ κ) a).1.coeff p = t j₁ + t j₂ := by
    rw [hsum, ← Finset.sum_subset (Finset.subset_univ {j₁, j₂}) (fun j _ hj => hzero j hj),
      Finset.sum_pair hjne]
  rw [hpair]
  calc (ZMod.valMinAbs (t j₁ + t j₂)).natAbs
      ≤ (ZMod.valMinAbs (t j₁) + ZMod.valMinAbs (t j₂)).natAbs :=
        ZMod.natAbs_valMinAbs_add_le _ _
    _ ≤ (ZMod.valMinAbs (t j₁)).natAbs + (ZMod.valMinAbs (t j₂)).natAbs := Int.natAbs_add_le _ _
    _ ≤ β + β := Nat.add_le_add (ht_bound j₁) (ht_bound j₂)
    _ = 2 * β := by ring

/-- **Hachi [NOZ26, §3, Lemma 6]: `‖ψ(a)‖∞ ≤ 2β`.** If every entry of the vector
`a : (R_q^H)^{d/k}` has centered coefficient `ℓ∞`-norm at most `β` (i.e. `‖a‖∞ ≤ β` in the
`mod± q` convention of [NOZ26, §2.1]), then the packed ring element `ψ(a) ∈ R_q` satisfies
`‖ψ(a)‖∞ ≤ 2β`.

The hypotheses are the standing assumptions of [NOZ26, §3]: `k = 2^κ` divides `d/2`
(`2·2^κ ∣ 2^α`) and `q` is odd (`(2 : ZMod q) ≠ 0`; the paper assumes `q ≡ 5 (mod 8)`, of
which only oddness is needed here). -/
theorem cInfNorm_psi_le (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) {β : ℕ}
    (a : Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
    (ha : (zmodCenteredView q).vecCInfNorm
      (fun i => ((a i : Rq (powTwoCyclotomic (R := ZMod q) α))).1) ≤ β) :
    (zmodCenteredView q).cInfNorm (psi α (2 ^ κ) a).1 ≤ 2 * β := by
  rw [CenteredCoeffView.cInfNorm]
  apply Finset.sup_le
  intro p _
  change (ZMod.valMinAbs ((psi α (2 ^ κ) a).1.coeff p)).natAbs ≤ 2 * β
  by_cases hp : p < 2 ^ α
  · exact coeff_psi_abs_le_two_vecCInfNorm q α κ h2 hk a ha hp
  · rw [coeff_eq_zero_of_le α (psi α (2 ^ κ) a) (by omega), ZMod.valMinAbs_zero]
    exact Nat.zero_le _

end ArkLib.Lattices.CyclotomicModulus

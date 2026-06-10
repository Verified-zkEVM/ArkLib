/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.LsCore
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Lyubashevsky–Seiler: Short Elements Are Invertible

The Lyubashevsky–Seiler invertibility result [LS18, Corollary 1.2]; recalled as Lemma 3 of
the Hachi paper [NOZ26]: over the power-of-two cyclotomic modulus `φ = X^{2^α} + 1`
(`powTwoCyclotomic α`) with a prime `q ≡ 5 (mod 8)`, a nonzero element of
`Rq (powTwoCyclotomic α) = ZMod q[X]/(X^{2^α}+1)` whose centered Euclidean norm is below
`√q` is a unit.

The statement is deliberately pinned to `powTwoCyclotomic α` (`X^{2^α}+1`): LS18 Cor. 1.2
is the `k = 2` splitting case (`q ≡ 2·2+1 ≡ 5 (mod 8)`, Euclidean bound `q^{1/2} = √q`),
and that splitting / minimum-distance analysis is specific to the negacyclic ring. For a
general cyclotomic `Φ_m` of power-of-two *degree* (e.g. `Φ₁₅`, `Φ₁₂`) the `q ≡ 5 (mod 8)`
condition and the `√q` bound are simply wrong, so phrasing the lemma for an arbitrary
`Φ` with `deg φ = 2^α` would be unsound.

This is one of the two unproven lemmas for the Greyhound [NS24] / Hachi [NOZ26]
weak-binding argument; the other is `scalarVecMul_mul_l2NormSq_le` in
`NormBounds.MicciancioYoung`.

## Overview

Write `n := 2^α`. The argument is the `k = 2` splitting case and reduces to an elementary
`mod q` divisibility count, needing no ideal lattices, canonical embedding, or Minkowski bound.

Since `q ≡ 5 (mod 8)`, `-1` is a square in `ZMod q` (`ZMod.exists_sq_eq_neg_one_iff`), say
`r^2 = -1`, and the negacyclic modulus splits as `X^n + 1 = (X^{n/2} - r)(X^{n/2} + r)`. Both
factors are irreducible over `ZMod q`: the multiplicative order of `q` modulo `2^{α+1}` is
`2^{α-1}` (lifting-the-exponent, `v₂(q^{2^k} - 1) = k + 2`), so every irreducible factor of
`cyclotomic (2^{α+1}) (ZMod q) = X^n + 1` has degree `n/2`, which forces each degree-`n/2`
factor to be irreducible.

A non-unit `c` is therefore not coprime to `X^n + 1`, so one factor `g = X^{n/2} - s`
(`s = ±r`, `s^2 = -1`) divides its lift `c̃`; evaluating at a root `ζ` of `g` (so
`ζ^{n/2} = s`) gives `c̃(ζ) = Σ_{j<n/2} (c̃_j + s·c̃_{n/2+j}) ζ^j = 0`. As `1, …, ζ^{n/2-1}`
are independent over `ZMod q`, each `c̃_j + s·c̃_{n/2+j} = 0`, and squaring (`s^2 = -1`) gives
`q ∣ (c̃_j² + c̃_{n/2+j}²)` over `ℤ`. Summing, `q ∣ ‖c‖₂²`. With `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q` this
forces `‖c‖₂² = 0`, hence `c = 0`, contradicting `‖c‖₁ > 0`. (Edge case `α = 0`: `Rq` is a
field, so a nonzero element is a unit.)

The supporting lemmas live in `NormBounds.LsCore` (the iso `Rq.equivQuotient`, the order
computation `orderOf_q_mod_two_pow`, the irreducibility `irreducible_X_pow_sub_C_r`, and the
coefficient kernel `dvd_sq_add_sq`); the splitting and `√-1` existence are
`powTwoCyclotomic_splits_of_sq_eq_neg_one` and `exists_sq_eq_neg_one_of_mod_eight_eq_five`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The power-of-two ("Hachi") cyclotomic modulus `X^{2^α}+1` over `ZMod q`. -/
local notation "Φ" => (powTwoCyclotomic (R := ZMod q) α)

omit [NeZero q] in
/-- **Norm bridge.** The centered squared `ℓ₂` norm is at most the square of the
centered `ℓ₁` norm: `‖c‖₂² ≤ ‖c‖₁²`. This is `Σ aₖ² ≤ (Σ aₖ)²` for nonnegative `aₖ`. -/
theorem Rq.l2NormSq_le_l1Norm_sq (c : Rq Φ) :
    Rq.l2NormSq Φ c ≤ (Rq.l1Norm Φ c) ^ 2 := by
  unfold Rq.l2NormSq Rq.l1Norm
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ ↦ Nat.zero_le _)

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- For a prime `q ≡ 5 (mod 8)` we have `q % 4 = 1 ≠ 3`, so `-1` is a square in `ZMod q`
(`ZMod.exists_sq_eq_neg_one_iff`). This `r` (`r² = -1`) drives the explicit splitting. -/
theorem exists_sq_eq_neg_one_of_mod_eight_eq_five (hq5 : q % 8 = 5) :
    ∃ r : ZMod q, r ^ 2 = -1 := by
  have h4 : q % 4 ≠ 3 := by omega
  obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := q)).mpr h4
  exact ⟨r, by rw [sq]; exact hr.symm⟩

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
open Polynomial in
/-- **Splitting into explicit factors.** Over `ZMod q`, given `r² = -1`, the negacyclic
modulus `X^{2^α}+1` factors as `(X^{2^{α-1}} - r)·(X^{2^{α-1}} + r)` for `α ≥ 1`. These are
the two degree-`2^{α-1}` pieces of the LS `k = 2` splitting; over `q ≡ 5 (mod 8)` they are
irreducible (the order-of-`q` argument), which is what makes the CRT factors fields. -/
theorem powTwoCyclotomic_splits_of_sq_eq_neg_one {r : ZMod q} (hr : r ^ 2 = -1) (hα : 1 ≤ α) :
    (X ^ (2 ^ (α - 1)) - C r) * (X ^ (2 ^ (α - 1)) + C r) = (X : (ZMod q)[X]) ^ (2 ^ α) + 1 := by
  have hm : 2 ^ (α - 1) * 2 = 2 ^ α := by rw [← pow_succ]; congr 1; omega
  have hCr : (C r) ^ 2 = (-1 : (ZMod q)[X]) := by rw [← C_pow, hr, C_neg, C_1]
  calc (X ^ (2 ^ (α - 1)) - C r) * (X ^ (2 ^ (α - 1)) + C r)
      = (X ^ (2 ^ (α - 1))) ^ 2 - (C r) ^ 2 := by ring
    _ = X ^ (2 ^ α) - (-1) := by rw [hCr, ← pow_mul, hm]
    _ = X ^ (2 ^ α) + 1 := by ring

omit [NeZero q] in
open Polynomial in
/-- `(powTwoCyclotomic α).φ.toPoly = X^(2^α) + 1`. -/
theorem phi_toPoly :
    (powTwoCyclotomic (R := ZMod q) α).φ.toPoly = X ^ (2 ^ α) + 1 := by
  change (CompPoly.CPolynomial.X ^ (2 ^ α) + 1 : CompPoly.CPolynomial (ZMod q)).toPoly = _
  rw [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.toPoly_X, CompPoly.CPolynomial.toPoly_one]

omit [NeZero q] in
open Polynomial in
/-- `(powTwoCyclotomic α).φ.natDegree = 2^α`. -/
theorem phi_natDegree :
    (powTwoCyclotomic (R := ZMod q) α).φ.natDegree = 2 ^ α := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, phi_toPoly]
  compute_degree!

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
open Polynomial in
/-- If `a` is coprime to `f` then `Ideal.Quotient.mk (span {f}) a` is a unit. -/
theorem isUnit_mk_of_isCoprime {a f : (ZMod q)[X]} (h : IsCoprime a f) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a) := by
  obtain ⟨u, v, huv⟩ := h
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (Ideal.span {f}) u) ?_
  have hf : Ideal.Quotient.mk (Ideal.span {f}) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  have hkey := congrArg (Ideal.Quotient.mk (Ideal.span {f})) huv
  rw [map_add, map_mul, map_mul, hf, mul_zero, add_zero, map_one] at hkey
  rw [mul_comm]; exact hkey

set_option maxHeartbeats 1600000 in
-- This combined assembly proof exceeds the default heartbeat budget.
omit [NeZero q] in
open Polynomial in
/-- **Algebraic core.** If `c : Rq Φ` over `q ≡ 5 (mod 8)` is *not* a unit,
then `q` divides its centered squared `ℓ₂` norm. A non-unit's image in
`(ZMod q)[X]/(X^{2^α}+1)` is non-coprime to the modulus, so an irreducible factor
`φᵢ = X^{2^{α-1}} ∓ r` of `X^{2^α}+1` (`powTwoCyclotomic_splits_of_sq_eq_neg_one`,
`irreducible_X_pow_sub_C_r`) divides its lift; evaluating at the root `ζ` of `AdjoinRoot φᵢ`
(`ζ^{2^{α-1}} = ±r`, `s² = -1`) and using the degree-`2^{α-1}` independence of
`1,…,ζ^{2^{α-1}-1}` (`dvd_sq_add_sq`) gives `q ∣ (c̃_j² + c̃_{2^{α-1}+j}²)` per `j`; summing
yields `q ∣ ‖c‖₂²`. Edge case `α = 0`: `Rq Φ` is a field, so a non-unit is `0`. -/
theorem q_dvd_l2NormSq_of_not_isUnit (hq5 : q % 8 = 5) {c : Rq Φ} (hc : ¬ IsUnit c) :
    (q : ℤ) ∣ (Rq.l2NormSq Φ c : ℤ) := by
  rcases Nat.eq_zero_or_pos α with hα0 | hαpos
  · -- α = 0: `φ.toPoly = X + 1` irreducible, so `Rq Φ` is a field; a non-unit is `0`.
    subst hα0
    have hφ : (powTwoCyclotomic (R := ZMod q) 0).φ.toPoly = X + 1 := by
      rw [phi_toPoly]; norm_num
    have hirr : Irreducible ((powTwoCyclotomic (R := ZMod q) 0).φ.toPoly) := by
      rw [hφ, show (X + 1 : (ZMod q)[X]) = X - C (-1) by rw [C_neg, C_1, sub_neg_eq_add]]
      exact irreducible_X_sub_C (-1)
    haveI hfact : Fact (Irreducible ((powTwoCyclotomic (R := ZMod q) 0).φ.toPoly)) := ⟨hirr⟩
    haveI hmax : ((powTwoCyclotomic (R := ZMod q) 0).modIdeal).IsMaximal := by
      rw [modIdeal]; exact PrincipalIdealRing.isMaximal_of_irreducible hirr
    have hisfield : IsField ((powTwoCyclotomic (R := ZMod q) 0).CyclotomicRing) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax
    have hnu := Rq.not_isUnit_toQuotientHom_of_not_isUnit
      (powTwoCyclotomic (R := ZMod q) 0) hc
    have hz : Rq.toQuotientHom (powTwoCyclotomic (R := ZMod q) 0) c = 0 := by
      by_contra hne
      obtain ⟨b, hb⟩ := hisfield.mul_inv_cancel hne
      exact hnu (IsUnit.of_mul_eq_one b hb)
    have hc0 : c = 0 := by
      have hmap : Rq.toQuotientHom (powTwoCyclotomic (R := ZMod q) 0) c
          = Rq.toQuotientHom (powTwoCyclotomic (R := ZMod q) 0) 0 := by
        rw [hz, map_zero]
      exact Rq.toQuotient_injective (powTwoCyclotomic (R := ZMod q) 0) hmap
    rw [hc0]
    have hzero : Rq.l2NormSq (powTwoCyclotomic (R := ZMod q) 0) (0 : Rq _) = 0 := by
      unfold Rq.l2NormSq
      refine Finset.sum_eq_zero (fun k _ ↦ ?_)
      rw [Rq.zero_val, CompPoly.CPolynomial.coeff_zero, ZMod.valMinAbs_zero, Int.natAbs_zero]
      norm_num
    rw [hzero]; norm_num
  · have hα : 1 ≤ α := hαpos
    obtain ⟨r, hr⟩ := exists_sq_eq_neg_one_of_mod_eight_eq_five (q := q) hq5
    set g1 : (ZMod q)[X] := X ^ (2 ^ (α - 1)) - C r with hg1
    set g2 : (ZMod q)[X] := X ^ (2 ^ (α - 1)) + C r with hg2
    set ct : (ZMod q)[X] := c.1.toPoly with hct
    have hmul : g1 * g2 = (powTwoCyclotomic (R := ZMod q) α).φ.toPoly := by
      rw [hg1, hg2, powTwoCyclotomic_splits_of_sq_eq_neg_one α hr hα, phi_toPoly]
    have hirr1 : Irreducible g1 := by
      rw [hg1]
      apply irreducible_X_pow_sub_C_r α hq5 hα r hr
      convert orderOf_q_mod_two_pow hq5 α hα using 2
    -- `g2 = X^{2^{α-1}} - C (-r)` with `(-r)² = -1`, reusing the same factor lemma for `-r`.
    have hrr : (-r) ^ 2 = -1 := by rw [neg_pow]; simp [hr]
    have hg2eq : g2 = X ^ (2 ^ (α - 1)) - C (-r) := by rw [hg2, C_neg, sub_neg_eq_add]
    have hirr2 : Irreducible g2 := by
      rw [hg2eq]
      apply irreducible_X_pow_sub_C_r α hq5 hα (-r) hrr
      convert orderOf_q_mod_two_pow hq5 α hα using 2
    have hnu : ¬ IsUnit (Ideal.Quotient.mk
        (Ideal.span {(powTwoCyclotomic (R := ZMod q) α).φ.toPoly}) ct) := by
      have hh := Rq.not_isUnit_toQuotientHom_of_not_isUnit
        (powTwoCyclotomic (R := ZMod q) α) hc
      rw [Rq.toQuotientHom] at hh
      simpa only [Rq.toQuotient, quotientHom_apply, modIdeal, hct] using hh
    have hdvd : g1 ∣ ct ∨ g2 ∣ ct := by
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨hd1, hd2⟩ := hcon
      have hcop1 : IsCoprime ct g1 := (hirr1.coprime_iff_not_dvd.mpr hd1).symm
      have hcop2 : IsCoprime ct g2 := (hirr2.coprime_iff_not_dvd.mpr hd2).symm
      have hcop : IsCoprime ct ((powTwoCyclotomic (R := ZMod q) α).φ.toPoly) := by
        rw [← hmul]; exact hcop1.mul_right hcop2
      exact hnu (isUnit_mk_of_isCoprime hcop)
    have finish : ∀ (g : (ZMod q)[X]) (s : ZMod q),
        Irreducible g → g = X ^ (2 ^ (α - 1)) - C s → s ^ 2 = -1 → g ∣ ct →
        (q : ℤ) ∣ (Rq.l2NormSq Φ c : ℤ) := by
      intro g s hirr hgeq hs hdvdg
      haveI : Fact (Irreducible g) := ⟨hirr⟩
      have hgmonic : g.Monic := by rw [hgeq]; exact monic_X_pow_sub_C s (by positivity)
      have hgnd : g.natDegree = 2 ^ (α - 1) := by rw [hgeq, natDegree_X_pow_sub_C]
      let F := AdjoinRoot g
      let ζ : F := AdjoinRoot.root g
      have hroot : (Polynomial.aeval ζ) g = 0 := by
        change (Polynomial.aeval (AdjoinRoot.root g)) g = 0
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have hζ : ζ ^ (2 ^ (α - 1)) = algebraMap (ZMod q) F s := by
        have h0 : (Polynomial.aeval ζ) (X ^ (2 ^ (α - 1)) - C s) = 0 := by
          rw [← hgeq]; exact hroot
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h0
        linear_combination h0
      have hctdeg : ct.natDegree < 2 ^ α := by
        have hlt : ct.degree < (powTwoCyclotomic (R := ZMod q) α).φ.toPoly.degree :=
          (powTwoCyclotomic (R := ZMod q) α).degree_toPoly_lt_of_reduced c.2
        rw [phi_toPoly] at hlt
        have hnd : ((X : (ZMod q)[X]) ^ (2 ^ α) + 1).natDegree = 2 ^ α := by compute_degree!
        have hφne : ((X : (ZMod q)[X]) ^ (2 ^ α) + 1) ≠ 0 := by
          intro h; rw [h, natDegree_zero] at hnd; exact absurd hnd.symm (by positivity)
        by_cases hctz : ct = 0
        · rw [hctz, natDegree_zero]; positivity
        · rw [Polynomial.degree_eq_natDegree hctz,
            Polynomial.degree_eq_natDegree hφne, hnd] at hlt
          exact_mod_cast hlt
      have hmkzero : AdjoinRoot.mk g ct = 0 := AdjoinRoot.mk_eq_zero.mpr hdvdg
      have hsum : ∑ k ∈ Finset.range (2 ^ α),
          algebraMap (ZMod q) F (ct.coeff k) * ζ ^ k = 0 := by
        have he : (Polynomial.aeval ζ) ct = AdjoinRoot.mk g ct := by
          change (Polynomial.aeval (AdjoinRoot.root g)) ct = AdjoinRoot.mk g ct
          rw [AdjoinRoot.aeval_eq]
        rw [Polynomial.aeval_eq_sum_range' hctdeg] at he
        rw [hmkzero] at he
        rw [← he]
        apply Finset.sum_congr rfl
        intro k _; rw [Algebra.smul_def]
      have hindep : LinearIndependent (ZMod q)
          (fun i : Fin (2 ^ (α - 1)) ↦ ζ ^ (i : ℕ)) := by
        have hli := (AdjoinRoot.powerBasis' hgmonic).basis.linearIndependent
        have hbpow : ⇑(AdjoinRoot.powerBasis' hgmonic).basis
            = fun i : Fin (AdjoinRoot.powerBasis' hgmonic).dim ↦
              (AdjoinRoot.powerBasis' hgmonic).gen ^ (i : ℕ) :=
          (AdjoinRoot.powerBasis' hgmonic).coe_basis
        rw [hbpow] at hli
        have hdim : (AdjoinRoot.powerBasis' hgmonic).dim = 2 ^ (α - 1) := hgnd
        rw [hdim] at hli
        exact hli
      set a : ℕ → ZMod q := fun k ↦ ct.coeff k with ha
      have hcoeff_eq : ∀ k, c.1.coeff k = a k := by
        intro k; rw [ha, hct, CompPoly.CPolynomial.coeff_toPoly]
      have hdvdj : ∀ j, j < 2 ^ (α - 1) →
          (q : ℤ) ∣ ((a j).valMinAbs ^ 2 + (a (2 ^ (α - 1) + j)).valMinAbs ^ 2) := by
        intro j hj
        exact dvd_sq_add_sq α hα ζ s hζ hs hindep a hsum j hj
      have hsumeq : (Rq.l2NormSq Φ c : ℤ)
          = ∑ k ∈ Finset.range (2 ^ α), ((c.1.coeff k).valMinAbs ^ 2 : ℤ) := by
        unfold Rq.l2NormSq
        rw [phi_natDegree, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        rw [sq_abs]
      have hpow : 2 ^ α = 2 ^ (α - 1) + 2 ^ (α - 1) := by
        rw [← two_mul, ← pow_succ']; congr 1; omega
      rw [hsumeq, hpow, Finset.sum_range_add]
      have hpair : (∑ j ∈ Finset.range (2 ^ (α - 1)), ((c.1.coeff j).valMinAbs ^ 2 : ℤ))
          + ∑ j ∈ Finset.range (2 ^ (α - 1)),
              ((c.1.coeff (2 ^ (α - 1) + j)).valMinAbs ^ 2 : ℤ)
          = ∑ j ∈ Finset.range (2 ^ (α - 1)),
              ((c.1.coeff j).valMinAbs ^ 2
                + (c.1.coeff (2 ^ (α - 1) + j)).valMinAbs ^ 2 : ℤ) := by
        rw [← Finset.sum_add_distrib]
      rw [hpair]
      apply Finset.dvd_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hcoeff_eq j, hcoeff_eq (2 ^ (α - 1) + j)]
      exact hdvdj j hj
    rcases hdvd with h1 | h2
    · exact finish g1 r hirr1 hg1 hr h1
    · exact finish g2 (-r) hirr2 hg2eq hrr h2

omit [NeZero q] in
/-- A ring element with zero centered squared `ℓ₂` norm is `0`: every centered coefficient
representative below `deg φ` vanishes (`ZMod.valMinAbs_eq_zero`), and the representative is
reduced (degree `< deg φ`), so the underlying polynomial is `0`. -/
theorem Rq.eq_zero_of_l2NormSq_eq_zero {c : Rq Φ} (h : Rq.l2NormSq Φ c = 0) : c = 0 := by
  unfold Rq.l2NormSq at h
  -- Each centered coefficient below `deg φ` is zero.
  have hlt : ∀ k, k < (powTwoCyclotomic (R := ZMod q) α).φ.natDegree → c.1.coeff k = 0 := by
    intro k hk
    have hsq : (c.1.coeff k).valMinAbs.natAbs ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff.mp h) k (Finset.mem_range.mpr hk)
    have hz0 : (c.1.coeff k).valMinAbs.natAbs = 0 := (Nat.pow_eq_zero.mp hsq).1
    rw [← ZMod.valMinAbs_eq_zero, ← Int.natAbs_eq_zero]
    exact hz0
  -- Hence the underlying polynomial is `0` (coeffs below `deg φ` by the above, coeffs at or
  -- above `deg φ` by reducedness).
  have htoP : c.1.toPoly = 0 := by
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < (powTwoCyclotomic (R := ZMod q) α).φ.natDegree
    · rw [← CompPoly.CPolynomial.coeff_toPoly]; exact hlt k hk
    · rw [not_lt] at hk
      have hdeg : c.1.toPoly.degree < (powTwoCyclotomic (R := ZMod q) α).φ.toPoly.degree :=
        (powTwoCyclotomic (R := ZMod q) α).degree_toPoly_lt_of_reduced c.2
      have hmonic : (powTwoCyclotomic (R := ZMod q) α).φ.toPoly.Monic := IsCyclotomic.monic
      have hφne : (powTwoCyclotomic (R := ZMod q) α).φ.toPoly ≠ 0 := hmonic.ne_zero
      have hdegφ : (powTwoCyclotomic (R := ZMod q) α).φ.toPoly.degree
          = ((powTwoCyclotomic (R := ZMod q) α).φ.natDegree : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hφne, CompPoly.CPolynomial.natDegree_toPoly]
      have hle' : (powTwoCyclotomic (R := ZMod q) α).φ.toPoly.degree ≤ (k : WithBot ℕ) := by
        rw [hdegφ]; exact_mod_cast hk
      exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg hle')
  have hc1 : c.1 = 0 := (CompPoly.CPolynomial.toPoly_eq_zero_iff c.1).mp htoP
  exact Subtype.ext (by rw [Rq.zero_val]; exact hc1)

omit [NeZero q] in
/-- **Lyubashevsky–Seiler: short elements are invertible** (LS18, Cor. 1.2; Hachi, Lemma 3).
Over the power-of-two cyclotomic modulus `powTwoCyclotomic α` (`φ = X^{2^α}+1`) with a prime
`q ≡ 5 (mod 8)`, a nonzero element of `Rq (powTwoCyclotomic α)` with centered `ℓ₁` norm
`≤ κ` and `κ² < q` is a unit: by the algebraic core a non-unit forces `q ∣ ‖c‖₂²`, while
`‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q`, so `‖c‖₂² = 0`, forcing `c = 0` against `‖c‖₁ > 0`. -/
theorem isUnit_of_l1Norm_le (hq5 : q % 8 = 5) {c : Rq Φ} {κ : ℕ}
    (hpos : 0 < Rq.l1Norm Φ c) (hle : Rq.l1Norm Φ c ≤ κ) (hκ : κ ^ 2 < q) :
    IsUnit c := by
  by_contra hc
  -- Algebraic core: a non-unit has `q ∣ ‖c‖₂²`.
  have hdvd : (q : ℤ) ∣ (Rq.l2NormSq Φ c : ℤ) := q_dvd_l2NormSq_of_not_isUnit α hq5 hc
  have hdvdn : q ∣ Rq.l2NormSq Φ c := by exact_mod_cast hdvd
  -- Norm bridge + hypotheses: `‖c‖₂² ≤ ‖c‖₁² ≤ κ² < q`.
  have hb : Rq.l2NormSq Φ c < q :=
    lt_of_le_of_lt (le_trans (Rq.l2NormSq_le_l1Norm_sq α c) (Nat.pow_le_pow_left hle 2)) hκ
  -- A multiple of `q` below `q` is `0`.
  have hz : Rq.l2NormSq Φ c = 0 := Nat.eq_zero_of_dvd_of_lt hdvdn hb
  -- Zero squared norm ⇒ `c = 0`, contradicting `‖c‖₁ > 0`.
  have hc0 : c = 0 := Rq.eq_zero_of_l2NormSq_eq_zero α hz
  have hl1zero : Rq.l1Norm Φ (0 : Rq Φ) = 0 := by
    unfold Rq.l1Norm
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    rw [Rq.zero_val, CompPoly.CPolynomial.coeff_zero, ZMod.valMinAbs_zero, Int.natAbs_zero]
  rw [hc0, hl1zero] at hpos
  exact absurd hpos (lt_irrefl 0)

end ArkLib.Lattices.CyclotomicModulus

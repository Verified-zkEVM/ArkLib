/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter

/-!
# Rate-dependent list decoding above the partition gate

This file is the fixed-order list-decoding form of the rate-partition row in [DKTZ26].
It turns the strict limiting gate

`ratePartitionGamma R a d = (27 / 20) * R * (d + 1) / (6 * d) ^ (R / a) > 1`

into finite interpolation parameters and then bounds the complete Reed--Solomon agreement
list. Here `R` is an upper bound on the code rate, `a` is the required agreement fraction,
and `d` is the highest derivative order. The theorem assumes `d ≥ 500`, as does the simplex
moment estimate used by the paper's closed gate.

The finite parameter record is selected from `(R, a, d)` before the field, block length,
code dimension, evaluation set, or received word. Its multiplicity `m` fixes
`ν = ratePartitionJetBound R m = ⌈2m/R⌉`, while
`ratePartitionMathematicalLength R d m` absorbs the finite rounding and reconstruction guards.
This quantifier order is what makes the final coefficient in the `C_L * n^d` bound depend only
on `(R, a, d)`.

The results here are mathematical list bounds. They neither implement the paper's decoder nor
assert its running time. Ordinary polynomial degree is used, so the zero polynomial is included
in `closePolynomialSet`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- **Complete fixed-order list bound from one finite rate-partition certificate.**

This is the finite mathematical content of the paper's `Through derivative d` row and
Theorem `thm:rate-list`. The symbols correspond as follows:

* `R` is the paper's rate envelope `ρ`, and `a` is the agreement fraction;
* `d` is the largest derivative order, `n` the block length, `k` the message dimension,
  and `A` the integral agreement threshold;
* `p.multiplicity` is the finite multiplicity `m` chosen from the strict gate, and
  `ν = ratePartitionJetBound R p.multiplicity` is the paper's jet cap `B_jet`;
* `domain : Fin n ↪ F` is the ordered set of `n` distinct evaluation points;
* `closePolynomialSet domain received k A` contains exactly the polynomials `P : F[X]`
  with `P.degree < k` that agree with `received` at at least `A` positions.

The hypotheses say `0 < R < a < 1`, `d ≥ 500`, `n` exceeds the finite threshold selected by
`p`, `1 ≤ k ≤ Rn`, and `an ≤ A ≤ n`. The characteristic guard is exactly the paper's

`char F = 0` or `char F > max {k - 1, d, ν}`.

The conclusion proves finiteness of the *complete* agreement set and the exact displayed bound

`|List(received,A)| ≤ ν^2 * (2ν / (a - R))^d * n^d`.

The proof reconstructs with `max k (d + 1)` even though interpolation uses the larger ambient
dimension `floor (R * n) + 1`. No field-size hypothesis or decoder claim is part of this result.
-/
theorem ratePartition_close_list_bound
    -- The ambient field is arbitrary; only the characteristic guard below constrains it.
    {F : Type u} [Field F]
    -- Fix the rate envelope, agreement fraction, derivative order, and code sizes.
    {R a : ℝ} {d n k A : ℕ}
    -- This parameter record fixes `m`, its positive weight, and a finite ratio above one.
    (p : RatePartitionFiniteParameters R a d)
    -- The paper's fixed-order regime is `0 < R < a < 1` with `d ≥ 500`.
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    -- The selected finite parameters impose one block-length threshold.
    (hn : ratePartitionMathematicalLength R d p.multiplicity ≤ n)
    -- Messages have degree below `k`, rate at most `R`, and agreement at least `a`.
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    -- An embedding supplies `n` distinct evaluation points; the received word is arbitrary.
    (domain : Fin n ↪ F) (received : Fin n → F)
    -- Taylor reconstruction and derivative separation require all caps below `ringChar F`.
    (hchar : ringChar F = 0 ∨
      max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) :
    -- The complete close-polynomial set is finite, including its possible zero polynomial.
    (closePolynomialSet domain received k A).Finite ∧
      -- Its cardinality is the paper's `C_L n^d` with
      -- `C_L = ν^2 (2ν/(a-R))^d` and `ν = ratePartitionJetBound R p.multiplicity`.
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
          (2 * ratePartitionJetBound R p.multiplicity / (a - R)) ^ d * n ^ d := by
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_mathematical_length_guards hR (hRa.trans haone) (by omega) hn hkR haA
  obtain ⟨cert⟩ := exists_ratePartitionMathematical_certificate p hR (hRa.trans haone)
    (hR.trans hRa) hd hn hkR haA hAn domain (fun i ↦ Polynomial.C (received i))
    (fun _ ↦ by simp)
  let K := max k (d + 1)
  have hkK : k ≤ K := Nat.le_max_left _ _
  have hdK : d < K := lt_of_lt_of_le (Nat.lt_succ_self d) (Nat.le_max_right _ _)
  have hKn : K ≤ n := by
    apply max_le
    · exact hkD.trans (by omega)
    · omega
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := hkR.trans
      ((mul_le_mul_of_nonneg_right hRa.le (Nat.cast_nonneg n)).trans haA)
    exact_mod_cast h
  have hν : 0 < ratePartitionJetBound R p.multiplicity := by
    apply Nat.lt_ceil.mpr
    have hm : (0 : ℝ) < p.multiplicity := by exact_mod_cast p.multiplicity_pos
    simpa only [Nat.cast_zero] using (show (0 : ℝ) < 2 * p.multiplicity / R by positivity)
  have hKsub : K - 1 ≤ max (k - 1) d := by
    rcases le_total k (d + 1) with hkd | hdk
    · rw [show K = d + 1 by simp [K, max_eq_right hkd]]
      exact Nat.le_max_right _ _
    · rw [show K = k by simp [K, max_eq_left hdk]]
      exact Nat.le_max_left _ _
  have hchar' : ringChar F = 0 ∨
      max (K - 1) (ratePartitionJetBound R p.multiplicity) < ringChar F := by
    apply hchar.imp_right
    intro hc
    exact (max_le_max hKsub le_rfl).trans_lt hc
  apply close_list_bound_of_curve_certificate_of_jetCharacteristic domain received cert hk
    hkK hdK hKn hkA hAn hν (sub_pos.mpr hRa) ?_ hchar'
  nlinarith

open Classical in
/-- **A strict rate gate fixes one list-bound recipe uniformly over all codes.**

Assume the paper's limiting ratio

`Γ(R,a,d) = (27/20) * R * (d+1) / (6d)^(R/a)`

is strictly larger than one. The theorem first chooses a finite parameter record `p` depending
only on `(R,a,d)`. It then quantifies over `F`, `n`, `k`, `A`, the evaluation embedding, and the
received word. Thus the multiplicity, jet cap `ν`, length threshold, and coefficient in
`ν^2 * (2ν/(a-R))^d * n^d` are fixed before any code or word is known.

Reading the nested quantifiers: every code beyond the selected length threshold, of dimension
`1 ≤ k ≤ Rn`, and decoded at an integral threshold `an ≤ A ≤ n`, has the complete-list bound
for every received word on every distinct evaluation set, provided the displayed characteristic
guard holds. This is the fixed-order gate theorem; approaching capacity requires a separate
choice of `d` as a function of the positive gap `a-R`.
-/
theorem exists_ratePartition_list_bound
    -- Choose the real rate data and derivative order before every field and code.
    {R a : ℝ} {d : ℕ}
    -- The fixed-order regime is `0 < R < a < 1` with derivative order at least `500`.
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    -- Strict surplus ensures that a finite multiplicity with positive interpolation margin exists.
    (hgate : 1 < ratePartitionGamma R a d) :
    -- The witness `p`, hence `m`, `ν`, and the length threshold, depends only on `(R,a,d)`.
    ∃ p : RatePartitionFiniteParameters R a d,
      -- Only after fixing `p` do we quantify over the field and integral code parameters.
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      -- Admissible codes lie beyond the finite threshold and satisfy `1 ≤ k ≤ Rn`.
      ratePartitionMathematicalLength R d p.multiplicity ≤ n → 0 < k →
      (k : ℝ) ≤ R * n →
      -- The decoding threshold is an integer with `an ≤ A ≤ n`.
      a * n ≤ A → A ≤ n →
      -- The guarantee is uniform over distinct evaluation points and every received word.
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      -- The characteristic exceeds the message, derivative, and jet caps, unless it is zero.
      (ringChar F = 0 ∨
        max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      -- This is the complete mathematical list, rather than a supplied candidate subset.
      (closePolynomialSet domain received k A).Finite ∧
        -- Its exact field-independent estimate is `C_L n^d` for the fixed `p`.
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          (ratePartitionJetBound R p.multiplicity : ℝ) ^ 2 *
            (2 * ratePartitionJetBound R p.multiplicity / (a - R)) ^ d * n ^ d := by
  obtain ⟨p⟩ := exists_ratePartitionFiniteParameters hR (hR.trans hRa) (by omega) hgate
  exact ⟨p, fun _ _ _ _ _ hn hk hkR haA hAn domain received hchar ↦
    ratePartition_close_list_bound p hR hRa haone hd hn hk hkR haA hAn domain received hchar⟩

end ReedSolomon

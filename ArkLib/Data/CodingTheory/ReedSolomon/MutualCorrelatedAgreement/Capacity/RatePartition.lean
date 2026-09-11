/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.CertificateBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.RatePartition.Adapter
/-!
# Rate-dependent exact correlated agreement on polynomial curves

This file states the MCA half of the fixed-order rate-partition row in [DKTZ26]. The rate data
are `0 < R < a < 1`, where `R` bounds `k/n` and `a` is the required agreement fraction; their
positive difference `δ = a - R` is the agreement gap. The integer `d ≥ 500` is the largest
derivative order.

A `RatePartitionFiniteParameters R a d` record contains a multiplicity `m`, a positive weighted
support, and a certified finite source/rank ratio `γ_m > 1`. It determines

* the jet cap `ν = ratePartitionJetBound R m = ⌈2m/R⌉`;
* the symbolic height `h = ratePartitionHeight ν γ_m = max 1 ⌈ν/(γ_m-1)⌉`;
* the finite block threshold `ratePartitionMathematicalLength R d m`.

For a power-batched curve with `ℓ + 1` received words, the common exceptional-set bound is

`ℓ * C_E * n^(d+1)`,

where

`C_E = h + 2^d * ν^(d+2) * (1/δ)^d * (h*(d+1)*(3d+5)/δ + 3)`.

The exceptional set is chosen after the received curve but before the challenge and candidate.
Outside it, every close candidate comes from degree-`< k` base-field constituent polynomials,
and its entire agreement set equals their common agreement set. The last equality is the full
agreement endpoint required for mutual correlated agreement.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

/-- **Fixed-order full-agreement MCA for a power-batched received curve.**

This is a power-batched extension-field strengthening of the paper's Theorem `thm:rate-mca`.
Its `ℓ = 1` base-field specialization gives that line result. The symbols are:

* `F` is the received-word field, `E` an algebraically closed proof field, and `iota : F →+* E`
  the scalar embedding;
* `R`, `a`, and `d` are the rate envelope, agreement fraction, and derivative order;
* `n`, `k`, and `A` are the block length, message dimension, and integral agreement threshold;
* `values : Fin (ℓ+1) → Fin n → F` gives the `ℓ+1` received words whose challenge-`z`
  combination is `Σ_t z^t values_t`;
* `p` fixes `m`, `ν = ⌈2m/R⌉`, the finite ratio `γ_m > 1`, and
  `h = max 1 ⌈ν/(γ_m-1)⌉` before the curve and challenge are chosen.

The hypotheses are `0 < R < a < 1`, `d ≥ 500`, the selected finite length lower bound,
`1 ≤ k ≤ Rn`, `an ≤ A ≤ n`, and `ℓ > 0`. The characteristic condition is precisely
`char F = 0` or `char F > max {k-1,d,ν}`. Reconstruction uses `max k (d+1)`, independently
of the interpolation dimension `floor (R*n)+1`.

The exceptional set has the exact bound `ℓ * C_E * n^(d+1)` displayed in the module
documentation. It is uniform over every later `z` and `P`. `HasExactPowerAgreement` concludes
that `P` is the power combination of degree-`< k` polynomials over `F` and that the complete
agreement set of `P` is exactly their common agreement set; it is stronger than retaining one
common subset of `A` positions.
-/
theorem exists_ratePartition_curveMCA
    -- Work over a received-word field and an algebraically closed geometric extension.
    {F E : Type u} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    -- Fix the rate envelope, agreement fraction, derivative order, and code/curve sizes.
    {R a : ℝ} {d n k A ℓ : ℕ}
    -- The finite interpolation parameters have already been chosen from `(R,a,d)`.
    (p : RatePartitionFiniteParameters R a d)
    -- This is the paper's fixed-order gate regime.
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    -- The block length clears every rounding, jet, and reconstruction guard selected by `p`.
    (hn : ratePartitionMathematicalLength R d p.multiplicity ≤ n)
    -- Messages have positive dimension and rate at most `R`; candidates agree at least `a`.
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    -- A positive-degree challenge curve is evaluated on `n` distinct base-field points.
    (hℓ : 0 < ℓ) (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    -- The embedding supports geometric counting; the characteristic guard is on `F`.
    (iota : F →+* E) (hchar : ringChar F = 0 ∨
      max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) :
    -- One finite set is selected before both the challenge `z` and candidate `P`.
    ∃ exceptional : Finset E,
      -- Its exact size is `ℓ * C_E * n^(d+1)` with gap `δ = a-R`.
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant (a - R)
        (ratePartitionJetBound R p.multiplicity)
        (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
          (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
      -- Every challenge outside that set is good simultaneously for every candidate.
      ∀ z ∉ exceptional,
        -- The candidate may live over `E`, but must have ordinary degree below `k`.
        ∀ P : E[X], P.degree < k →
        -- A candidate entering the conclusion agrees with the batched word at `A` positions.
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        -- It descends to base-field witnesses and has exactly their common agreement set.
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨hdD, hDlower, hkD, hDn, hνn, hmn, hceil, hn2⟩ :=
    ratePartition_mathematical_length_guards hR (hRa.trans haone) (by omega) hn hkR haA
  obtain ⟨cert⟩ := exists_ratePartitionMathematical_certificate p hR (hRa.trans haone)
    (hR.trans hRa) hd hn hkR haA hAn domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _)
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
  have hh : 0 < ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
      (ratePartitionFiniteRatio R a d p.multiplicity) := lt_of_lt_of_le Nat.zero_lt_one
        (le_max_left _ _)
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
  apply exists_curveMCA_of_certificate_of_jetCharacteristic domain values iota cert hk
    hkK (by omega) hdK hKn hkA hAn hν hh hℓ
    le_rfl (sub_pos.mpr hRa) (by linarith) ?_ hchar'
  nlinarith
open Classical in
/-- **Base-field form of fixed-order power-curve MCA.**

This theorem descends both challenges and candidates in `exists_ratePartition_curveMCA` to the
received-word field `F`. It retains the same paper symbols, hypotheses, and exact
`ℓ * C_E * n^(d+1)` budget. For `values_0,...,values_ℓ`, the word at challenge `z : F` is
`Σ_t z^t values_t`.

The quantifier order remains essential: one exceptional subset of `F` is chosen for the entire
received curve, before `z` and `P`. Outside it, every degree-`< k` candidate with at least `A`
agreements is an exact power combination of degree-`< k` witnesses over `F`, and its full
agreement set equals the witnesses' common agreement set.
-/
theorem exists_ratePartition_baseCurveMCA
    -- All algebraic data and the returned exceptional challenges now lie in one field.
    {F : Type u} [Field F]
    -- Fix the rate data, derivative order, block length, code, threshold, and curve degree.
    {R a : ℝ} {d n k A ℓ : ℕ}
    -- The finite parameter record was selected before the field and received curve.
    (p : RatePartitionFiniteParameters R a d)
    -- The same strict rate window and order floor as the extension-field theorem.
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    -- The block length exceeds the threshold determined by `p`.
    (hn : ratePartitionMathematicalLength R d p.multiplicity ≤ n)
    -- The code rate and integral agreement threshold realize the real parameters.
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    -- Supply a positive-degree received curve on `n` distinct evaluation points.
    (hℓ : 0 < ℓ) (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    -- Characteristic zero is unrestricted; positive characteristic clears all degree caps.
    (hchar : ringChar F = 0 ∨
      max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) :
    -- The descended exceptional set is selected before every challenge and candidate.
    ∃ exceptional : Finset F,
      -- Descent does not increase the exact `ℓ * C_E * n^(d+1)` cardinality bound.
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant (a - R)
        (ratePartitionJetBound R p.multiplicity)
        (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
          (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
      -- Every later base-field challenge outside the set works for every candidate.
      ∀ z ∉ exceptional,
        -- Ordinary degree includes the zero polynomial and requires `P.degree < k`.
        ∀ P : F[X], P.degree < k →
        -- The candidate must meet the integral agreement threshold on the batched word.
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        -- Base-field constituents reproduce `P` and exactly its complete agreement set.
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨ex, hc, hg⟩ := exists_ratePartition_curveMCA p hR hRa haone hd hn hk hkR haA hAn
    hℓ domain values iota hchar
  obtain ⟨ex', hc', hg'⟩ := exists_exceptional_powerAgreement_descend domain values iota k A ex hg
  exact ⟨ex', (Nat.cast_le.mpr hc').trans hc, hg'⟩

open Classical in
/-- **Fixed-order full-agreement MCA on an affine line of received words.**

This is the `ℓ = 1` specialization of the power-curve theorem and matches the line-MCA
conclusion of the paper's fixed-order row. The challenge word is `i ↦ f i + z * g i`. Put
`δ = a-R`, `ν = ratePartitionJetBound R p.multiplicity`,
`γ = ratePartitionFiniteRatio R a d p.multiplicity`, and
`h = ratePartitionHeight ν γ`. One exceptional set has size at most

`C_E * n^(d+1)`, where
`C_E = h + 2^d * ν^(d+2) * (1/δ)^d * (h*(d+1)*(3d+5)/δ + 3)`.

For each nonexceptional challenge, every close degree-`< k` polynomial `P` has witnesses
`P₀,P₁ : F[X]`, each of degree below `k`, such that `P=P₀+zP₁`. The conclusion additionally
identifies the entire agreement set of `P` with the positions where `P₀` agrees with `f` and
`P₁` agrees with `g`. This full-set equality excludes accidental agreements created only by
cancellation at `z`.
-/
theorem exists_ratePartition_lineMCA
    -- The received line, candidate, witnesses, and exceptional challenges all lie over `F`.
    {F : Type u} [Field F]
    -- Fix the rate data, derivative order, and integral code parameters.
    {R a : ℝ} {d n k A : ℕ}
    -- The record fixes the finite multiplicity, jet cap, ratio, and symbolic height.
    (p : RatePartitionFiniteParameters R a d)
    -- The fixed-order theorem assumes `0 < R < a < 1` and `d ≥ 500`.
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    -- The block length is beyond the finite threshold attached to `p`.
    (hn : ratePartitionMathematicalLength R d p.multiplicity ≤ n)
    -- Messages have dimension at least one, rate at most `R`, and agreement at least `a`.
    (hk : 0 < k) (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    -- `domain` gives distinct evaluation points; `f` and `g` span the received line.
    (domain : Fin n ↪ F) (f g : Fin n → F)
    -- The positive characteristic, when present, exceeds `k-1`, `d`, and the jet cap.
    (hchar : ringChar F = 0 ∨
      max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) :
    -- A single exceptional set works for all subsequently quantified challenges and candidates.
    ∃ exceptional : Finset F,
      -- Its exact bound is the paper's `C_E * n^(d+1)` at gap `a-R`.
      (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant (a - R)
        (ratePartitionJetBound R p.multiplicity)
        (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
          (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
      -- Every challenge outside the set is good for every candidate polynomial.
      ∀ z ∉ exceptional,
        -- Candidate messages use ordinary polynomial degree below `k`.
        ∀ P : F[X], P.degree < k →
        -- Enter the conclusion when `P` agrees with the challenge word in at least `A` places.
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        -- Recover two base-field witnesses and equality of the full agreement sets.
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨ex, hc, hg⟩ := exists_ratePartition_baseCurveMCA p hR hRa haone hd hn hk hkR haA hAn
    (by norm_num : 0 < 1) domain ![f, g] hchar
  refine ⟨ex, by simpa only [Nat.cast_one, one_mul] using hc, ?_⟩
  intro z hz P hP hA
  have hw : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  have h := hg z hz P hP (by rwa [hw])
  simpa using exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P h
open Classical in
/-- **A strict rate gate fixes one line-MCA recipe before all fields and received lines.**

The limiting gate is

`Γ(R,a,d) = (27/20) * R * (d+1) / (6d)^(R/a) > 1`.

From this strict surplus the theorem first chooses `p : RatePartitionFiniteParameters R a d`.
Consequently its multiplicity `m`, jet cap `ν`, finite ratio `γ_m`, symbolic height `h`, length
threshold, and exceptional coefficient `C_E` all depend only on `(R,a,d)`. The field, block
length, code dimension, agreement threshold, evaluation points, and received line are quantified
after `p`.

For every admissible later choice, the theorem returns one exceptional set before `z` and `P`.
The final `HasExactCorrelatedPair` supplies degree-`< k` witnesses `P₀,P₁`, proves
`P=P₀+zP₁`, and equates the candidate's complete agreement set with the common agreement set.
This is a fixed derivative-order result. Using it uniformly up to capacity additionally requires
choosing `d` from the positive gap `a-R`; that choice is outside this declaration.
-/
theorem exists_ratePartition_lineMCA_parameters
    -- The real rate data and derivative order are fixed before any finite parameter search.
    {R a : ℝ} {d : ℕ}
    -- The fixed-order regime is `0 < R < a < 1` with `d ≥ 500`.
    (hR : 0 < R) (hRa : R < a) (haone : a < 1) (hd : 500 ≤ d)
    -- Strict limiting surplus makes the finite parameter search terminate.
    (hgate : 1 < ratePartitionGamma R a d) :
    -- This witness fixes every list/MCA constant solely from `(R,a,d)`.
    ∃ p : RatePartitionFiniteParameters R a d,
      -- The field and integral code parameters are chosen only after `p`.
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      -- Require the selected length threshold and a positive message dimension.
      ratePartitionMathematicalLength R d p.multiplicity ≤ n → 0 < k →
      -- The realized rate is at most `R`, while the integral threshold realizes `a`.
      (k : ℝ) ≤ R * n → a * n ≤ A → A ≤ n →
      -- The statement is uniform over every distinct evaluation set and received line.
      ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
      -- The positive characteristic clears the message, derivative, and jet degrees.
      (ringChar F = 0 ∨
        max (max (k - 1) d) (ratePartitionJetBound R p.multiplicity) < ringChar F) →
      -- One set is chosen from the line before the challenge and candidate.
      ∃ exceptional : Finset F,
        -- The exact exceptional budget is `C_E * n^(d+1)` for the fixed parameter record.
        (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant (a - R)
          (ratePartitionJetBound R p.multiplicity)
          (ratePartitionHeight (ratePartitionJetBound R p.multiplicity)
            (ratePartitionFiniteRatio R a d p.multiplicity)) d * (n : ℝ) ^ (d + 1) ∧
        -- Every nonexceptional challenge works simultaneously for every close candidate.
        ∀ z ∉ exceptional,
          -- The candidate has ordinary degree below the message dimension.
          ∀ P : F[X], P.degree < k →
          -- At least `A` agreements trigger the exact-witness conclusion.
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          -- The candidate is a witness-line point with exactly the common agreement set.
          HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨p⟩ := exists_ratePartitionFiniteParameters hR (hR.trans hRa) (by omega) hgate
  exact ⟨p, fun _ _ _ _ _ hn hk hkR haA hAn domain f g hchar ↦
    exists_ratePartition_lineMCA p hR hRa haone hd hn hk hkR haA hAn domain f g hchar⟩

end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nishimwe Prince
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# [BCIKS20] correlated agreement on the `epsCa` carrier

`RS_correlatedAgreement_affineLines_uniqueDecodingRegime` states [BCIKS20]'s unique-decoding-regime
correlated agreement through the predicate `δ_ε_correlatedAgreementAffineLines`. The
capacity-regime catalogue in `ProximityGap/CapacityBounds.lean` instead speaks about the numeric
carrier `epsCa`.

This module transports the former onto the latter, so the proven [BCIKS20] bound is usable wherever
`epsCa` is the currency.

## Main statement

- `rs_epsCa_le_of_le_relUDR` — for a Reed-Solomon code and a fold radius at most the relative
  unique-decoding radius, `ε_ca(C, δ_fld, δ_int) ≤ n / |F|` at every interleaved radius
  `δ_int ≥ δ_fld`.

## Relation to [BCHKS25] Theorem 1.3

`CodingTheory.rs_epsCa_le_in_unique_decoding_range` states [BCHKS25] Theorem 1.3 on the same
carrier and overlapping hypotheses, and is an external admit. It is **not** implied by the theorem
below, and the theorem below is not implied by it: [BCHKS25]'s own comparison (their Table 1)
records that [BCI+20] needs `a > n` exceptional coefficients where [BCHKS25] needs `a = O(1)`, so
the bound here carries a factor `n` that Theorem 1.3 removes. Concretely, at `ρ = 1/2` and
`n = 1024` the
[BCHKS25] bound is roughly `12/|F|` at the bottom of its radius range against `1024/|F|` here, and
the ratio grows linearly in `n`.

The two are therefore complementary: this one is proved in-tree and axiom-clean, Theorem 1.3 is
sharper and still admitted.

## References

- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf. *Proximity Gaps for Reed-Solomon Codes*.
- [BCHKS25] Ben-Sasson, Carmon, Haböck, Kopparty, Saraf. *On Proximity Gaps for Reed-Solomon
  Codes*. Cryptology ePrint Archive, Paper 2025/2055. Theorem 1.3 and Table 1.
-/

namespace ProximityGap

open NNReal Code CoreDefinitions
open scoped BigOperators ProbabilityTheory

section UniqueDecodingRegime

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
/-- **[BCIKS20] correlated agreement, stated on `epsCa`.** For a Reed-Solomon code and a fold
radius `δ_fld` at most the relative unique-decoding radius,

  `ε_ca(C, δ_fld, δ_int) ≤ n / |F|`

for every interleaved radius `δ_int ≥ δ_fld`, where `n = |ι|`.

The proof is a transport, not a new argument:
`RS_correlatedAgreement_affineLines_uniqueDecodingRegime` supplies the predicate form,
`δ_ε_correlatedAgreementAffineLines_iff_epsCa_le` moves it onto the equal-radius carrier
`epsCa C δ_fld δ_fld`, `errorBound_eq_n_div_q_of_le_relUDR` evaluates [BCIKS20]'s piecewise
`errorBound` to `n/|F|` in this regime, and `epsCa_antitone_right` extends the result from
`δ_int = δ_fld` to every larger interleaved radius.

Antitonicity in the interleaved radius is what makes the two-radius form free: enlarging `δ_int`
enlarges the joint-proximity event that zeroes out each supremand.

The bound is stated as the `ENNReal` coercion of the `ℝ≥0` quotient `n / |F|`, matching
`errorBound`'s own type, rather than as an `ENNReal` quotient of two coerced cardinalities. -/
theorem rs_epsCa_le_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ_fld δ_int : ℝ≥0}
    (hδ : δ_fld ≤ relativeUniqueDecodingRadius
            (ι := ι) (F := F) (C := ReedSolomon.code domain deg))
    (hle : δ_fld ≤ δ_int) :
    epsCa (F := F) (A := F) ((ReedSolomon.code domain deg : Set (ι → F))) δ_fld δ_int
      ≤ ((Fintype.card ι / Fintype.card F : ℝ≥0) : ENNReal) := by
  classical
  -- [BCIKS20]'s unique-decoding-regime correlated agreement, in predicate form.
  have hCA := RS_correlatedAgreement_affineLines_uniqueDecodingRegime
      (deg := deg) (domain := domain) (δ := δ_fld) hδ
  -- In this regime the piecewise `errorBound` is exactly `n / |F|`.
  have hErr : errorBound δ_fld deg domain
      = (Fintype.card ι / Fintype.card F : ℝ≥0) :=
    errorBound_eq_n_div_q_of_le_relUDR hδ
  -- Move the predicate onto the equal-radius carrier.
  have hEq : epsCa (F := F) (A := F)
      ((ReedSolomon.code domain deg : Set (ι → F))) δ_fld δ_fld
      ≤ ((errorBound δ_fld deg domain : ℝ≥0) : ENNReal) :=
    (δ_ε_correlatedAgreementAffineLines_iff_epsCa_le (F := F) (A := F) _ _ _).mp hCA
  rw [hErr] at hEq
  -- Extend from `δ_int = δ_fld` to every larger interleaved radius.
  exact le_trans
    (epsCa_antitone_right (F := F) (A := F)
      ((ReedSolomon.code domain deg : Set (ι → F))) δ_fld hle)
    hEq

omit [Field F] [Fintype F] [DecidableEq ι] in
/-- A positive radius at most the relative unique-decoding radius satisfies the strict form
`2·δ·n < d` that the MCA/CA comparison lemmas take as their hypothesis.

`relativeUniqueDecodingRadius` is `((d - 1) / 2) / n` with **truncated** `ℝ≥0` subtraction, so
the degenerate `d = 0` case is not vacuous on its face: there the radius collapses to `0` and
the positivity hypothesis is what rules it out. For `d ≥ 1` the bound is the honest
`2·δ·n ≤ d - 1 < d`. -/
lemma two_mul_lt_dist_of_le_relUDR {C : Set (ι → F)} {δ : ℝ≥0}
    (hδ_pos : 0 < δ) (hδ : δ ≤ relativeUniqueDecodingRadius C) :
    2 * (δ : ℝ) * Fintype.card ι < Code.dist C := by
  have hn_pos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos (α := ι))
  rw [relativeUniqueDecodingRadius] at hδ
  -- `δ · n ≤ (d - 1) / 2`, then `2 · δ · n ≤ d - 1`, all in `ℝ≥0`.
  have h1 : δ * (Fintype.card ι : ℝ≥0) ≤ ((Code.dist C : ℝ≥0) - 1) / 2 :=
    (le_div_iff₀ hn_pos).mp hδ
  have h2 : 2 * δ * (Fintype.card ι : ℝ≥0) ≤ (Code.dist C : ℝ≥0) - 1 := by
    have hmul := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ≥0) ≤ 2)
    calc 2 * δ * (Fintype.card ι : ℝ≥0)
        = 2 * (δ * (Fintype.card ι : ℝ≥0)) := by ring
      _ ≤ 2 * (((Code.dist C : ℝ≥0) - 1) / 2) := hmul
      _ = (Code.dist C : ℝ≥0) - 1 := by
          rw [mul_div_cancel₀]; norm_num
  -- The left-hand side is strictly positive, which rules out the degenerate `d = 0` branch.
  have hδn : (0 : ℝ≥0) < 2 * δ * (Fintype.card ι : ℝ≥0) :=
    mul_pos (mul_pos (by norm_num) hδ_pos) hn_pos
  have hd_pos : 0 < Code.dist C := by
    rcases Nat.eq_zero_or_pos (Code.dist C) with hd0 | hd
    · exfalso
      rw [hd0] at h2
      simp only [Nat.cast_zero, zero_tsub] at h2
      exact absurd h2 (not_le.mpr hδn)
    · exact hd
  -- For `d ≥ 1`, `d - 1 < d` in `ℝ≥0`, so the strict inequality transfers to `ℝ`.
  have h3 : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist C : ℝ≥0) := by
    refine lt_of_le_of_lt h2 ?_
    have hdR : (0 : ℝ≥0) < (Code.dist C : ℝ≥0) := by exact_mod_cast hd_pos
    exact tsub_lt_self hdR one_pos
  exact_mod_cast h3

omit [DecidableEq ι] in
/-- **[BCIKS20] affine-line MCA for Reed-Solomon codes in the unique-decoding range.** For a
positive fold radius at most the relative unique-decoding radius,

  `ε_mca(C, δ) ≤ n / |F|` .

Below half the minimum distance, affine-line MCA and correlated agreement agree
(`mcaError_eq_epsCa_of_pos_of_two_mul_lt_dist`), so `rs_epsCa_le_of_le_relUDR` transfers directly.

This is the MCA-side companion of `rs_epsCa_le_of_le_relUDR`, and it is what
`ProximityGap.GrandChallenges` consumes: `McaLowerWitness` is stated on `mcaError`, not on
`epsCa`. -/
theorem rs_mcaError_le_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ_pos : 0 < δ)
    (hδ : δ ≤ relativeUniqueDecodingRadius
            (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain deg) (δ : ℝ)
      ≤ ((Fintype.card ι / Fintype.card F : ℝ≥0) : ENNReal) :=
  le_trans
    (mcaError_le_epsCa_of_pos_of_two_mul_lt_dist (ReedSolomon.code domain deg) δ hδ_pos
      (two_mul_lt_dist_of_le_relUDR hδ_pos hδ))
    (rs_epsCa_le_of_le_relUDR hδ le_rfl)

end UniqueDecodingRegime

end ProximityGap

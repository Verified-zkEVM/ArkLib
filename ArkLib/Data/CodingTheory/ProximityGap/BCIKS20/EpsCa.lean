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

end UniqueDecodingRegime

end ProximityGap

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Shared-level tensor folds for interleaved Reed–Solomon codes

The scalar hypothesis is a uniform exact power-agreement guarantee
(`ReedSolomon.UniformExactPowerAgreement`) for every received line `w 0 + z • w 1`, with at most
`e` exceptional challenges and threshold `L ≥ k`. From it, every interleaved Reed–Solomon code
`code domain k ^⋈ κ` has a full-set level witness (`TensorMCA.FullSetLevelWitness`) with the same
count `e`, independently of the number of rows `κ` and of the number of words opened at a level.
The height-three fold of such a code then has at most `3 * e * |F| ^ 2` bad challenge triples.

Both statements are specializations of
`ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement`. The only Reed–Solomon
inputs are `ReedSolomon.determinedByAgreement_code`, which needs `k ≤ L`, and the identification
`ReedSolomon.uniformExactPowerAgreement_iff_uniformExactAgreement` for the line generator
`z ↦ (1, z)`; the line `w 0 + z • w 1` is the binary fold `(1 - z) • w 0 + z • (w 0 + w 1)`.

## Main statements

* `ReedSolomon.uniformExactAgreement_binaryEqualityGenerator_of_line`: the scalar line
  guarantee in the equality-weight parametrization.
* `ReedSolomon.fullSetLevelWitness_code` and
  `ReedSolomon.fullSetLevelWitness_interleaved_of_exactAgreement`: the level witnesses.
* `ReedSolomon.interleavedRS_tensorFoldBad_card_le_heightThree`: the height-three count.

## References

ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/TensorFoldAgreement.lean`:

* `fullSetLevelWitness_interleaved_of_exactAgreement` assumed `LineExactAgreementBound domain k
  agreement exceptionalCount`, `0 < width` and `k ≤ agreement`, for `Fin n` columns and
  `Fin width` rows. Here the scalar hypothesis is `UniformExactPowerAgreement` at `ℓ = 1`, which
  states the same line guarantee with the challenge set counted in `ℕ` (the source's
  `LineExactAgreementBound` is not ported); columns are any finite type, rows any finite type
  including an empty one, and there is no width hypothesis. The proof is
  `TensorMCA.fullSetLevelWitness_of_uniformExactAgreement` followed by
  `TensorMCA.FullSetLevelWitness.moduleInterleavedCode`.
* `interleavedRS_tensorFoldBad_card_le_heightThree`: the same statement over the new witness.
* The private `lineProjectionBad`, `scalar_lineProjectionBad_card_le`,
  `interleaved_lineProjectionBad_card_le` and
  `exists_exceptional_fullSetLine_interleaved_of_exactAgreement` are covered by the generic
  results listed in `ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement`, and
  `scalar_lineProjectionBad_card_le` by `uniformExactAgreement_binaryEqualityGenerator_of_line`.

Deferred: scalar providers of the line guarantee (list-decoding and curve-counting results) and
the probability form of the count.
-/

@[expose] public section

namespace ReedSolomon

open CoreDefinitions Code TensorMCA

variable {F : Type} {ι : Type*} [Field F] [Fintype ι] [DecidableEq F]

/-- **The line guarantee in equality weights.** If every received line `w 0 + z • w 1` has a
uniform exact power-agreement guarantee with at most `e` exceptional challenges at threshold `L`,
and `k ≤ L`, then every binary fold `(1 - z) • V false + z • V true` over `code domain k` has a
uniform exact-agreement guarantee for `binaryEqualityGenerator` with the same count.

The hypothesis is applied to the line `(V false, V true - V false)`. The two parametrizations have
the same projection-bad challenges (`isProjectionBad_binaryEqualityGenerator_iff`), and
`k ≤ L` makes exact agreement the same as a count of projection-bad challenges
(`Code.uniformExactAgreement_iff_encard_le`). -/
theorem uniformExactAgreement_binaryEqualityGenerator_of_line (domain : ι ↪ F) {k L e : ℕ}
    (hline : ∀ w : Fin 2 → ι → F, UniformExactPowerAgreement domain w k L e) (hk : k ≤ L)
    (V : Bool → ι → F) :
    UniformExactAgreement binaryEqualityGenerator (code domain k) L e V := by
  have hC := determinedByAgreement_code domain hk
  have h := (uniformExactAgreement_iff_encard_le hC).mp
    ((uniformExactPowerAgreement_iff_uniformExactAgreement domain _).mp
      (hline ![V false, V true - V false]))
  rw [univariatePowersGenerator_one_eq_affineLineGenerator] at h
  rw [uniformExactAgreement_iff_encard_le hC]
  simpa only [isProjectionBad_binaryEqualityGenerator_iff] using h

variable [DecidableEq ι]

/-- **Level witness for a Reed–Solomon code.** Under the line guarantee with count `e` at
threshold `L ≥ k`, the code `code domain k` has a full-set level witness with count `e`. The
hypothesis `k ≤ L` makes codewords determined by `L` agreements; without it a close codeword
need not be the fold of the codewords found on its agreement set. -/
theorem fullSetLevelWitness_code (domain : ι ↪ F) {k L e : ℕ}
    (hline : ∀ w : Fin 2 → ι → F, UniformExactPowerAgreement domain w k L e) (hk : k ≤ L) :
    FullSetLevelWitness (code domain k) L e :=
  fullSetLevelWitness_of_uniformExactAgreement (determinedByAgreement_code domain hk)
    (uniformExactAgreement_binaryEqualityGenerator_of_line domain hline hk)

/-- **Level witness for an interleaved Reed–Solomon code.** Under the line guarantee with count
`e` at threshold `L ≥ k`, the interleaved code `code domain k ^⋈ κ` has a full-set level witness
with count `e` for every finite row type `κ`, including an empty one. The count depends neither on
`κ` nor on the number of words opened at a level. -/
theorem fullSetLevelWitness_interleaved_of_exactAgreement (domain : ι ↪ F) {k L e : ℕ}
    (hline : ∀ w : Fin 2 → ι → F, UniformExactPowerAgreement domain w k L e) (hk : k ≤ L)
    (κ : Type) [Fintype κ] : FullSetLevelWitness ((code domain k)^⋈κ) L e :=
  (fullSetLevelWitness_code domain hline hk).moduleInterleavedCode

/-- **Height-three count.** Under the line guarantee with count `e` at threshold `L ≥ k`, the
height-three fold of eight arrays over `code domain k ^⋈ κ` has at most `3 * e * |F| ^ 2` bad
challenge triples: each level contributes `e` values of its challenge for every choice of the
other two. Divided by `|F| ^ 3`, this is the error `3 * e / |F|`, independent of `κ`. Outside the
bad set, `hasFullTensorDecomposition_of_not_mem_bad` gives the leaf decomposition. -/
theorem interleavedRS_tensorFoldBad_card_le_heightThree [Fintype F] (domain : ι ↪ F) {k L e : ℕ}
    (hline : ∀ w : Fin 2 → ι → F, UniformExactPowerAgreement domain w k L e) (hk : k ≤ L)
    {κ : Type} [Fintype κ] (u : (Fin 3 → Bool) → ι → κ → F) :
    (tensorFoldBad (fullSetLevelWitness_interleaved_of_exactAgreement domain hline hk κ) u).card ≤
      3 * e * Fintype.card F ^ 2 :=
  tensorFoldBad_card_le _ u

end ReedSolomon

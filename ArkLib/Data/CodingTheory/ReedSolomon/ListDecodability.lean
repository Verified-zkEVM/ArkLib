/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ListDecodability.AgreementBound
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The Johnson-type list-decoding bound for Reed–Solomon codes

  This file proves that the Reed–Solomon code
  `RS[F, L, m]` of rate `ρ` is `(1 - √ρ - η, 1/(2η√ρ))`-list decodable for every `η > 0`
  (`ReedSolomon.listDecodable_reedSolomon`) which appears as theorem 4.3
  in [ACFY24].
  The bound is independent of the size of `F`.

## References

  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]

-/

namespace ReedSolomon

open Finset ReedSolomon

variable {ι F : Type*} [Fintype ι] [Field F]

/-- The main counting estimate: any finite set of codewords within relative distance
`1 - √ρ - η` of a word `y` has at most `1/(2η√ρ)` elements.

This is the Reed-Solomon instance of the alphabet-agnostic counting bound
`Code.card_le_of_pairwise_agree_le`: two distinct codewords agree in fewer than `m` positions
(`agree_lt_of_mem_code`), and `m ≤ (√ρ)² · |ι|` by definition of the rate. -/
lemma card_le_of_subset_closeCodewords [Nonempty ι] (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    {η : ℝ} (hη : 0 < η) (y : ι → F) (T : Finset (ι → F))
    (hT : ∀ c ∈ T, c ∈ Code.closeCodewordsRel (ReedSolomon.code domain m : Set (ι → F)) y
      (1 - (ReedSolomon.sqrtRate m domain : ℝ) - η)) :
    (T.card : ℝ) ≤ 1 / (2 * η * (ReedSolomon.sqrtRate m domain : ℝ)) := by
  classical
  refine Code.card_le_of_pairwise_agree_le (sqrtRate_pos hm) hη ?_ y T hT
  intro c hc c' hc' hne
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h1 : Code.agree c c' ≤ min m (Fintype.card ι) :=
    le_min (le_of_lt (ReedSolomon.agree_lt_of_mem_code hc hc' hne)) Code.agree_le_card
  rw [ReedSolomon.sqrtRate_sq, div_mul_cancel₀ _ (ne_of_gt hnpos)]
  exact_mod_cast h1

open NNReal in
/-- **Theorem 4.3.** The Reed–Solomon code `RS[F, domain, m]` of rate `ρ` is
`(1 - √ρ - η, 1/(2η√ρ))`-list decodable, for every `η > 0`. -/
theorem listDecodable_reedSolomon [Nonempty ι] (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    {η : ℝ≥0} (hη : 0 < η) :
    Code.IsListDecodable (ReedSolomon.code domain m : Set (ι → F))
      (1 - (ReedSolomon.sqrtRate m domain) - η)
      (1 / (2 * η * (ReedSolomon.sqrtRate m domain))) := by
  rw [Code.isListDecodable_iff_forall_finset_card_le]
  intro y T hT
  exact card_le_of_subset_closeCodewords domain hm hη y T fun c hc ↦ hT _ hc

end ReedSolomon

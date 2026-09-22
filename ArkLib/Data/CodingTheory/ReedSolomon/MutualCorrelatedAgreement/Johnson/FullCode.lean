/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
public import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Reed–Solomon codes at full rate

A Reed–Solomon code whose degree bound is at least the block length is the whole ambient space:
Lagrange interpolation on all evaluation points represents every received word by a polynomial of
degree below `Fintype.card ι`. Every family of received words then consists of codewords, so the
mutual correlated agreement error is `0` for every generator at every real radius.

## Main statements

* `ReedSolomon.code_eq_top_of_card_le`: `code domain k = ⊤` when `Fintype.card ι ≤ k`.
* `ReedSolomon.fullRate_code_eq_top`: the case `k = Fintype.card ι`.
* `ReedSolomon.mcaError_eq_zero_of_card_le`: the MCA error of such a code is `0` for every
  generator and every radius.
* `ReedSolomon.mcaError_affineLine_fullRate_eq_zero`: the affine-line generator at
  `k = Fintype.card ι`.

## References

Ported from `Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/FullCode.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.

* `fullRate_code_eq_top` has the source statement. It is derived from the new
  `code_eq_top_of_card_le`, which allows any degree bound `k ≥ Fintype.card ι`.
* `mcaError_affineLine_fullRate_eq_zero` adds `[SampleableType F]`, which the current
  `CoreDefinitions.mcaError` requires of the seed space and the source's `mcaError` did not, and
  drops the source's `[Nonempty ι]`, which the proof does not use. It is derived from the new
  `mcaError_eq_zero_of_card_le`, which holds for every generator. The generic step, that the full
  module code has zero MCA error, is `CoreDefinitions.mcaError_top_eq_zero` in
  `ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator`.

The rest of the source's `Johnson/` directory is not ported here.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions

/-- **Reed–Solomon codes of degree bound at least the block length are full.** If
`Fintype.card ι ≤ k`, every word `w : ι → F` is the evaluation of its Lagrange interpolant on all
of `ι`, which has degree below `Fintype.card ι ≤ k`. The field hypothesis is needed for Lagrange
interpolation. For `k < Fintype.card ι` the code is a proper subspace. -/
theorem code_eq_top_of_card_le {ι F : Type*} [Fintype ι] [Field F] (domain : ι ↪ F) {k : ℕ}
    (hk : Fintype.card ι ≤ k) :
    code domain k = ⊤ := by
  let := Classical.decEq ι
  refine top_unique fun w _ ↦ mem_code_iff_eval.mpr
    ⟨Lagrange.interpolate Finset.univ domain w, ?_, fun i ↦
      Lagrange.eval_interpolate_at_node w domain.injective.injOn (Finset.mem_univ i)⟩
  exact (Lagrange.degree_interpolate_lt w domain.injective.injOn).trans_le
    (by simpa using hk)

/-- A Reed–Solomon code of degree bound equal to its block length is the full ambient code. This
is `code_eq_top_of_card_le` at `k = Fintype.card ι`. -/
theorem fullRate_code_eq_top {ι F : Type*} [Fintype ι] [Field F] (domain : ι ↪ F) :
    code domain (Fintype.card ι) = ⊤ :=
  code_eq_top_of_card_le domain le_rfl

/-- **Zero MCA error at full rate.** If `Fintype.card ι ≤ k`, then for every generator `G` and
every real radius `δ`, including `δ < 0` and `δ ≥ 1`, the MCA error of `code domain k` is `0`:
the code is `⊤` (`code_eq_top_of_card_le`), so every family consists of codewords. -/
theorem mcaError_eq_zero_of_card_le {ι F ℓ S : Type} [Fintype ι] [Field F] [Fintype ℓ]
    [Nonempty S] [Fintype S] [SampleableType S] (G : Generator S ℓ F) (domain : ι ↪ F) {k : ℕ}
    (hk : Fintype.card ι ≤ k) (δ : ℝ) :
    mcaError G (code domain k) δ = 0 := by
  rw [code_eq_top_of_card_le domain hk]
  exact mcaError_top_eq_zero G δ

/-- At full rate, affine-line MCA has zero error at every real radius. This is
`mcaError_eq_zero_of_card_le` for `AffineLineGenerator F` at `k = Fintype.card ι`. -/
theorem mcaError_affineLine_fullRate_eq_zero {ι F : Type} [Fintype ι] [Field F] [Fintype F]
    [SampleableType F] (domain : ι ↪ F) (δ : ℝ) :
    mcaError (AffineLineGenerator F) (code domain (Fintype.card ι)) δ = 0 :=
  mcaError_eq_zero_of_card_le _ domain le_rfl δ

end ReedSolomon

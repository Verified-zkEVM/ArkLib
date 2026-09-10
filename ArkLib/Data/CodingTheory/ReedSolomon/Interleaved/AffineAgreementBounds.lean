/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds

/-!
# Affine-space MCA bounds for interleaved Reed--Solomon codes

An affine-space MCA challenge combines `s + 1` received words using a seed in `F^s`. The general
affine-to-line reduction selects one affine line through this seed space whose bad-seed density
controls the full affine space. Applying that reduction directly to a row-wise interleaved module
code, then using affine-line interleaving invariance, reduces the result to a scalar exact-line
agreement certificate.

## Reading the statement

The theorem is uniform in the field `F`, block length `n`, dimension `k`, agreement threshold
`A`, interleaving width `t`, and affine dimension `s`. The hypotheses `0 < t` and `1 ≤ s` exclude
the two degenerate generators. The radius lies strictly between zero and one, and `hthreshold`
connects its real-valued distance condition to the integer agreement threshold.

If every received scalar line has at most `B` exceptional challenges, the conclusion bounds the
MCA error of the width-`t` code by `B / (|F| - 1)`. The standard affine-to-line factor is the only
loss, so the bound has no dependence on `t` or `s`.

## Mathematical scope

`mcaError` already takes the supremum over all `s + 1` received interleaved words. No received
family or exceptional set is assumed by the conclusion. The result is a coding-theoretic
probability over uniform field seeds; it does not model transcript generation, Fiat--Shamir
sampling, or commitment authentication.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial Code CoreDefinitions LinearCode
open scoped BigOperators ProbabilityTheory ENNReal

open Classical in
/-- A scalar exact-line certificate bounds positive-dimensional affine MCA for every nonempty
row-wise interleaving by `B / (|F| - 1)`. -/
theorem mcaError_affineSpace_interleaved_le_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k A t s : ℕ} (domain : Fin n ↪ F) (B : ℝ)
    (hline : LineExactAgreementBound domain k A B)
    (radius : NNReal) (ht : 0 < t) (hs : 1 ≤ s)
    (hradiusPos : 0 < radius) (hradiusLt : radius < 1)
    (hthreshold : A ≤ ⌈(n : ℝ) * (1 - (radius : ℝ))⌉₊) :
    mcaError (AffineSpaceGenerator F s)
        ((ReedSolomon.code domain k) ^⋈ (Fin t)) (radius : ℝ) ≤
      ENNReal.ofReal (B / ((Fintype.card F : ℝ) - 1)) := by
  have hlineError := mcaError_interleaved_le_of_exactAgreement domain B hline radius ht
    hradiusPos hradiusLt hthreshold
  obtain ⟨exceptional, hExceptionalCard, _⟩ := hline (fun _ ↦ 0) (fun _ ↦ 0)
  have hB : 0 ≤ B := (Nat.cast_nonneg exceptional.card).trans hExceptionalCard
  unfold mcaError
  refine iSup_le fun U ↦ ?_
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨W, hLineTransfer⟩ :=
    AffineMCALemmas.exists_line_bound hs
      ((ReedSolomon.code domain k) ^⋈ (Fin t)) U (radius : ℝ)
  have hWError :
      Pr_{let z ←$ᵖ F}[IsMCA (AffineLineGenerator F)
        ((ReedSolomon.code domain k) ^⋈ (Fin t)) z W (radius : ℝ)] ≤
        ENNReal.ofReal (B / (Fintype.card F : ℝ)) := by
    exact (le_iSup (fun V ↦
      Pr_{let z ←$ᵖ F}[IsMCA (AffineLineGenerator F)
        ((ReedSolomon.code domain k) ^⋈ (Fin t)) z V (radius : ℝ)]) W).trans hlineError
  rw [Probability.prob_uniform_eq_ofReal] at hWError
  have hLineDensity :
      ((Finset.univ.filter fun z : F ↦
        IsMCA (AffineLineGenerator F)
          ((ReedSolomon.code domain k) ^⋈ (Fin t)) z W (radius : ℝ)).card : ℝ) /
            (Fintype.card F : ℝ) ≤ B / (Fintype.card F : ℝ) := by
    exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg hB (by positivity))).mp hWError
  have hq : (1 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card (α := F)
  have hChain := hLineTransfer.trans hLineDensity
  have hFactor : 0 < 1 - 1 / (Fintype.card F : ℝ) := by
    rw [sub_pos, div_lt_one] <;> linarith
  simpa [Fintype.card_fun, Fintype.card_fin, Finset.prod_const] using
    (show
      ((Finset.univ.filter fun x : Fin s → F ↦
        IsMCA (AffineSpaceGenerator F s)
          ((ReedSolomon.code domain k) ^⋈ (Fin t)) x U (radius : ℝ)).card : ℝ) /
            (Fintype.card F : ℝ) ^ s ≤
          B / ((Fintype.card F : ℝ) - 1) by
      calc
        _ ≤ (B / (Fintype.card F : ℝ)) /
              (1 - 1 / (Fintype.card F : ℝ)) :=
          (le_div_iff₀ hFactor).2 (by simpa [mul_comm] using hChain)
        _ = B / ((Fintype.card F : ℝ) - 1) := by field_simp)

end

end ReedSolomon

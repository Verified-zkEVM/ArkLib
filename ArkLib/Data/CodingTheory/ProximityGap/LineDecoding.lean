/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Line decoding

Line decoding strengthens list decoding by requiring nearby words on a sampled affine line to
align with one affine pair of codewords. ArkLib follows [GG25] Definition 3.1, whose concluding
event requires both proximity and alignment. The proximity conjunct is absent from [ABF26]
Definition 4.20; without it, the stated MCA consequence is false. The discrepancy and a finite
counterexample are recorded in the
[ABF26 knowledge-base page](../../../../../docs/kb/papers/ABF26.md).

## Main definitions

- `CodingTheory.IsLineDecodable` — `(δ, a, b)`-line-decodability of an `F`-additive code.

## Main statements

- `CodingTheory.IsLineDecodable.mcaError_le` — `(δ, a, n+1)`-line-decodability gives
  `ε_mca(C, δ) ≤ a / |F|`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §4.4.
- [GG25] Goyal-Guruswami. Definition 3.1 / Theorem 3.5 (original source).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open CoreDefinitions ProximityGap

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- A code is `(δ, a, b)`-line-decodable when every family of nearby codewords along an affine
line that occurs with probability at least `a / |F|` agrees with one affine pair of codewords on
the same nearby challenges with probability at least `b / |F|`.

In formula:

  `∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ, U γ ∈ C) →`
  `  Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ] ≥ a / |F| →`
  `  ∃ u₁ u₂ ∈ C, Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ ∧`
  `                            U γ = u₁ + γ • u₂] ≥ b / |F|`

The function `U` takes values in the ambient word space, with membership in `C` imposed
separately. Probabilities are `ENNReal`-valued. -/
def IsLineDecodable (C : Set (ι → A)) (δ : ℝ≥0) (a b : ℕ) : Prop :=
  ∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ : F, U γ ∈ C) →
    (a : ENNReal) / (Fintype.card F : ENNReal)
        ≤ Pr_{let γ ← $ᵖ F}[δᵣ(f₁ + γ • f₂, U γ) ≤ δ] →
    ∃ u₁ ∈ C, ∃ u₂ ∈ C,
      (b : ENNReal) / (Fintype.card F : ENNReal)
          ≤ Pr_{let γ ← $ᵖ F}[
              δᵣ(f₁ + γ • f₂, U γ) ≤ δ ∧ U γ = u₁ + γ • u₂]

/-- If `C` is `(δ, a, n+1)`-line-decodable, then its affine-line MCA error is at most
`a / |F|`:

  `IsLineDecodable (F := F) C δ a (n+1) → mcaError(AffineLineGenerator F, C, δ) ≤ a / |F|`

where `n = |ι|`. The hypotheses retain the source conditions `0 < δ < 1` and `n < |F|`. -/
theorem IsLineDecodable.mcaError_le
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a : ℕ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_h : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
            (Fintype.card ι + 1)) :
    mcaError (AffineLineGenerator F) C (δ : ℝ)
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) := by
  sorry -- ABF26-T4.21; external admit [GG25 Thm 3.5].

end

end CodingTheory

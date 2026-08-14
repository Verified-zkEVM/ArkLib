/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Line decoding (ABF26 §4.4)

Line decoding is a structural strengthening of list decoding that lifts a fiberwise
"line is close to *some* codeword" statement into an aligned "line is close to a *single*
affine pair `u₁ + γ·u₂`". Definition 4.20 of *Open Problems in List Decoding and Correlated
Agreement* (Arnon, Boneh, Fenzi; April 8, 2026) formalises this; the immediate downstream
fact is Theorem 4.21, which converts a line-decoding bound into a mutual correlated
agreement (MCA) bound.

## Main definitions

- `CodingTheory.LineDecodable` — ABF26 Definition 4.20: `(δ, a, b)`-line-decodability of
  an `F`-additive code `C`.

## Main statements

- `CodingTheory.LineDecodable.mcaError_le` — ABF26 Theorem 4.21 [GG25 Thm 3.5]:
  `(δ, a, n+1)`-line-decodability gives an MCA bound `ε_mca(C, δ) ≤ a / |F|`.
  Admitted as an external result; the proof in GG25 routes through the line-decoder's
  alignment guarantee and a `Δ_S = 0`-witness argument.

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
/-- **ABF26 Definition 4.20 [GG25 Def 3.1].** A code `C ⊆ A^ι` is `(δ, a, b)`-**line-decodable**
when every `γ`-indexed family of codewords that aligns with a random line `f₁ + γ·f₂` on at
least an `a/|F|` fraction of `γ`'s is itself induced (on at least a `b/|F|` fraction of `γ`'s)
by a single affine pair `(u₁, u₂)` of codewords on those same close challenges.

In formula:

  `∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ, U γ ∈ C) →`
  `  Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ] ≥ a / |F| →`
  `  ∃ u₁ u₂ ∈ C, Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ ∧`
  `                            U γ = u₁ + γ • u₂] ≥ b / |F|`

The hypothesis pins each `U γ` inside `C`; ABF26 writes this as `U : F → C` but Lean is
cleaner with a function into the ambient space plus a side condition. The probabilities
are read in `ENNReal`, matching the convention in
[`ProximityGap.Errors`](ProximityGap.Errors.lean). -/
def LineDecodable (C : Set (ι → A)) (δ : ℝ≥0) (a b : ℕ) : Prop :=
  ∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ : F, U γ ∈ C) →
    (a : ENNReal) / (Fintype.card F : ENNReal)
        ≤ Pr_{let γ ← $ᵖ F}[δᵣ(f₁ + γ • f₂, U γ) ≤ δ] →
    ∃ u₁ ∈ C, ∃ u₂ ∈ C,
      (b : ENNReal) / (Fintype.card F : ENNReal)
          ≤ Pr_{let γ ← $ᵖ F}[
              δᵣ(f₁ + γ • f₂, U γ) ≤ δ ∧ U γ = u₁ + γ • u₂]

/-- **ABF26 Theorem 4.21 [GG25 Thm 3.5].** If `C` is `(δ, a, n+1)`-line-decodable, then its
mutual correlated agreement error is bounded by `a / |F|`:

  `LineDecodable (F := F) C δ a (n+1) → mcaError(AffineLineGenerator F, C, δ) ≤ a / |F|`

where `n = |ι|`. The conclusion uses the canonical affine-line generator and real-radius
`mcaError`. The proof in [GG25] applies line decoding to codewords selected for the bad
seeds and uses the `n+1` aligned seeds to force the common affine pair required to rule
out the MCA obstruction.

GG25 Theorem 3.5 assumes `δ ∈ (0,1)`; both inequalities are explicit below.
Admitted as an external result; formalising the GG25 argument is tracked separately. -/
theorem LineDecodable.mcaError_le
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a : ℕ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_h : LineDecodable (F := F) ((C : Set (ι → A))) δ a
            (Fintype.card ι + 1)) :
    mcaError (AffineLineGenerator F) C (δ : ℝ)
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) := by
  sorry -- ABF26-T4.21; external admit [GG25 Thm 3.5].

end

end CodingTheory

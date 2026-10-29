/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineCoefficients.Basic

/-!
# Correlated agreement from uniformly sampled affine coefficients

Uniform coefficient vectors induce the uniform distribution on their affine image, even
when the directions are dependent. This gives a coefficient-form BCIKS20 bound for batching.
-/

@[expose] public section

namespace ProximityGap

open OracleComp Finset
open scoped NNReal ENNReal ProbabilityTheory

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (m : ℕ)

/-- Coefficient-form affine-space correlated agreement, with the same radius and error
as `correlatedAgreement_affine_spaces`. No independence of the directions is required. -/
theorem correlatedAgreement_affine_coefficients
    {ι : Type} [Fintype ι] [Nonempty ι] [NeZero m]
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg) (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι) (hε : errorBound δ deg domain < 1)
    (u : Fin (m + 1) → ι → F)
    (hprob : Pr{let cs ← $ᵗ (Fin m → F)}[Code.relDistFromCode
      (u 0 + ∑ i, cs i • u i.succ)
        (ReedSolomon.code domain deg).carrier ≤ δ] > errorBound δ deg domain) :
    Code.jointAgreement (ReedSolomon.code domain deg).carrier δ u := by
  classical
  apply correlatedAgreement_affine_spaces hdeg hδ_pos hδ hRS hε u
  exact lt_of_lt_of_eq hprob (uniform_affine_combination m u (fun f ↦
    Code.relDistFromCode f (ReedSolomon.code domain deg).carrier ≤ δ))

end ProximityGap

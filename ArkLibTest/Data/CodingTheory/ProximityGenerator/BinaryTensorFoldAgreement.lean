/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement

/-! # Public statements for binary tensor folding

These examples check the equality-weight interpretation and the full-set agreement interface.
-/

namespace TensorMCA

open CoreDefinitions LinearCode
open scoped BigOperators

variable {ι F A : Type} [Fintype ι] [DecidableEq ι]
  [Field F] [Fintype F] [DecidableEq F]
  [AddCommMonoid A] [Module F A] [DecidableEq A]

/-- Public-import canary for the equality-weight view through ArkLib's tensor generator. -/
example (r : Fin 2 → F) (u : (Fin 2 → Bool) → ι → A) :
    binaryTensorFold r u = fun i ↦
      ∑ leaf, PolynomialGenIsMCA.tensorGeneratorPi
        (fun _ ↦ binaryEqualityGenerator) r leaf • u leaf i :=
  binaryTensorFold_eq_tensorGeneratorPi r u

/-- The abstract hypothesis is uniform over a family, rather than a scalar-only line premise. -/
example {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u₀ u₁ : Fin 5 → ι → A) :
    (levelExceptional hlevel u₀ u₁).card ≤ exceptionalCount :=
  levelExceptional_card_le hlevel u₀ u₁

/-- Height zero has no level event. -/
example {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin 0 → Bool) → ι → A) : tensorFoldBad hlevel u = ∅ :=
  tensorFoldBad_eq_empty_height_zero hlevel u

/-- Height one pays for exactly one possible level event. -/
example {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin 1 → Bool) → ι → A) :
    (tensorFoldBad hlevel u).card ≤ exceptionalCount := by
  simpa using tensorFoldBad_card_le hlevel u

/-- Height two pays for one width-independent exceptional event per level. -/
example {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin 2 → Bool) → ι → A) :
    (tensorFoldBad hlevel u).card ≤
      2 * exceptionalCount * Fintype.card F := by
  simpa using tensorFoldBad_card_le hlevel u

end TensorMCA

namespace ReedSolomon

open Code TensorMCA

/-- The interleaved specialization has height-three factor three at width eight. -/
example {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hkAgreement : k ≤ agreement)
    (u : (Fin 3 → Bool) → Fin n → Fin 8 → F) :
    (tensorFoldBad
      (fullSetLevelWitness_interleaved_of_exactAgreement
        domain hline (by omega) hkAgreement) u).card ≤
        3 * exceptionalCount * Fintype.card F ^ 2 :=
  interleavedRS_tensorFoldBad_card_le_heightThree domain hline (by omega) hkAgreement u

end ReedSolomon

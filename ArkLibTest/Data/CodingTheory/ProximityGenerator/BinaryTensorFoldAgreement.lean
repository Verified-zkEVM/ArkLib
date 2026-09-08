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

/-- Height two pays for all three internal nodes, including two nodes sharing the second-level
challenge. -/
example {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hline : FullSetLineWitness C agreement exceptionalCount)
    (u : (Fin 2 → Bool) → ι → A) :
    (tensorFoldBad hline u).card ≤
      3 * exceptionalCount * Fintype.card F := by
  simpa using tensorFoldBad_card_le hline u

end TensorMCA

namespace ReedSolomon

open Code TensorMCA

/-- The interleaved specialization retains the height-three factor seven at width eight. -/
example {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount : ℕ}
    (domain : Fin n ↪ F)
    (hline : LineExactAgreementBound domain k agreement exceptionalCount)
    (hkAgreement : k ≤ agreement)
    (u : (Fin 3 → Bool) → Fin n → Fin 8 → F) :
    (tensorFoldBad
      (fullSetLineWitness_interleaved_of_exactAgreement
        domain hline (by omega) hkAgreement) u).card ≤
        7 * exceptionalCount * Fintype.card F ^ 2 :=
  interleavedRS_tensorFoldBad_card_le_heightThree domain hline (by omega) hkAgreement u

end ReedSolomon

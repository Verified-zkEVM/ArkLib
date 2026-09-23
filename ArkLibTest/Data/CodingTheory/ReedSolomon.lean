/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
import Mathlib.Tactic.NormNum

/-!
# Reed–Solomon acceptance tests

Concrete instances check the agreement threshold, its distance interpretation, codeword
determination, and the single-word power-agreement guarantee.
-/

open Polynomial ReedSolomon CoreDefinitions

namespace ReedSolomonAcceptance

-- Block length `10`, message length `3`, gap `1 / 4`: the threshold is `3 + ⌈5 / 2⌉ = 6`.
example : agreementThreshold (1 / 4) 10 3 ≤ 6 ↔
    (3 : ℝ) + (1 / 4) * 10 ≤ (6 : ℕ) := by
  exact agreementThreshold_le_iff_real (by norm_num) 10 3 6

example :
    (Code.relHammingDist ![false, true] ![false, false] : ℝ) ≤
        capacityRadius (1 / 4) 2 1 ↔
      agreementThreshold (1 / 4) 2 1 ≤ Code.agree ![false, false] ![false, true] := by
  exact relHammingDist_le_capacityRadius_iff_agreementThreshold_le
    (delta := 1 / 4) (messageDim := 1) (by norm_num) (by decide)
    ![false, false] ![false, true]

end ReedSolomonAcceptance

namespace PowerAgreementTest

/-- The evaluation points `0, 1, 2` in `ℚ`. -/
def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

example : Code.DeterminedByAgreement (code domain3 2) 2 :=
  determinedByAgreement_code domain3 le_rfl

-- A single received word has uniform exact power agreement with no exceptional challenge.
example : UniformExactPowerAgreement domain3 ![![1, 2, 5]] 2 0 0 :=
  uniformExactPowerAgreement_singleton domain3 _ 2 0

end PowerAgreementTest

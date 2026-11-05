/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.CertificateWitnesses
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance case for the generic certificate witnesses

A safe MCA witness for `RS[2, 2]` over `ZMod 5` from
`GrandChallenges.lineExactAgreementBound_of_heightSlotCount` with certificate parameters
`(m, M, μ, h) = (1, 1, 1, 1)`. The slot inequality is small enough for `decide`.
-/

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative
open ProximityGap ProximityGap.GrandChallenges

namespace CertificateWitnessesTest

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable instance : SampleableType (ZMod 5) := SampleableType.ofFintype _

/-- `RS[2, 2]` over `ZMod 5`, certificate parameters `(m, M, μ, h) = (1, 1, 1, 1)`. -/
noncomputable example (domain : Fin 2 ↪ ZMod 5) :
    McaLowerWitness (ReedSolomon.code domain 2) (10 ^ 12) :=
  McaLowerWitness.ofLineExactAgreement (δ := 0) domain
    (lineExactAgreementBound_of_heightSlotCount (n := 2) (k := 2) (A := 2) (m := 1) (M := 1)
      (μ := 1) (h := 1) domain le_rfl le_rfl le_rfl le_rfl le_rfl (by norm_num) (by decide)
      (Or.inr (by rw [ZMod.ringChar_zmod_n]; norm_num)))
    zero_le_one (by norm_num) (by
      simp only [FirstOrder.Squarefree.retainedSquarefreeLineAgreementEnvelope,
        FirstOrder.Squarefree.retainedOrdinaryCurveAgreementCharge, agreementIncidenceRatio,
        ZMod.card]
      norm_num)

end CertificateWitnessesTest

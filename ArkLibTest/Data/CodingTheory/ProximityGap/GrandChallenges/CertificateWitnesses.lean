/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.CertificateWitnesses
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance cases for the generic certificate witnesses

* Safe side: `RS[2, 2]` over `ZMod 5` with certificate parameters `(m, M, μ, h) = (1, 1, 1, 1)`.
  The slot inequality is small enough for `decide`. The resulting line bound exceeds `|F|`, so the
  example only shows that the hypotheses of `lineExactAgreementBound_of_heightSlotCount` and
  `McaLowerWitness.ofLineExactAgreement` can be met together; the threshold `10 ^ 12` is not a
  meaningful MCA bound.
* Unsafe side: `RS[8, 2]` over `ZMod 17` on the powers of the primitive `8`-th root of unity `2`.
  The coset list at `s = 1`, `r = 3` has `⌊C(7, 3) / 8⌋ = 4` codewords within relative distance
  `5/8` of one word, so `ListUpperWitness.ofCosetList` gives an unsafe witness at `ε* = 1/17`.
-/

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative
open ProximityGap ProximityGap.GrandChallenges

namespace CertificateWitnessesTest

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

noncomputable instance : SampleableType (ZMod 5) := SampleableType.ofFintype _

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

noncomputable instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

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

/-- `2` is a primitive `8`-th root of unity in `ZMod 17`. -/
theorem isPrimitiveRoot_two : IsPrimitiveRoot (2 : ZMod 17) 8 :=
  IsPrimitiveRoot.mk_of_lt 2 (by norm_num) (by decide) fun l hl0 hl8 ↦ by
    interval_cases l <;> decide

/-- The coset construction at `n = 8`, `s = 1`, `r = 3`: four codewords of `RS[8, 2]` over
`ZMod 17` agree with one word on `3` of the `8` points, so the list size exceeds
`ε* · |F| = 1`. -/
noncomputable example :
    ListUpperWitness (ReedSolomon.code (primitiveRootDomain isPrimitiveRoot_two) 2 :
      Set (Fin 8 → ZMod 17)) 1 (1 / 17) :=
  ListUpperWitness.ofCosetList isPrimitiveRoot_two (s := 1) (r := 3) (δ := 5 / 8)
    (one_dvd 8) (by norm_num) (by norm_num) (by push_cast; norm_num) 1 le_rfl (by
      rw [ZMod.card]
      norm_num [Nat.choose]
      rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
      norm_num)

end CertificateWitnessesTest

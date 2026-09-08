/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.Binius.RingSwitchingPipeline
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Accounting

/-!
# GF16 ring-switching challenge-error accounting

The live Binius rank-four, retained-dimension-two fixture has one batching challenge with
error 3/16 and two scalar challenges with error 2/16 each. The exact sums below concern the
production error functions already used by the complete pipeline's knowledge contract.
They do not invoke an RBR-to-ordinary-soundness bridge or certify the later interleaved FRI opening.
The scalar variant adds a deterministic head message and has the same challenge accounting.
-/

noncomputable section

namespace Binius.RingSwitchingAccountingTests

open ProtocolSpec RingSwitching.Packing ConcreteCommitment RingSwitchingCommitmentTests
open scoped NNReal

local instance : Fintype PackedField := Fintype.ofFinite PackedField
local instance : DecidableEq PackedField := Classical.decEq PackedField

/-- The full-family pipeline has one batching and two tail challenge indices. -/
theorem fullFamily_challenge_count :
    Fintype.card (FullFamilyOpening.pSpec data 2 batch).ChallengeIdx = 3 := by
  change Fintype.card {i : Fin 7 //
    (!v[Direction.P_to_V, Direction.V_to_P, Direction.P_to_V, Direction.V_to_P,
      Direction.P_to_V, Direction.V_to_P, Direction.P_to_V] i) = Direction.V_to_P} = 3
  decide

/-- The extra deterministic scalar head leaves the challenge count unchanged. -/
theorem scalar_challenge_count :
    Fintype.card (ScalarOpening.pSpec data 2 batch).ChallengeIdx = 3 := by
  change Fintype.card {i : Fin 8 //
    (!v[Direction.P_to_V, Direction.P_to_V, Direction.V_to_P, Direction.P_to_V,
      Direction.V_to_P, Direction.P_to_V, Direction.V_to_P, Direction.P_to_V] i) =
        Direction.V_to_P} = 3
  decide

/-- Sum the production error function used by the GF16 Binius pipeline. -/
theorem fullFamily_error_sum :
    (∑ i, FullFamilyOpening.rbrError data 2 batch i) = (7 : ℝ≥0) / 16 := by
  rw [FullFamilyOpening.rbrError_sum, batch_error, field_card]
  norm_num

/-- The scalar protocol's additional message contributes no additional challenge error. -/
theorem scalar_error_sum :
    (∑ i, ScalarOpening.rbrError data 2 batch i) = (7 : ℝ≥0) / 16 := by
  rw [ScalarOpening.rbrError_sum, batch_error, field_card]
  norm_num

end Binius.RingSwitchingAccountingTests

end

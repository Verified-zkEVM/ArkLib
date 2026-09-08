/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.FRIBinius.RingSwitchingCommitment
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Completeness
import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Knowledge
import ArkLibTest.ProofSystem.Binius.ConcreteCommitment

/-!
# A full-family ring-switch consumer of the actual GF16 Binius oracle

The field, arbitrary rank-four basis, retained dimension two, rate exponent one and period one
come from the concrete commitment fixture. The input witness is the unpacked nonconstant X0
polynomial and the oracle is its production novel-basis codeword family. No first-basis-element
normalization or identity-polynomial commitment is used.
-/

noncomputable section

namespace Binius.RingSwitchingCommitmentTests

open Module MvPolynomial OracleSpec OracleComp ProtocolSpec ProbabilityTheory
open RingSwitching.Packing RingSwitching.Packing.FullFamily
open ConcreteCommitment
open scoped NNReal

local instance : Fintype PackedField := Fintype.ofFinite PackedField
local instance : DecidableEq PackedField := Classical.decEq PackedField
local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨by simpa only [ZMod.ringChar_zmod_n] using Nat.prime_two⟩
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩
local instance : Fact (1 ∣ 2) := ⟨one_dvd 2⟩

abbrev data : PackingData (ZMod 2) where
  P := PackedField
  E := PackedField
  ιP := Fin 4
  ιE := Fin 4
  packBasis := binaryBasis
  openBasis := binaryBasis
abbrev pc := FRIBinius.binaryBasefoldPackedCommitment
  2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide)
abbrev batch := BatchingStrategy.gammaPowers PackedField 4

def family := data.unpack (coordinate 0)
def input : Input data 2 :=
  (fun i => aeval separatingPoint (family i).val, separatingPoint)
def oracle : ∀ j, pc.OStmt j := honestOracle (coordinate 0)
def slices := honestSlices data 2 input.2 (coordinate 0)

/-- The new exact commitment relation is the actual production unique-distance relation. -/
theorem actual_relation (p : PackedField⦃≤ 1⦄[X Fin 2]) (o : InitialOracles) :
    pc.commitsTo o p ↔ commitment.initialCompatibility (p, o) := Iff.rfl

/-- The adapter's honest constructor is the actual production oracle constructor. -/
theorem actual_honest_constructor : pc.commit (coordinate 0) = honestOracle (coordinate 0) := rfl

/-- Reading the oracle through the production accessor yields the actual novel-basis codeword. -/
theorem oracle_first_codeword :
    BinaryBasefold.getFirstOracle (ZMod 2) binaryBasis oracle =
      BinaryBasefold.firstOracleEncoding (ZMod 2) binaryBasis
        (h_ℓ_add_R_rate := show 2 + 1 < 2 ^ 2 by decide) (coordinate 0) :=
  BinaryBasefold.getFirstOracle_honestInitialOracleStatement (ZMod 2) binaryBasis 1 (coordinate 0)

/-- Rank-four batching in the actual field of sixteen elements has error three sixteenths. -/
theorem batch_error : batch.error = (3 : ℝ≥0) / 16 := by
  change ((4 - 1 : ℕ) : ℝ≥0) / (Fintype.card PackedField : ℝ≥0) = _
  rw [field_card]
  norm_num

/-- The legacy functionality premise is also discharged by the real commitment theorem. -/
theorem legacy_functional : commitment.Functional :=
  FRIBinius.binaryBasefold_functional 2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide)

/-- The full-family source relation has a concrete witness on the real nonconstant commitment. -/
theorem input_related : ((input, oracle), family) ∈ relIn data 2 pc := by
  refine ⟨fun _ => rfl, ?_⟩
  change pc.commitsTo oracle (data.packedMLE (data.unpack (coordinate 0)))
  exact (congrArg (pc.commitsTo oracle) (data.packedMLE_unpack (coordinate 0))).mpr
    (honestOracle_compatible (coordinate 0))

/-- The generic commitment cannot interpret the same actual oracle as the other coordinate. -/
theorem rejects_other_coordinate : ¬ pc.commitsTo oracle (coordinate 1) :=
  honestOracle_rejects_other_coordinate

/-- The production phase accepts every batching challenge and returns the identical real oracle. -/
theorem verifier_accept (c : PackedField) :
    (verifier data 2 batch pc).toVerifier.verify (input, oracle) (FullTranscript.mk2 slices c) =
      pure (nextStatement data 2 batch input slices c, oracle) := by
  rw [verifier_verify]
  have hc : data.claimConsistent input.1 slices := by
    change data.claimConsistent input.1 (honestSlices data 2 input.2 (coordinate 0))
    simpa only [family, data.packedMLE_unpack] using honest_check data 2 pc input_related
  exact if_pos hc

/-- The actual packed polynomial and the same oracle satisfy the sumcheck output relation. -/
theorem output_related (c : PackedField) :
    ((nextStatement data 2 batch input slices c, oracle), coordinate 0) ∈ relOut data 2 batch pc :=
  ⟨data.sumcheckClaim_of_slices (honestSlices_mem_sliceRel data 2 _ _) _,
    honestOracle_compatible _⟩

def falseInput : Input data 2 := (fun i => input.1 i + 1, input.2)

/-- An altered full family fails while retaining the same otherwise valid production commitment. -/
theorem false_check : ¬ data.claimConsistent falseInput.1 slices := by
  intro h
  have ht := honest_check data 2 pc input_related
  have ht' : data.claimConsistent input.1 slices := by
    change data.claimConsistent input.1 (honestSlices data 2 input.2 (coordinate 0))
    simpa only [family, data.packedMLE_unpack] using ht
  have he := data.transpose.injective
    (((data.claimConsistent_iff_transpose _ _).mp h).trans
      ((data.claimConsistent_iff_transpose _ _).mp ht').symm)
  have hv := congrFun he (0 : Fin 4)
  change input.1 0 + 1 = input.1 0 at hv
  exact one_ne_zero (add_left_cancel (hv.trans (add_zero _).symm))

/-- The actual materialized verifier aborts on that false family for every challenge. -/
theorem verifier_reject (c : PackedField) :
    (verifier data 2 batch pc).toVerifier.verify (falseInput, oracle)
      (FullTranscript.mk2 slices c) = failure := by
  rw [verifier_verify]
  exact if_neg false_check

/-- Actual worst-case knowledge uses the production binding proof and its same-oracle KSF. -/
theorem worstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn data 2 pc) (relOut data 2 batch pc) (verifier data 2 batch pc).toVerifier
      (WitMid data 2) (extractor data 2 batch pc)
      (knowledgeStateFunction data 2 batch pc init impl) (rbrError data batch) :=
  rbrKnowledgeSoundnessWorstCaseWith data 2 batch pc
    (FRIBinius.binaryBasefoldPackedCommitment_functional
      2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide)) Function.injective_id init impl

/-- Actual perfect completeness is uniform over initial oracle states. -/
theorem complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data 2 batch pc).perfectCompleteness init impl
      (relIn data 2 pc) (relOut data 2 batch pc) :=
  perfectCompleteness data 2 batch pc init impl

end Binius.RingSwitchingCommitmentTests

end

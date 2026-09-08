/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.ExactCommitment
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarFamily.Security
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarFamily.Execution
import ArkLibTest.ProofSystem.RingSwitching.Packing.ScalarHead

/-!
# scalar-family composition acceptance

A concrete nonconstant source has an opening value in a rank-two product algebra. Packing has
rank one and the challenge is uniform in ZMod5, giving nonzero batching error 1/5. Tests reject
false scalar claims and false slices independently at the three-step verifier.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.ScalarFamily

open MvPolynomial Module OracleSpec OracleComp ProtocolSpec
open RingSwitching.Packing.ScalarFamily
open scoped NNReal

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev data : PackingData (ZMod 5) where
  P := ZMod 5
  E := Fin 2 → ZMod 5
  ιP := Unit
  ιE := Fin 2
  packBasis := Basis.singleton Unit _
  openBasis := Pi.basisFun _ _

abbrev layout := ScalarHead.packedPrefixLayout data 1 0 (Equiv.ofUnique _ _)
abbrev bat := BatchingStrategy.gammaPowers (ZMod 5) 2
abbrev pc := ExactPackedCommitment.polynomialOracle data.P 1

def source : layout.Source := ⟨X 0, by simp [mem_restrictDegree_iff_degreeOf_le]⟩
def point : Fin 1 → data.E := fun _ i => if i = 0 then 2 else 3
def query : layout.Query := (Fin.elim0, point)
def stmt : ScalarHead.Input data 1 layout := (query, layout.eval query source)
def ost := pc.commit (data.packedMLE (layout.components source))
def α := ScalarHead.partials data 1 layout query (layout.components source)
def slices := FullFamily.honestSlices data 1 point (data.packedMLE (layout.components source))
def tr (c : ZMod 5) : FullTranscript (pSpec data bat) :=
  ScalarHead.transcript data α ++ₜ FullTranscript.mk2 slices c

/-- The original scalar relation has the nonconstant source as a witness. -/
theorem source_related : ((stmt, ost), source) ∈ relIn data 1 layout pc :=
  ScalarHead.relIn_honest data 1 layout pc query source

/-- The full-family seam is related, with the identical commitment oracle. -/
theorem seam_related :
    ((ScalarHead.nextStatement data 1 layout stmt α, ost), layout.components source) ∈
      FullFamily.relIn data 1 pc :=
  ScalarHead.honest_relOut data 1 layout pc source_related

/-- Every batching challenge accepts the honest three-step transcript. -/
theorem accept (c : ZMod 5) :
    (verifier data 1 layout bat pc).toVerifier.run (stmt, ost) (tr c) =
      pure (FullFamily.nextStatement data 1 bat
        (ScalarHead.nextStatement data 1 layout stmt α) slices c, ost) := by
  rw [verifier_run]
  exact if_pos (ScalarHead.honest_check data 1 layout pc source_related) |>.trans
    (if_pos (FullFamily.honest_check data 1 pc seam_related))

/-- The packed witness and same commitment satisfy the output relation for every challenge. -/
theorem output_related (c : ZMod 5) :
    ((FullFamily.nextStatement data 1 bat (ScalarHead.nextStatement data 1 layout stmt α)
      slices c, ost), data.packedMLE (layout.components source)) ∈ relOut data 1 bat pc :=
  FullFamily.honest_relOut data 1 bat pc seam_related c

/-- The composed knowledge contract uses the exact production extractor and both phase proofs. -/
theorem worst_case {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (relIn data 1 layout pc) (relOut data 1 bat pc) (verifier data 1 layout bat pc).toVerifier
      (WitMid data 1 layout) (extractor data 1 layout bat pc)
      (knowledgeStateFunction data 1 layout bat pc init impl) (rbrError data bat) :=
  rbrKnowledgeSoundnessWorstCaseWith data 1 layout bat pc pc.commitsTo_functional
    Function.injective_id init impl

/-- The sole challenge incurs a nonzero 1/5 batching error. -/
theorem error (i : (pSpec data bat).ChallengeIdx) :
    rbrError data bat i = (1 / 5 : ℝ≥0) := by
  rw [rbrError_eq]
  norm_num [bat, BatchingStrategy.gammaPowers]

/-- Perfect completeness of the oracle reduction from every shared initial state. -/
theorem complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data 1 layout bat pc).perfectCompleteness init impl
      (relIn data 1 layout pc) (relOut data 1 bat pc) :=
  perfectCompleteness data 1 layout bat pc init impl

def falseStmt : ScalarHead.Input data 1 layout := (query, stmt.2 + 1)

/-- Changing only the original scalar claim makes the first guard fail. -/
theorem false_scalar_check : ¬ ScalarHead.check data 1 layout falseStmt α := by
  intro h
  have ht := ScalarHead.honest_check data 1 layout pc source_related
  change stmt.2 + 1 = ∑ i, layout.weight stmt.1 i * α i at h
  change stmt.2 = ∑ i, layout.weight stmt.1 i * α i at ht
  have hz : (1 : data.E) = 0 := add_left_cancel (h.trans (ht.symm.trans (add_zero _).symm))
  have hz0 := congrFun hz 0
  exact (by decide : (1 : ZMod 5) ≠ 0) hz0

/-- First-guard rejection persists through the composed verifier at every challenge. -/
theorem false_scalar_rejected (c : ZMod 5) :
    (verifier data 1 layout bat pc).toVerifier.run (falseStmt, ost) (tr c) = failure := by
  rw [verifier_run]
  exact if_neg false_scalar_check

/-- The reduction rejects the false scalar even after its suffix prover makes the
batching challenge query; the query transport is the append transport. -/
theorem false_scalar_reduction_rejected :
    ((reduction data 1 layout bat pc).toReduction.run (falseStmt, ost) source).run = (do
      let _ ← liftAppendRight (ScalarHead.pSpec data)
        ((FullFamily.prover data 1 bat pc).run
          (ScalarHead.nextStatement data 1 layout falseStmt α, ost) (layout.components source))
      pure none) :=
  reduction_reject_scalar data 1 layout bat pc falseStmt ost source false_scalar_check

/-- Perturb one slice while keeping the honest scalar family and commitment fixed. -/
def falseSlices : data.ιE → data.P := fun i => slices i + if i = 0 then 1 else 0

theorem false_slices_check : ¬ data.claimConsistent α falseSlices := by
  intro h
  have ht := FullFamily.honest_check data 1 pc seam_related
  have he : falseSlices = slices :=
    ((data.claimConsistent_iff_transpose _ _).mp h).symm.trans
      ((data.claimConsistent_iff_transpose _ _).mp ht)
  have h0 := congrFun he 0
  simp only [falseSlices] at h0
  exact (by decide : (1 : ZMod 5) ≠ 0) (add_left_cancel (h0.trans (add_zero _).symm))

/-- The second guard rejects false slices even after a valid scalar check. -/
theorem false_slices_rejected (c : ZMod 5) :
    (verifier data 1 layout bat pc).toVerifier.run (stmt, ost)
      (ScalarHead.transcript data α ++ₜ FullTranscript.mk2 falseSlices c) = failure := by
  rw [verifier_run]
  exact if_pos (ScalarHead.honest_check data 1 layout pc source_related) |>.trans
    (if_neg false_slices_check)

end RingSwitching.Packing.Tests.ScalarFamily

end

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.WitnessAttachment
public import ArkLib.ProofSystem.Spartan.Sumcheck.First
public import ArkLib.ProofSystem.Spartan.Sumcheck.Second
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound
public import ArkLib.OracleReduction.Security.GuardedBridges

/-!
# The Spartan oracle reduction

Seven stages reduce an original R1CS instance to the terminal oracle check. The witness is
attached before every challenge, and all subsequent stages retain the same matrix and witness
oracles. The honest prover uses the executable virtual-polynomial realizations.
-/

@[expose] public section

namespace Spartan

open OracleComp OracleSpec ProtocolSpec Realization
open scoped NNReal

variable {R : Type} [Field R] [DecidableEq R] [SampleableType R] (sz : R1CS.Size)

local notation "params" => PublicParams.forSize sz

local instance : ∀ i, OracleInterface.{0, 0} (R1CS.OracleStatement R sz i) :=
  WitnessAttachment.sourceOracleInterface sz

namespace Assembly

/-- The public context at each boundary of the seven stages. -/
abbrev Statement : Fin 8 → Type :=
  ![R1CS.Statement R sz, R1CS.Statement R (params).toSizeR1CS,
    FirstSumcheck.Statement (R := R) params, Evaluation.Statement (R := R) params,
    Batching.InputStatement (R := R) params, Batching.Statement (R := R) params,
    FinalStatement (R := R) params, Unit]

/-- Only the attachment input has a private witness. -/
abbrev Witness : Fin 8 → Type := ![R1CS.Witness R sz, Unit, Unit, Unit, Unit, Unit, Unit, Unit]

/-- Attachment adds the witness oracle to the original matrix family. -/
abbrev OracleIndex : Fin 8 → Type :=
  ![R1CS.MatrixIdx, R1CS.MatrixIdx ⊕ Fin 1, R1CS.MatrixIdx ⊕ Fin 1,
    R1CS.MatrixIdx ⊕ Fin 1, R1CS.MatrixIdx ⊕ Fin 1, R1CS.MatrixIdx ⊕ Fin 1,
    R1CS.MatrixIdx ⊕ Fin 1, R1CS.MatrixIdx ⊕ Fin 1]

/-- The source matrices and the retained padded oracle family. -/
abbrev Oracles : (i : Fin 8) → OracleIndex i → Type
  | 0 => R1CS.OracleStatement R sz
  | 1 => OracleStatement (R := R) params
  | 2 => OracleStatement (R := R) params
  | 3 => OracleStatement (R := R) params
  | 4 => OracleStatement (R := R) params
  | 5 => OracleStatement (R := R) params
  | 6 => OracleStatement (R := R) params
  | 7 => OracleStatement (R := R) params

instance oracleInterface : ∀ i j, OracleInterface.{0, 0} (Oracles (R := R) sz i j)
  | 0 => WitnessAttachment.sourceOracleInterface sz
  | 1 => Terminal.oracleInterface params
  | 2 => Terminal.oracleInterface params
  | 3 => Terminal.oracleInterface params
  | 4 => Terminal.oracleInterface params
  | 5 => Terminal.oracleInterface params
  | 6 => Terminal.oracleInterface params
  | 7 => Terminal.oracleInterface params

/-- The lengths of the attachment, challenge, sumcheck, claims, batch, sumcheck, and check. -/
abbrev length : Fin 7 → ℕ :=
  ![1, 1, Fin.vsum (fun _ : Fin (params).ℓ_m => 2), 1, 1,
    Fin.vsum (fun _ : Fin (params).ℓ_n => 2), 0]

/-- The protocol of each stage, in transcript order. -/
abbrev stageSpec : (i : Fin 7) → ProtocolSpec (length sz i)
  | 0 => WitnessAttachment.pSpec (R := R) sz
  | 1 => RandomEvaluation.pSpec R (params).ℓ_m
  | 2 => Sumcheck.Spec.pSpec R 3 (params).ℓ_m
  | 3 => SendEvaluations.pSpec R
  | 4 => Batching.pSpec R
  | 5 => Sumcheck.Spec.pSpec R 2 (params).ℓ_n
  | 6 => !p[]

instance messageInterface : ∀ i j, OracleInterface.{0, 0} ((stageSpec (R := R) sz i).Message j)
  | 0 => by
    letI : OracleInterface (R1CS.Witness R (params).toSizeR1CS) := Terminal.witnessInterface params
    exact inferInstanceAs (∀ j, OracleInterface ((WitnessAttachment.pSpec (R := R) sz).Message j))
  | 1 => inferInstanceAs (∀ j, OracleInterface ((RandomEvaluation.pSpec R (params).ℓ_m).Message j))
  | 2 => inferInstanceAs (∀ j, OracleInterface ((Sumcheck.Spec.pSpec R 3 (params).ℓ_m).Message j))
  | 3 => inferInstanceAs (∀ j, OracleInterface ((SendEvaluations.pSpec R).Message j))
  | 4 => inferInstanceAs (∀ j, OracleInterface ((Batching.pSpec R).Message j))
  | 5 => inferInstanceAs (∀ j, OracleInterface ((Sumcheck.Spec.pSpec R 2 (params).ℓ_n).Message j))
  | 6 => inferInstanceAs (∀ j, OracleInterface ((!p[] : ProtocolSpec 0).Message j))

instance challengeSampling : ∀ i j, SampleableType ((stageSpec (R := R) sz i).Challenge j)
  | 0 => inferInstanceAs (∀ j, SampleableType ((WitnessAttachment.pSpec (R := R) sz).Challenge j))
  | 1 => inferInstanceAs (∀ j, SampleableType ((RandomEvaluation.pSpec R (params).ℓ_m).Challenge j))
  | 2 => inferInstanceAs (∀ j, SampleableType ((Sumcheck.Spec.pSpec R 3 (params).ℓ_m).Challenge j))
  | 3 => inferInstanceAs (∀ j, SampleableType ((SendEvaluations.pSpec R).Challenge j))
  | 4 => inferInstanceAs (∀ j, SampleableType ((Batching.pSpec R).Challenge j))
  | 5 => inferInstanceAs (∀ j, SampleableType ((Sumcheck.Spec.pSpec R 2 (params).ℓ_n).Challenge j))
  | 6 => inferInstanceAs (∀ j, SampleableType ((!p[] : ProtocolSpec 0).Challenge j))

variable {ι : Type} (oSpec : OracleSpec.{0, 0} ι)

/-- Each component uses the preceding component's exact output context. -/
def stage : (i : Fin 7) → OracleReduction oSpec
    (Statement (R := R) sz i.castSucc) (Oracles (R := R) sz i.castSucc)
    (Witness (R := R) sz i.castSucc) (Statement (R := R) sz i.succ)
    (Oracles (R := R) sz i.succ) (Witness (R := R) sz i.succ) (stageSpec (R := R) sz i)
  | 0 => WitnessAttachment.oracleReduction sz oSpec
  | 1 => ZeroCheck.oracleReduction params oSpec
  | 2 => FirstSumcheck.oracleReduction params oSpec
  | 3 => SendEvaluations.oracleReduction params oSpec
  | 4 => Batching.oracleReduction params oSpec
  | 5 => SecondSumcheck.oracleReduction params oSpec
  | 6 => Terminal.finalReduction params oSpec

/-- Relations at the boundaries, starting with the original R1CS relation. -/
def relation : (i : Fin 8) → Set ((Statement (R := R) sz i ×
    (∀ j, Oracles (R := R) sz i j)) × Witness (R := R) sz i)
  | 0 => WitnessAttachment.relIn sz
  | 1 => ZeroCheck.relIn params
  | 2 => ZeroCheck.relOut params
  | 3 => SendEvaluations.relIn params
  | 4 => Batching.relIn params
  | 5 => Batching.relOut params
  | 6 => Terminal.relIn params
  | 7 => Terminal.relOut params

/-- The component guards use semantic polynomial evaluations only in their proof views. -/
noncomputable def stageGuardedForm : (i : Fin 7) →
    (stage (R := R) sz oSpec i).verifier.toVerifier.GuardedForm
  | 0 => WitnessAttachment.guardedForm sz oSpec
  | 1 => ZeroCheck.guardedForm params oSpec
  | 2 => FirstSumcheck.guardedForm params oSpec
  | 3 => SendEvaluations.guardedForm params oSpec
  | 4 => Batching.guardedForm params oSpec
  | 5 => SecondSumcheck.guardedForm params oSpec
  | 6 => Terminal.guardedForm params oSpec

end Assembly

/-- The complete transcript specification. -/
abbrev pSpec := ProtocolSpec.seqCompose (Assembly.stageSpec (R := R) sz)

instance : ∀ i, OracleInterface ((pSpec (R := R) sz).Message i) :=
  inferInstanceAs (∀ i, OracleInterface
    ((ProtocolSpec.seqCompose (Assembly.stageSpec (R := R) sz)).Message i))

instance : ∀ i, SampleableType ((pSpec (R := R) sz).Challenge i) :=
  inferInstanceAs (∀ i, SampleableType
    ((ProtocolSpec.seqCompose (Assembly.stageSpec (R := R) sz)).Challenge i))

/-- The seven-stage Spartan PIOP, including an executable honest prover. -/
def oracleReduction {ι : Type} (oSpec : OracleSpec.{0, 0} ι) :
    OracleReduction oSpec (R1CS.Statement R sz) (R1CS.OracleStatement R sz)
      (R1CS.Witness R sz) Unit (OracleStatement (R := R) params) Unit (pSpec (R := R) sz) :=
  OracleReduction.seqCompose (Assembly.Statement (R := R) sz) (Assembly.Oracles sz)
    (Assembly.Witness sz) (Assembly.stage sz oSpec)

/-- The conjunction of all component guards, with their retained-context outputs.
Its semantic sumcheck views use nonconstructive polynomial equality. -/
noncomputable def guardedForm {ι : Type} (oSpec : OracleSpec.{0, 0} ι) :
    (oracleReduction (R := R) sz oSpec).verifier.toVerifier.GuardedForm :=
  OracleVerifier.seqComposeGuardedForm (Assembly.Statement (R := R) sz)
    (Assembly.Oracles (R := R) sz)
    (V := fun i => (Assembly.stage (R := R) sz oSpec i).verifier)
    (Assembly.stageGuardedForm (R := R) sz oSpec)

variable {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The actual honest prover is perfectly complete for the original R1CS relation. -/
theorem perfectCompleteness :
    (oracleReduction (R := R) sz oSpec).perfectCompleteness init impl
      (WitnessAttachment.relIn sz) (Terminal.relOut params) := by
  apply OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
    (Assembly.Statement (R := R) sz) (Assembly.Oracles (R := R) sz)
    (Assembly.Witness (R := R) sz) init impl
    (Assembly.relation (R := R) sz) (Assembly.stage (R := R) sz oSpec)
  · intro i
    fin_cases i
    · exact inferInstanceAs (WitnessAttachment.oracleProver sz oSpec).OutputIsPure
    · exact inferInstanceAs (RandomEvaluation.oracleProver oSpec R (params).ℓ_m
        (R1CS.Statement R (params).toSizeR1CS) (OracleStatement (R := R) params)).OutputIsPure
    · exact FirstSumcheck.oracleProver_outputIsPure params oSpec
    · exact ⟨_, fun _ => rfl⟩
    · exact inferInstanceAs (Batching.oracleProver (R := R) params oSpec).OutputIsPure
    · exact SecondSumcheck.oracleProver_outputIsPure params oSpec
    · exact ⟨_, fun _ => rfl⟩
  · exact Assembly.stageGuardedForm (R := R) sz oSpec
  · intro i state
    fin_cases i
    · exact WitnessAttachment.perfectCompleteness sz oSpec (pure state) impl
    · exact ZeroCheck.challenge_perfectCompleteness params oSpec
    · exact FirstSumcheck.perfectCompleteness params oSpec (pure state) impl
    · exact SendEvaluations.reduction_perfectCompleteness params oSpec (pure state) impl
    · exact Batching.batch_perfectCompleteness params oSpec (pure state) impl
    · exact SecondSumcheck.perfectCompleteness params oSpec (pure state) impl
    · exact Terminal.finalReduction_perfectCompleteness params oSpec (pure state) impl

end Spartan

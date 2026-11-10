/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Execution

/-!
# Eager oracle sampling with VCVio

A fixed deterministic oracle is VCVio's `QueryImpl spec Id`. Sample that table using
`uniformSample`, then answer queries with `pure (table q)` under `simulateQ`.
Samplers have type `ProbComp α`. This module provides finite function-table samplers, including
the Fiat-Shamir challenge tables sampled by `D_IP.sample`. The bridges from `Fintype` are
noncomputable because they choose enumerations of the finite query and answer types.
-/

@[expose] public section

namespace OracleReduction

open OracleComp OracleSpec
open scoped ENNReal

variable {ι : Type}

/-! ## §1. Function-table carriers -/

/-- Explicit `SampleableType (α → β)` construction from `VCVCompatible` domain and range.

`(QueryImpl (α →ₒ β) Id)` is definitionally `α → β`. This remains a definition rather than a
global instance because `SampleableType` carries sampler data and VCVio already provides
function-specific sampling instances. -/
@[reducible] noncomputable def sampleableTypePiVCV
    {α β : Type} [VCVCompatible α] [VCVCompatible β] :
    SampleableType (α → β) := by
  letI : FinEnum α := VCVCompatible.toFinEnum
  letI : FinEnum β := VCVCompatible.toFinEnum
  letI : Nonempty (α → β) := ⟨fun _ => default⟩
  infer_instance

/-! ## Paper-named samplers

`D_ROM.sample` and `D_IP.sample` sample deterministic oracle tables uniformly. Repeated queries
to the sampled table receive the same answer.
-/

section SamplingExamples

/-! ### `D_ROM.sample` — random-function constructor. -/

/-- Generic `D_ROM.sample` constructor for any random-function oracle spec:
uniformly sample one deterministic table realization. -/
@[reducible]
def D_ROM.sample {ι : Type} (spec : OracleSpec ι)
    [instSampleable : SampleableType (QueryImpl spec Id)] :
    ProbComp (QueryImpl spec Id) :=
  uniformSample _ (h := instSampleable)

/-! ### `D_IP.sample` — ideal-protocol Fiat-Shamir challenger.

The Fiat-Shamir challenge oracle (`fsChallengeOracle` / `srChallengeOracle`) answers
`(i, x, α[<i])` with a value of type `pSpec.Challenge i`. Here `x : Statement` is the query
context and `α[<i]` is the preceding prover-message tuple. In the single-salt setting,
`Statement := StmtIn × Salt`, so the query context is `(𝕩, τ)`.
`D_IP.sample` samples one table of answers for all such queries. -/

/-- Bridge instance: finiteness of the statement, message, and challenge types, plus inhabited
challenge types, suffices to derive `SampleableType (QueryImpl (fsChallengeOracle Statement pSpec)
Id)`. (`VCVCompatible` hypotheses supply all of these.) -/
noncomputable instance instSampleableTypeFSChallengeOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {Statement : Type}
    [Fintype Statement]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)] :
    SampleableType (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) := by
  -- Each prefix message type is definitionally the corresponding message type in `pSpec`.
  letI : ∀ k : Fin (n + 1), Fintype (pSpec.MessagesUpTo k) := fun k => by
    letI : ∀ i : pSpec.MessageIdxUpTo k, Fintype (pSpec.MessageUpTo k i) :=
      fun i => (inferInstance :
        Fintype (pSpec.Message ⟨i.1.castLE (by omega), i.property⟩))
    infer_instance
  -- The challenge-oracle domain is a sigma of a challenge index and its finite query type.
  letI : Fintype (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain := by
    dsimp only [ProtocolSpec.fsChallengeOracle, ProtocolSpec.srChallengeOracle,
      OracleInterface.toOracleSpec, ProtocolSpec.challengeOracleInterfaceSR,
      OracleSpec.toPFunctor, OracleInterface.Query]
    infer_instance
  -- Spell out the dependent range family to keep synthesis from repeatedly unfolding the spec.
  letI : ∀ q : (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain,
      Fintype ((ProtocolSpec.fsChallengeOracle Statement pSpec).Range q) :=
    fun q => (inferInstance : Fintype (pSpec.Challenge q.1))
  letI : Fintype (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) :=
    show Fintype ((q : (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain) →
      (ProtocolSpec.fsChallengeOracle Statement pSpec).Range q) from Fintype.ofFinite _
  -- A challenge table is nonempty because every challenge response type is inhabited.
  letI : Nonempty (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) :=
    ⟨fun q => (default : pSpec.Challenge q.1)⟩
  apply SampleableType.ofFintype

/-- Uniformly sample a deterministic Fiat-Shamir challenge table. Each query contains a
challenge index, a context of type `Statement`, and the preceding prover-message tuple. -/
@[reducible]
noncomputable def D_IP.sample {n : ℕ} (Statement : Type) (pSpec : ProtocolSpec n)
    [Fintype Statement]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)] :
    ProbComp (QueryImpl (ProtocolSpec.fsChallengeOracle Statement pSpec) Id) :=
  D_ROM.sample (instSampleable := instSampleableTypeFSChallengeOracle)

end SamplingExamples

end OracleReduction

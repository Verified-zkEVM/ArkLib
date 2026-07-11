/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : ArkLib Contributors
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Oracle Interaction Examples

Small clients of the oracle interaction layer. These examples are intentionally
minimal : they exercise the core `Interaction.Spec`/`OracleDecoration` idioms
used by downstream protocols without depending on a larger proof system.
-/

open OracleComp OracleSpec

namespace Interaction.Oracle.Examples

namespace TwoRoundExample

open Interaction.TwoParty

/-! ## Two appended oracle rounds -/

abbrev RoundOneQuery := Bool
abbrev RoundTwoQuery := Bool × Bool
abbrev Response := Nat /- can also vary per round -/
abbrev Challenge := Nat

/-- Toy oracle message type: just send the function. -/
abbrev RoundOneOracle := RoundOneQuery → Response
abbrev RoundTwoOracle := RoundTwoQuery → Response

/-- How to query the oracle. In our case, we already have a recipe that says "just
  evaluate the function". -/
abbrev roundOneOracleSpec : OracleSpec RoundOneQuery :=
  @OracleInterface.spec RoundOneOracle inferInstance

abbrev roundTwoOracleSpec : OracleSpec RoundTwoQuery :=
  @OracleInterface.spec RoundTwoOracle inferInstance


/-! ### Round one -/
/-- Round one: prover sends an oracle message, verifier sends a public challenge. -/
abbrev roundOneTranscriptSpec : Interaction.Spec :=
  .node RoundOneOracle fun _ =>
    .node Challenge fun _ =>
      .done

/-- Round one has a sender message followed by a receiver message. -/
abbrev roundOneRoles : RoleDecoration roundOneTranscriptSpec :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

/-- Attach an oracle interface to the sender's round message and skip receiver nodes. -/
abbrev roundOneOracleDecoration :
    Interaction.OracleDecoration roundOneTranscriptSpec roundOneRoles :=
  ⟨inferInstanceAs (OracleInterface RoundOneOracle), fun _ => fun _ => ⟨⟩⟩

abbrev roundOneTranscript (oracle : RoundOneOracle) (challenge : Challenge) :
    Interaction.Spec.Transcript roundOneTranscriptSpec :=
  ⟨oracle, ⟨challenge, ⟨⟩⟩⟩

abbrev roundOneQuery (oracle : RoundOneOracle) (challenge : Challenge) (query : RoundOneQuery) :
    Interaction.OracleDecoration.QueryHandle
      roundOneTranscriptSpec roundOneRoles roundOneOracleDecoration
      (roundOneTranscript oracle challenge) :=
  .inl query

/-- A minimal verifier step: after the sender message, query that oracle and
return a receiver challenge plus an output. -/
noncomputable def roundOneVerifierStep
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    Interaction.OracleDecoration.OracleCounterpart oSpec OStmtIn
      (fun {ιₐ} (_ : OracleSpec ιₐ) => Response)
    roundOneTranscriptSpec roundOneRoles roundOneOracleDecoration accSpec :=
  fun _ =>
    let receiverStep :
        OracleComp (oSpec + [OStmtIn]ₒ + (accSpec + roundOneOracleSpec))
          ((_ : Challenge) × Response) := do
      let valueAtFalse : Response ← liftM <| roundOneOracleSpec.query false
      pure ⟨0, valueAtFalse⟩
    receiverStep

/-! ### Round two -/

/-- Round two has the same local shape, but is presented as the continuation
expected by `Spec.append`. -/
abbrev roundTwoTranscriptSpec (_ : Interaction.Spec.Transcript roundOneTranscriptSpec) : Interaction.Spec :=
  .node RoundTwoOracle fun _ =>
    .node Challenge fun _ =>
      .done

abbrev roundTwoRoles (tr₁ : Interaction.Spec.Transcript roundOneTranscriptSpec) :
    RoleDecoration (roundTwoTranscriptSpec tr₁) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

abbrev roundTwoOracleDecoration (tr₁ : Interaction.Spec.Transcript roundOneTranscriptSpec) :
    Interaction.OracleDecoration (roundTwoTranscriptSpec tr₁) (roundTwoRoles tr₁) :=
  ⟨inferInstanceAs (OracleInterface RoundTwoOracle), fun _ => fun _ => ⟨⟩⟩

abbrev roundTwoTranscript (tr₁ : Interaction.Spec.Transcript roundOneTranscriptSpec)
    (oracle : RoundTwoOracle) (challenge : Challenge) :
    Interaction.Spec.Transcript (roundTwoTranscriptSpec tr₁) :=
  ⟨oracle, ⟨challenge, ⟨⟩⟩⟩

abbrev roundTwoQuery (tr₁ : Interaction.Spec.Transcript roundOneTranscriptSpec)
    (oracle : RoundTwoOracle) (challenge : Challenge) (query : RoundTwoQuery) :
    Interaction.OracleDecoration.QueryHandle
      (roundTwoTranscriptSpec tr₁) (roundTwoRoles tr₁) (roundTwoOracleDecoration tr₁)
      (roundTwoTranscript tr₁ oracle challenge) :=
  .inl query

/-! ### Composed protocol -/

/-- Two rounds composed by the core `Spec.append` surface. -/
abbrev protocolSpec : Interaction.Spec :=
  roundOneTranscriptSpec.append roundTwoTranscriptSpec

abbrev protocolRoles : RoleDecoration protocolSpec :=
  Interaction.Spec.Decoration.append roundOneRoles roundTwoRoles

abbrev protocolOracleDecoration :
    Interaction.OracleDecoration protocolSpec protocolRoles :=
  Role.Refine.append roundOneOracleDecoration roundTwoOracleDecoration

abbrev protocolTranscript (oracle1 : RoundOneOracle) (challenge1 : Challenge)
    (oracle2 : RoundTwoOracle) (challenge2 : Challenge) :
    Interaction.Spec.Transcript protocolSpec :=
  Interaction.Spec.Transcript.append roundOneTranscriptSpec roundTwoTranscriptSpec
    (roundOneTranscript oracle1 challenge1)
    (roundTwoTranscript (roundOneTranscript oracle1 challenge1) oracle2 challenge2)

/-- Embed a first-round query into the composed protocol. -/
abbrev firstRoundQuery (oracle1 : RoundOneOracle) (challenge1 : Challenge)
    (oracle2 : RoundTwoOracle) (challenge2 : Challenge) (query : RoundOneQuery) :
    Interaction.OracleDecoration.QueryHandle
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2) :=
  Interaction.OracleDecoration.QueryHandle.appendLeft
    roundOneTranscriptSpec roundTwoTranscriptSpec
    roundOneRoles roundTwoRoles
    roundOneOracleDecoration roundTwoOracleDecoration
    (roundOneTranscript oracle1 challenge1)
    (roundTwoTranscript (roundOneTranscript oracle1 challenge1) oracle2 challenge2)
    (roundOneQuery oracle1 challenge1 query)

/-- Embed a second-round query into the composed protocol. -/
abbrev secondRoundQuery (oracle1 : RoundOneOracle) (challenge1 : Challenge)
    (oracle2 : RoundTwoOracle) (challenge2 : Challenge) (query : RoundTwoQuery) :
    Interaction.OracleDecoration.QueryHandle
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2) :=
  Interaction.OracleDecoration.QueryHandle.appendRight
    roundOneTranscriptSpec roundTwoTranscriptSpec
    roundOneRoles roundTwoRoles
    roundOneOracleDecoration roundTwoOracleDecoration
    (roundOneTranscript oracle1 challenge1)
    (roundTwoTranscript (roundOneTranscript oracle1 challenge1) oracle2 challenge2)
    (roundTwoQuery (roundOneTranscript oracle1 challenge1) oracle2 challenge2 query)

theorem answerQuery_firstRound (oracle1 : RoundOneOracle) (challenge1 : Challenge)
    (oracle2 : RoundTwoOracle) (challenge2 : Challenge) (query : RoundOneQuery) :
    Interaction.OracleDecoration.answerQuery
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2)
      (firstRoundQuery oracle1 challenge1 oracle2 challenge2 query) = oracle1 query :=
  rfl

theorem answerQuery_secondRound (oracle1 : RoundOneOracle) (challenge1 : Challenge)
    (oracle2 : RoundTwoOracle) (challenge2 : Challenge) (query : RoundTwoQuery) :
    Interaction.OracleDecoration.answerQuery
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2)
      (secondRoundQuery oracle1 challenge1 oracle2 challenge2 query) = oracle2 query :=
  rfl

end TwoRoundExample

end Interaction.Oracle.Examples

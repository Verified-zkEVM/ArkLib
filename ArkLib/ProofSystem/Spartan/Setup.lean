/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.OracleInterfaces
import ArkLib.Interaction.Oracle.Composition

open Interaction.TwoParty

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

section WitnessOracleRound

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- First Spartan round: the prover sends the witness oracle. -/
def witnessSpec : Interaction.Oracle.Spec :=
  .oracle (Witness R pp) fun _ => .done

/-- The witness oracle is sent by the prover. -/
def witnessRoles :
    Interaction.Oracle.Spec.RoleDeco (witnessSpec R pp) :=
  ⟨⟩

/-- Oracle-interface decoration for the witness oracle message. -/
def witnessOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (witnessSpec R pp) :=
  ⟨inferInstance, ⟨⟩⟩

/-- Route post-witness oracle queries either to the original matrix oracles or
to the newly sent witness oracle. -/
def simulateWithWitnessOracle :
    QueryImpl [WithWitnessOracleFamily R pp]ₒ
      (OracleComp
        ([InputOracleFamily R pp]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (witnessSpec R pp)
            (witnessOracleDeco R pp)
            ⟨⟨⟩, ⟨⟩⟩))
  | ⟨.inl idx, q⟩ =>
      liftM <| ([InputOracleFamily R pp]ₒ).query ⟨idx, q⟩
  | ⟨.inr (), q⟩ =>
      liftM <|
        (Interaction.Oracle.Spec.toOracleSpec
          (witnessSpec R pp)
          (witnessOracleDeco R pp)
          ⟨⟨⟩, ⟨⟩⟩).query (.inl q)

/-- Spartan's first oracle reduction: append the witness oracle to the input
R1CS matrix oracle family. -/
def witnessReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => witnessSpec R pp)
      (fun _ => witnessRoles R pp)
      (fun _ => witnessOracleDeco R pp)
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => Statement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => WithWitnessOracleFamily R pp)
      (fun _ _ => Witness R pp) where
  prover _ sWithOracles witness := do
    let proverStep :
        Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
          (witnessSpec R pp).toInteractionSpec
          ((witnessSpec R pp).toSpecRoles (witnessRoles R pp))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => Statement R pp)
                (fun _ => WithWitnessOracleFamily R pp)
                PUnit.unit)
              (Witness R pp)) := do
      pure
        ⟨witness,
          (⟨⟨sWithOracles.stmt,
            fun
            | .inl idx => sWithOracles.oracleStmt idx
            | .inr () => witness⟩, witness⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => Statement R pp)
                (fun _ => WithWitnessOracleFamily R pp)
                PUnit.unit)
              (Witness R pp))⟩
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (witnessSpec R pp).toInteractionSpec
        ((witnessSpec R pp).toSpecRoles (witnessRoles R pp))
        proverStep
  verifier := {
    toFun := fun _ stmt _ => stmt
    simulate := fun _ pt =>
      match pt with
      | ⟨⟨⟩, ⟨⟩⟩ => simulateWithWitnessOracle R pp
  }

end WitnessOracleRound

section FirstChallengeRound

variable (R : Type) [BEq R] [CommRing R] [IsDomain R] [Fintype R]
  [LawfulBEq R] [Nontrivial R] (pp : PublicParams)

/-- Second Spartan setup round: the verifier samples `τ`. -/
def firstChallengeSpec : Interaction.Oracle.Spec :=
  .public (FirstChallenge R pp) fun _ => .done

/-- The verifier sends the first challenge. -/
def firstChallengeRoles :
    Interaction.Oracle.Spec.RoleDeco (firstChallengeSpec R pp) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- The first challenge round sends no oracle message. -/
def firstChallengeOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (firstChallengeSpec R pp) :=
  fun _ => ⟨⟩

/-- Identity simulation for the oracle family across the first challenge. -/
def simulateAfterFirstChallenge
    (pt : Interaction.Oracle.Spec.PublicTranscript (firstChallengeSpec R pp)) :
    QueryImpl [WithWitnessOracleFamily R pp]ₒ
      (OracleComp
        ([WithWitnessOracleFamily R pp]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (firstChallengeSpec R pp)
            (firstChallengeOracleDeco R pp)
            pt)) :=
  fun q => liftM <| ([WithWitnessOracleFamily R pp]ₒ).query q

/-- Sample the first Spartan challenge and remember it in the local statement. -/
def firstChallengeReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [Nontrivial R]
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => firstChallengeSpec R pp)
      (fun _ => firstChallengeRoles R pp)
      (fun _ => firstChallengeOracleDeco R pp)
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => AfterFirstChallengeStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterFirstChallengeOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let proverStep :
        Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
          (firstChallengeSpec R pp).toInteractionSpec
          ((firstChallengeSpec R pp).toSpecRoles (firstChallengeRoles R pp))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => AfterFirstChallengeStatement R pp)
                (fun _ => AfterFirstChallengeOracleFamily R pp)
                PUnit.unit)
              PUnit) :=
      fun τ => do
        let state : AfterFirstChallengeStatement R pp := ⟨τ, sWithOracles.stmt⟩
        pure
          ⟨⟨state, sWithOracles.oracleStmt⟩,
            PUnit.unit⟩
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (firstChallengeSpec R pp).toInteractionSpec
        ((firstChallengeSpec R pp).toSpecRoles (firstChallengeRoles R pp))
        proverStep
  verifier := {
    toFun := fun _ stmt => do
      let τ ← sampleFirstChallenge
      pure ⟨τ, ⟨τ, stmt⟩⟩
    simulate := fun _ pt =>
      simulateAfterFirstChallenge R pp pt
  }

end FirstChallengeRound

section SetupPrefix

variable (R : Type) [BEq R] [CommRing R] [instDomain : IsDomain R] [instFintype : Fintype R]
  [LawfulBEq R] [Nontrivial R] (pp : PublicParams)

/-- Spartan setup context: witness oracle message followed by the first
verifier challenge. -/
abbrev setupContext : Interaction.Oracle.Spec :=
  (witnessSpec R pp).append (fun _ => firstChallengeSpec R pp)

/-- Role decoration for the Spartan setup prefix. -/
abbrev setupRoles :
    Interaction.Oracle.Spec.RoleDeco (setupContext R pp) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (witnessSpec R pp)
    (fun _ => firstChallengeSpec R pp)
    (witnessRoles R pp)
    (fun _ => firstChallengeRoles R pp)

/-- Oracle-message decoration for the Spartan setup prefix. -/
abbrev setupOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (setupContext R pp) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (witnessSpec R pp)
    (fun _ => firstChallengeSpec R pp)
    (witnessOracleDeco R pp)
    (fun _ => firstChallengeOracleDeco R pp)

/-- Spartan setup prefix as a composed oracle reduction. -/
def setupReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [Nontrivial R] [IsDomain R] [Fintype R]
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => setupContext R pp)
      (fun _ => setupRoles R pp)
      (fun _ => setupOracleDeco R pp)
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => AfterFirstChallengeStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterFirstChallengeOracleFamily R pp)
      (fun _ _ => PUnit) := by
  exact Interaction.Oracle.Reduction.comp
    (witnessReduction (R := R) (pp := pp) (oSpec := oSpec))
    (fun _ _ =>
      firstChallengeReduction (R := R) (pp := pp) (oSpec := oSpec)
        sampleFirstChallenge)

end SetupPrefix

end

end OracleLayer

end Spartan


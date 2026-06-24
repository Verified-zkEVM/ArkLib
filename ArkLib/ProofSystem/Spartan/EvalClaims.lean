/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.FirstSumcheck

open Interaction.TwoParty

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

section EvalClaimRound

variable (R : Type) [BEq R] [CommRing R] [IsDomain R] [Fintype R]
  [LawfulBEq R] [Nontrivial R] (pp : PublicParams)

/-- The evaluation claims determined by the concrete Spartan oracle statement
and the first sum-check terminal point. If the first sum-check rejected, later
rounds are semantically irrelevant and the honest prover sends zeros. -/
def evalClaimsFromOracleStmt
    (state : AfterFirstSumcheckStatement R pp)
    (oracleStmt : OracleStatement (AfterFirstSumcheckOracleFamily R pp)) :
    EvalClaims R :=
  match state.1 with
  | none => fun _ => 0
  | some result =>
      fun matrix =>
        CPoly.CMvPolynomial.eval result.point
          (matrixVecPolynomial (R := R) pp matrix state.2.2 oracleStmt)

/-- The prover publicly sends the three evaluation claims
`A z(r_x)`, `B z(r_x)`, and `C z(r_x)`. -/
def evalClaimSpec : Interaction.Oracle.Spec :=
  .public (EvalClaims R) fun _ => .done

/-- Evaluation claims are sent by the prover. -/
def evalClaimRoles :
    Interaction.Oracle.Spec.RoleDeco (evalClaimSpec R) :=
  ⟨.sender, fun _ => ⟨⟩⟩

/-- The evaluation-claim round sends no oracle message. -/
def evalClaimOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (evalClaimSpec R) :=
  fun _ => ⟨⟩

/-- Identity simulation for the oracle family across the evaluation-claim
message. -/
def simulateAfterEvalClaim
    (pt : Interaction.Oracle.Spec.PublicTranscript (evalClaimSpec R)) :
    QueryImpl [AfterEvalClaimOracleFamily R pp]ₒ
      (OracleComp
        ([AfterFirstSumcheckOracleFamily R pp]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (evalClaimSpec R)
            (evalClaimOracleDeco R)
            pt)) :=
  fun q => liftM <| ([AfterFirstSumcheckOracleFamily R pp]ₒ).query q

/-- Send the first-sumcheck terminal evaluation claims while carrying the
Spartan matrix/witness oracle family unchanged. -/
def evalClaimReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => evalClaimSpec R)
      (fun _ => evalClaimRoles R)
      (fun _ => evalClaimOracleDeco R)
      (fun _ => AfterFirstSumcheckStatement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ => AfterFirstSumcheckOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => AfterEvalClaimStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterEvalClaimOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let claims := evalClaimsFromOracleStmt R pp sWithOracles.stmt sWithOracles.oracleStmt
    let proverStep :
        Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
          (evalClaimSpec R).toInteractionSpec
          ((evalClaimSpec R).toSpecRoles (evalClaimRoles R))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => AfterEvalClaimStatement R pp)
                (fun _ => AfterEvalClaimOracleFamily R pp)
                PUnit.unit)
              PUnit) :=
      pure
        ⟨claims,
          ⟨⟨⟨claims, sWithOracles.stmt⟩, sWithOracles.oracleStmt⟩,
            PUnit.unit⟩⟩
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (evalClaimSpec R).toInteractionSpec
        ((evalClaimSpec R).toSpecRoles (evalClaimRoles R))
        proverStep
  verifier := {
    toFun := fun _ state claims =>
      pure ⟨claims, state⟩
    simulate := fun _ pt =>
      simulateAfterEvalClaim R pp pt
  }

end EvalClaimRound

section LinearCombinationRound

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- The verifier samples coefficients for the random linear combination of
`A z(r_x)`, `B z(r_x)`, and `C z(r_x)`. -/
def linearCombinationSpec : Interaction.Oracle.Spec :=
  .public (LinearCombinationChallenge R) fun _ => .done

/-- Linear-combination coefficients are sent by the verifier. -/
def linearCombinationRoles :
    Interaction.Oracle.Spec.RoleDeco (linearCombinationSpec R) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- The linear-combination round sends no oracle message. -/
def linearCombinationOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (linearCombinationSpec R) :=
  fun _ => ⟨⟩

/-- Identity simulation for the oracle family across the linear-combination
challenge. -/
def simulateAfterLinearCombination
    (pt : Interaction.Oracle.Spec.PublicTranscript (linearCombinationSpec R)) :
    QueryImpl [AfterLinearCombinationOracleFamily R pp]ₒ
      (OracleComp
        ([AfterEvalClaimOracleFamily R pp]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (linearCombinationSpec R)
            (linearCombinationOracleDeco R)
            pt)) :=
  fun q => liftM <| ([AfterEvalClaimOracleFamily R pp]ₒ).query q

/-- Sample the random linear-combination challenge and remember it in the
Spartan local statement. -/
def linearCombinationReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleLinearCombination : OracleComp oSpec (LinearCombinationChallenge R)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => linearCombinationSpec R)
      (fun _ => linearCombinationRoles R)
      (fun _ => linearCombinationOracleDeco R)
      (fun _ => AfterEvalClaimStatement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ => AfterEvalClaimOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => AfterLinearCombinationStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterLinearCombinationOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let proverStep :
        Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
          (linearCombinationSpec R).toInteractionSpec
          ((linearCombinationSpec R).toSpecRoles (linearCombinationRoles R))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => AfterLinearCombinationStatement R pp)
                (fun _ => AfterLinearCombinationOracleFamily R pp)
                PUnit.unit)
              PUnit) :=
      fun ρ => do
        pure
          ⟨⟨⟨ρ, sWithOracles.stmt⟩, sWithOracles.oracleStmt⟩,
            PUnit.unit⟩
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (linearCombinationSpec R).toInteractionSpec
        ((linearCombinationSpec R).toSpecRoles (linearCombinationRoles R))
        proverStep
  verifier := {
    toFun := fun _ state => do
      let ρ ← sampleLinearCombination
      pure ⟨ρ, ⟨ρ, state⟩⟩
    simulate := fun _ pt =>
      simulateAfterLinearCombination R pp pt
  }

end LinearCombinationRound

end

end OracleLayer

end Spartan


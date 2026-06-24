/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.SecondSumcheck

open Interaction.TwoParty

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

section TerminalCheck

variable (R : Type) [BEq R] [CommRing R] [IsDomain R] [Fintype R] [LawfulBEq R]
  [Nontrivial R] (pp : PublicParams)

/-- Spartan's terminal check either keeps the fully accumulated statement or
rejects with `none`. -/
abbrev TerminalCheckStatement : Type :=
  Option (AfterSecondSumcheckStatement R pp)

/-- The terminal check does not change the queryable Spartan oracle family. -/
abbrev TerminalCheckOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  AfterSecondSumcheckOracleFamily R pp

/-- The verifier's expected terminal value, computed directly from a concrete
Spartan oracle statement. -/
def terminalExpectedFromOracleStmt
    (state : AfterSecondSumcheckStatement R pp)
    (oracleStmt : OracleStatement (AfterSecondSumcheckOracleFamily R pp)) : R :=
  match state with
  | ⟨some second, ⟨ρ, ⟨_, ⟨some first, ⟨_, stmt⟩⟩⟩⟩⟩ =>
      let a : R :=
        OracleInterface.answer (oracleStmt (.inl .A)) (first.point, second.point)
      let b : R :=
        OracleInterface.answer (oracleStmt (.inl .B)) (first.point, second.point)
      let c : R :=
        OracleInterface.answer (oracleStmt (.inl .C)) (first.point, second.point)
      let weighted := ρ .A * a + ρ .B * b + ρ .C * c
      weighted * zEvalFromOracleStmt (R := R) pp stmt oracleStmt second.point
  | _ => 0

/-- Direct terminal check against a concrete oracle statement. -/
def terminalCheckFromOracleStmt
    (state : AfterSecondSumcheckStatement R pp)
    (oracleStmt : OracleStatement (AfterSecondSumcheckOracleFamily R pp)) :
    TerminalCheckStatement R pp :=
  match state with
  | ⟨some second, ⟨_, ⟨_, ⟨some _, _⟩⟩⟩⟩ =>
      if second.value == terminalExpectedFromOracleStmt R pp state oracleStmt then
        some state
      else
        none
  | _ => none

/-- Evaluate the terminal check using verifier-side oracle queries. -/
def terminalCheckByQueries
    (state : AfterSecondSumcheckStatement R pp) :
    OracleComp [AfterSecondSumcheckOracleFamily R pp]ₒ (TerminalCheckStatement R pp) :=
  match state with
  | ⟨some second, ⟨ρ, ⟨_, ⟨some first, ⟨_, stmt⟩⟩⟩⟩⟩ => do
      let z ← zEvalByQueries (R := R) pp stmt second.point
      let a : R ← liftM <|
        ([AfterSecondSumcheckOracleFamily R pp]ₒ).query
          ⟨.inl .A, (first.point, second.point)⟩
      let b : R ← liftM <|
        ([AfterSecondSumcheckOracleFamily R pp]ₒ).query
          ⟨.inl .B, (first.point, second.point)⟩
      let c : R ← liftM <|
        ([AfterSecondSumcheckOracleFamily R pp]ₒ).query
          ⟨.inl .C, (first.point, second.point)⟩
      let expected := (ρ .A * a + ρ .B * b + ρ .C * c) * z
      pure <| if second.value == expected then some state else none
  | _ => pure none

/-- Query simulation of the verifier-side terminal check agrees with the
direct concrete-oracle computation. -/
theorem simulateQ_terminalCheckByQueries
    (state : AfterSecondSumcheckStatement R pp)
    (oracleStmt : OracleStatement (AfterSecondSumcheckOracleFamily R pp)) :
    simulateQ
      (OracleInterface.toOracleImpl (AfterSecondSumcheckOracleFamily R pp) oracleStmt)
      (terminalCheckByQueries (R := R) pp state) =
    pure (terminalCheckFromOracleStmt R pp state oracleStmt) := by
  rcases state with ⟨second, ρ, claims, first, τ, stmt⟩
  cases second <;> cases first <;>
    simp [terminalCheckByQueries, terminalCheckFromOracleStmt,
      terminalExpectedFromOracleStmt, simulateQ_zEvalByQueries,
      OracleInterface.toOracleImpl]
  rfl

/-- The terminal check is represented as a verifier-owned public unit round so
the verifier has a receiver-node monad in which it can query the carried oracle
family. -/
def terminalCheckSpec (_R : Type) (_pp : PublicParams) : Interaction.Oracle.Spec :=
  .public PUnit fun _ => .done

/-- The terminal unit round belongs to the verifier. -/
def terminalCheckRoles :
    Interaction.Oracle.Spec.RoleDeco (terminalCheckSpec R pp) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- The terminal check sends no new oracle message. -/
def terminalCheckOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (terminalCheckSpec R pp) :=
  fun _ => ⟨⟩

/-- Identity simulation for the oracle family across the terminal check. -/
def simulateAfterTerminalCheck
    (pt : Interaction.Oracle.Spec.PublicTranscript (terminalCheckSpec R pp)) :
    QueryImpl [TerminalCheckOracleFamily R pp]ₒ
      (OracleComp
        ([AfterSecondSumcheckOracleFamily R pp]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (terminalCheckSpec R pp)
            (terminalCheckOracleDeco R pp)
            pt)) :=
  fun q => liftM <| ([AfterSecondSumcheckOracleFamily R pp]ₒ).query q

/-- Terminal verifier check for the two sum-check terminal claims and the
carried Spartan matrix/witness oracle family. -/
def terminalCheckReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => terminalCheckSpec R pp)
      (fun _ => terminalCheckRoles R pp)
      (fun _ => terminalCheckOracleDeco R pp)
      (fun _ => AfterSecondSumcheckStatement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ => AfterSecondSumcheckOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => TerminalCheckStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => TerminalCheckOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let proverStep :
        Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
          (terminalCheckSpec R pp).toInteractionSpec
          ((terminalCheckSpec R pp).toSpecRoles (terminalCheckRoles R pp))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => TerminalCheckStatement R pp)
                (fun _ => TerminalCheckOracleFamily R pp)
                PUnit.unit)
              PUnit) :=
      fun _ => do
        let out :=
          terminalCheckFromOracleStmt R pp sWithOracles.stmt sWithOracles.oracleStmt
        pure ⟨⟨out, sWithOracles.oracleStmt⟩, PUnit.unit⟩
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (terminalCheckSpec R pp).toInteractionSpec
        ((terminalCheckSpec R pp).toSpecRoles (terminalCheckRoles R pp))
        proverStep
  verifier := {
    toFun := fun _ state => do
      let out ← terminalCheckByQueries (R := R) pp state
      pure ⟨PUnit.unit, out⟩
    simulate := fun _ pt =>
      simulateAfterTerminalCheck R pp pt
  }

end TerminalCheck

end

end OracleLayer

end Spartan


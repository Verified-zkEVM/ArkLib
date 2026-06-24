/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Composed
import ArkLib.ProofSystem.Spartan.Terminal

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

section SetupThenTerminalCheck

variable (R : Type) [BEq R] [CommRing R] [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Spartan prefix through the terminal verifier check. -/
abbrev setupThenTerminalCheckContext [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec :=
  (setupThenSecondSumcheckContext R pp).append (fun _ => terminalCheckSpec R pp)

/-- Role decoration for the Spartan prefix through the terminal verifier
check. -/
abbrev setupThenTerminalCheckRoles [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.RoleDeco (setupThenTerminalCheckContext R pp) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (setupThenSecondSumcheckContext R pp)
    (fun _ => terminalCheckSpec R pp)
    (setupThenSecondSumcheckRoles R pp)
    (fun _ => terminalCheckRoles R pp)

/-- Oracle-message decoration for the Spartan prefix through the terminal
verifier check. -/
abbrev setupThenTerminalCheckOracleDeco [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.OracleDeco (setupThenTerminalCheckContext R pp) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (setupThenSecondSumcheckContext R pp)
    (fun _ => terminalCheckSpec R pp)
    (setupThenSecondSumcheckOracleDeco R pp)
    (fun _ => terminalCheckOracleDeco R pp)

/-- Spartan setup through the terminal verifier check, composed with the
generic oracle-reduction composition primitive. -/
abbrev setupThenTerminalCheckReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [instDomain : IsDomain R] [instFintype : Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp))
    (sampleSumcheckChallenge : OracleComp oSpec R)
    (sampleLinearCombination : OracleComp oSpec (LinearCombinationChallenge R)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => (setupThenSecondSumcheckContext R pp).append
        (fun _ => terminalCheckSpec R pp))
      (fun _ =>
        Interaction.Oracle.Spec.RoleDeco.append
          (setupThenSecondSumcheckContext R pp)
          (fun _ => terminalCheckSpec R pp)
          (setupThenSecondSumcheckRoles R pp)
          (fun _ => terminalCheckRoles R pp))
      (fun _ =>
        Interaction.Oracle.Spec.OracleDeco.append
          (setupThenSecondSumcheckContext R pp)
          (fun _ => terminalCheckSpec R pp)
          (setupThenSecondSumcheckOracleDeco R pp)
          (fun _ => terminalCheckOracleDeco R pp))
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => TerminalCheckStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => TerminalCheckOracleFamily R pp)
      (fun _ _ => PUnit) :=
  Interaction.Oracle.Reduction.comp
    (Context₂ := fun _ _ => terminalCheckSpec R pp)
    (Roles₂ := fun _ _ => terminalCheckRoles R pp)
    (OracleDeco₂ := fun _ _ => terminalCheckOracleDeco R pp)
    (StatementOut := fun _ _ _ => TerminalCheckStatement R pp)
    (ιₛₒ := fun _ _ _ => R1CS.MatrixIdx ⊕ Unit)
    (OStatementOut := fun _ _ _ => TerminalCheckOracleFamily R pp)
    (WitnessOut := fun _ _ _ => PUnit)
    (setupThenSecondSumcheckReduction (R := R) (pp := pp) (oSpec := oSpec)
      D sampleFirstChallenge sampleSumcheckChallenge sampleLinearCombination)
    (fun _ _ => terminalCheckReduction (R := R) (pp := pp) (oSpec := oSpec))

end SetupThenTerminalCheck

end

end OracleLayer

end Spartan

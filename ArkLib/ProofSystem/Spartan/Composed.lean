/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Setup
import ArkLib.ProofSystem.Spartan.FirstSumcheck
import ArkLib.ProofSystem.Spartan.EvalClaims
import ArkLib.ProofSystem.Spartan.SecondSumcheck
import ArkLib.Interaction.Oracle.Composition

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

section SetupThenFirstSumcheck

variable (R : Type) [BEq R] [CommRing R] [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Spartan prefix through the first virtual sum-check. -/
abbrev setupThenFirstSumcheckContext [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec :=
  (setupContext R pp).append (fun _ => firstSumcheckContext R pp)

/-- Role decoration for the Spartan prefix through the first virtual
sum-check. -/
abbrev setupThenFirstSumcheckRoles [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.RoleDeco (setupThenFirstSumcheckContext R pp) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (setupContext R pp)
    (fun _ => firstSumcheckContext R pp)
    (setupRoles R pp)
    (fun _ => firstSumcheckRoles R pp)

/-- Oracle-message decoration for the Spartan prefix through the first virtual
sum-check. -/
abbrev setupThenFirstSumcheckOracleDeco [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.OracleDeco (setupThenFirstSumcheckContext R pp) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (setupContext R pp)
    (fun _ => firstSumcheckContext R pp)
    (setupOracleDeco R pp)
    (fun _ => firstSumcheckOracleDeco R pp)

/-- Spartan setup followed by the first virtual sum-check, composed with the
generic oracle-reduction composition primitive. -/
abbrev setupThenFirstSumcheckReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [instDomain : IsDomain R] [instFintype : Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp))
    (sampleSumcheckChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => (setupContext R pp).append (fun _ => firstSumcheckContext R pp))
      (fun _ =>
        Interaction.Oracle.Spec.RoleDeco.append
          (setupContext R pp)
          (fun _ => firstSumcheckContext R pp)
          (setupRoles R pp)
          (fun _ => firstSumcheckRoles R pp))
      (fun _ =>
        Interaction.Oracle.Spec.OracleDeco.append
          (setupContext R pp)
          (fun _ => firstSumcheckContext R pp)
          (setupOracleDeco R pp)
          (fun _ => firstSumcheckOracleDeco R pp))
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => AfterFirstSumcheckStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterFirstSumcheckOracleFamily R pp)
      (fun _ _ => PUnit) :=
  Interaction.Oracle.Reduction.comp
    (Context₂ := fun _ _ => firstSumcheckContext R pp)
    (Roles₂ := fun _ _ => firstSumcheckRoles R pp)
    (OracleDeco₂ := fun _ _ => firstSumcheckOracleDeco R pp)
    (StatementOut := fun _ _ _ => AfterFirstSumcheckStatement R pp)
    (ιₛₒ := fun _ _ _ => R1CS.MatrixIdx ⊕ Unit)
    (OStatementOut := fun _ _ _ => AfterFirstSumcheckOracleFamily R pp)
    (WitnessOut := fun _ _ _ => PUnit)
    (setupReduction (R := R) (pp := pp) (oSpec := oSpec)
      sampleFirstChallenge)
    (fun _ _ =>
      firstSumcheckContinuationReduction (R := R) (pp := pp) (oSpec := oSpec)
        D sampleSumcheckChallenge)

end SetupThenFirstSumcheck

section SetupThenEvalClaim

variable (R : Type) [BEq R] [CommRing R] [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Spartan prefix through the evaluation-claim message following the first
virtual sum-check. -/
abbrev setupThenEvalClaimContext [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec :=
  (setupThenFirstSumcheckContext R pp).append (fun _ => evalClaimSpec R)

/-- Role decoration for the Spartan prefix through the evaluation-claim
message. -/
abbrev setupThenEvalClaimRoles [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.RoleDeco (setupThenEvalClaimContext R pp) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (setupThenFirstSumcheckContext R pp)
    (fun _ => evalClaimSpec R)
    (setupThenFirstSumcheckRoles R pp)
    (fun _ => evalClaimRoles R)

/-- Oracle-message decoration for the Spartan prefix through the
evaluation-claim message. -/
abbrev setupThenEvalClaimOracleDeco [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.OracleDeco (setupThenEvalClaimContext R pp) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (setupThenFirstSumcheckContext R pp)
    (fun _ => evalClaimSpec R)
    (setupThenFirstSumcheckOracleDeco R pp)
    (fun _ => evalClaimOracleDeco R)

/-- Spartan setup, first virtual sum-check, and the subsequent public
evaluation-claim message, composed using the generic oracle-reduction
composition primitive. -/
abbrev setupThenEvalClaimReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [instDomain : IsDomain R] [instFintype : Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp))
    (sampleSumcheckChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => (setupThenFirstSumcheckContext R pp).append (fun _ => evalClaimSpec R))
      (fun _ =>
        Interaction.Oracle.Spec.RoleDeco.append
          (setupThenFirstSumcheckContext R pp)
          (fun _ => evalClaimSpec R)
          (setupThenFirstSumcheckRoles R pp)
          (fun _ => evalClaimRoles R))
      (fun _ =>
        Interaction.Oracle.Spec.OracleDeco.append
          (setupThenFirstSumcheckContext R pp)
          (fun _ => evalClaimSpec R)
          (setupThenFirstSumcheckOracleDeco R pp)
          (fun _ => evalClaimOracleDeco R))
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => AfterEvalClaimStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterEvalClaimOracleFamily R pp)
      (fun _ _ => PUnit) :=
  Interaction.Oracle.Reduction.comp
    (Context₂ := fun _ _ => evalClaimSpec R)
    (Roles₂ := fun _ _ => evalClaimRoles R)
    (OracleDeco₂ := fun _ _ => evalClaimOracleDeco R)
    (StatementOut := fun _ _ _ => AfterEvalClaimStatement R pp)
    (ιₛₒ := fun _ _ _ => R1CS.MatrixIdx ⊕ Unit)
    (OStatementOut := fun _ _ _ => AfterEvalClaimOracleFamily R pp)
    (WitnessOut := fun _ _ _ => PUnit)
    (setupThenFirstSumcheckReduction (R := R) (pp := pp) (oSpec := oSpec)
      D sampleFirstChallenge sampleSumcheckChallenge)
    (fun _ _ => evalClaimReduction (R := R) (pp := pp) (oSpec := oSpec))

end SetupThenEvalClaim

section SetupThenLinearCombination

variable (R : Type) [BEq R] [CommRing R] [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Spartan prefix through the random linear-combination challenge before the
second sum-check. -/
abbrev setupThenLinearCombinationContext [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec :=
  (setupThenEvalClaimContext R pp).append (fun _ => linearCombinationSpec R)

/-- Role decoration for the Spartan prefix through the linear-combination
challenge. -/
abbrev setupThenLinearCombinationRoles [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.RoleDeco (setupThenLinearCombinationContext R pp) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (setupThenEvalClaimContext R pp)
    (fun _ => linearCombinationSpec R)
    (setupThenEvalClaimRoles R pp)
    (fun _ => linearCombinationRoles R)

/-- Oracle-message decoration for the Spartan prefix through the
linear-combination challenge. -/
abbrev setupThenLinearCombinationOracleDeco [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.OracleDeco (setupThenLinearCombinationContext R pp) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (setupThenEvalClaimContext R pp)
    (fun _ => linearCombinationSpec R)
    (setupThenEvalClaimOracleDeco R pp)
    (fun _ => linearCombinationOracleDeco R)

/-- Spartan setup, first virtual sum-check, evaluation claims, and
linear-combination challenge, composed with the generic oracle-reduction
composition primitive. -/
abbrev setupThenLinearCombinationReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [instDomain : IsDomain R] [instFintype : Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp))
    (sampleSumcheckChallenge : OracleComp oSpec R)
    (sampleLinearCombination : OracleComp oSpec (LinearCombinationChallenge R)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => (setupThenEvalClaimContext R pp).append
        (fun _ => linearCombinationSpec R))
      (fun _ =>
        Interaction.Oracle.Spec.RoleDeco.append
          (setupThenEvalClaimContext R pp)
          (fun _ => linearCombinationSpec R)
          (setupThenEvalClaimRoles R pp)
          (fun _ => linearCombinationRoles R))
      (fun _ =>
        Interaction.Oracle.Spec.OracleDeco.append
          (setupThenEvalClaimContext R pp)
          (fun _ => linearCombinationSpec R)
          (setupThenEvalClaimOracleDeco R pp)
          (fun _ => linearCombinationOracleDeco R))
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => AfterLinearCombinationStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterLinearCombinationOracleFamily R pp)
      (fun _ _ => PUnit) :=
  Interaction.Oracle.Reduction.comp
    (Context₂ := fun _ _ => linearCombinationSpec R)
    (Roles₂ := fun _ _ => linearCombinationRoles R)
    (OracleDeco₂ := fun _ _ => linearCombinationOracleDeco R)
    (StatementOut := fun _ _ _ => AfterLinearCombinationStatement R pp)
    (ιₛₒ := fun _ _ _ => R1CS.MatrixIdx ⊕ Unit)
    (OStatementOut := fun _ _ _ => AfterLinearCombinationOracleFamily R pp)
    (WitnessOut := fun _ _ _ => PUnit)
    (setupThenEvalClaimReduction (R := R) (pp := pp) (oSpec := oSpec)
      D sampleFirstChallenge sampleSumcheckChallenge)
    (fun _ _ =>
      linearCombinationReduction (R := R) (pp := pp) (oSpec := oSpec)
        sampleLinearCombination)

end SetupThenLinearCombination

section SetupThenSecondSumcheck

variable (R : Type) [BEq R] [CommRing R] [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Spartan prefix through the second virtual sum-check. -/
abbrev setupThenSecondSumcheckContext [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec :=
  (setupThenLinearCombinationContext R pp).append (fun _ => secondSumcheckContext R pp)

/-- Role decoration for the Spartan prefix through the second virtual
sum-check. -/
abbrev setupThenSecondSumcheckRoles [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.RoleDeco (setupThenSecondSumcheckContext R pp) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (setupThenLinearCombinationContext R pp)
    (fun _ => secondSumcheckContext R pp)
    (setupThenLinearCombinationRoles R pp)
    (fun _ => secondSumcheckRoles R pp)

/-- Oracle-message decoration for the Spartan prefix through the second
virtual sum-check. -/
abbrev setupThenSecondSumcheckOracleDeco [IsDomain R] [Fintype R] :
    Interaction.Oracle.Spec.OracleDeco (setupThenSecondSumcheckContext R pp) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (setupThenLinearCombinationContext R pp)
    (fun _ => secondSumcheckContext R pp)
    (setupThenLinearCombinationOracleDeco R pp)
    (fun _ => secondSumcheckOracleDeco R pp)

/-- Spartan setup through the second virtual sum-check, composed with the
generic oracle-reduction composition primitive. -/
abbrev setupThenSecondSumcheckReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [instDomain : IsDomain R] [instFintype : Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp))
    (sampleSumcheckChallenge : OracleComp oSpec R)
    (sampleLinearCombination : OracleComp oSpec (LinearCombinationChallenge R)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => (setupThenLinearCombinationContext R pp).append
        (fun _ => secondSumcheckContext R pp))
      (fun _ =>
        Interaction.Oracle.Spec.RoleDeco.append
          (setupThenLinearCombinationContext R pp)
          (fun _ => secondSumcheckContext R pp)
          (setupThenLinearCombinationRoles R pp)
          (fun _ => secondSumcheckRoles R pp))
      (fun _ =>
        Interaction.Oracle.Spec.OracleDeco.append
          (setupThenLinearCombinationContext R pp)
          (fun _ => secondSumcheckContext R pp)
          (setupThenLinearCombinationOracleDeco R pp)
          (fun _ => secondSumcheckOracleDeco R pp))
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => AfterSecondSumcheckStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterSecondSumcheckOracleFamily R pp)
      (fun _ _ => PUnit) :=
  Interaction.Oracle.Reduction.comp
    (Context₂ := fun _ _ => secondSumcheckContext R pp)
    (Roles₂ := fun _ _ => secondSumcheckRoles R pp)
    (OracleDeco₂ := fun _ _ => secondSumcheckOracleDeco R pp)
    (StatementOut := fun _ _ _ => AfterSecondSumcheckStatement R pp)
    (ιₛₒ := fun _ _ _ => R1CS.MatrixIdx ⊕ Unit)
    (OStatementOut := fun _ _ _ => AfterSecondSumcheckOracleFamily R pp)
    (WitnessOut := fun _ _ _ => PUnit)
    (setupThenLinearCombinationReduction (R := R) (pp := pp) (oSpec := oSpec)
      D sampleFirstChallenge sampleSumcheckChallenge sampleLinearCombination)
    (fun _ _ =>
      secondSumcheckContinuationReduction (R := R) (pp := pp) (oSpec := oSpec)
        D sampleSumcheckChallenge)

end SetupThenSecondSumcheck

end

end OracleLayer

end Spartan

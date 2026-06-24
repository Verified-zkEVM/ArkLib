/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Composition
import ArkLib.Interaction.Oracle.Program

open Interaction.TwoParty

/-!
# Programmatic oracle verifier composition helpers

Experimental composition hooks for verifier programs. The legacy composition
module remains unchanged; this file holds the bridge points for the terminal
output shape.
-/

open OracleComp OracleSpec

namespace Interaction.Oracle
namespace Verifier

/-- Retarget a suffix verifier using a prefix verifier leaf packaged as
`TerminalOutput`.

Once a prefix verifier program has produced the next oracle problem, the suffix
verifier's input-oracle reads can be routed through that terminal simulator. -/
def TerminalOutput.retargetMonads
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context₁ : SharedIn → Spec}
    {OracleDeco₁ : (shared : SharedIn) → Spec.OracleDeco (Context₁ shared)}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface.{0, 0} (OStatementIn shared i)]
    {StatementMid :
      (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {OStatementMid :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
        ιₛₘ shared pt₁ → Type}
    [∀ shared pt₁ i, OracleInterface.{0, 0} (OStatementMid shared pt₁ i)]
    {shared : SharedIn}
    {pt₁ : Spec.PublicTranscript (Context₁ shared)}
    (midOut : TerminalOutput SharedIn Context₁ OracleDeco₁ OStatementIn
      StatementMid OStatementMid shared pt₁)
    (answerQ : QueryImpl ((Context₁ shared).toOracleSpec (OracleDeco₁ shared) pt₁) Id)
    (s₂ : Oracle.Spec) (roles₂ : Spec.RoleDeco s₂) (od₂ : Spec.OracleDeco s₂)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {Output : Interaction.Spec.Transcript s₂.toInteractionSpec → Type}
    (cpt : Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      s₂.toInteractionSpec
      (RoleDecoration.withMonads (s₂.toSpecRoles roles₂)
        (s₂.toMonadDecoration oSpec (OStatementMid shared pt₁) roles₂ od₂ accSpec))
      Output) :
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      s₂.toInteractionSpec
      (RoleDecoration.withMonads (s₂.toSpecRoles roles₂)
        (s₂.toMonadDecoration oSpec (OStatementIn shared) roles₂ od₂ accSpec))
      Output :=
  Verifier.retargetMonads midOut.simulate answerQ s₂ roles₂ od₂ accSpec cpt

end Verifier
end Interaction.Oracle

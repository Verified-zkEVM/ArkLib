/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution
import ArkLib.Interaction.Oracle.Program

/-!
# Programmatic oracle verifier execution helpers

Additive execution support for explicit verifier access families. The ordinary
oracle execution module remains the stable runner.
-/

open Interaction.TwoParty
open OracleComp OracleSpec

namespace Interaction
namespace Oracle

/-- Run a prover strategy against a verifier counterpart whose receiver-node
effects are supplied by an explicit verifier access family. -/
def Spec.runWithOracleCounterpartAccess
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (access : Verifier.AccessFamily oSpec OStmtIn)
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → (accImpl : QueryImpl accSpec Id) →
    {OutputP OutputC : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    Interaction.Spec.StrategyOver focalMonadicSyntax PUnit.unit
      s.toInteractionSpec
      (RoleDecoration.withMonads
        (s.toSpecRoles roles) (s.toProverMonadDecoration oSpec))
      OutputP →
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      s.toInteractionSpec
      (RoleDecoration.withMonads (s.toSpecRoles roles)
        (s.toVerifierAccessDecoration access roles od accSpec))
      OutputC →
    OracleComp oSpec ((tr : Interaction.Spec.Transcript s.toInteractionSpec) ×
      OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, _, _, output, cOutput =>
      pure ⟨⟨⟩, output, cOutput⟩
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let z ← runWithOracleCounterpartAccess access inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«public» _ rest, ⟨.receiver, rRest⟩, odRest, _, accSpec, accImpl, _, OutputC,
      respond, dualSample => do
      let readImpl : QueryImpl (Verifier.ReadSpec OStmtIn accSpec) (OracleComp oSpec) :=
        Verifier.AccessFamily.readImpl
          (fun q => liftM (inputImpl q))
          (fun q => liftM (accImpl q))
      let z' : Sigma (fun x =>
          Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
            (rest x).toInteractionSpec
            (RoleDecoration.withMonads ((rest x).toSpecRoles (rRest x))
              ((rest x).toVerifierAccessDecoration access (rRest x) (odRest x) accSpec))
            (fun p => OutputC ⟨x, p⟩)) ←
        access.runM readImpl dualSample
      let x := z'.1
      let dualRest := z'.2
      let next ← respond x
      let z ← runWithOracleCounterpartAccess access inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next dualRest
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«oracle» _ cont, roles, ⟨oi, odRest⟩, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id :=
        fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpartAccess access inputImpl
        (cont ⟨⟩) roles odRest (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩

end Oracle
end Interaction

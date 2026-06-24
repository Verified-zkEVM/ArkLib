/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core
import ArkLib.Interaction.Oracle.Composition
import VCVio.OracleComp.SimSemantics.SimulateQ

open Interaction.TwoParty

/-!
# Oracle.Spec Execution

Concrete execution for `Interaction.Oracle.Spec` reductions.
-/

open OracleComp OracleSpec

namespace Interaction

/-! ## Execution for Oracle.Spec-based reductions -/

namespace Oracle

/-- Run a prover strategy against a verifier counterpart on `Oracle.Spec`,
threading accumulated oracle access. -/
def Spec.runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
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
        (s.toMonadDecoration oSpec OStmtIn roles od accSpec))
      OutputC →
    OracleComp oSpec ((tr : Interaction.Spec.Transcript s.toInteractionSpec) ×
      OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, _, _, output, cOutput =>
      pure ⟨⟨⟩, output, cOutput⟩
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«public» X rest, ⟨.receiver, rRest⟩, odRest, _, accSpec, accImpl, OutputP, OutputC,
      respond, dualSample => do
      let routeImpl : QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (oSpec.query q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      have dualSample' : OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec) _ := by
        simpa using dualSample
      let z' : Sigma (fun x =>
          Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
            (rest x).toInteractionSpec
            (RoleDecoration.withMonads ((rest x).toSpecRoles (rRest x))
              ((rest x).toMonadDecoration oSpec OStmtIn (rRest x) (odRest x) accSpec))
            (fun p => OutputC ⟨x, p⟩)) ←
        simulateQ routeImpl dualSample'
      let x := z'.1
      let dualRest := z'.2
      let next ← respond x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next dualRest
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«oracle» _ cont, roles, ⟨oi, odRest⟩, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id :=
        fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpart inputImpl
        (cont ⟨⟩) roles odRest (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩

/-- Run a two-phase oracle interaction in staged form.

This is the semantic counterpart of sequential composition before proving it
equal to the single appended interaction. It first runs the prefix strategy and
counterpart, then runs the suffix at the prefix public transcript. The suffix
verifier receives the accumulator obtained from the full prefix transcript:
`Spec.accumulatedSpec` gives the oracle spec and `Spec.accumulatedImpl` gives
the concrete implementation answering those accumulated oracle-message
queries. -/
def Spec.runWithOracleCounterpartStaged
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s₁ : Spec) → (s₂ : Spec.PublicTranscript s₁ → Spec) →
    (r₁ : Spec.RoleDeco s₁) →
    (r₂ : (pt₁ : Spec.PublicTranscript s₁) → Spec.RoleDeco (s₂ pt₁)) →
    (od₁ : Spec.OracleDeco s₁) →
    (od₂ : (pt₁ : Spec.PublicTranscript s₁) → Spec.OracleDeco (s₂ pt₁)) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → QueryImpl accSpec Id →
    {MidP MidC : Interaction.Spec.Transcript s₁.toInteractionSpec → Type} →
    {OutP OutC :
      (pt₁ : Spec.PublicTranscript s₁) → Spec.PublicTranscript (s₂ pt₁) → Type} →
    Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
      Interaction.TwoParty.Participant.focal
      s₁.toInteractionSpec (s₁.toSpecRoles r₁) MidP →
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      s₁.toInteractionSpec
      (RoleDecoration.withMonads (s₁.toSpecRoles r₁)
        (s₁.toMonadDecoration oSpec OStmtIn r₁ od₁ accSpec))
      MidC →
    ((tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) → MidP tr₁ →
      OracleComp oSpec
        (Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
          Interaction.TwoParty.Participant.focal
          ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec)
          ((s₂ (s₁.projectPublic tr₁)).toSpecRoles (r₂ (s₁.projectPublic tr₁)))
          (fun tr₂ => OutP (s₁.projectPublic tr₁)
            ((s₂ (s₁.projectPublic tr₁)).projectPublic tr₂)))) →
    ((tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) → MidC tr₁ →
      Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
        ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec)
        (RoleDecoration.withMonads
          ((s₂ (s₁.projectPublic tr₁)).toSpecRoles (r₂ (s₁.projectPublic tr₁)))
          ((s₂ (s₁.projectPublic tr₁)).toMonadDecoration oSpec OStmtIn
            (r₂ (s₁.projectPublic tr₁)) (od₂ (s₁.projectPublic tr₁))
            (Spec.accumulatedSpec s₁ od₁ tr₁ accSpec).2))
        (fun tr₂ => OutC (s₁.projectPublic tr₁)
          ((s₂ (s₁.projectPublic tr₁)).projectPublic tr₂))) →
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (s₁.append s₂).toInteractionSpec) ×
        Spec.PublicTranscript.liftAppend s₁ s₂ OutP ((s₁.append s₂).projectPublic tr) ×
        Spec.PublicTranscript.liftAppend s₁ s₂ OutC ((s₁.append s₂).projectPublic tr))
  | .done, s₂, _, r₂, _, od₂, _, accSpec, accImpl, _, _, _, _, strat₁, cpt₁,
      contP, contC => do
      let strat₂ ← contP ⟨⟩ strat₁
      let strat₂' :=
        Interaction.TwoParty.Focal.toConstantMonads
          (s₂ ⟨⟩).toInteractionSpec
          ((s₂ ⟨⟩).toSpecRoles (r₂ ⟨⟩))
          strat₂
      Spec.runWithOracleCounterpart inputImpl
        (s₂ ⟨⟩) (r₂ ⟨⟩) (od₂ ⟨⟩) accSpec accImpl strat₂' (contC ⟨⟩ cpt₁)
  | .«public» _ rest, s₂, ⟨.sender, rRest⟩, r₂, od₁, od₂, _, accSpec, accImpl,
      _, _, OutP, OutC, strat₁, cpt₁, contP, contC => do
      let ⟨x, next⟩ ← strat₁
      let z ← runWithOracleCounterpartStaged inputImpl
        (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (rRest x) (fun pt => r₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩)
        (OutP := fun pt₁ pt₂ => OutP ⟨x, pt₁⟩ pt₂)
        (OutC := fun pt₁ pt₂ => OutC ⟨x, pt₁⟩ pt₂)
        accSpec accImpl next (cpt₁ x)
        (fun tr₁ mid => contP ⟨x, tr₁⟩ mid)
        (fun tr₁ mid => contC ⟨x, tr₁⟩ mid)
      pure ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«public» _ rest, s₂, ⟨.receiver, rRest⟩, r₂, od₁, od₂, _, accSpec, accImpl,
      _, MidC, OutP, OutC, strat₁, cpt₁, contP, contC => do
      let routeImpl : QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (oSpec.query q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      have cpt₁' : OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec) _ := by
        simpa using cpt₁
      let z' : Sigma (fun x =>
          Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
            (rest x).toInteractionSpec
            (RoleDecoration.withMonads ((rest x).toSpecRoles (rRest x))
              ((rest x).toMonadDecoration oSpec OStmtIn (rRest x) (od₁ x) accSpec))
            (fun p => MidC ⟨x, p⟩)) ←
        simulateQ routeImpl cpt₁'
      let x := z'.1
      let cptRest := z'.2
      let next ← strat₁ x
      let z ← runWithOracleCounterpartStaged inputImpl
        (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (rRest x) (fun pt => r₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩)
        (OutP := fun pt₁ pt₂ => OutP ⟨x, pt₁⟩ pt₂)
        (OutC := fun pt₁ pt₂ => OutC ⟨x, pt₁⟩ pt₂)
        accSpec accImpl next cptRest
        (fun tr₁ mid => contP ⟨x, tr₁⟩ mid)
        (fun tr₁ mid => contC ⟨x, tr₁⟩ mid)
      pure ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«oracle» _ cont, s₂, r₁, r₂, ⟨oi, odRest⟩, od₂, _, accSpec, accImpl, _, _,
      OutP, OutC, strat₁, cpt₁, contP, contC => do
      let ⟨x, next⟩ ← strat₁
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id :=
        fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpartStaged inputImpl
        (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        r₁ (fun pt => r₂ ⟨⟨⟩, pt⟩) odRest (fun pt => od₂ ⟨⟨⟩, pt⟩)
        (OutP := fun pt₁ pt₂ => OutP ⟨⟨⟩, pt₁⟩ pt₂)
        (OutC := fun pt₁ pt₂ => OutC ⟨⟨⟩, pt₁⟩ pt₂)
        (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX)
        next (cpt₁ x)
        (fun tr₁ mid => contP ⟨x, tr₁⟩ mid)
        (fun tr₁ mid => contC ⟨x, tr₁⟩ mid)
      pure ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩

/-- Execute an `Oracle.Reduction` against concrete oracle input statements.
Produces the realized transcript, prover output (statement + oracle statements +
witness), and verifier output (statement + output oracle simulation). -/
def Reduction.executeConcrete
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       HonestProverOutput
         (StatementWithOracles
           (fun _ => StatementOut shared ((Context shared).projectPublic tr))
           (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
           shared)
         (WitnessOut shared ((Context shared).projectPublic tr)) ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) := do
  let strategy ← reduction.prover shared s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    Spec.runWithOracleCounterpart
      (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
      strategy (reduction.verifier.toFun shared s.stmt)
  pure ⟨tr, proverOut,
    ⟨stmtOutV,
     reduction.verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩

/-- Run an arbitrary prover strategy against the verifier of an
`Oracle.Reduction` on a concrete oracle input statement. -/
def Reduction.runConcrete
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    {OutputP : Interaction.Spec.Transcript (Context shared).toInteractionSpec → Type}
    (prover : Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
      Interaction.TwoParty.Participant.focal
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared)) OutputP) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       OutputP tr ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) :=
  let inputImpl := OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt
  let prover' :=
    Interaction.TwoParty.Focal.toConstantMonads
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared))
      prover
  do
    let ⟨tr, outP, stmtOutV⟩ ←
      Spec.runWithOracleCounterpart inputImpl
        (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
        prover' (reduction.verifier.toFun shared s.stmt)
    pure ⟨tr, outP,
      ⟨stmtOutV,
       reduction.verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩

/-- Map the private honest-prover witness component of a concrete execution
result while leaving the public transcript, public statement-with-oracles, and
verifier-side oracle simulation unchanged. -/
def Reduction.mapExecuteWitness
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut₁ WitnessOut₂ :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (liftWitness :
      (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) →
        WitnessOut₁ shared ((Context shared).projectPublic tr) →
        WitnessOut₂ shared ((Context shared).projectPublic tr)) :
    ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
      HonestProverOutput
        (StatementWithOracles
          (fun _ => StatementOut shared ((Context shared).projectPublic tr))
          (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
          shared)
        (WitnessOut₁ shared ((Context shared).projectPublic tr)) ×
      (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) →
    ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
      HonestProverOutput
        (StatementWithOracles
          (fun _ => StatementOut shared ((Context shared).projectPublic tr))
          (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
          shared)
        (WitnessOut₂ shared ((Context shared).projectPublic tr)) ×
      (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) :=
  let _ := oSpec
  let _ := s
  fun ⟨tr, out, view⟩ => ⟨tr, ⟨out.stmt, liftWitness tr out.wit⟩, view⟩

/-- Forget the private honest-prover witness component of a concrete execution
result, keeping only the public transcript/output view. -/
def Reduction.forgetExecuteWitness
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared) :
    ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
      HonestProverOutput
        (StatementWithOracles
          (fun _ => StatementOut shared ((Context shared).projectPublic tr))
          (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
          shared)
        (WitnessOut shared ((Context shared).projectPublic tr)) ×
      (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) →
    ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
      StatementWithOracles
        (fun _ => StatementOut shared ((Context shared).projectPublic tr))
        (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
        shared ×
      (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) :=
  let _ := oSpec
  let _ := s
  fun ⟨tr, out, view⟩ => ⟨tr, out.stmt, view⟩

/-- Execute an `Oracle.Reduction` honestly and erase the prover's private output
witness, retaining the public outgoing statement-with-oracles and verifier-side
oracle simulation. -/
def Reduction.executePublicConcrete
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       StatementWithOracles
         (fun _ => StatementOut shared ((Context shared).projectPublic tr))
         (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
         shared ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) :=
  (Reduction.forgetExecuteWitness
    (oSpec := oSpec)
    (Context := Context)
    (OracleDeco := OracleDeco)
    (StatementIn := StatementIn)
    (OStatementIn := OStatementIn)
    (StatementOut := StatementOut)
    (OStatementOut := OStatementOut)
    (WitnessOut := WitnessOut)
    shared s) <$> reduction.executeConcrete shared s w

/-- Two reductions with the same public oracle interface are honestly publicly
equivalent when witness-related input transport preserves their public concrete
executions. -/
def Reduction.HonestPubliclyEquivalent
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn WitnessIn₁ WitnessIn₂ : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut₁ WitnessOut₂ :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (liftWitness :
      (shared : SharedIn) →
        StatementWithOracles StatementIn OStatementIn shared →
          WitnessIn₁ shared → WitnessIn₂ shared)
    (reduction₁ : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn₁ StatementOut OStatementOut WitnessOut₁)
    (reduction₂ : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn₂ StatementOut OStatementOut WitnessOut₂) : Prop :=
  ∀ (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn₁ shared),
      reduction₁.executePublicConcrete shared s w =
        reduction₂.executePublicConcrete shared s (liftWitness shared s w)

/-- Two reductions with the same public oracle interface are honestly execution
equivalent when input-witness transport and output-witness transport make their
full concrete executions agree. -/
def Reduction.HonestExecutionEquivalent
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn WitnessIn₁ WitnessIn₂ : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut₁ WitnessOut₂ :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (liftWitnessIn :
      (shared : SharedIn) →
        StatementWithOracles StatementIn OStatementIn shared →
          WitnessIn₁ shared → WitnessIn₂ shared)
    (liftWitnessOut :
      (shared : SharedIn) →
        (s : StatementWithOracles StatementIn OStatementIn shared) →
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) →
          WitnessOut₁ shared ((Context shared).projectPublic tr) →
          WitnessOut₂ shared ((Context shared).projectPublic tr))
    (reduction₁ : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn₁ StatementOut OStatementOut WitnessOut₁)
    (reduction₂ : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn₂ StatementOut OStatementOut WitnessOut₂) : Prop :=
  ∀ (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn₁ shared),
      (Reduction.mapExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (OracleDeco := OracleDeco)
        (StatementIn := StatementIn)
        (OStatementIn := OStatementIn)
        (StatementOut := StatementOut)
        (OStatementOut := OStatementOut)
        (WitnessOut₁ := WitnessOut₁)
        (WitnessOut₂ := WitnessOut₂)
        shared s
        (liftWitnessOut shared s)) <$> reduction₁.executeConcrete shared s w =
          reduction₂.executeConcrete shared s (liftWitnessIn shared s w)

/-- Public execution is full concrete execution with private prover witnesses
erased. -/
theorem Reduction.executePublic_eq_map_execute
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    reduction.executePublicConcrete shared s w =
      (Reduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (OracleDeco := OracleDeco)
        (StatementIn := StatementIn)
        (OStatementIn := OStatementIn)
        (StatementOut := StatementOut)
        (OStatementOut := OStatementOut)
        (WitnessOut := WitnessOut)
        shared s) <$> reduction.executeConcrete shared s w :=
  rfl

/-- Honest execution equivalence implies honest public equivalence. -/
theorem Reduction.HonestExecutionEquivalent.toPublic
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn WitnessIn₁ WitnessIn₂ : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut₁ WitnessOut₂ :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {liftWitnessIn :
      (shared : SharedIn) →
        StatementWithOracles StatementIn OStatementIn shared →
          WitnessIn₁ shared → WitnessIn₂ shared}
    {liftWitnessOut :
      (shared : SharedIn) →
        (s : StatementWithOracles StatementIn OStatementIn shared) →
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) →
          WitnessOut₁ shared ((Context shared).projectPublic tr) →
          WitnessOut₂ shared ((Context shared).projectPublic tr)}
    {reduction₁ : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn₁ StatementOut OStatementOut WitnessOut₁}
    {reduction₂ : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn₂ StatementOut OStatementOut WitnessOut₂}
    (hEq : Reduction.HonestExecutionEquivalent
      liftWitnessIn liftWitnessOut reduction₁ reduction₂) :
    Reduction.HonestPubliclyEquivalent liftWitnessIn reduction₁ reduction₂ := by
  intro shared s w
  rw [Reduction.executePublic_eq_map_execute,
    Reduction.executePublic_eq_map_execute]
  have hForget :
      (Reduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (OracleDeco := OracleDeco)
        (StatementIn := StatementIn)
        (OStatementIn := OStatementIn)
        (StatementOut := StatementOut)
        (OStatementOut := OStatementOut)
        (WitnessOut := WitnessOut₂)
        shared s) ∘
        (Reduction.mapExecuteWitness
          (oSpec := oSpec)
          (Context := Context)
          (OracleDeco := OracleDeco)
          (StatementIn := StatementIn)
          (OStatementIn := OStatementIn)
          (StatementOut := StatementOut)
          (OStatementOut := OStatementOut)
          (WitnessOut₁ := WitnessOut₁)
          (WitnessOut₂ := WitnessOut₂)
          shared s
          (liftWitnessOut shared s)) =
        (Reduction.forgetExecuteWitness
          (oSpec := oSpec)
          (Context := Context)
          (OracleDeco := OracleDeco)
          (StatementIn := StatementIn)
          (OStatementIn := OStatementIn)
          (StatementOut := StatementOut)
          (OStatementOut := OStatementOut)
          (WitnessOut := WitnessOut₁)
          shared s) := by
    funext z
    cases z
    rfl
  simpa [Functor.map_map, Function.comp, hForget] using
    congrArg
      (Functor.map
        (Reduction.forgetExecuteWitness
          (oSpec := oSpec)
          (Context := Context)
          (OracleDeco := OracleDeco)
          (StatementIn := StatementIn)
          (OStatementIn := OStatementIn)
          (StatementOut := StatementOut)
          (OStatementOut := OStatementOut)
          (WitnessOut := WitnessOut₂)
          shared s))
      (hEq shared s w)

/-- Run an arbitrary prover strategy against an `Oracle.Verifier`, producing the
full transcript, prover output, and the verifier's statement output paired with
its output oracle simulation. This is the `Oracle.Spec` analog of
`OracleVerifier.run`. -/
def Verifier.run
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    {OutputP : Interaction.Spec.Transcript (Context shared).toInteractionSpec → Type}
    (prover : Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
      Interaction.TwoParty.Participant.focal
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared)) OutputP) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       OutputP tr ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) := do
  let prover' :=
    Interaction.TwoParty.Focal.toConstantMonads
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared))
      prover
  let ⟨tr, outP, stmtOutV⟩ ←
    Spec.runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
      prover' (verifier.toFun shared stmt)
  pure ⟨tr, outP,
    ⟨stmtOutV,
     verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩

/-- Running a reduction against an arbitrary prover strategy is just running
that strategy against the reduction verifier, with the input oracle statement
implemented by `simOracle0`. -/
theorem Reduction.runConcrete_eq_verifier_run
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    {OutputP : Interaction.Spec.Transcript (Context shared).toInteractionSpec → Type}
    (prover : Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
      Interaction.TwoParty.Participant.focal
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared)) OutputP) :
    reduction.runConcrete shared s prover =
      Verifier.run reduction.verifier shared s.stmt
        (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
        prover :=
  rfl

/-- Honest concrete execution is honest prover setup followed by the oracle
interaction runner. -/
theorem Reduction.executeConcrete_eq_runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    reduction.executeConcrete shared s w =
      (do
        let strategy ← reduction.prover shared s w
        let ⟨tr, proverOut, stmtOutV⟩ ←
          Spec.runWithOracleCounterpart
            (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
            (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
            strategy (reduction.verifier.toFun shared s.stmt)
        pure ⟨tr, proverOut,
          ⟨stmtOutV,
           reduction.verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩) :=
  rfl

/-- Concrete execution of a composed reduction is a single interaction over the
appended oracle context, using the composed prover strategy and composed
verifier counterpart.

This theorem is intentionally structural: the suffix verifier's queries to the
middle oracle are routed by `Reduction.comp`'s verifier simulation, rather than
being identified with the prefix prover's concrete output oracle by type-level
transport. -/
theorem Reduction.executeConcrete_comp_eq_runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context₁ : SharedIn → Spec}
    {Roles₁ : (shared : SharedIn) → Spec.RoleDeco (Context₁ shared)}
    {OracleDeco₁ : (shared : SharedIn) → Spec.OracleDeco (Context₁ shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementMid :
      (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {OStatementMid :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
        ιₛₘ shared pt₁ → Type}
    [∀ shared pt₁ i, OracleInterface (OStatementMid shared pt₁ i)]
    {WitnessMid :
      (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Type}
    {Context₂ : (shared : SharedIn) → Spec.PublicTranscript (Context₁ shared) → Spec}
    {Roles₂ : (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.RoleDeco (Context₂ shared pt₁)}
    {OracleDeco₂ : (shared : SharedIn) →
      (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.OracleDeco (Context₂ shared pt₁)}
    {StatementOut :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.PublicTranscript (Context₂ shared pt₁) → Type}
    {ιₛₒ : (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.PublicTranscript (Context₂ shared pt₁) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      (pt₂ : Spec.PublicTranscript (Context₂ shared pt₁)) → ιₛₒ shared pt₁ pt₂ → Type}
    [∀ shared pt₁ pt₂ i, OracleInterface (OStatementOut shared pt₁ pt₂ i)]
    {WitnessOut :
      (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Spec.PublicTranscript (Context₂ shared pt₁) → Type}
    (r₁ : Reduction oSpec SharedIn Context₁ Roles₁ OracleDeco₁
      StatementIn OStatementIn WitnessIn StatementMid OStatementMid WitnessMid)
    (r₂ : (shared : SharedIn) → (pt₁ : Spec.PublicTranscript (Context₁ shared)) →
      Reduction oSpec PUnit
        (fun _ => Context₂ shared pt₁)
        (fun _ => Roles₂ shared pt₁)
        (fun _ => OracleDeco₂ shared pt₁)
        (fun _ => StatementMid shared pt₁)
        (fun _ => OStatementMid shared pt₁)
        (fun _ => WitnessMid shared pt₁)
        (fun _ pt₂ => StatementOut shared pt₁ pt₂)
        (OStatementOut := fun _ pt₂ => OStatementOut shared pt₁ pt₂)
        (fun _ pt₂ => WitnessOut shared pt₁ pt₂))
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    (Reduction.comp r₁ r₂).executeConcrete shared s w =
      (do
        let strategy ← (Reduction.comp r₁ r₂).prover shared s w
        let ⟨tr, proverOut, stmtOutV⟩ ←
          Spec.runWithOracleCounterpart
            (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
            ((Context₁ shared).append (Context₂ shared))
            (Spec.RoleDeco.append (Context₁ shared) (Context₂ shared)
              (Roles₁ shared) (Roles₂ shared))
            (Spec.OracleDeco.append (Context₁ shared) (Context₂ shared)
              (OracleDeco₁ shared) (OracleDeco₂ shared))
            []ₒ (fun q => q.elim)
            strategy
            ((Reduction.comp r₁ r₂).verifier.toFun shared s.stmt)
        pure ⟨tr, proverOut,
          ⟨stmtOutV,
            (Reduction.comp r₁ r₂).verifier.simulate shared
              (((Context₁ shared).append (Context₂ shared)).projectPublic tr)⟩⟩) :=
  rfl

/-- Mapping the prover-side output of a strategy before execution is equivalent
to executing first and then mapping the prover component of the result. -/
theorem Spec.runWithOracleCounterpart_mapOutputWithMonads
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → (accImpl : QueryImpl accSpec Id) →
    {OutputP OutputP' OutputC : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    (fP : ∀ tr, OutputP tr → OutputP' tr) →
    (strat : Interaction.Spec.StrategyOver focalMonadicSyntax PUnit.unit
      s.toInteractionSpec
      (RoleDecoration.withMonads
        (s.toSpecRoles roles) (s.toProverMonadDecoration oSpec))
      OutputP) →
    (cpt : Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      s.toInteractionSpec
      (RoleDecoration.withMonads (s.toSpecRoles roles)
        (s.toMonadDecoration oSpec OStmtIn roles od accSpec))
      OutputC) →
    Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl
      (Interaction.Spec.ShapeOver.mapOutput focalMonadicShape
        (agent := PUnit.unit)
        (spec := s.toInteractionSpec)
        (ctxs := RoleDecoration.withMonads (s.toSpecRoles roles)
          (s.toProverMonadDecoration oSpec))
        fP strat) cpt =
      (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
        Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl strat cpt
  | .done, _, _, _, _, _, _, _, _, _, output, cOutput => by
      unfold Interaction.Spec.ShapeOver.mapOutput
      simp [runWithOracleCounterpart, toInteractionSpec, toSpecRoles]
  | .«public» _X rest, ⟨.sender, rRest⟩, odRest, _, accSpec, accImpl,
      OutputP, OutputP', OutputC, fP, strat, cptFn => by
      unfold Interaction.Spec.ShapeOver.mapOutput
      simp only [toInteractionSpec, toSpecRoles,
        PFunctor.FreeM.mapLens_roll, executionLens,
        toProverMonadDecoration, Interaction.Spec.MonadDecoration.constant,
        RoleDecoration.withMonads, RoleDecoration.monadsOver,
        Interaction.Spec.Decoration.ofOver, runWithOracleCounterpart,
        focalMonadicShape, focalMonadicSyntax,
        bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
      refine congrArg (fun k => strat >>= k) ?_
      funext ⟨x, next⟩
      let addPrefix :
          ((tr : Interaction.Spec.Transcript (rest x).toInteractionSpec) ×
            OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
          ((tr : Interaction.Spec.Transcript
            (Oracle.Spec.public _X rest).toInteractionSpec) ×
            OutputP' tr × OutputC tr) :=
        fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
      simpa [bind_assoc, addPrefix, Functor.map_map, Function.comp_def] using
        congrArg (fun z => addPrefix <$> z)
          (runWithOracleCounterpart_mapOutputWithMonads inputImpl
            (rest x) (rRest x) (odRest x) accSpec accImpl
            (fun tr => fP ⟨x, tr⟩) next (cptFn x))
  | .«public» _X rest, ⟨.receiver, rRest⟩, odRest, _, accSpec, accImpl,
      OutputP, OutputP', OutputC, fP, strat, cpt => by
      unfold Interaction.Spec.ShapeOver.mapOutput
      simp only [toInteractionSpec, toSpecRoles, toMonadDecoration,
        PFunctor.FreeM.mapLens_roll, executionLens,
        toProverMonadDecoration, Interaction.Spec.MonadDecoration.constant,
        RoleDecoration.withMonads, RoleDecoration.monadsOver,
        Interaction.Spec.Decoration.ofOver,
        runWithOracleCounterpart,
        focalMonadicShape, focalMonadicSyntax,
        bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
      let routeImpl : QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (oSpec.query q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      refine congrArg (fun k => simulateQ routeImpl cpt >>= k) ?_
      funext ⟨x, cptRest⟩
      refine congrArg (fun k => strat x >>= k) ?_
      funext next
      let addPrefix :
          ((tr : Interaction.Spec.Transcript (rest x).toInteractionSpec) ×
            OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
          ((tr : Interaction.Spec.Transcript (Oracle.Spec.public _X rest).toInteractionSpec) ×
            OutputP' tr × OutputC tr) :=
        fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
      refine
        (congrArg (fun z => addPrefix <$> z)
          (runWithOracleCounterpart_mapOutputWithMonads inputImpl
            (rest x) (rRest x) (odRest x) accSpec accImpl
            (fun tr => fP ⟨x, tr⟩) next cptRest)).trans ?_
      exact
        Functor.map_map
          (fun z => ⟨z.1, (fP ⟨x, z.1⟩ z.2.1, z.2.2)⟩)
          addPrefix
          (Spec.runWithOracleCounterpart inputImpl
            (rest x) (rRest x) (odRest x) accSpec accImpl next cptRest)
  | .«oracle» _X cont, roles, ⟨oi, odRest⟩, _, accSpec, accImpl,
      OutputP, OutputP', OutputC, fP, strat, cptFn => by
      unfold Interaction.Spec.ShapeOver.mapOutput
      simp only [toInteractionSpec, toSpecRoles,
        PFunctor.FreeM.mapLens_roll, executionLens,
        toProverMonadDecoration, Interaction.Spec.MonadDecoration.constant,
        RoleDecoration.withMonads, RoleDecoration.monadsOver,
        Interaction.Spec.Decoration.ofOver, runWithOracleCounterpart,
        focalMonadicShape, focalMonadicSyntax,
        bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
      refine congrArg (fun k => strat >>= k) ?_
      funext ⟨x, next⟩
      let addPrefix :
          ((tr : Interaction.Spec.Transcript (cont ⟨⟩).toInteractionSpec) ×
            OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
          ((tr : Interaction.Spec.Transcript
            (Oracle.Spec.oracle _X cont).toInteractionSpec) ×
            OutputP' tr × OutputC tr) :=
        fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
      simpa [bind_assoc, addPrefix, Functor.map_map, Function.comp_def] using
        congrArg (fun z => addPrefix <$> z)
          (runWithOracleCounterpart_mapOutputWithMonads inputImpl
            (cont ⟨⟩) roles odRest
            (accSpec + @OracleInterface.spec _ oi)
            (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run x))
          (fun tr => fP ⟨x, tr⟩) next (cptFn x))

/-- Mapping the prover-side output of an arbitrary prover strategy before
running a verifier is equivalent to running first and then mapping the prover
component of the result. -/
theorem Verifier.run_mapOutput
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    {OutputP OutputP' :
      Interaction.Spec.Transcript (Context shared).toInteractionSpec → Type}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (prover : Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
      Interaction.TwoParty.Participant.focal
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared)) OutputP) :
    verifier.run shared stmt inputImpl
      (Interaction.TwoParty.Focal.mapOutput fP prover) =
      (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
        verifier.run shared stmt inputImpl prover := by
  simp only [Verifier.run]
  rw [Interaction.TwoParty.Focal.toConstantMonads_mapOutput]
  have hrun :
      Spec.runWithOracleCounterpart inputImpl
        (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
        (Interaction.Spec.ShapeOver.mapOutput focalMonadicShape
          (agent := PUnit.unit)
          (spec := (Context shared).toInteractionSpec)
          (ctxs := RoleDecoration.withMonads
            ((Context shared).toSpecRoles (Roles shared))
            (Interaction.Spec.MonadDecoration.constant
              ⟨OracleComp oSpec, inferInstance⟩
              (Context shared).toInteractionSpec))
          fP
          (Interaction.TwoParty.Focal.toConstantMonads
            (Context shared).toInteractionSpec
            ((Context shared).toSpecRoles (Roles shared))
            prover))
        (verifier.toFun shared stmt) =
        (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
          Spec.runWithOracleCounterpart inputImpl
            (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
            (Interaction.TwoParty.Focal.toConstantMonads
              (Context shared).toInteractionSpec
              ((Context shared).toSpecRoles (Roles shared))
              prover)
            (verifier.toFun shared stmt) := by
    simpa [Spec.toProverMonadDecoration] using
      (Spec.runWithOracleCounterpart_mapOutputWithMonads inputImpl
        (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
        fP
        (Interaction.TwoParty.Focal.toConstantMonads
          (Context shared).toInteractionSpec
          ((Context shared).toSpecRoles (Roles shared))
          prover)
        (verifier.toFun shared stmt))
  rw [hrun]
  simp [Functor.map_map]

end Oracle

end Interaction


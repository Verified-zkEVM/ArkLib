/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core
import ArkLib.Interaction.Oracle.ProgramSpec

open Interaction.TwoParty

/-!
# Oracle verifier programs

Execution for the verifier-local `Oracle.Verifier.Program` layer.
-/

open OracleComp OracleSpec

namespace Interaction
namespace Oracle

/-- Terminal verifier output for an oracle reduction.

A verifier does not merely return a local statement: it returns the next oracle
problem. The `stmt` field is the public statement, while `simulate` explains
how queries to the output oracle problem are answered using the input oracle
statement and the oracle messages exposed by the public transcript. -/
structure Verifier.TerminalOutput
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (shared : SharedIn)
    (pt : Spec.PublicTranscript (Context shared)) where
  /-- The local verifier output statement. -/
  stmt : StatementOut shared pt
  /-- The output oracle implementation induced by this verifier leaf. -/
  simulate : QueryImpl [OStatementOut shared pt]ₒ
    (OracleComp
      ([OStatementIn shared]ₒ + (Context shared).toOracleSpec (OracleDeco shared) pt))

namespace Verifier

/-- Thin verifier-local program layer over `Oracle.Spec`.

This is the semantic verifier surface needed for composition with monadic
terminal leaves. Unlike raw `StrategyOver`, a `Program` has explicit
verifier-local binds at every point in the protocol tree, including terminal
positions where no protocol node remains. The public receiver constructor is
split into a monadic message choice and a pure continuation builder, so no
recursive `Program` value is stored inside the verifier monad. -/
inductive Program {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    (access : Verifier.AccessFamily oSpec OStmtIn) :
    (s : Spec) → Spec.RoleDeco s → Spec.OracleDeco s →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ →
    (Spec.PublicTranscript s → Type) → Type 1 where
  /-- Terminal verifier-local computation. -/
  | done {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}
      {Out : Spec.PublicTranscript Spec.done → Type}
      (out : access.M accSpec (Out ⟨⟩)) :
      Program OStmtIn access .done ⟨⟩ ⟨⟩ accSpec Out
  /-- Verifier-local bind that does not correspond to a protocol node. -/
  | bind {s : Spec} {roles : Spec.RoleDeco s} {od : Spec.OracleDeco s}
      {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}
      {Out : Spec.PublicTranscript s → Type} {α : Type}
      (act : access.M accSpec α)
      (next : α → Program OStmtIn access s roles od accSpec Out) :
      Program OStmtIn access s roles od accSpec Out
  /-- Public message owned by the prover. -/
  | publicSender {X : Type} {rest : X → Spec}
      {rRest : (x : X) → Spec.RoleDeco (rest x)}
      {odRest : (x : X) → Spec.OracleDeco (rest x)}
      {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}
      {Out : Spec.PublicTranscript (Spec.«public» X rest) → Type}
      (next : (x : X) →
        Program OStmtIn access (rest x) (rRest x) (odRest x) accSpec
          (fun pt => Out ⟨x, pt⟩)) :
      Program OStmtIn access (Spec.«public» X rest)
        ⟨Interaction.TwoParty.Role.sender, rRest⟩ odRest accSpec Out
  /-- Public message owned by the verifier. The monadic action samples only the
  public message; the branch continuation is pure in that message. -/
  | publicReceiver {X : Type} {rest : X → Spec}
      {rRest : (x : X) → Spec.RoleDeco (rest x)}
      {odRest : (x : X) → Spec.OracleDeco (rest x)}
      {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}
      {Out : Spec.PublicTranscript (Spec.«public» X rest) → Type}
      {NextState : X → Type}
      (sample : access.M accSpec ((x : X) × NextState x))
      (next : (x : X) → NextState x →
        Program OStmtIn access (rest x) (rRest x) (odRest x) accSpec
          (fun pt => Out ⟨x, pt⟩)) :
      Program OStmtIn access (Spec.«public» X rest)
        ⟨Interaction.TwoParty.Role.receiver, rRest⟩ odRest accSpec Out
  /-- Prover oracle message. The verifier cannot branch on the message value;
  it only extends the accumulated oracle-message access for the continuation. -/
  | oracle {X : Type} {cont : PUnit.{1} → Spec}
      {roles : Spec.RoleDeco (cont ⟨⟩)}
      {oi : OracleInterface X}
      {odRest : Spec.OracleDeco (cont ⟨⟩)}
      {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}
      {Out : Spec.PublicTranscript (Spec.«oracle» X cont) → Type}
      (next :
        Program OStmtIn access (cont ⟨⟩) roles odRest
          (accSpec + @OracleInterface.spec X oi)
          (fun pt => Out ⟨⟨⟩, pt⟩)) :
      Program OStmtIn access (Spec.«oracle» X cont) roles ⟨oi, odRest⟩ accSpec Out

/-- Oracle verifier represented by a verifier-local `Program`.

This is the composition-ready verifier surface: the protocol shape, roles, and
oracle decoration still come entirely from `Oracle.Spec`, while verifier-local
monadic work is represented by `Verifier.Program` rather than by forcing all
effects into raw `StrategyOver` leaves. -/
structure WithProgram {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (VerifierAccess :
      (shared : SharedIn) → Verifier.AccessFamily oSpec (OStatementIn shared))
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] where
  toProgram : (shared : SharedIn) →
    StatementIn shared →
      Verifier.Program (OStatementIn shared) (VerifierAccess shared)
        (Context shared) (Roles shared) (OracleDeco shared) []ₒ
        (fun pt =>
          TerminalOutput SharedIn Context OracleDeco OStatementIn
            StatementOut OStatementOut shared pt)

end Verifier

/-- Standard programmatic oracle verifier using the current ambient executable
access family. -/
abbrev Verifier.Programmatic {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] :=
  Verifier.WithProgram oSpec SharedIn Context Roles OracleDeco
    StatementIn OStatementIn
    (fun shared => Verifier.AccessFamily.ambient (oSpec := oSpec)
      (OStmtIn := OStatementIn shared))
    StatementOut OStatementOut

/-- Oracle reduction whose verifier is represented by a verifier-local
`Program`.

This is the composition-oriented reduction package: the prover stays an ordinary
oracle prover strategy, while the verifier keeps local binds and terminal
computation in `Verifier.Program` rather than splitting terminal output from a
global simulator field. -/
structure Reduction.WithProgram {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (Setup : Type → Type)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (ProverMd :
      (shared : SharedIn) → Interaction.Spec.MonadDecoration (Context shared).toInteractionSpec)
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (VerifierAccess :
      (shared : SharedIn) → Verifier.AccessFamily oSpec (OStatementIn shared))
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) where
  prover : Prover.WithMonads Setup SharedIn Context Roles ProverMd
    StatementIn WitnessIn OStatementIn StatementOut OStatementOut WitnessOut
  verifier : Verifier.WithProgram oSpec SharedIn Context Roles OracleDeco
    StatementIn OStatementIn VerifierAccess StatementOut OStatementOut

/-- Standard executable programmatic oracle reduction. -/
abbrev Reduction.Programmatic {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared))
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type) :=
  Reduction.WithProgram oSpec (OracleComp oSpec) SharedIn Context Roles OracleDeco
    (fun shared => (Context shared).toProverMonadDecoration oSpec)
    StatementIn OStatementIn WitnessIn
    (fun shared => Verifier.AccessFamily.ambient (oSpec := oSpec)
      (OStmtIn := OStatementIn shared))
    StatementOut OStatementOut WitnessOut

namespace Verifier.Program

/-- Map the terminal output family of a verifier-local program. -/
def mapOutput
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {access : Verifier.AccessFamily oSpec OStmtIn} :
    {s : Spec} → {roles : Spec.RoleDeco s} → {od : Spec.OracleDeco s} →
    {ιₐ : Type} → {accSpec : OracleSpec.{0, 0} ιₐ} →
    {Out Out' : Spec.PublicTranscript s → Type} →
    Verifier.Program OStmtIn access s roles od accSpec Out →
    (∀ pt, Out pt → Out' pt) →
      Verifier.Program OStmtIn access s roles od accSpec Out'
  | .done, _, _, _, accSpec, _, _, .done out, f =>
      .bind out fun out =>
        .done (by
          letI := access.instMonad accSpec
          exact pure (f ⟨⟩ out))
  | s, roles, od, _, _, _, _, .bind act next, f =>
      .bind act fun a => mapOutput (next a) f
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, _, _, _,
      .publicSender next, f =>
      .publicSender fun x =>
        mapOutput (next x) fun pt out => f ⟨x, pt⟩ out
  | .«public» _ rest, ⟨.receiver, rRest⟩, odRest, _, _, _, _,
      .publicReceiver sample next, f =>
      .publicReceiver sample fun x state =>
        mapOutput (next x state) fun pt out => f ⟨x, pt⟩ out
  | .«oracle» _ cont, roles, ⟨oi, odRest⟩, _, _, _, _,
      .oracle next, f =>
      .oracle <| mapOutput next fun pt out => f ⟨⟨⟩, pt⟩ out

/-- Rewrite the oracle effects used by an ambient verifier-local program.

This is the `Verifier.Program` analogue of `Counterpart.mapOracles`: every
verifier-local action is routed through `simulateQ`, while the protocol tree is
traversed structurally. At prover-oracle nodes both source and target
accumulators grow by the newly received oracle interface, and those fresh
queries are routed identically. -/
def mapAmbientOracles
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
    {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [∀ i, OracleInterface (OStmt₂ i)] :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ₁ : Type} → (accSpec₁ : OracleSpec.{0, 0} ιₐ₁) →
    {ιₐ₂ : Type} → (accSpec₂ : OracleSpec.{0, 0} ιₐ₂) →
    QueryImpl (Verifier.AmbientAccessSpec oSpec OStmt₁ accSpec₁)
      (OracleComp (Verifier.AmbientAccessSpec oSpec OStmt₂ accSpec₂)) →
    {Out : Spec.PublicTranscript s → Type} →
    Verifier.Program OStmt₁
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStmt₁))
      s roles od accSpec₁ Out →
    Verifier.Program OStmt₂
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStmt₂))
      s roles od accSpec₂ Out
  | .done, _, _, _, _, _, _, route, _, .done out =>
      .done (simulateQ route out)
  | s, roles, od, _, accSpec₁, _, accSpec₂, route, _, .bind act next =>
      .bind (simulateQ route act) fun a =>
        mapAmbientOracles s roles od accSpec₁ accSpec₂ route (next a)
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec₁, _, accSpec₂, route, _,
      .publicSender next =>
      .publicSender fun x =>
        mapAmbientOracles (rest x) (rRest x) (odRest x) accSpec₁ accSpec₂ route
          (next x)
  | .«public» _ rest, ⟨.receiver, rRest⟩, odRest, _, accSpec₁, _, accSpec₂, route, _,
      .publicReceiver sample next =>
      .publicReceiver (simulateQ route sample) fun x state =>
        mapAmbientOracles (rest x) (rRest x) (odRest x) accSpec₁ accSpec₂ route
          (next x state)
  | .«oracle» X cont, roles, ⟨oi, odRest⟩, _, accSpec₁, _, accSpec₂, route, _,
      .oracle next =>
      let oiSpec := @OracleInterface.spec X oi
      let targetSpec := Verifier.AmbientAccessSpec oSpec OStmt₂ (accSpec₂ + oiSpec)
      let routeNext :
          QueryImpl (Verifier.AmbientAccessSpec oSpec OStmt₁ (accSpec₁ + oiSpec))
            (OracleComp targetSpec) := fun
        | .inl q => (route (.inl q)).liftComp _
        | .inr (.inl q) => (route (.inr q)).liftComp _
        | .inr (.inr q) => liftM (targetSpec.query (.inr (.inr q)))
      .oracle <|
        mapAmbientOracles (cont ⟨⟩) roles odRest (accSpec₁ + oiSpec)
          (accSpec₂ + oiSpec) routeNext next

/-- Retarget a suffix verifier program from a middle oracle statement interface
to the original input oracle statement interface, using a monadic route for
prefix transcript-oracle queries.

The middle interface is interpreted by the prefix verifier's packaged
`TerminalOutput`. Ambient oracle queries and accumulated transcript-oracle
queries pass through unchanged; middle oracle reads are simulated by
`midOut.simulate`, with prefix transcript-oracle reads routed into the target
ambient access spec. This is the programmatic composition form: no concrete
oracle-message transcript is available while building the verifier program. -/
def retargetAmbientWithRoute
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
    (midOut : Verifier.TerminalOutput SharedIn Context₁ OracleDeco₁ OStatementIn
      StatementMid OStatementMid shared pt₁)
    (s₂ : Spec) (roles₂ : Spec.RoleDeco s₂) (od₂ : Spec.OracleDeco s₂)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    (prefixRoute : QueryImpl
      ((Context₁ shared).toOracleSpec (OracleDeco₁ shared) pt₁)
      (OracleComp (Verifier.AmbientAccessSpec oSpec (OStatementIn shared) accSpec)))
    {Out : Spec.PublicTranscript s₂ → Type}
    (program : Verifier.Program (OStatementMid shared pt₁)
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStatementMid shared pt₁))
      s₂ roles₂ od₂ accSpec Out) :
    Verifier.Program (OStatementIn shared)
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStatementIn shared))
      s₂ roles₂ od₂ accSpec Out :=
  let targetSpec := Verifier.AmbientAccessSpec oSpec (OStatementIn shared) accSpec
  let liftRoute : QueryImpl
      ([OStatementIn shared]ₒ + (Context₁ shared).toOracleSpec (OracleDeco₁ shared) pt₁)
      (OracleComp targetSpec) := fun
    | .inl q => liftM (targetSpec.query (.inl (.inr q)))
    | .inr q => prefixRoute q
  let route : QueryImpl
      (Verifier.AmbientAccessSpec oSpec (OStatementMid shared pt₁) accSpec)
      (OracleComp targetSpec) := fun
    | .inl (.inl q) => liftM (targetSpec.query (.inl (.inl q)))
    | .inl (.inr q) => simulateQ liftRoute (midOut.simulate q)
    | .inr q => liftM (targetSpec.query (.inr q))
  mapAmbientOracles s₂ roles₂ od₂ accSpec accSpec route program

/-- Retarget a suffix verifier program using concrete answers for prefix
transcript-oracle queries.

This is the legacy/full-transcript specialization of
`retargetAmbientWithRoute`. Programmatic composition should use the route-based
form so hidden oracle messages remain represented by accumulated read
capability. -/
def retargetAmbient
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
    (midOut : Verifier.TerminalOutput SharedIn Context₁ OracleDeco₁ OStatementIn
      StatementMid OStatementMid shared pt₁)
    (answerQ : QueryImpl ((Context₁ shared).toOracleSpec (OracleDeco₁ shared) pt₁) Id)
    (s₂ : Spec) (roles₂ : Spec.RoleDeco s₂) (od₂ : Spec.OracleDeco s₂)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {Out : Spec.PublicTranscript s₂ → Type}
    (program : Verifier.Program (OStatementMid shared pt₁)
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStatementMid shared pt₁))
      s₂ roles₂ od₂ accSpec Out) :
    Verifier.Program (OStatementIn shared)
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStatementIn shared))
      s₂ roles₂ od₂ accSpec Out :=
  retargetAmbientWithRoute midOut s₂ roles₂ od₂ accSpec
    (fun q => pure (answerQ q)) program

/-- Lift the accumulated transcript-oracle access used by an ambient verifier
program.

The ambient oracle access and input-oracle-statement access are preserved
directly. Only the accumulated prover-oracle-message summand is rerouted. -/
def liftAmbientAcc
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (s : Spec) (roles : Spec.RoleDeco s) (od : Spec.OracleDeco s)
    {ιₐ₁ : Type} (accSpec₁ : OracleSpec.{0, 0} ιₐ₁)
    {ιₐ₂ : Type} (accSpec₂ : OracleSpec.{0, 0} ιₐ₂)
    (accRoute : QueryImpl accSpec₁
      (OracleComp (Verifier.AmbientAccessSpec oSpec OStmtIn accSpec₂)))
    {Out : Spec.PublicTranscript s → Type}
    (program : Verifier.Program OStmtIn
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStmtIn))
      s roles od accSpec₁ Out) :
    Verifier.Program OStmtIn
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStmtIn))
      s roles od accSpec₂ Out :=
  let targetSpec := Verifier.AmbientAccessSpec oSpec OStmtIn accSpec₂
  let route : QueryImpl (Verifier.AmbientAccessSpec oSpec OStmtIn accSpec₁)
      (OracleComp targetSpec) := fun
    | .inl (.inl q) => liftM (targetSpec.query (.inl (.inl q)))
    | .inl (.inr q) => liftM (targetSpec.query (.inl (.inr q)))
    | .inr q => accRoute q
  mapAmbientOracles s roles od accSpec₁ accSpec₂ route program

/-- Compose ambient verifier programs along `Oracle.Spec.append`.

The continuation is invoked only after the prefix program reaches a terminal
leaf, and it receives the public transcript-indexed accumulator implied by the
prefix control path. No concrete prover-oracle messages are needed to build
the suffix program. -/
def compAuxAmbient
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)] :
    (s₁ : Spec) → (s₂ : Spec.PublicTranscript s₁ → Spec) →
    (roles₁ : Spec.RoleDeco s₁) →
    (roles₂ : (pt₁ : Spec.PublicTranscript s₁) → Spec.RoleDeco (s₂ pt₁)) →
    (od₁ : Spec.OracleDeco s₁) →
    (od₂ : (pt₁ : Spec.PublicTranscript s₁) → Spec.OracleDeco (s₂ pt₁)) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) →
    {Mid : Spec.PublicTranscript s₁ → Type} →
    {Out : (pt₁ : Spec.PublicTranscript s₁) →
      Spec.PublicTranscript (s₂ pt₁) → Type} →
    Verifier.Program OStmtIn
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStmtIn))
      s₁ roles₁ od₁ accSpec Mid →
    ((pt₁ : Spec.PublicTranscript s₁) → Mid pt₁ →
      Verifier.Program OStmtIn
        (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStmtIn))
        (s₂ pt₁) (roles₂ pt₁) (od₂ pt₁)
        (Spec.accumulatedPublicSpec s₁ od₁ pt₁ accSpec).2
        (fun pt₂ => Out pt₁ pt₂)) →
    Verifier.Program OStmtIn
      (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStmtIn))
      (s₁.append s₂) (Spec.RoleDeco.append s₁ s₂ roles₁ roles₂)
      (Spec.OracleDeco.append s₁ s₂ od₁ od₂) accSpec
      (fun pt => Spec.PublicTranscript.liftAppend s₁ s₂ Out pt)
  | Spec.done, _, _, _, _, _, _, _, _, _, Verifier.Program.done mid, cont =>
      .bind mid fun mid => cont ⟨⟩ mid
  | s₁, s₂, roles₁, roles₂, od₁, od₂, _, accSpec, _, Out,
      Verifier.Program.bind act next, cont =>
      .bind act fun a =>
        compAuxAmbient s₁ s₂ roles₁ roles₂ od₁ od₂ accSpec
          (Out := Out) (next a) cont
  | .«public» _ rest, s₂, ⟨.sender, rRest⟩, roles₂, odRest, od₂, _, accSpec, _, Out,
      Verifier.Program.publicSender next, cont =>
      .publicSender fun x =>
        compAuxAmbient (rest x) (fun pt => s₂ ⟨x, pt⟩) (rRest x)
          (fun pt => roles₂ ⟨x, pt⟩) (odRest x) (fun pt => od₂ ⟨x, pt⟩)
          accSpec (Out := fun pt₁ pt₂ => Out ⟨x, pt₁⟩ pt₂) (next x)
          (fun pt₁ mid => cont ⟨x, pt₁⟩ mid)
  | .«public» _ rest, s₂, ⟨.receiver, rRest⟩, roles₂, odRest, od₂, _, accSpec, _,
      Out, Verifier.Program.publicReceiver sample next, cont =>
      .publicReceiver sample fun x state =>
        compAuxAmbient (rest x) (fun pt => s₂ ⟨x, pt⟩) (rRest x)
          (fun pt => roles₂ ⟨x, pt⟩) (odRest x) (fun pt => od₂ ⟨x, pt⟩)
          accSpec (Out := fun pt₁ pt₂ => Out ⟨x, pt₁⟩ pt₂) (next x state)
          (fun pt₁ mid => cont ⟨x, pt₁⟩ mid)
  | .«oracle» X cont₁, s₂, roles₁, roles₂, ⟨oi, odRest⟩, od₂, _, accSpec, _, Out,
      Verifier.Program.oracle next, cont =>
      .oracle <|
        compAuxAmbient (cont₁ ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) roles₁
          (fun pt => roles₂ ⟨⟨⟩, pt⟩) odRest (fun pt => od₂ ⟨⟨⟩, pt⟩)
          (accSpec + @OracleInterface.spec X oi)
          (Out := fun pt₁ pt₂ => Out ⟨⟨⟩, pt₁⟩ pt₂) next
          (fun pt₁ mid => cont ⟨⟨⟩, pt₁⟩ mid)

/-- Run a verifier-local oracle program directly against a prover strategy.

This runner is the semantic reason for the `Verifier.Program` layer: verifier
local binds are interpreted by `access.runM`, while protocol nodes are consumed
from the prover strategy. No verifier-local bind is lowered into a fake
protocol node. -/
def run
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (access : Verifier.AccessFamily oSpec OStmtIn)
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → (accImpl : QueryImpl accSpec Id) →
    {OutputP : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    {OutputV : Spec.PublicTranscript s → Type} →
    Verifier.Program OStmtIn access s roles od accSpec OutputV →
    Interaction.Spec.StrategyOver focalMonadicSyntax PUnit.unit
      s.toInteractionSpec
      (RoleDecoration.withMonads
        (s.toSpecRoles roles) (s.toProverMonadDecoration oSpec))
      OutputP →
    OracleComp oSpec ((tr : Interaction.Spec.Transcript s.toInteractionSpec) ×
      OutputP tr × OutputV (s.projectPublic tr))
  | .done, _, _, _, accSpec, accImpl, _, _, .done outM, proverOut => do
      let readImpl : QueryImpl (Verifier.ReadSpec OStmtIn accSpec) (OracleComp oSpec) :=
        Verifier.AccessFamily.readImpl
          (fun q => liftM (inputImpl q))
          (fun q => liftM (accImpl q))
      let out ← access.runM readImpl outM
      pure ⟨⟨⟩, proverOut, out⟩
  | s, roles, od, _, accSpec, accImpl, _, _, .bind act next, prover => do
      let readImpl : QueryImpl (Verifier.ReadSpec OStmtIn accSpec) (OracleComp oSpec) :=
        Verifier.AccessFamily.readImpl
          (fun q => liftM (inputImpl q))
          (fun q => liftM (accImpl q))
      let a ← access.runM readImpl act
      run access inputImpl s roles od accSpec accImpl (next a) prover
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec, accImpl, _, _,
      .publicSender nextProgram, prover => do
      let ⟨x, proverRest⟩ ← prover
      let z ← run access inputImpl (rest x) (rRest x) (odRest x) accSpec accImpl
        (nextProgram x) proverRest
      pure ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«public» _ rest, ⟨.receiver, rRest⟩, odRest, _, accSpec, accImpl, _, _,
      .publicReceiver sample nextProgram, prover => do
      let readImpl : QueryImpl (Verifier.ReadSpec OStmtIn accSpec) (OracleComp oSpec) :=
        Verifier.AccessFamily.readImpl
          (fun q => liftM (inputImpl q))
          (fun q => liftM (accImpl q))
      let sampled ← access.runM readImpl sample
      let x := sampled.1
      let proverRest ← prover x
      let z ← run access inputImpl (rest x) (rRest x) (odRest x) accSpec accImpl
        (nextProgram x sampled.2) proverRest
      pure ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«oracle» _ cont, roles, ⟨oi, odRest⟩, _, accSpec, accImpl, _, _,
      .oracle nextProgram, prover => do
      let ⟨x, proverRest⟩ ← prover
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id :=
        fun q => (oi.toOC.impl q).run x
      let z ← run access inputImpl (cont ⟨⟩) roles odRest
        (accSpec + @OracleInterface.spec _ oi) (QueryImpl.add accImpl implX)
        nextProgram proverRest
      pure ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩

end Verifier.Program

/-- Run an arbitrary prover strategy against a verifier-local program. -/
def Verifier.WithProgram.run
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {VerifierAccess :
      (shared : SharedIn) → Oracle.Verifier.AccessFamily oSpec (OStatementIn shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier.WithProgram oSpec SharedIn Context Roles
      OracleDeco StatementIn OStatementIn VerifierAccess StatementOut OStatementOut)
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
       Oracle.Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
        StatementOut OStatementOut shared ((Context shared).projectPublic tr)) :=
  let prover' :=
    Interaction.TwoParty.Focal.toConstantMonads
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared))
      prover
  Verifier.Program.run (VerifierAccess shared) inputImpl
    (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
    (verifier.toProgram shared stmt) prover'

/-- Run a programmatic reduction verifier against an arbitrary prover strategy
and concrete input oracle statement. -/
def Reduction.WithProgram.runConcrete
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {Setup : Type → Type}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {ProverMd :
      (shared : SharedIn) → Interaction.Spec.MonadDecoration (Context shared).toInteractionSpec}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {VerifierAccess :
      (shared : SharedIn) → Verifier.AccessFamily oSpec (OStatementIn shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction.WithProgram oSpec Setup SharedIn Context Roles
      OracleDeco ProverMd StatementIn OStatementIn WitnessIn VerifierAccess
      StatementOut OStatementOut WitnessOut)
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
       Oracle.Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
        StatementOut OStatementOut shared ((Context shared).projectPublic tr)) :=
  reduction.verifier.run shared s.stmt
    (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
    prover

/-- Honest execution of a standard programmatic oracle reduction. -/
def Reduction.Programmatic.executeConcrete
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
    (reduction : Oracle.Reduction.Programmatic oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
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
       Oracle.Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
        StatementOut OStatementOut shared ((Context shared).projectPublic tr)) := do
  let strategy ← reduction.prover shared s w
  Verifier.Program.run
    (Verifier.AccessFamily.ambient (oSpec := oSpec) (OStmtIn := OStatementIn shared))
    (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
    (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
    (reduction.verifier.toProgram shared s.stmt) strategy

end Oracle
end Interaction

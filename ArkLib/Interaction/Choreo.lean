/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction
import ArkLib.Interaction.Oracle.Protocol
import ArkLib.Interaction.Oracle.Chain

/-!
# Two-Party Choreography Prototype

This file contains a small typed EDSL for writing a two-party protocol once and
projecting it to the existing focal/counterpart `StrategyOver` fibers.

The plain two-party surface targets finite protocols such as Schnorr. The oracle
reduction surface extends the same authoring style to
`Interaction.Oracle.Spec.Protocol`.
-/

open Interaction.TwoParty

namespace Interaction
namespace Choreo

universe u

namespace Scoped

/-- A two-party choreography whose continuations are allowed to depend on the
message just sent.

The message is in scope because the continuation is indexed by it, while private
role-local data is still carried by the corresponding endpoint state. -/
structure Program (m : Type u → Type u)
    (PState VState POut VOut : Type u) where
  /-- The underlying interaction tree. -/
  spec : Spec
  /-- Sender/receiver decoration from the prover/focal perspective. -/
  roles : RoleDecoration spec
  /-- Generate the prover endpoint from prover-local state. -/
  prover :
    PState →
      m (Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
        spec roles (fun _ => POut))
  /-- Generate the verifier endpoint from verifier-local state. -/
  verifier :
    VState →
      Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.counterpart
        spec roles (fun _ => VOut)

variable {m : Type u → Type u}

/-- Terminal scoped choreography. -/
def done [Monad m] {PState VState POut VOut : Type u}
    (pout : PState → POut) (vout : VState → VOut) :
    Program m PState VState POut VOut where
  spec := .done
  roles := ⟨⟩
  prover := fun pstate => pure (pout pstate)
  verifier := fun vstate => vout vstate

/-- A prover-to-verifier message whose continuation may depend on the sent
message. The verifier receives the message through the continuation, so it does
not need to store it manually in its local state. -/
def proverSend [Monad m]
    {PState VState POut VOut : Type u}
    (X : Type u) {PState' : X → Type u}
    (send : PState → m ((x : X) × PState' x))
    (rest : (x : X) → Program m (PState' x) VState POut VOut) :
    Program m PState VState POut VOut where
  spec := .node X fun x => (rest x).spec
  roles := ⟨.sender, fun x => (rest x).roles⟩
  prover := fun pstate => pure <| do
    let msgAndState ← send pstate
    let msg := msgAndState.1
    let nextPState := msgAndState.2
    let restProver ← (rest msg).prover nextPState
    pure ⟨msg, restProver⟩
  verifier := fun vstate msg => pure ((rest msg).verifier vstate)

/-- A prover-to-verifier message with a non-dependent next prover state.

This is the surface DSL's common case. It lets message actions return an ordinary
product, while `proverSend` remains available for genuinely message-indexed
private state. -/
def proverSendConst [Monad m]
    {PState VState PState' POut VOut : Type u}
    (X : Type u)
    (send : PState → m (X × PState'))
    (rest : X → Program m PState' VState POut VOut) :
    Program m PState VState POut VOut where
  spec := .node X fun x => (rest x).spec
  roles := ⟨.sender, fun x => (rest x).roles⟩
  prover := fun pstate => pure <| do
    let msgAndState ← send pstate
    let msg := msgAndState.1
    let nextPState := msgAndState.2
    let restProver ← (rest msg).prover nextPState
    pure ⟨msg, restProver⟩
  verifier := fun vstate msg => pure ((rest msg).verifier vstate)

/-- A verifier-to-prover message whose continuation may depend on the sent
message. The prover receives the message through the continuation, so it does
not need to store it manually in its local state. -/
def verifierSend [Monad m]
    {PState VState POut VOut : Type u}
    (X : Type u) {VState' : X → Type u}
    (send : VState → m ((x : X) × VState' x))
    (rest : (x : X) → Program m PState (VState' x) POut VOut) :
    Program m PState VState POut VOut where
  spec := .node X fun x => (rest x).spec
  roles := ⟨.receiver, fun x => (rest x).roles⟩
  prover := fun pstate => pure fun msg => (rest msg).prover pstate
  verifier := fun vstate => do
    let msgAndState ← send vstate
    let msg := msgAndState.1
    let nextVState := msgAndState.2
    pure ⟨msg, (rest msg).verifier nextVState⟩

/-- A verifier-to-prover message with a non-dependent next verifier state.

This is the surface DSL's common case. It lets message actions return an ordinary
product, while `verifierSend` remains available for genuinely message-indexed
private state. -/
def verifierSendConst [Monad m]
    {PState VState VState' POut VOut : Type u}
    (X : Type u)
    (send : VState → m (X × VState'))
    (rest : X → Program m PState VState' POut VOut) :
    Program m PState VState POut VOut where
  spec := .node X fun x => (rest x).spec
  roles := ⟨.receiver, fun x => (rest x).roles⟩
  prover := fun pstate => pure fun msg => (rest msg).prover pstate
  verifier := fun vstate => do
    let msgAndState ← send vstate
    let msg := msgAndState.1
    let nextVState := msgAndState.2
    pure ⟨msg, (rest msg).verifier nextVState⟩

end Scoped

namespace OracleScoped

/-! ## Executable oracle choreography programs

This layer is the oracle analogue of `Scoped.Program`: it builds one decorated
`Interaction.Oracle.Spec.Protocol` together with the two projected endpoints.
The program is parameterized by the verifier's current accumulated oracle spec,
so `proverOracle` can extend that accumulator for the continuation without
assuming a particular protocol shape.
-/

/-- A stateful executable oracle choreography over one decorated oracle
protocol. -/
structure Program
    {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    (PState VState POut VOut : Type) where
  /-- The decorated oracle protocol generated by the choreography. -/
  protocol : Interaction.Oracle.Spec.Protocol
  /-- Generate the prover endpoint from prover-local state. -/
  prover :
    PState →
      OracleComp oSpec
        (Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
          Interaction.TwoParty.Participant.focal
          protocol.spec.toInteractionSpec
          (protocol.spec.toSpecRoles protocol.roles)
          (fun _ => POut))
  /-- Generate the verifier endpoint from verifier-local state. -/
  verifier :
    VState →
      Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
        protocol.spec.toInteractionSpec
        (RoleDecoration.withMonads
          (protocol.spec.toSpecRoles protocol.roles)
          (protocol.spec.toMonadDecoration oSpec OStmtIn
            protocol.roles protocol.oracleDeco accSpec))
        (fun _ => VOut)

variable {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
variable [∀ i, OracleInterface (OStmtIn i)]
variable {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}

/-- Terminal executable oracle choreography. -/
def done {PState VState POut VOut : Type}
    (pout : PState → POut) (vout : VState → VOut) :
    Program oSpec OStmtIn accSpec PState VState POut VOut where
  protocol := Interaction.Oracle.Spec.Protocol.done
  prover := fun pstate => pure (pout pstate)
  verifier := fun vstate => vout vstate

/-- A public prover-to-verifier message in an executable oracle choreography.

The message is public, so the continuation may depend on its value. -/
def proverSend
    {PState VState PState' POut VOut : Type}
    (X : Type)
    (send : PState → OracleComp oSpec (X × PState'))
    (rest : X → Program oSpec OStmtIn accSpec PState' VState POut VOut) :
    Program oSpec OStmtIn accSpec PState VState POut VOut where
  protocol := Interaction.Oracle.Spec.Protocol.public .sender X fun x =>
    (rest x).protocol
  prover := fun pstate => pure <| do
    let msgAndState ← send pstate
    let msg := msgAndState.1
    let nextPState := msgAndState.2
    let restProver ← (rest msg).prover nextPState
    pure ⟨msg, restProver⟩
  verifier := fun vstate msg => (rest msg).verifier vstate

/-- A public verifier-to-prover message in an executable oracle choreography.

The verifier action runs in the standard oracle-verifier access monad for the
current accumulated oracle spec. -/
def verifierSend
    {PState VState VState' POut VOut : Type}
    (X : Type)
    (send : VState → OracleComp (oSpec + [OStmtIn]ₒ + accSpec) (X × VState'))
    (rest : X → Program oSpec OStmtIn accSpec PState VState' POut VOut) :
    Program oSpec OStmtIn accSpec PState VState POut VOut where
  protocol := Interaction.Oracle.Spec.Protocol.public .receiver X fun x =>
    (rest x).protocol
  prover := fun pstate => pure fun msg => (rest msg).prover pstate
  verifier := fun vstate => do
    let msgAndState ← send vstate
    pure ⟨msgAndState.1, (rest msgAndState.1).verifier msgAndState.2⟩

/-- A final public verifier-to-prover message followed by terminal endpoint
computations.

The verifier terminal computation is monadic and is lowered into the sender
action for this final public node. This is exactly the case needed for a
one-round oracle reduction such as sum-check: the verifier samples a public
challenge, then performs terminal checks and oracle queries with that challenge
in scope.

TODO: generalize this lowering to a real administrative/local-node compiler for
arbitrary terminal verifier computations, rather than only final public nodes.

TODO(monadic verifier leaves): replace this helper once
`Oracle.Verifier.WithMonads.toFun`, execution, composition, and chain
projection allow terminal verifier leaves of type
`OracleComp (oSpec + [OStmtIn]ₒ + accumulatedSpec) VOut`. Then
`oracle_reduction_end verifier ... => do ...` should compile directly to the
leaf, instead of being pushed into the preceding `verifier_send`. -/
def verifierSendFinish
    {PState VState VState' POut VOut : Type}
    (X : Type)
    (send : VState → OracleComp (oSpec + [OStmtIn]ₒ + accSpec) (X × VState'))
    (pout : X → PState → POut)
    (vout : X → VState' → OracleComp (oSpec + [OStmtIn]ₒ + accSpec) VOut) :
    Program oSpec OStmtIn accSpec PState VState POut VOut where
  protocol := Interaction.Oracle.Spec.Protocol.public .receiver X fun _ =>
    Interaction.Oracle.Spec.Protocol.done
  prover := fun pstate => pure fun msg => pure (pout msg pstate)
  verifier := fun vstate => do
    let msgAndState ← send vstate
    let out ← vout msgAndState.1 msgAndState.2
    pure ⟨msgAndState.1, out⟩

/-- A prover oracle message in an executable oracle choreography.

The continuation runs with the verifier's accumulated oracle spec extended by
the message interface. The verifier endpoint is structurally independent of the
hidden oracle payload, but subsequent verifier actions can query it through the
extended access monad. -/
def proverOracle
    {PState VState PState' POut VOut : Type}
    (X : Type) [OracleInterface X]
    (send : PState → OracleComp oSpec (X × PState'))
    (rest :
      Program oSpec OStmtIn (accSpec + @OracleInterface.spec X inferInstance)
        PState' VState POut VOut) :
    Program oSpec OStmtIn accSpec PState VState POut VOut where
  protocol := Interaction.Oracle.Spec.Protocol.oracle X rest.protocol
  prover := fun pstate => pure <| do
    let msgAndState ← send pstate
    let msg := msgAndState.1
    let nextPState := msgAndState.2
    let restProver ← rest.prover nextPState
    pure ⟨msg, restProver⟩
  verifier := fun vstate _msg => rest.verifier vstate

/-! ### Reduction-level packages -/

/-- An executable oracle choreography packaged as a full oracle reduction.

`Program` describes the interactive endpoint behavior and determines the
protocol shape. `ReductionProgram` adds state initialization, terminal output
projections, and `simulate`, which is deliberately not part of the verifier
endpoint: it explains how output-oracle queries are answered from input oracles
and transcript oracle handles after the protocol has run.

TODO: this currently packages one flat `Program` per shared input. For repeated
or state-machine protocols, keep using `OracleProtocol.ChainProgram` below until
the executable DSL grows a chain/telescope compiler that derives the chain from
the same choreographic source. -/
structure ReductionProgram
    {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type) where
  /-- Prover private state for each shared input. -/
  PState : SharedIn → Type
  /-- Verifier private state for each shared input. -/
  VState : SharedIn → Type
  /-- Raw terminal prover endpoint output before reduction packaging. -/
  POut : SharedIn → Type
  /-- Raw terminal verifier endpoint output before reduction packaging. -/
  VOut : SharedIn → Type
  /-- The executable choreography. Its generated protocol is the reduction
  protocol for this shared input. -/
  program : (shared : SharedIn) →
    Program (oSpec := oSpec) (OStmtIn := OStatementIn shared) (accSpec := []ₒ)
      (PState shared) (VState shared) (POut shared) (VOut shared)
  /-- Initialize prover state from the input statement, input oracle statements,
  and witness. -/
  proverInit : (shared : SharedIn) →
    StatementWithOracles StatementIn OStatementIn shared →
      WitnessIn shared → PState shared
  /-- Initialize verifier state from the input statement. -/
  verifierInit : (shared : SharedIn) → StatementIn shared → VState shared
  /-- Public output statement family. -/
  StatementOut : (shared : SharedIn) →
    Interaction.Oracle.Spec.PublicTranscript ((program shared).protocol.spec) → Type
  /-- Output oracle statement index family. -/
  ιₛₒ : (shared : SharedIn) →
    Interaction.Oracle.Spec.PublicTranscript ((program shared).protocol.spec) → Type
  /-- Output oracle statement family. -/
  OStatementOut : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript ((program shared).protocol.spec)) →
      ιₛₒ shared pt → Type
  /-- Oracle interface evidence for output oracle statements. -/
  outOracle : ∀ shared pt i, OracleInterface (OStatementOut shared pt i)
  /-- Output witness family. -/
  WitnessOut : (shared : SharedIn) →
    Interaction.Oracle.Spec.PublicTranscript ((program shared).protocol.spec) → Type
  /-- Package terminal prover output into statement/oracle/witness output. -/
  proverOutput : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript ((program shared).protocol.spec)) →
      POut shared →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared pt)
            (fun _ => OStatementOut shared pt)
            shared)
          (WitnessOut shared pt)
  /-- Package terminal verifier output into the output statement. -/
  verifierOutput : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript ((program shared).protocol.spec)) →
      VOut shared → StatementOut shared pt
  /-- Simulate output oracle queries from input oracle statements and transcript
  oracle handles. This is the semantic content that cannot be inferred from
  endpoint strategies alone. -/
  simulate : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript ((program shared).protocol.spec)) →
      QueryImpl [OStatementOut shared pt]ₒ
        (OracleComp
          ([OStatementIn shared]ₒ +
            ((program shared).protocol.spec).toOracleSpec
              ((program shared).protocol.oracleDeco) pt))

namespace ReductionProgram

/-- The protocol generated by a packaged reduction choreography. -/
abbrev protocol
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    (program : ReductionProgram oSpec SharedIn StatementIn OStatementIn WitnessIn)
    (shared : SharedIn) : Interaction.Oracle.Spec.Protocol :=
  (program.program shared).protocol

/-- Project a packaged choreography to an executable oracle reduction. -/
def toReduction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    (reductionProgram :
      ReductionProgram oSpec SharedIn StatementIn OStatementIn WitnessIn) :
    @Interaction.Oracle.Reduction _ oSpec SharedIn
      (fun shared => (reductionProgram.program shared).protocol.spec)
      (fun shared => (reductionProgram.program shared).protocol.roles)
      (fun shared => (reductionProgram.program shared).protocol.oracleDeco)
      StatementIn _ OStatementIn inferInstance WitnessIn
      reductionProgram.StatementOut
      (fun shared pt => reductionProgram.ιₛₒ shared pt)
      reductionProgram.OStatementOut
      reductionProgram.outOracle
      reductionProgram.WitnessOut := by
  letI : ∀ shared pt i,
      OracleInterface (reductionProgram.OStatementOut shared pt i) :=
    reductionProgram.outOracle
  exact {
    prover := fun shared sWithOracles witness => do
      let strat ←
        (reductionProgram.program shared).prover
          (reductionProgram.proverInit shared sWithOracles witness)
      pure <|
        Interaction.TwoParty.Focal.toConstantMonads
          ((reductionProgram.program shared).protocol.spec).toInteractionSpec
          (((reductionProgram.program shared).protocol.spec).toSpecRoles
            ((reductionProgram.program shared).protocol.roles))
          (Interaction.TwoParty.Focal.mapOutput
            (fun tr out =>
              reductionProgram.proverOutput shared
                (((reductionProgram.program shared).protocol.spec).projectPublic tr)
                out)
            strat)
    verifier := {
      toFun := fun shared stmt =>
        Interaction.Spec.ShapeOver.mapOutput counterpartMonadicShape
          (agent := PUnit.unit)
          (spec := ((reductionProgram.program shared).protocol.spec).toInteractionSpec)
          (ctxs := RoleDecoration.withMonads
            (((reductionProgram.program shared).protocol.spec).toSpecRoles
              ((reductionProgram.program shared).protocol.roles))
            (((reductionProgram.program shared).protocol.spec).toMonadDecoration oSpec
              (OStatementIn shared)
              ((reductionProgram.program shared).protocol.roles)
              ((reductionProgram.program shared).protocol.oracleDeco) []ₒ))
          (fun tr out =>
            reductionProgram.verifierOutput shared
              (((reductionProgram.program shared).protocol.spec).projectPublic tr)
              out)
          ((reductionProgram.program shared).verifier
            (reductionProgram.verifierInit shared stmt))
      simulate := reductionProgram.simulate
    }
  }

end ReductionProgram

end OracleScoped

namespace OracleProtocol

/-! ## Oracle reduction and chain packaging

The executable DSL above is the source of protocol shape for one oracle
segment. Reduction-level packages add the extra data that is not part of an
endpoint strategy, most importantly output-oracle simulation.
-/

/-- Repeat the same decorated oracle protocol shape for a fixed number of rounds. -/
def replicate (round : Interaction.Oracle.Spec.Protocol) :
    (n : Nat) → Interaction.Oracle.Spec.Chain n :=
  Interaction.Oracle.Spec.Chain.replicate round.spec round.roles round.oracleDeco

/-- Flatten a decorated oracle chain into a decorated oracle protocol. -/
def fromChain {n : Nat} (chain : Interaction.Oracle.Spec.Chain n) :
    Interaction.Oracle.Spec.Protocol where
  spec := Interaction.Oracle.Spec.Chain.toSpec n chain
  roles := Interaction.Oracle.Spec.Chain.toRoles n chain
  oracleDeco := Interaction.Oracle.Spec.Chain.toOracleDeco n chain

/-! ### Executable chain programs

`ChainProgram` is the first executable oracle choreography layer. It bundles the
state initialization, round handlers, terminal projections, and output-oracle
simulation needed by `Interaction.Oracle.Reduction.ofChain`, while keeping the
decorated chain as the single protocol-shape source.
-/

/-- A stateful oracle choreography over a fixed `Spec.Chain`. -/
structure ChainProgram
    {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (n : Nat)
    (chain : SharedIn → Interaction.Oracle.Spec.Chain n)
    (StatementOut :
      (shared : SharedIn) →
        Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.Chain.toSpec n (chain shared)) → Type)
    {ιₛₒ : (shared : SharedIn) →
      Interaction.Oracle.Spec.PublicTranscript
        (Interaction.Oracle.Spec.Chain.toSpec n (chain shared)) → Type}
    (OStatementOut :
      (shared : SharedIn) →
        (pt : Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.Chain.toSpec n (chain shared))) →
          ιₛₒ shared pt → Type)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) →
        Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.Chain.toSpec n (chain shared)) → Type) where
  /-- Prover private execution state indexed by the remaining chain. -/
  ProverState : (shared : SharedIn) →
    {k : Nat} → Interaction.Oracle.Spec.Chain k → Type
  /-- Verifier private execution state indexed by the remaining chain. -/
  VerifierState : (shared : SharedIn) →
    {k : Nat} → Interaction.Oracle.Spec.Chain k → Type
  /-- Initialize the prover state from the input statement, input oracle data,
  and witness. -/
  proverInit : (shared : SharedIn) →
    StatementWithOracles StatementIn OStatementIn shared →
      WitnessIn shared → ProverState shared (chain shared)
  /-- Initialize the verifier state from the input statement. -/
  verifierInit : (shared : SharedIn) →
    StatementIn shared → VerifierState shared (chain shared)
  /-- Prover handlers for each round in the concrete chain. -/
  proverSteps : (shared : SharedIn) →
    Interaction.Oracle.Spec.Chain.Prover.RoundSteps
      (m := OracleComp oSpec) (ProverState shared) n (chain shared)
  /-- Verifier handlers for each round in the concrete chain. -/
  verifierSteps : (shared : SharedIn) →
    Interaction.Oracle.Spec.Chain.Verifier.RoundSteps
      (oSpec := oSpec) (OStmtIn := OStatementIn shared)
      (VerifierState shared) n (chain shared)
  /-- Project the terminal prover state to the public output statement. -/
  proverStmtResult : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript
      (Interaction.Oracle.Spec.Chain.toSpec n (chain shared))) →
      Interaction.Oracle.Spec.Chain.outputFamily
        (ProverState shared) n (chain shared) pt →
      StatementOut shared pt
  /-- Project the terminal verifier state to the public output statement. -/
  verifierStmtResult : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript
      (Interaction.Oracle.Spec.Chain.toSpec n (chain shared))) →
      Interaction.Oracle.Spec.Chain.outputFamily
        (VerifierState shared) n (chain shared) pt →
      StatementOut shared pt
  /-- Produce output oracle statements from the terminal prover state. -/
  oracleStmtResult : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript
      (Interaction.Oracle.Spec.Chain.toSpec n (chain shared))) →
      Interaction.Oracle.Spec.Chain.outputFamily
        (ProverState shared) n (chain shared) pt →
      ∀ i, OStatementOut shared pt i
  /-- Produce the terminal witness from the terminal prover state. -/
  witnessResult : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript
      (Interaction.Oracle.Spec.Chain.toSpec n (chain shared))) →
      Interaction.Oracle.Spec.Chain.outputFamily
        (ProverState shared) n (chain shared) pt →
      WitnessOut shared pt
  /-- Simulate output oracle queries using the input oracle data and transcript
  oracle handles. -/
  simulate : (shared : SharedIn) →
    (pt : Interaction.Oracle.Spec.PublicTranscript
      (Interaction.Oracle.Spec.Chain.toSpec n (chain shared))) →
      QueryImpl [OStatementOut shared pt]ₒ
        (OracleComp
          ([OStatementIn shared]ₒ +
            (Interaction.Oracle.Spec.Chain.toSpec n (chain shared)).toOracleSpec
              (Interaction.Oracle.Spec.Chain.toOracleDeco n (chain shared)) pt))

namespace ChainProgram

/-- Project a stateful oracle choreography to an executable oracle reduction. -/
def toReduction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {n : Nat}
    {chain : SharedIn → Interaction.Oracle.Spec.Chain n}
    {StatementOut :
      (shared : SharedIn) →
        Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.Chain.toSpec n (chain shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      Interaction.Oracle.Spec.PublicTranscript
        (Interaction.Oracle.Spec.Chain.toSpec n (chain shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) →
        (pt : Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.Chain.toSpec n (chain shared))) →
          ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) →
        Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.Chain.toSpec n (chain shared)) → Type}
    (program : ChainProgram oSpec SharedIn StatementIn OStatementIn WitnessIn
      n chain StatementOut OStatementOut WitnessOut) :
    Interaction.Oracle.Reduction oSpec SharedIn
      (fun shared => Interaction.Oracle.Spec.Chain.toSpec n (chain shared))
      (fun shared => Interaction.Oracle.Spec.Chain.toRoles n (chain shared))
      (fun shared => Interaction.Oracle.Spec.Chain.toOracleDeco n (chain shared))
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut :=
  Interaction.Oracle.Reduction.ofChain
    program.ProverState
    program.VerifierState
    program.proverInit
    program.verifierInit
    program.proverSteps
    program.verifierSteps
    program.proverStmtResult
    program.verifierStmtResult
    program.oracleStmtResult
    program.witnessResult
    program.simulate

end ChainProgram

end OracleProtocol

/-! ## Surface notation

The surface notation expands to the scoped constructors. A message declaration
names the public transcript value next to its sender, while `from` exposes the
sender's current private state as a Lean pattern. The `send ... keeping ...`
form returns both the public message and the next private state.
-/

declare_syntax_cat choreo_step

/-- `choreo_begin body` marks a scoped choreography expression. -/
syntax "choreo_begin " choreo_step : term

/-- Return a public message and the sender's next private state. -/
syntax:arg "send " term " keeping " term : term

/-- Accept an `Option Unit`-valued verifier decision. -/
syntax "accept" : term

/-- Reject an `Option Unit`-valued verifier decision. -/
syntax "reject" : term

/-- Prover-to-verifier message with public-message and private-state patterns. -/
syntax:arg
  "prover_send[" term "] " ident &"from" term " => " term " ;; "
  choreo_step : choreo_step

/-- Verifier-to-prover message with public-message and private-state patterns. -/
syntax:arg
  "verifier_send[" term "] " ident &"from" term " => " term " ;; "
  choreo_step : choreo_step

/-- Terminal scoped choreography with final local-state patterns. -/
syntax:arg
  "choreo_end " &"prover" term " => " term
  " ;; " &"verifier" term " => " term : choreo_step

private partial def expandChoreoStep :
    Lean.TSyntax `choreo_step → Lean.MacroM (Lean.TSyntax `term)
  | `(choreo_step| prover_send[$X:term] $msg:ident from $pstate:term =>
      $action:term ;; $rest:choreo_step) => do
      let restTerm ← expandChoreoStep rest
      `(Choreo.Scoped.proverSendConst $X (fun $pstate => $action) (fun $msg => $restTerm))
  | `(choreo_step| verifier_send[$X:term] $msg:ident from $vstate:term =>
      $action:term ;; $rest:choreo_step) => do
      let restTerm ← expandChoreoStep rest
      `(Choreo.Scoped.verifierSendConst $X (fun $vstate => $action) (fun $msg => $restTerm))
  | `(choreo_step| choreo_end prover $pstate:term => $pout:term ;;
      verifier $vstate:term => $vout:term) =>
      `(Choreo.Scoped.done (fun $pstate => $pout) (fun $vstate => $vout))
  | _ => Lean.Macro.throwUnsupported

macro_rules
  | `(choreo_begin $body:choreo_step) => expandChoreoStep body
  | `(send $msg:term keeping $state:term) => `(pure (⟨$msg, $state⟩))
  | `(accept) => `(some ())
  | `(reject) => `(none)

/-! ## Oracle reduction surface notation -/

/-- Repeat a decorated oracle round protocol into an `n`-round oracle chain. -/
syntax "oracle_chain[" term "] " "repeat " term : term

/-- Flatten an oracle chain into a decorated oracle protocol. -/
syntax "oracle_protocol " "from_chain[" term "] " term : term

/-- Query the current prover oracle message by its oracle interface. -/
syntax:arg "oracle_query[" term "] " term : term

declare_syntax_cat oracle_reduction_step
declare_syntax_cat oracle_reduction_block

/-- Public prover-to-verifier message in an executable oracle choreography. -/
syntax:arg
  "prover_send[" term "] " ident &"from" term " => " term " ;; "
  oracle_reduction_step : oracle_reduction_step

/-- Public verifier-to-prover message in an executable oracle choreography. -/
syntax:arg
  "verifier_send[" term "] " ident &"from" term " => " term " ;; "
  oracle_reduction_step : oracle_reduction_step

/-- Prover oracle message in an executable oracle choreography. -/
syntax:arg
  "prover_oracle[" term "] " ident &"from" term " => " term " ;; "
  oracle_reduction_step : oracle_reduction_step

/-- Terminal executable oracle choreography with final local-state patterns. -/
syntax:arg
  "oracle_reduction_end " &"prover" term " => " term
  " ;; " &"verifier" term " => " term : oracle_reduction_step

/-- Full executable oracle reduction choreography.

The block owns the local endpoint state, initialization, protocol messages,
terminal endpoint computations, output projections, and `simulate`. The protocol
shape, prover endpoint, verifier endpoint, and oracle decoration are inferred
from the message choreography itself. -/
syntax
  "prover_state " ident " => " term " ;; "
  "verifier_state " ident " => " term " ;; "
  "prover_result " ident " => " term " ;; "
  "verifier_result " ident " => " term " ;; "
  "prover_init " ident ident ident " => " term " ;; "
  "verifier_init " ident ident " => " term " ;; "
  oracle_reduction_step " ;; "
  "statement_out " ident ident " => " term " ;; "
  "output_oracle " ident ident " => "
    "index " term " ;; "
    "statement " term " ;; "
    "interface " ident " => " term " ;; "
    &"simulate" ident " => " term " ;; "
  "witness_out " ident ident " => " term " ;; "
  "prover_output " ident ident ident " => " term " ;; "
  "verifier_output " ident ident ident " => " term : oracle_reduction_block

/-- `oracle_reduction_begin ... oracle_reduction_end ...` packages one
executable oracle reduction program. -/
syntax "oracle_reduction_begin " oracle_reduction_block : term

private partial def expandOracleReductionStep :
    Lean.TSyntax `oracle_reduction_step → Lean.MacroM (Lean.TSyntax `term)
  | `(oracle_reduction_step| prover_send[$X:term] $msg:ident from $pstate:term =>
      $action:term ;; $rest:oracle_reduction_step) => do
      let restTerm ← expandOracleReductionStep rest
      `(Choreo.OracleScoped.proverSend $X (fun $pstate => $action) (fun $msg => $restTerm))
  | `(oracle_reduction_step| verifier_send[$X:term] $msg:ident from $vstate:term =>
      $action:term ;; oracle_reduction_end prover $pstateEnd:term => $pout:term ;;
      verifier $vstateEnd:term => $vout:term) =>
      `(Choreo.OracleScoped.verifierSendFinish $X
        (fun $vstate => $action)
        (fun $msg $pstateEnd => $pout)
        (fun $msg $vstateEnd => $vout))
  | `(oracle_reduction_step| verifier_send[$X:term] $msg:ident from $vstate:term =>
      $action:term ;; $rest:oracle_reduction_step) => do
      let restTerm ← expandOracleReductionStep rest
      `(Choreo.OracleScoped.verifierSend $X (fun $vstate => $action) (fun $msg => $restTerm))
  | `(oracle_reduction_step| prover_oracle[$X:term] $_msg:ident from $pstate:term =>
      $action:term ;; $rest:oracle_reduction_step) => do
      let restTerm ← expandOracleReductionStep rest
      `(Choreo.OracleScoped.proverOracle $X (fun $pstate => $action) $restTerm)
  | `(oracle_reduction_step| oracle_reduction_end prover $pstate:term => $pout:term ;;
      verifier $vstate:term => $vout:term) =>
      `(Choreo.OracleScoped.done (fun $pstate => $pout) (fun $vstate => $vout))
  | _ => Lean.Macro.throwUnsupported

macro_rules
  | `(oracle_chain[$n:term] repeat $round:term) =>
      `(Choreo.OracleProtocol.replicate $round $n)
  | `(oracle_protocol from_chain[$n:term] $chain:term) =>
      `(Choreo.OracleProtocol.fromChain (n := $n) $chain)
  | `(oracle_query[$X:term] $q:term) =>
      `(liftM <| (@OracleInterface.spec $X inferInstance).query $q)
  | `(oracle_reduction_begin
      prover_state $sharedPState:ident => $pstate:term ;;
      verifier_state $sharedVState:ident => $vstate:term ;;
      prover_result $sharedPOut:ident => $pout:term ;;
      verifier_result $sharedVOut:ident => $vout:term ;;
      prover_init $sharedPInit:ident $stmtWithOracles:ident $witness:ident => $proverInit:term ;;
      verifier_init $sharedVInit:ident $stmtIn:ident => $verifierInit:term ;;
      $body:oracle_reduction_step ;;
      statement_out $sharedStmtOut:ident $ptStmtOut:ident => $statementOut:term ;;
      output_oracle $sharedOracle:ident $ptOracle:ident =>
        index $oracleOutIndex:term ;;
        statement $oracleOut:term ;;
        interface $idxOI:ident => $oracleInterface:term ;;
        simulate $querySim:ident => $simulate:term ;;
      witness_out $sharedWOut:ident $ptWOut:ident => $witnessOut:term ;;
      prover_output $sharedPResult:ident $ptPResult:ident $outPResult:ident => $proverOutput:term ;;
      verifier_output $sharedVResult:ident $ptVResult:ident $outVResult:ident =>
        $verifierOutput:term) => do
      let program ← expandOracleReductionStep body
      `({
        PState := fun $sharedPState => $pstate
        VState := fun $sharedVState => $vstate
        POut := fun $sharedPOut => $pout
        VOut := fun $sharedVOut => $vout
        program := fun _ => $program
        proverInit := fun $sharedPInit $stmtWithOracles $witness => $proverInit
        verifierInit := fun $sharedVInit $stmtIn => $verifierInit
        StatementOut := fun $sharedStmtOut $ptStmtOut => $statementOut
        ιₛₒ := fun $sharedOracle $ptOracle => $oracleOutIndex
        OStatementOut := fun $sharedOracle $ptOracle => $oracleOut
        outOracle := fun $sharedOracle $ptOracle $idxOI => $oracleInterface
        WitnessOut := fun $sharedWOut $ptWOut => $witnessOut
        proverOutput := fun $sharedPResult $ptPResult $outPResult => $proverOutput
        verifierOutput := fun $sharedVResult $ptVResult $outVResult => $verifierOutput
        simulate := fun $sharedOracle $ptOracle $querySim => $simulate
      })

end Choreo
end Interaction

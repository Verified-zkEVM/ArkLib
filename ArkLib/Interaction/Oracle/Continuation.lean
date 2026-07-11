/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution

set_option linter.style.longFile 2000

open OracleComp OracleSpec
open Interaction.TwoParty

namespace Interaction

namespace OracleDecoration

/-! ## Oracle reduction composition -/

namespace OracleReduction

/-- Freeze the shared input of an oracle reduction, reindexing the ambient
protocol spine over `PUnit`. This is a bridge utility for proofs that want to
view a fixed shared spine as a degenerate one-point ambient index. -/
def freezeSharedToPUnit
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) :
    OracleReduction oSpec
      PUnit
      (fun _ => Context shared)
      (fun _ => Roles shared)
      (fun _ => oracleDeco shared)
      (fun _ => StatementIn shared)
      (fun _ => OStmtIn shared)
      (fun _ => WitnessIn shared)
      (fun _ tr => StatementOut shared tr)
      (fun _ tr => OStmtOut shared tr)
      (fun _ tr => WitnessOut shared tr) where
  prover _ s w := do
    let input' :
        StatementWithOracles StatementIn OStmtIn shared :=
      ⟨s.stmt, s.oracleStmt⟩
    let remapOutput :
        (tr : Spec.Transcript (Context shared)) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared)
          (WitnessOut shared tr) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) PUnit.unit)
          (WitnessOut shared tr)
      | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
    let strat ← reduction.prover shared input' w
    pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
  verifier _ {_} accSpec stmt :=
    reduction.verifier shared accSpec stmt
  simulate _ tr :=
    reduction.simulate shared tr

/-- Identity continuation: no further interaction, and the carried local
statement, oracle family, and witness are forwarded unchanged. -/
def id
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type} :
    OracleReduction oSpec SharedIn
      (fun _ => .done)
      (fun _ => ⟨⟩)
      (fun _ => ⟨⟩)
      StatementIn OStmtIn WitnessIn
      (fun shared _ => StatementIn shared)
      (fun shared _ => OStmtIn shared)
      (fun shared _ => WitnessIn shared) where
  prover _ sWithOracles w :=
    pure ⟨⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩, w⟩
  verifier _ {_} _accSpec stmt :=
    stmt
  simulate _ _ :=
    fun q => liftM <| ([OStmtIn _]ₒ).query q

/-- Freeze the shared spine of a continuation-shaped oracle reduction and
promote the carried statement to the new ambient index. This is a bridge
utility for one-shot views whose ambient input is precisely the explicit
current statement. -/
def promoteStatementToShared
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) :
    OracleReduction oSpec
      (StatementIn shared)
      (fun _ => Context shared)
      (fun _ => Roles shared)
      (fun _ => oracleDeco shared)
      (fun _ => PUnit)
      (fun _ => OStmtIn shared)
      (fun _ => WitnessIn shared)
      (fun _ tr => StatementOut shared tr)
      (fun _ tr => OStmtOut shared tr)
      (fun _ tr => WitnessOut shared tr) where
  prover stmt sWithOracles w := do
    let input' :
        StatementWithOracles StatementIn OStmtIn shared :=
      ⟨stmt, sWithOracles.oracleStmt⟩
    let remapOutput :
        (tr : Spec.Transcript (Context shared)) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared)
          (WitnessOut shared tr) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) stmt)
          (WitnessOut shared tr)
      | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
    let strat ← reduction.prover shared input' w
    pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
  verifier stmt {_} accSpec _ :=
    reduction.verifier shared accSpec stmt
  simulate _ tr :=
    reduction.simulate shared tr

/-- Reindex the shared input of a continuation along a pure map. This is useful
for composing with a later continuation that ignores some earlier transcript
components of the shared input. -/
def pullbackShared
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {SharedIn' : Type}
    (f : SharedIn' → SharedIn)
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut) :
    OracleReduction oSpec SharedIn'
      (fun shared => Context (f shared))
      (fun shared => Roles (f shared))
      (fun shared => oracleDeco (f shared))
      (fun shared => StatementIn (f shared))
      (fun shared => OStmtIn (f shared))
      (fun shared => WitnessIn (f shared))
      (fun shared tr => StatementOut (f shared) tr)
      (fun shared tr => OStmtOut (f shared) tr)
      (fun shared tr => WitnessOut (f shared) tr) where
  prover shared sWithOracles w := do
    let input' :
        StatementWithOracles StatementIn OStmtIn (f shared) :=
      ⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩
    let remapOutput :
        (tr : Spec.Transcript (Context (f shared))) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut (f shared) tr) (fun _ => OStmtOut (f shared) tr) (f shared))
          (WitnessOut (f shared) tr) →
        HonestProverOutput
          (StatementWithOracles
            (fun _ => StatementOut (f shared) tr) (fun _ => OStmtOut (f shared) tr) shared)
          (WitnessOut (f shared) tr)
      | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
    let strat ← reduction.prover (f shared) input' w
    pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
  verifier shared {_} accSpec :=
    reduction.verifier (f shared) accSpec
  simulate shared tr :=
    reduction.simulate (f shared) tr

/-! ## Intrinsic continuation chains -/

/-- An oracle-native intrinsic chain of `n` continuation rounds. Each round
packages its current `Spec`, `RoleDecoration`, and `OracleDecoration`
directly, so no external stage family or total `roles/od` map is needed. -/
inductive Chain : Nat → Type _
  | nil : Chain 0
  | cons {n : Nat}
      (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
      (cont : Spec.Transcript spec → Chain n) : Chain (n + 1)

namespace Chain

/-- Flatten an intrinsic continuation chain into a `Spec`. -/
def toSpec : {n : Nat} → Chain n → Spec
  | 0, .nil => .done
  | _ + 1, .cons spec _ _ cont => spec.append fun tr => toSpec (cont tr)

/-- Flatten the per-round role decorations of an intrinsic continuation chain. -/
def roles : {n : Nat} → (c : Chain n) → RoleDecoration (toSpec c)
  | 0, .nil => PUnit.unit
  | _ + 1, .cons _ headRoles _ cont =>
      Spec.Decoration.append headRoles fun tr => roles (cont tr)

/-- Flatten the per-round oracle decorations of an intrinsic continuation chain. -/
def od : {n : Nat} → (c : Chain n) → OracleDecoration (toSpec c) (roles c)
  | 0, .nil => PUnit.unit
  | _ + 1, .cons _ _ headOD cont =>
      Role.Refine.append headOD fun tr => od (cont tr)

/-- Lift a family on the remaining intrinsic chain to a family on transcripts of
the flattened chain. -/
def outputFamily
    (Family : {n : Nat} → Chain n → Type) :
    {n : Nat} → (c : Chain n) → Spec.Transcript (toSpec c) → Type
  | 0, c, _ => Family c
  | _ + 1, .cons spec _ _ cont, tr =>
      Spec.Transcript.liftAppend spec
        (fun tr₁ => toSpec (cont tr₁))
        (fun tr₁ tr₂ => outputFamily Family (cont tr₁) tr₂)
        tr

/-- Collapse a lifted chain output back to the unique terminal chain state. -/
def outputAtEnd
    (Family : {n : Nat} → Chain n → Type) :
    {n : Nat} → (c : Chain n) → (tr : Spec.Transcript (toSpec c)) →
    outputFamily Family c tr → Family .nil
  | 0, .nil, _, out => out
  | _ + 1, .cons spec _ _ cont, tr, out =>
      let split :=
        Spec.Transcript.split spec (fun tr₁ => toSpec (cont tr₁)) tr
      let tailOut :=
        Spec.Transcript.unliftAppend spec
          (fun tr₁ => toSpec (cont tr₁))
          (fun tr₁ tr₂ => outputFamily Family (cont tr₁) tr₂)
          tr out
      outputAtEnd Family (cont split.1) split.2 tailOut

end Chain

private def chainStrategy
    {ι : Type} {oSpec : OracleSpec ι}
    {Family : {n : Nat} → Chain n → Type}
    (step : {n : Nat} → (c : Chain (n + 1)) → Family c →
      OracleComp oSpec
        (match c with
        | .cons spec roles _ cont =>
            Spec.Strategy.withRoles (OracleComp oSpec) spec roles
              (fun tr => Family (cont tr)))) :
    {n : Nat} → (c : Chain n) → Family c →
    OracleComp oSpec
      (Spec.Strategy.withRoles (OracleComp oSpec) (Chain.toSpec c) (Chain.roles c)
        (Chain.outputFamily Family c))
  | 0, .nil, out => pure out
  | _ + 1, .cons spec roles od cont, state => do
      let strat ← step (.cons spec roles od cont) state
      Spec.Strategy.compWithRoles strat fun tr next =>
        chainStrategy step (cont tr) next

private def chainVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {Family : {n : Nat} → Chain n → Type}
    {ιₐ : Type} (accSpec : OracleSpec ιₐ)
    (step : {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
      {n : Nat} → (c : Chain (n + 1)) → Family c →
      (match c with
      | .cons spec roles od cont =>
          Spec.Counterpart.withMonads spec roles
            (toMonadDecoration oSpec OStmtIn spec roles od accSpec)
            (fun tr => Family (cont tr)))) :
    {n : Nat} → (c : Chain n) → Family c →
    Spec.Counterpart.withMonads (Chain.toSpec c) (Chain.roles c)
      (toMonadDecoration oSpec OStmtIn (Chain.toSpec c) (Chain.roles c) (Chain.od c) accSpec)
      (Chain.outputFamily Family c)
  | 0, .nil, out => out
  | _ + 1, .cons spec roles od cont, state => by
      simpa [Chain.toSpec, Chain.roles, Chain.od, Chain.outputFamily,
        toMonadDecoration_append] using
        (Spec.Counterpart.withMonads.append
          (step accSpec (.cons spec roles od cont) state)
          (fun tr next =>
            chainVerifier
              ((accSpecAfter spec roles od accSpec tr).2)
              step
              (cont tr)
              next))

/-- Compose an intrinsic oracle continuation chain while threading arbitrary
internal prover and verifier state along the chain. Unlike `stateChainComp`,
the round structure lives directly in the chain itself, so callers do not need
an external stage family or transport through stage-indexed decorations. -/
def chainComp
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {n : Nat}
    (chain : SharedIn → Chain n)
    {ProverState : (shared : SharedIn) → {m : Nat} → Chain m → Type}
    {VerifierState : (shared : SharedIn) → {m : Nat} → Chain m → Type}
    {StatementOut : (shared : SharedIn) →
      Spec.Transcript (Chain.toSpec (chain shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) → Type}
    {OStmtOut :
      (shared : SharedIn) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) →
      Spec.Transcript (Chain.toSpec (chain shared)) → Type}
    (proverInit :
      (shared : SharedIn) →
      StatementWithOracles StatementIn OStmtIn shared →
        WitnessIn shared →
      OracleComp oSpec (ProverState shared (chain shared)))
    (proverStep :
      (shared : SharedIn) →
      {m : Nat} → (c : Chain (m + 1)) → ProverState shared c →
      OracleComp oSpec
        (match c with
        | .cons spec roles _ cont =>
            Spec.Strategy.withRoles (OracleComp oSpec) spec roles
              (fun tr => ProverState shared (cont tr))))
    (proverResult :
      (shared : SharedIn) →
      (s : StatementWithOracles StatementIn OStmtIn shared) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      ProverState shared Chain.nil →
      HonestProverOutput
        (StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared)
        (WitnessOut shared tr))
    (verifierInit :
      (shared : SharedIn) → StatementIn shared →
      VerifierState shared (chain shared))
    (verifierStep :
      (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
      {m : Nat} → (c : Chain (m + 1)) → VerifierState shared c →
      (match c with
      | .cons spec roles od cont =>
          Spec.Counterpart.withMonads spec roles
            (toMonadDecoration oSpec (OStmtIn shared) spec roles od accSpec)
            (fun tr => VerifierState shared (cont tr))))
    (verifierResult :
      (shared : SharedIn) → (stmt : StatementIn shared) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      VerifierState shared Chain.nil →
      StatementOut shared tr)
    (simulateResult :
      (shared : SharedIn) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp ([OStmtIn shared]ₒ +
          toOracleSpec (Chain.toSpec (chain shared))
            (Chain.roles (chain shared))
            (Chain.od (chain shared))
            tr))) :
    OracleReduction oSpec SharedIn
      (fun shared => Chain.toSpec (chain shared))
      (fun shared => Chain.roles (chain shared))
      (fun shared => Chain.od (chain shared))
      StatementIn OStmtIn WitnessIn
      StatementOut
      OStmtOut
      WitnessOut where
  prover shared sWithOracles witness := do
    let init ← proverInit shared sWithOracles witness
    let strat ← chainStrategy (proverStep shared) (chain shared) init
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr pOut =>
        proverResult shared sWithOracles tr
          (Chain.outputAtEnd
            (fun {_} c => ProverState shared c)
            (chain shared) tr pOut))
      strat
  verifier shared {_} accSpec stmt :=
    Spec.Counterpart.withMonads.mapOutput
      (Chain.toSpec (chain shared))
      (Chain.roles (chain shared))
      (toMonadDecoration oSpec (OStmtIn shared)
        (Chain.toSpec (chain shared))
        (Chain.roles (chain shared))
        (Chain.od (chain shared))
        accSpec)
      (fun tr vOut =>
        verifierResult shared stmt tr
          (Chain.outputAtEnd
            (fun {_} c => VerifierState shared c)
            (chain shared) tr vOut))
      (chainVerifier accSpec (verifierStep shared) (chain shared) (verifierInit shared stmt))
  simulate shared tr :=
    simulateResult shared tr

/-- Run an arbitrary prover strategy against an oracle continuation's verifier and
package the resulting plain verifier output with transcript-dependent oracle
access semantics. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    {OutputP : Spec.Transcript (Context shared) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared) OutputP)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) × OutputP tr ×
      (StatementOut shared tr × QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp
          ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (oracleDeco shared) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (oracleDeco shared) accSpec accImpl
      prover (reduction.verifier shared accSpec stmt)
  pure ⟨tr, outP, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

/-- Execute an oracle continuation honestly and package the verifier's plain
output with transcript-dependent oracle access semantics. -/
def execute
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStmtIn shared)
    (w : WitnessIn shared)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) ×
      HonestProverOutput
        (StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStmtOut shared tr) shared)
        (WitnessOut shared tr) ×
      (StatementOut shared tr × QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp
          ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (oracleDeco shared) tr)))) := do
  let strategy ← reduction.prover shared s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 (OStmtIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (oracleDeco shared) accSpec accImpl
      strategy (reduction.verifier shared accSpec s.stmt)
  pure ⟨tr, proverOut, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

private def liftSimulatedMidOracleContextContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {oracleDeco₁ : (shared : SharedIn) → OracleDecoration (ctx₁ shared) (roles₁ shared)}
    {StmtMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → Type}
    {OStmtMid :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      ιₛₘ shared tr₁ → Type}
    [∀ shared tr₁ i, OracleInterface (OStmtMid shared tr₁ i)]
    {WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {oracleDeco₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      OracleDecoration (ctx₂ shared tr₁) (roles₂ shared tr₁)}
    (reduction1 : OracleReduction oSpec SharedIn
      ctx₁ roles₁ oracleDeco₁ StatementIn OStmtIn WitnessIn StmtMid OStmtMid WitMid)
    (shared : SharedIn)
    (tr₁ : Spec.Transcript (ctx₁ shared))
    (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) :
    QueryImpl
      ([OStmtMid shared tr₁]ₒ +
        toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
      (OracleComp
        ([OStmtIn shared]ₒ +
          toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
            (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
            (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
            (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)))
  | .inl q =>
      simulateQ
        (liftAppendLeftContext
          (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
          (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
          (od₁ := oracleDeco₁ shared) (od₂ := fun tr => oracleDeco₂ shared tr)
          (OStmt := OStmtIn shared) tr₁ tr₂)
        (reduction1.simulate shared tr₁ q)
  | .inr q =>
      liftM <| ([OStmtIn shared]ₒ +
          toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
            (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
            (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
            (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).query (.inr q)

private def liftPrefixOracleContext
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    (s : StatementIn) (tr₁ : Spec.Transcript (ctx₁ s))
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    QueryImpl ([OStmtIn s]ₒ + toOracleSpec (ctx₁ s) (roles₁ s) (oracleDeco₁ s) tr₁)
      (OracleComp ((oSpec + [OStmtIn s]ₒ) + accSpec))
  | .inl q =>
      liftM <| ([OStmtIn s]ₒ).query q
  | .inr q =>
      pure <| OracleDecoration.answerQuery (ctx₁ s) (roles₁ s) (oracleDeco₁ s) tr₁ q

private def retargetContinuationVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    (reduction1 : OracleReduction oSpec StatementIn
      ctx₁ roles₁ oracleDeco₁
      (fun _ => PUnit) OStmtIn (fun _ => WitnessIn)
      StmtMid OStmtMid WitMid)
    (s : StatementIn) (tr₁ : Spec.Transcript (ctx₁ s)) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (od : OracleDecoration spec roles) →
    (Output : Spec.Transcript spec → Type) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec (OStmtMid s tr₁) spec roles od accSpec)
      Output →
    Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec (OStmtIn s) spec roles od accSpec)
      Output
  | .done, _, _, _, _, _, cpt =>
      cpt
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, Output, _, accSpec, cpt =>
      fun x =>
        retargetContinuationVerifier reduction1 s tr₁
          (rest x) (rRest x) (odRest x) (fun p => Output ⟨x, p⟩)
          (accSpec + @OracleInterface.spec _ oi) (cpt x)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, Output, _, accSpec, cpt =>
      let route :
          QueryImpl ((oSpec + [OStmtMid s tr₁]ₒ) + accSpec)
            (OracleComp ((oSpec + [OStmtIn s]ₒ) + accSpec)) :=
        fun
        | .inl (.inl q) =>
            liftM <| oSpec.query q
        | .inl (.inr q) =>
            simulateQ (liftPrefixOracleContext
              (oSpec := oSpec) (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
              s tr₁ accSpec) (reduction1.simulate s tr₁ q)
        | .inr q =>
            liftM <| accSpec.query q
      simulateQ route <| do
        let ⟨x, cptRest⟩ ← cpt
        pure ⟨x, retargetContinuationVerifier reduction1 s tr₁
          (rest x) (rRest x) (odFn x) (fun p => Output ⟨x, p⟩)
          accSpec cptRest⟩

private def liftSimulatedMidOracleContext
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {oracleDeco₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    (reduction1 : OracleReduction oSpec StatementIn
      ctx₁ roles₁ oracleDeco₁
      (fun _ => PUnit) OStmtIn (fun _ => WitnessIn)
      StmtMid OStmtMid WitMid)
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁)) :
    QueryImpl
      ([OStmtMid s tr₁]ₒ +
        toOracleSpec ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
      (OracleComp
        ([OStmtIn s]ₒ +
          toOracleSpec ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
  | .inl q =>
      simulateQ
        (liftAppendLeftContext
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
          (roles₁ := roles₁ s) (roles₂ := roles₂ s)
          (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
          (OStmt := OStmtIn s) tr₁ tr₂)
        (reduction1.simulate s tr₁ q)
  | .inr q =>
      liftM <| ([OStmtIn s]ₒ +
          toOracleSpec ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)).query (.inr q)

private theorem simulateQ_liftSimulatedMidOracleContext_eq
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {oracleDeco₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    (reduction1 : OracleReduction oSpec StatementIn
      ctx₁ roles₁ oracleDeco₁
      (fun _ => PUnit) OStmtIn (fun _ => WitnessIn)
      StmtMid OStmtMid WitMid)
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁))
    (oStmtIn : OracleStatement (OStmtIn s))
    (midImpl : QueryImpl [OStmtMid s tr₁]ₒ Id)
    (hMid : ∀ i (q : OracleInterface.Query (OStmtMid s tr₁ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl (ctx₁ s) (roles₁ s) (oracleDeco₁ s) oStmtIn tr₁)
        (reduction1.simulate s tr₁ ⟨i, q⟩) = pure (midImpl ⟨i, q⟩)) :
    ∀ q,
      simulateQ
        (OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
          oStmtIn
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
        (liftSimulatedMidOracleContext
          (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
          (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
          reduction1 s tr₁ tr₂ q) =
      (QueryImpl.add midImpl
        (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))) q := by
  intro q
  cases q with
  | inl q =>
      rcases q with ⟨i, q⟩
      simp only [liftSimulatedMidOracleContext, add_apply_inl]
      rw [← QueryImpl.simulateQ_compose]
      have hroute :
          ((OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
              (Spec.Decoration.append (roles₁ s) (roles₂ s))
              (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
              oStmtIn
              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)) ∘ₛ
              (liftAppendLeftContext
                (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
                (roles₁ := roles₁ s) (roles₂ := roles₂ s)
                (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
                (OStmt := OStmtIn s) tr₁ tr₂)) =
          OracleDecoration.oracleContextImpl (ctx₁ s) (roles₁ s) (oracleDeco₁ s) oStmtIn tr₁ := by
        funext q'
        exact simulateQ_liftAppendLeftContext_eq
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
            (roles₁ := roles₁ s) (roles₂ := roles₂ s)
            (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
            (OStmt := OStmtIn s) tr₁ tr₂ oStmtIn q'
      rw [simulateQ_ext (fun q' => congrFun hroute q')]
      simpa [QueryImpl.add] using hMid i q
  | inr q =>
      simp [liftSimulatedMidOracleContext, QueryImpl.add, OracleDecoration.oracleContextImpl,
        simulateQ_query]

private theorem simulateQ_liftSimulatedMidOracleContextContinuation_eq
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {oracleDeco₁ : (shared : SharedIn) → OracleDecoration (ctx₁ shared) (roles₁ shared)}
    {StatementMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → Type}
    {OStatementMid :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → ιₛₘ shared tr₁ → Type}
    [∀ shared tr₁ i, OracleInterface (OStatementMid shared tr₁ i)]
    {WitnessMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {oracleDeco₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      OracleDecoration (ctx₂ shared tr₁) (roles₂ shared tr₁)}
    (reduction1 : OracleReduction oSpec SharedIn
      ctx₁ roles₁ oracleDeco₁
      StatementIn OStatementIn WitnessIn
      StatementMid OStatementMid WitnessMid)
    (shared : SharedIn)
    (tr₁ : Spec.Transcript (ctx₁ shared))
    (tr₂ : Spec.Transcript (ctx₂ shared tr₁))
    (oStatementIn : OracleStatement (OStatementIn shared))
    (midImpl : QueryImpl [OStatementMid shared tr₁]ₒ Id)
    (hMid : ∀ i (q : OracleInterface.Query (OStatementMid shared tr₁ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl
          (ctx₁ shared) (roles₁ shared) (oracleDeco₁ shared) oStatementIn tr₁)
        (reduction1.simulate shared tr₁ ⟨i, q⟩) = pure (midImpl ⟨i, q⟩)) :
    ∀ q,
      simulateQ
        (OracleDecoration.oracleContextImpl ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
          oStatementIn
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
        (liftSimulatedMidOracleContextContinuation
          (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
          (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
          reduction1 shared tr₁ tr₂ q) =
      (QueryImpl.add midImpl
        (OracleDecoration.answerQuery ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))) q := by
  intro q
  cases q with
  | inl q =>
      rcases q with ⟨i, q⟩
      simp only [liftSimulatedMidOracleContextContinuation]
      rw [← QueryImpl.simulateQ_compose]
      have hRoute :
          ((OracleDecoration.oracleContextImpl ((ctx₁ shared).append (ctx₂ shared))
              (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
              (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
              oStatementIn
              (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ∘ₛ
              (liftAppendLeftContext
                (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
                (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
                (od₁ := oracleDeco₁ shared) (od₂ := fun tr => oracleDeco₂ shared tr)
                (OStmt := OStatementIn shared) tr₁ tr₂)) =
          OracleDecoration.oracleContextImpl
            (ctx₁ shared) (roles₁ shared) (oracleDeco₁ shared) oStatementIn tr₁ := by
        funext q'
        exact simulateQ_liftAppendLeftContext_eq
          (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
          (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
          (od₁ := oracleDeco₁ shared) (od₂ := fun tr => oracleDeco₂ shared tr)
          (OStmt := OStatementIn shared) tr₁ tr₂ oStatementIn q'
      rw [simulateQ_ext (fun q' => congrFun hRoute q')]
      simpa [QueryImpl.add] using hMid i q
  | inr q =>
      simp [liftSimulatedMidOracleContextContinuation, QueryImpl.add,
        OracleDecoration.oracleContextImpl, simulateQ_query]

private theorem simulateQ_liftAppendRightContext_withImpl_eq
    {StatementIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {oracleDeco₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁))
    (midImpl : QueryImpl [OStmtMid s tr₁]ₒ Id) :
    ∀ q,
      simulateQ
        (QueryImpl.add midImpl
          (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
        (liftAppendRightContext
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
          (roles₁ := roles₁ s) (roles₂ := roles₂ s)
          (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
          (OStmt := OStmtMid s tr₁) tr₁ tr₂ q) =
      (QueryImpl.add midImpl
        (OracleDecoration.answerQuery (ctx₂ s tr₁) (roles₂ s tr₁) (oracleDeco₂ s tr₁) tr₂)) q := by
  intro q
  exact simulateQ_liftAppendRightContext_eq_of_impl
    (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
    (roles₁ := roles₁ s) (roles₂ := roles₂ s)
    (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
    (OStmt := OStmtMid s tr₁) tr₁ tr₂ midImpl q
/-
  intro q
  cases q with
  | inl q =>
      simp [QueryImpl.add, liftAppendRightContext, simulateQ_query]
  | inr q =>
      have hLifted :
          liftAppendRightContext
            (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
            (roles₁ := roles₁ s) (roles₂ := roles₂ s)
            (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
            (OStmt := OStmtMid s tr₁) tr₁ tr₂ (.inr q) =
          cast
            (congrArg
              (OracleComp <| [OStmtMid s tr₁]ₒ +
                OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                  (Spec.Decoration.append (roles₁ s) (roles₂ s))
                  (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                  (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
              (OracleDecoration.QueryHandle.appendRight_range
                (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s)
                (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q))
            (liftM (query
              (spec := [OStmtMid s tr₁]ₒ +
                OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                  (Spec.Decoration.append (roles₁ s) (roles₂ s))
                  (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                  (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
              (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s)
                (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q))) := by
        simpa [liftAppendRightContext, liftAppendRightQuery] using
          (liftM_cast_query_add_right
            (spec₁ := [OStmtMid s tr₁]ₒ)
            (spec₂ := OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
              (Spec.Decoration.append (roles₁ s) (roles₂ s))
              (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
            (t := OracleDecoration.QueryHandle.appendRight
              (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s)
              (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q)
            (h := OracleDecoration.QueryHandle.appendRight_range
              (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s)
              (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q))
      calc
        simulateQ
            (QueryImpl.add midImpl
              (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
                (Spec.Decoration.append (roles₁ s) (roles₂ s))
                (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
            (liftAppendRightContext
              (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
              (roles₁ := roles₁ s) (roles₂ := roles₂ s)
              (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
              (OStmt := OStmtMid s tr₁) tr₁ tr₂ (.inr q)) =
          cast
            (OracleDecoration.QueryHandle.appendRight_range
              (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr)
              tr₁ tr₂ q)
            (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
              (Spec.Decoration.append (roles₁ s) (roles₂ s))
              (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendRight
                (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr)
                tr₁ tr₂ q)) := by
                  rw [hLifted]
                  simpa [QueryImpl.add] using
                    (simulateQ_cast_query
                      (spec := [OStmtMid s tr₁]ₒ +
                        OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                          (Spec.Decoration.append (roles₁ s) (roles₂ s))
                          (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
                      (α := ([OStmtMid s tr₁]ₒ +
                        OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                          (Spec.Decoration.append (roles₁ s) (roles₂ s))
                          (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)).Range
                          (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                            (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s)
                            (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q))
                      (β := ([OStmtMid s tr₁]ₒ +
                        OracleDecoration.toOracleSpec (ctx₂ s tr₁)
                          (roles₂ s tr₁) (oracleDeco₂ s tr₁) tr₂).Range (Sum.inr q))
                      (h := (OracleDecoration.QueryHandle.appendRight_range
                        (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s)
                        (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q :
                          ([OStmtMid s tr₁]ₒ +
                            OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                              (Spec.Decoration.append (roles₁ s) (roles₂ s))
                              (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)).Range
                            (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                              (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s)
                              (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q) =
                          ([OStmtMid s tr₁]ₒ +
                            OracleDecoration.toOracleSpec (ctx₂ s tr₁)
                              (roles₂ s tr₁) (oracleDeco₂ s tr₁) tr₂).Range (Sum.inr q)))
                      (impl := QueryImpl.add midImpl
                        (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
                          (Spec.Decoration.append (roles₁ s) (roles₂ s))
                          (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
                      (q := query
                        (spec := [OStmtMid s tr₁]ₒ +
                          OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                            (Spec.Decoration.append (roles₁ s) (roles₂ s))
                            (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
                            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
                        (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                          (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s)
                          (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr) tr₁ tr₂ q)))
        _ = OracleDecoration.answerQuery
              (ctx₂ s tr₁) (roles₂ s tr₁) (oracleDeco₂ s tr₁) tr₂ q := by
              simpa using OracleDecoration.QueryHandle.answerQuery_appendRight
                (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr)
                tr₁ tr₂ q
-/

private def compSimulate
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {oracleDeco₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn
      ctx₁ roles₁ oracleDeco₁
      (fun _ => PUnit) OStmtIn (fun _ => WitnessIn)
      StmtMid OStmtMid WitMid)
    (reduction2 : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleReduction oSpec
        PUnit
        (fun _ => ctx₂ s tr₁)
        (fun _ => roles₂ s tr₁)
        (fun _ => oracleDeco₂ s tr₁)
        (fun _ => StmtMid s tr₁)
        (fun _ => OStmtMid s tr₁)
        (fun _ => WitMid s tr₁)
        (fun _ tr₂ => StmtOut s tr₁ tr₂)
        (fun _ tr₂ => OStmtOut s tr₁ tr₂)
        (fun _ tr₂ => WitOut s tr₁ tr₂))
    (s : StatementIn) (tr : Spec.Transcript ((ctx₁ s).append (ctx₂ s))) :
    QueryImpl
      [liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr]ₒ
      (OracleComp ([OStmtIn s]ₒ + toOracleSpec ((ctx₁ s).append (ctx₂ s))
        (Spec.Decoration.append (roles₁ s) (roles₂ s))
        (Role.Refine.append (oracleDeco₁ s) (fun tr₁ => oracleDeco₂ s tr₁)) tr)) := by
  intro qOut
  let split := Spec.Transcript.split (ctx₁ s) (ctx₂ s) tr
  let tr₁ := split.1
  let tr₂ := split.2
  let qSplit : ([OStmtOut s tr₁ tr₂]ₒ).Domain :=
    splitLiftAppendOracleQuery (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr qOut
  let routedSuffix :=
    simulateQ
      (liftAppendRightContext
        (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
        (roles₁ := roles₁ s) (roles₂ := roles₂ s)
        (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
        (OStmt := OStmtMid s tr₁) tr₁ tr₂)
      ((reduction2 s tr₁).simulate PUnit.unit tr₂ qSplit)
  let routed :=
    simulateQ
      (liftSimulatedMidOracleContext
        (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
        (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
        reduction1 s tr₁ tr₂)
      routedSuffix
  let baseSpec := fun tr' =>
    [OStmtIn s]ₒ + toOracleSpec ((ctx₁ s).append (ctx₂ s))
      (Spec.Decoration.append (roles₁ s) (roles₂ s))
      (Role.Refine.append (oracleDeco₁ s) (fun tr₁ => oracleDeco₂ s tr₁)) tr'
  let baseIdx := fun tr' =>
    (i : ιₛᵢ s) × OracleInterface.Query (OStmtIn s i) ⊕
      OracleDecoration.QueryHandle
        ((ctx₁ s).append (ctx₂ s))
        (Spec.Decoration.append (roles₁ s) (roles₂ s))
        (Role.Refine.append (oracleDeco₁ s) (fun tr₁ => oracleDeco₂ s tr₁))
        tr'
  have routed' :
      let split := Spec.Transcript.split (ctx₁ s) (ctx₂ s) tr
      OracleComp
        (baseSpec (Spec.Transcript.append (ctx₁ s) (ctx₂ s) split.1 split.2))
        (([OStmtOut s split.1 split.2]ₒ).Range
          (splitLiftAppendOracleQuery (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr qOut)) := by
    simpa [baseSpec, split, tr₁, tr₂, qSplit] using routed
  refine _root_.Interaction.OracleDecoration.collapseAppendOracleComp
    (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
    (Idx := baseIdx)
    (baseSpec := baseSpec)
    (ιₛ := ιₛₒ s) (OStmt := OStmtOut s) (tr := tr) (qOut := qOut) ?_
  exact routed'

/-- Binary sequential composition of oracle reductions. The first reduction runs
over `ctx₁`, producing intermediate outputs. The second reduction is a
continuation over the shared input `(s, tr₁)`, taking the intermediate bundled
oracle statement and witness as its local input. -/
private def compFlat {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {oracleDeco₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn
      ctx₁ roles₁ oracleDeco₁
      (fun _ => PUnit) OStmtIn (fun _ => WitnessIn)
      StmtMid OStmtMid WitMid)
    (reduction2 : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleReduction oSpec
        PUnit
        (fun _ => ctx₂ s tr₁)
        (fun _ => roles₂ s tr₁)
        (fun _ => oracleDeco₂ s tr₁)
        (fun _ => StmtMid s tr₁)
        (fun _ => OStmtMid s tr₁)
        (fun _ => WitMid s tr₁)
        (fun _ tr₂ => StmtOut s tr₁ tr₂)
        (fun _ tr₂ => OStmtOut s tr₁ tr₂)
        (fun _ tr₂ => WitOut s tr₁ tr₂)) :
    OracleReduction oSpec StatementIn
      (fun s => (ctx₁ s).append (ctx₂ s))
      (fun s => Spec.Decoration.append (roles₁ s) (roles₂ s))
      (fun s => Role.Refine.append (oracleDeco₁ s) (fun tr₁ => oracleDeco₂ s tr₁))
      (fun _ => PUnit)
      OStmtIn
      (fun _ => WitnessIn)
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s))
      (fun s tr => liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr)
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut s)) where
  prover s sWithOracles w := do
    let strat₁ ← reduction1.prover s sWithOracles w
    let strat ← Spec.Strategy.compWithRoles strat₁
      (fun tr₁ midOut => do
        let midStmt :
            StatementWithOracles
              (fun _ => StmtMid s tr₁) (fun _ => OStmtMid s tr₁) PUnit.unit :=
          ⟨midOut.stmt.stmt, midOut.stmt.oracleStmt⟩
        (reduction2 s tr₁).prover PUnit.unit midStmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out => by
        let split := Spec.Transcript.split (ctx₁ s) (ctx₂ s) tr
        let splitOuter := Spec.Transcript.liftAppendProd
          (ctx₁ s) (ctx₂ s)
          (fun tr₁ tr₂ =>
            StatementWithOracles (fun _ => StmtOut s tr₁ tr₂)
              (fun _ => OStmtOut s tr₁ tr₂) PUnit.unit)
          (WitOut s) tr out
        let splitStmtOracle := Spec.Transcript.unliftAppend
          (ctx₁ s) (ctx₂ s)
          (fun tr₁ tr₂ =>
            StatementWithOracles (fun _ => StmtOut s tr₁ tr₂)
              (fun _ => OStmtOut s tr₁ tr₂) PUnit.unit)
          tr splitOuter.1
        have htr :
            Spec.Transcript.append
              (ctx₁ s) (ctx₂ s)
              split.1 split.2 = tr := by
          simpa [split] using
            (Spec.Transcript.append_split (ctx₁ s) (ctx₂ s) tr)
        have stmtOut :
            Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr := by
          exact cast
            (congrArg
              (fun tr' => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s) tr')
              htr)
            (Spec.Transcript.packAppend (ctx₁ s) (ctx₂ s) (StmtOut s)
              split.1 split.2 splitStmtOracle.stmt)
        have oracleOut :
            OracleStatement
              (liftAppendOracleFamily (ctx₁ s) (ctx₂ s)
                (ιₛₒ s) (OStmtOut s) tr) := by
          intro i
          exact splitStmtOracle.oracleStmt
            (Spec.Transcript.unliftAppend (ctx₁ s) (ctx₂ s) (ιₛₒ s) tr i)
        exact ⟨⟨stmtOut, oracleOut⟩, splitOuter.2⟩)
      strat
  verifier s {ιₐ} accSpec _ := by
    simpa [toMonadDecoration_append] using
      (Spec.Counterpart.withMonads.append
        (reduction1.verifier s accSpec PUnit.unit)
        (fun tr₁ sMid =>
          retargetContinuationVerifier reduction1 s tr₁
            (ctx₂ s tr₁) (roles₂ s tr₁) (oracleDeco₂ s tr₁)
            (fun tr₂ => StmtOut s tr₁ tr₂)
            ((accSpecAfter (ctx₁ s) (roles₁ s) (oracleDeco₁ s) accSpec tr₁).2)
            ((reduction2 s tr₁).verifier PUnit.unit
              ((accSpecAfter (ctx₁ s) (roles₁ s) (oracleDeco₁ s) accSpec tr₁).2)
              sMid)))
  simulate := compSimulate reduction1 reduction2

/-- Binary sequential composition of oracle continuations over a fixed shared
input. The first continuation runs over `ctx₁`, producing intermediate outputs.
The suffix continuation is indexed by the ambient spine `⟨shared, tr₁⟩`, so the
shared input together with the prefix transcript determines the fixed protocol
context for the second stage. -/
def comp {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {oracleDeco₁ : (shared : SharedIn) → OracleDecoration (ctx₁ shared) (roles₁ shared)}
    {StmtMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → Type}
    {OStatementMid :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      ιₛₘ shared tr₁ → Type}
    [∀ shared tr₁ i, OracleInterface (OStatementMid shared tr₁ i)]
    {WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {oracleDeco₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      OracleDecoration (ctx₂ shared tr₁) (roles₂ shared tr₁)}
    {StmtOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → ιₛₒ shared tr₁ tr₂ → Type}
    [∀ shared tr₁ tr₂ i, OracleInterface (OStatementOut shared tr₁ tr₂ i)]
    {WitOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type}
    (reduction1 : OracleReduction oSpec SharedIn
      ctx₁ roles₁ oracleDeco₁ StatementIn OStatementIn WitnessIn
      StmtMid OStatementMid WitMid)
    (reduction2 : OracleReduction oSpec
      (Sigma fun shared : SharedIn => Spec.Transcript (ctx₁ shared))
      (fun st => ctx₂ st.1 st.2)
      (fun st => roles₂ st.1 st.2)
      (fun st => oracleDeco₂ st.1 st.2)
      (fun st => StmtMid st.1 st.2)
      (fun st => OStatementMid st.1 st.2)
      (fun st => WitMid st.1 st.2)
      (fun st tr₂ => StmtOut st.1 st.2 tr₂)
      (fun st tr₂ => OStatementOut st.1 st.2 tr₂)
      (fun st tr₂ => WitOut st.1 st.2 tr₂)) :
    OracleReduction oSpec SharedIn
      (fun shared => (ctx₁ shared).append (ctx₂ shared))
      (fun shared => Spec.Decoration.append (roles₁ shared) (roles₂ shared))
      (fun shared => Role.Refine.append (oracleDeco₁ shared) (fun tr₁ => oracleDeco₂ shared tr₁))
      StatementIn OStatementIn WitnessIn
      (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared))
      (fun shared tr =>
        liftAppendOracleFamily
          (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared) tr)
      (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared))
    where
  prover shared sWithOracles w := do
    let strat₁ ← reduction1.prover shared sWithOracles w
    let strat ← Spec.Strategy.compWithRoles strat₁
      (fun tr₁ midOut => do
        let reduction2Fixed := freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩
        let midStmt :
            StatementWithOracles
              (fun _ => StmtMid shared tr₁) (fun _ => OStatementMid shared tr₁) PUnit.unit :=
          ⟨midOut.stmt.stmt, midOut.stmt.oracleStmt⟩
        reduction2Fixed.prover PUnit.unit midStmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
        let splitOuter := Spec.Transcript.liftAppendProd
          (ctx₁ shared) (ctx₂ shared)
          (fun tr₁ tr₂ =>
            StatementWithOracles (fun _ => StmtOut shared tr₁ tr₂)
              (fun _ => OStatementOut shared tr₁ tr₂) PUnit.unit)
          (WitOut shared) tr out
        let splitStmtOracle := Spec.Transcript.unliftAppend
          (ctx₁ shared) (ctx₂ shared)
          (fun tr₁ tr₂ =>
            StatementWithOracles (fun _ => StmtOut shared tr₁ tr₂)
              (fun _ => OStatementOut shared tr₁ tr₂) PUnit.unit)
          tr splitOuter.1
        have htr :
            Spec.Transcript.append
              (ctx₁ shared) (ctx₂ shared)
              split.1 split.2 = tr := by
          simpa [split] using
            (Spec.Transcript.append_split
              (ctx₁ shared) (ctx₂ shared) tr)
        have stmtOut :
            Spec.Transcript.liftAppend
              (ctx₁ shared) (ctx₂ shared)
              (StmtOut shared) tr := by
          exact cast
            (congrArg
              (fun tr' =>
                Spec.Transcript.liftAppend
                  (ctx₁ shared) (ctx₂ shared)
                  (StmtOut shared) tr')
              htr)
            (Spec.Transcript.packAppend
              (ctx₁ shared) (ctx₂ shared)
              (StmtOut shared)
              split.1 split.2 splitStmtOracle.stmt)
        let oracleOut :
            OracleStatement
              (liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
                (ιₛₒ shared) (OStatementOut shared) tr) := by
          intro i
          exact splitStmtOracle.oracleStmt
            (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) tr i)
        ⟨⟨stmtOut, oracleOut⟩, splitOuter.2⟩)
      strat
  verifier shared {ιₐ} accSpec stmt := by
    let reduction1Fixed := promoteStatementToShared reduction1 shared
    simpa [toMonadDecoration_append] using
      (Spec.Counterpart.withMonads.append
        (reduction1.verifier shared accSpec stmt)
        (fun tr₁ sMid =>
          let reduction2Fixed := freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩
          retargetContinuationVerifier reduction1Fixed stmt tr₁
            (ctx₂ shared tr₁) (roles₂ shared tr₁) (oracleDeco₂ shared tr₁)
            (fun tr₂ => StmtOut shared tr₁ tr₂)
            ((accSpecAfter (ctx₁ shared) (roles₁ shared) (oracleDeco₁ shared)
              accSpec tr₁).2)
            (reduction2Fixed.verifier PUnit.unit
              ((accSpecAfter (ctx₁ shared) (roles₁ shared) (oracleDeco₁ shared)
                accSpec tr₁).2)
              sMid)))
  simulate shared tr := by
    intro qOut
    let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
    let tr₁ := split.1
    let tr₂ := split.2
    let reduction2Fixed := freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩
    let qSplit : ([OStatementOut shared tr₁ tr₂]ₒ).Domain :=
      splitLiftAppendOracleQuery
        (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared) tr qOut
    let routedSuffix :=
      simulateQ
        (liftAppendRightContext
          (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
          (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
          (od₁ := oracleDeco₁ shared) (od₂ := fun tr₁ => oracleDeco₂ shared tr₁)
          (OStmt := OStatementMid shared tr₁) tr₁ tr₂)
        (reduction2Fixed.simulate PUnit.unit tr₂ qSplit)
    let routed :=
      simulateQ
        (liftSimulatedMidOracleContextContinuation
          (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
          (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
          reduction1 shared tr₁ tr₂)
        routedSuffix
    let baseSpec := fun tr' =>
      [OStatementIn shared]ₒ +
        toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr₁ => oracleDeco₂ shared tr₁)) tr'
    let baseIdx := fun tr' =>
      (i : ιₛᵢ shared) × OracleInterface.Query (OStatementIn shared i) ⊕
        OracleDecoration.QueryHandle
          ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr₁ => oracleDeco₂ shared tr₁))
          tr'
    have routed' :
        let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
        OracleComp
          (baseSpec (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) split.1 split.2))
          (([OStatementOut shared split.1 split.2]ₒ).Range
            (splitLiftAppendOracleQuery
              (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared) tr qOut)) := by
      simpa [baseSpec, split, tr₁, tr₂, qSplit] using routed
    refine _root_.Interaction.OracleDecoration.collapseAppendOracleComp
      (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
      (Idx := baseIdx)
      (baseSpec := baseSpec)
      (ιₛ := ιₛₒ shared) (OStmt := OStatementOut shared) (tr := tr) (qOut := qOut) ?_
    exact routed'

/-- If the prefix reduction's simulated oracle output agrees with `midImpl`, and
the suffix continuation's simulated oracle output agrees with `outImpl` when run
against `midImpl`, then routing the suffix simulator through the appended
message context and then routing mid-oracle queries through the prefix reduction
agrees with `outImpl`. This is the low-level simulator-composition theorem used
to lift concrete reified oracle outputs through sequential composition. -/
theorem simulate_compFlat {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : StatementIn → Type}
    {OStmtIn : (s : StatementIn) → ιₛᵢ s → Type}
    [∀ s i, OracleInterface (OStmtIn s i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {oracleDeco₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {oracleDeco₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn
      ctx₁ roles₁ oracleDeco₁
      (fun _ => PUnit) OStmtIn (fun _ => WitnessIn)
      StmtMid OStmtMid WitMid)
    (reduction2 : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleReduction oSpec
        PUnit
        (fun _ => ctx₂ s tr₁)
        (fun _ => roles₂ s tr₁)
        (fun _ => oracleDeco₂ s tr₁)
        (fun _ => StmtMid s tr₁)
        (fun _ => OStmtMid s tr₁)
        (fun _ => WitMid s tr₁)
        (fun _ tr₂ => StmtOut s tr₁ tr₂)
        (fun _ tr₂ => OStmtOut s tr₁ tr₂)
        (fun _ tr₂ => WitOut s tr₁ tr₂))
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁))
    (oStmtIn : OracleStatement (OStmtIn s))
    (midImpl : QueryImpl [OStmtMid s tr₁]ₒ Id)
    (outImpl : QueryImpl [OStmtOut s tr₁ tr₂]ₒ Id)
    (hMid : ∀ i (q : OracleInterface.Query (OStmtMid s tr₁ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl (ctx₁ s) (roles₁ s) (oracleDeco₁ s) oStmtIn tr₁)
        (reduction1.simulate s tr₁ ⟨i, q⟩) = pure (midImpl ⟨i, q⟩))
    (hOut : ∀ i (q : OracleInterface.Query (OStmtOut s tr₁ tr₂ i)),
      simulateQ
        (QueryImpl.add midImpl
          (OracleDecoration.answerQuery (ctx₂ s tr₁) (roles₂ s tr₁) (oracleDeco₂ s tr₁) tr₂))
        ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩) = pure (outImpl ⟨i, q⟩)) :
    ∀ i (q : OracleInterface.Query (OStmtOut s tr₁ tr₂ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
          oStmtIn
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
        (simulateQ
          (liftSimulatedMidOracleContext
            (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
            (StmtMid := StmtMid) (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
            (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
            reduction1 s tr₁ tr₂)
          (simulateQ
            (liftAppendRightContext
              (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
              (roles₁ := roles₁ s) (roles₂ := roles₂ s)
              (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
              (OStmt := OStmtMid s tr₁) tr₁ tr₂)
            ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩))) =
      pure (outImpl ⟨i, q⟩) := by
  intro i q
  rw [← QueryImpl.simulateQ_compose]
  change
    simulateQ
      (fun q =>
        simulateQ
          (OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
            oStmtIn
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
          (liftSimulatedMidOracleContext
            (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
            (StmtMid := StmtMid) (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
            (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
            reduction1 s tr₁ tr₂ q))
      (simulateQ
        (liftAppendRightContext
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
          (roles₁ := roles₁ s) (roles₂ := roles₂ s)
          (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
          (OStmt := OStmtMid s tr₁) tr₁ tr₂)
        ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩)) =
      pure (outImpl ⟨i, q⟩)
  rw [simulateQ_ext
    (simulateQ_liftSimulatedMidOracleContext_eq
      (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
      (StmtMid := StmtMid) (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
      (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
      reduction1 s tr₁ tr₂ oStmtIn midImpl hMid)]
  rw [← QueryImpl.simulateQ_compose]
  change
    simulateQ
      (fun q =>
        simulateQ
          (QueryImpl.add midImpl
            (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
              (Spec.Decoration.append (roles₁ s) (roles₂ s))
              (Role.Refine.append (oracleDeco₁ s) (fun tr => oracleDeco₂ s tr))
              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
          (liftAppendRightContext
            (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
            (roles₁ := roles₁ s) (roles₂ := roles₂ s)
            (od₁ := oracleDeco₁ s) (od₂ := fun tr => oracleDeco₂ s tr)
            (OStmt := OStmtMid s tr₁) tr₁ tr₂ q))
      ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩) =
      pure (outImpl ⟨i, q⟩)
  rw [simulateQ_ext
    (simulateQ_liftAppendRightContext_withImpl_eq
      (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
      (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
      (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
      s tr₁ tr₂ midImpl)]
  simpa using hOut i q

/-- Public append-transcript bridge for binary oracle composition: if the split
simulators for the two stages agree with `midImpl` and `outImpl`, then a fused
query to `OracleReduction.comp reduction1 reduction2` is answered by routing to
the split query and repackaging the split answer through
`answerSplitLiftAppendQuery`. -/
theorem simulate_comp {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {StatementIn : SharedIn → Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {oracleDeco₁ : (shared : SharedIn) → OracleDecoration (ctx₁ shared) (roles₁ shared)}
    {StatementMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → Type}
    {OStatementMid :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → ιₛₘ shared tr₁ → Type}
    [∀ shared tr₁ i, OracleInterface (OStatementMid shared tr₁ i)]
    {WitnessMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {oracleDeco₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      OracleDecoration (ctx₂ shared tr₁) (roles₂ shared tr₁)}
    {StatementOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → ιₛₒ shared tr₁ tr₂ → Type}
    [∀ shared tr₁ tr₂ i, OracleInterface (OStatementOut shared tr₁ tr₂ i)]
    {WitnessOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type}
    (reduction1 : OracleReduction oSpec SharedIn
      ctx₁ roles₁ oracleDeco₁
      StatementIn OStatementIn WitnessIn
      StatementMid OStatementMid WitnessMid)
    (reduction2 : OracleReduction oSpec
      (Sigma fun shared : SharedIn => Spec.Transcript (ctx₁ shared))
      (fun st => ctx₂ st.1 st.2)
      (fun st => roles₂ st.1 st.2)
      (fun st => oracleDeco₂ st.1 st.2)
      (fun st => StatementMid st.1 st.2)
      (fun st => OStatementMid st.1 st.2)
      (fun st => WitnessMid st.1 st.2)
      (fun st tr₂ => StatementOut st.1 st.2 tr₂)
      (fun st tr₂ => OStatementOut st.1 st.2 tr₂)
      (fun st tr₂ => WitnessOut st.1 st.2 tr₂))
    (shared : SharedIn)
    (_stmt : StatementIn shared)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared)))
    (midImpl :
      let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
      QueryImpl [OStatementMid shared split.1]ₒ Id)
    (outImpl :
      let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
      QueryImpl [OStatementOut shared split.1 split.2]ₒ Id)
    (hMid :
      let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
      ∀ i (q : OracleInterface.Query (OStatementMid shared split.1 i)),
      simulateQ
        (OracleDecoration.oracleContextImpl
          (ctx₁ shared) (roles₁ shared) (oracleDeco₁ shared) oStatementIn split.1)
        (reduction1.simulate shared split.1 ⟨i, q⟩) = pure (midImpl ⟨i, q⟩))
  (hOut :
      let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
      ∀ i (q : OracleInterface.Query (OStatementOut shared split.1 split.2 i)),
      simulateQ
        (QueryImpl.add midImpl
          (OracleDecoration.answerQuery
            (ctx₂ shared split.1) (roles₂ shared split.1) (oracleDeco₂ shared split.1) split.2))
        ((freezeSharedToPUnit reduction2 ⟨shared, split.1⟩).simulate PUnit.unit split.2 ⟨i, q⟩) =
          pure (outImpl ⟨i, q⟩)) :
    ∀ (qOut :
      ([liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
        (ιₛₒ shared) (OStatementOut shared)
        tr]ₒ).Domain),
      simulateQ
        (OracleDecoration.oracleContextImpl
          ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
          oStatementIn tr)
        ((OracleReduction.comp reduction1 reduction2).simulate shared
          tr qOut) =
      answerSplitLiftAppendQuery
        (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared)
        tr qOut
        (outImpl (splitLiftAppendOracleQuery
          (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared) tr qOut)) := by
  intro qOut
  let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
  let tr₁ := split.1
  let tr₂ := split.2
  let qSplit :=
    splitLiftAppendOracleQuery
      (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared) tr qOut
  let oracleCtx :=
    OracleDecoration.oracleContextImpl
      ((ctx₁ shared).append (ctx₂ shared))
      (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
      (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
      oStatementIn tr
  let routedRaw :=
    simulateQ
      (liftSimulatedMidOracleContextContinuation
        (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
        (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
        reduction1 shared tr₁ tr₂)
      (simulateQ
        (liftAppendRightContext
          (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
          (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
          (od₁ := oracleDeco₁ shared) (od₂ := fun tr => oracleDeco₂ shared tr)
          (OStmt := OStatementMid shared tr₁) tr₁ tr₂)
        ((freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩).simulate PUnit.unit tr₂ qSplit))
  let baseSpec := fun tr' =>
    [OStatementIn shared]ₒ +
      toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
        (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
        (Role.Refine.append (oracleDeco₁ shared) (fun tr₁ => oracleDeco₂ shared tr₁)) tr'
  let baseIdx := fun tr' =>
    (i : ιₛᵢ shared) × OracleInterface.Query (OStatementIn shared i) ⊕
      OracleDecoration.QueryHandle
        ((ctx₁ shared).append (ctx₂ shared))
        (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
        (Role.Refine.append (oracleDeco₁ shared) (fun tr₁ => oracleDeco₂ shared tr₁))
        tr'
  let oracleCtxSplit :
      QueryImpl (baseSpec (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) Id :=
    cast
      (by
        have htr : Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂ = tr := by
          simpa [split, tr₁, tr₂] using
            (Spec.Transcript.append_split (ctx₁ shared) (ctx₂ shared) tr)
        simpa [baseSpec] using
          (congrArg (fun tr' => QueryImpl (baseSpec tr') Id) htr).symm)
      oracleCtx
  have htrAppend :
      Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂ = tr := by
    simpa [split, tr₁, tr₂] using
      (Spec.Transcript.append_split (ctx₁ shared) (ctx₂ shared) tr)
  have hMid' :
      ∀ i (q : OracleInterface.Query (OStatementMid shared tr₁ i)),
        simulateQ
          (OracleDecoration.oracleContextImpl
            (ctx₁ shared) (roles₁ shared) (oracleDeco₁ shared) oStatementIn tr₁)
          (reduction1.simulate shared tr₁ ⟨i, q⟩) = pure (midImpl ⟨i, q⟩) := by
    simpa [split, tr₁, tr₂] using hMid
  have hOut' :
      ∀ i (q : OracleInterface.Query (OStatementOut shared tr₁ tr₂ i)),
        simulateQ
          (QueryImpl.add midImpl
            (OracleDecoration.answerQuery
              (ctx₂ shared tr₁) (roles₂ shared tr₁) (oracleDeco₂ shared tr₁) tr₂))
          ((freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩).simulate PUnit.unit tr₂ ⟨i, q⟩) =
            pure (outImpl ⟨i, q⟩) := by
    simpa [split, tr₁, tr₂] using hOut
  have hRoutedDirect :
      simulateQ
        (OracleDecoration.oracleContextImpl
          ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
          oStatementIn
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
        routedRaw = outImpl qSplit := by
    rw [← QueryImpl.simulateQ_compose]
    change
      simulateQ
        (fun q =>
          simulateQ
            (OracleDecoration.oracleContextImpl
              ((ctx₁ shared).append (ctx₂ shared))
              (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
              (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
              oStatementIn
              (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
            (liftSimulatedMidOracleContextContinuation
              (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
              (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
              reduction1 shared tr₁ tr₂ q))
        (simulateQ
          (liftAppendRightContext
            (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
            (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
            (od₁ := oracleDeco₁ shared) (od₂ := fun tr => oracleDeco₂ shared tr)
            (OStmt := OStatementMid shared tr₁) tr₁ tr₂)
          ((freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩).simulate PUnit.unit tr₂ qSplit)) =
        outImpl qSplit
    rw [simulateQ_ext
      (simulateQ_liftSimulatedMidOracleContextContinuation_eq
        (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
        (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
        reduction1 shared tr₁ tr₂ oStatementIn midImpl hMid')]
    rw [← QueryImpl.simulateQ_compose]
    change
      simulateQ
        (fun q =>
          simulateQ
            (QueryImpl.add midImpl
              (OracleDecoration.answerQuery
                ((ctx₁ shared).append (ctx₂ shared))
                (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
                (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
                (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)))
            (liftAppendRightContext
              (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
              (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
              (od₁ := oracleDeco₁ shared) (od₂ := fun tr => oracleDeco₂ shared tr)
              (OStmt := OStatementMid shared tr₁) tr₁ tr₂ q))
        ((freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩).simulate PUnit.unit tr₂ qSplit) =
        outImpl qSplit
    rw [simulateQ_ext
      (simulateQ_liftAppendRightContext_withImpl_eq
        (ctx₁ := ctx₁) (roles₁ := roles₁) (oracleDeco₁ := oracleDeco₁)
        (ctx₂ := ctx₂) (roles₂ := roles₂) (oracleDeco₂ := oracleDeco₂)
        (ιₛₘ := ιₛₘ) (OStmtMid := OStatementMid)
        shared tr₁ tr₂ midImpl)]
    simpa [qSplit] using hOut' qSplit.1 qSplit.2
  have hCtxCast :
      oracleCtxSplit =
        OracleDecoration.oracleContextImpl
          ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
          oStatementIn
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂) := by
    dsimp [oracleCtxSplit, oracleCtx, baseSpec]
    apply (cast_eq_iff_heq).2
    simpa using
      (congr_arg_heq
        (fun tr' =>
          OracleDecoration.oracleContextImpl
            ((ctx₁ shared).append (ctx₂ shared))
            (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
            (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
            oStatementIn tr')
        htrAppend.symm)
  have hRouted :
      simulateQ oracleCtxSplit routedRaw = outImpl qSplit := by
    rw [hCtxCast]
    exact hRoutedDirect
  have hPublic :
      simulateQ oracleCtx
        ((OracleReduction.comp reduction1 reduction2).simulate shared tr qOut) =
      answerSplitLiftAppendQuery
        (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared)
        tr qOut
        (simulateQ oracleCtxSplit routedRaw) := by
    simpa [OracleReduction.comp, split, tr₁, tr₂, qSplit, baseSpec, baseIdx,
      oracleCtx, oracleCtxSplit, routedRaw]
      using
        (simulateQ_collapseAppendOracleComp
          (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
          (Idx := baseIdx)
          (baseSpec := baseSpec)
          (ιₛ := ιₛₒ shared) (OStmt := OStatementOut shared)
          (tr := tr) (qOut := qOut)
          (impl := oracleCtx)
          routedRaw)
  calc
    simulateQ oracleCtx
        ((OracleReduction.comp reduction1 reduction2).simulate shared tr qOut) =
      answerSplitLiftAppendQuery
        (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared)
        tr qOut
        (simulateQ oracleCtxSplit routedRaw) := hPublic
    _ =
      answerSplitLiftAppendQuery
        (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared)
        tr qOut
        (outImpl qSplit) := by
        simpa [answerSplitLiftAppendQuery] using hRouted

end OracleReduction

end OracleDecoration

end Interaction

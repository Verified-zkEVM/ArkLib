/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Composition

open Interaction.TwoParty

/-!
# N-ary Chain Composition for Oracle.Spec

A `Spec.Chain n` is a self-contained recipe for an `n`-round oracle protocol:
at each level it carries the current round's `Oracle.Spec`, `RoleDeco`, and
`OracleDeco`, with a `PublicTranscript`-indexed continuation to the next level.
The chain is still only protocol shape. Stateful parties are modeled by the
composition combinators, which thread a caller-chosen state family indexed by
the remaining chain.

Converting to an `Oracle.Spec` via `Chain.toSpec` uses only `Oracle.Spec.append`.

## Main definitions

* `Oracle.Spec.Chain` — depth-indexed telescope: oracle spec + decorations +
  continuation.
* `Chain.toSpec` / `Chain.toRoles` / `Chain.toOracleDeco` — flatten a chain to a
  single `Oracle.Spec` with its decorations.
* `Chain.splitPublicTranscript` / `Chain.appendPublicTranscript` —
  `PublicTranscript` operations for the first round vs the rest.
* `Chain.outputFamily` — lift a family on remaining chains to a family on the
  flattened `PublicTranscript`.
* `Chain.Prover.RoundSteps` / `Chain.Verifier.RoundSteps` — per-node round
  handlers for one concrete chain, avoiding unnecessary quantification over
  arbitrary chains.
* `Chain.Prover.comp` / `Chain.Verifier.comp` — compose concrete-chain prover
  strategies / verifier counterparts along the chain.
* `Oracle.Reduction.ofChain` — compose concrete-chain steps into a full
  `Oracle.Reduction`.

## Design notes

This mirrors the non-oracle `Spec.RoleChain` and `Reduction.ofChain`
(in `Interaction/Reduction.lean`), but uses `Oracle.Spec` throughout:

- Continuation depends on `PublicTranscript` (not full `Transcript`).
- Uses `Prover.compAux` / `Verifier.compAux` / `Counterpart.liftAcc` from
  `Oracle/Composition.lean` as the binary step.
- Per-node steps may produce the next state for the remaining chain.
- Final output types are computed from the full `PublicTranscript` via
  `Chain.outputFamily`.

## Three composition mechanisms

| Mechanism | State? | Transcript-dependent? | Use when |
|---|---|---|---|
| `Oracle.Spec.append` + `Reduction.comp` | No | Yes | Binary composition |
| `Oracle.Spec.Chain.Prover.comp` | Yes | Yes | N-ary prover composition |
| `Oracle.Spec.Chain.Verifier.comp` | Yes | Yes | N-ary verifier composition |
-/

open OracleComp OracleSpec

namespace Interaction.Oracle

namespace Spec

/-! ## Chain type -/

/-- A self-contained recipe for an `n`-round oracle protocol. At each level,
carries the current round's `Oracle.Spec`, `RoleDeco`, `OracleDeco`, and a
`PublicTranscript`-indexed continuation to the remaining rounds. -/
def Chain : Nat → Type 1
  | 0 => PUnit
  | n + 1 => (spec : Oracle.Spec) × (_ : RoleDeco spec) ×
             (_ : OracleDeco spec) × (PublicTranscript spec → Chain n)

namespace Chain

/-! ## Flattening -/

/-- Flatten a chain into a concrete `Oracle.Spec` via iterated `append`. -/
def toSpec : (n : Nat) → Chain n → Oracle.Spec
  | 0, _ => .done
  | n + 1, ⟨spec, _, _, cont⟩ => spec.append (fun pt => toSpec n (cont pt))

/-- Flatten the role decorations along a chain. -/
def toRoles : (n : Nat) → (c : Chain n) → RoleDeco (toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, roles, _, cont⟩ =>
      RoleDeco.append spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))

/-- Flatten the oracle decorations along a chain. -/
def toOracleDeco : (n : Nat) → (c : Chain n) → OracleDeco (toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, _, od, cont⟩ =>
      OracleDeco.append spec (fun pt => toSpec n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))

@[simp] theorem toSpec_zero (c : Chain 0) : toSpec 0 c = .done := rfl

theorem toSpec_succ {n : Nat} (spec : Oracle.Spec)
    (roles : RoleDeco spec) (od : OracleDeco spec)
    (cont : PublicTranscript spec → Chain n) :
    toSpec (n + 1) ⟨spec, roles, od, cont⟩ =
      spec.append (fun pt => toSpec n (cont pt)) := rfl

/-! ## Constant chains -/

/-- Constant oracle rounds: the same oracle spec, roles, and oracle decoration
at every level, with continuation independent of the public transcript. -/
def replicate (spec : Oracle.Spec) (roles : RoleDeco spec) (od : OracleDeco spec) :
    (n : Nat) → Chain n
  | 0 => ⟨⟩
  | n + 1 => ⟨spec, roles, od, fun _ => replicate spec roles od n⟩

/-! ## PublicTranscript operations -/

/-- Split a `PublicTranscript` of a flattened `(n+1)`-round chain into the first
round's public transcript and the remainder. -/
def splitPublicTranscript (n : Nat) (c : Chain (n + 1)) :
    PublicTranscript (toSpec (n + 1) c) →
    (pt₁ : PublicTranscript c.1) × PublicTranscript (toSpec n (c.2.2.2 pt₁)) :=
  PublicTranscript.split c.1 (fun pt => toSpec n (c.2.2.2 pt))

/-- Combine a first-round public transcript with a remainder. -/
def appendPublicTranscript (n : Nat) (c : Chain (n + 1))
    (pt₁ : PublicTranscript c.1) (pt₂ : PublicTranscript (toSpec n (c.2.2.2 pt₁))) :
    PublicTranscript (toSpec (n + 1) c) :=
  PublicTranscript.append c.1 (fun pt => toSpec n (c.2.2.2 pt)) pt₁ pt₂

@[simp]
theorem splitPublicTranscript_appendPublicTranscript (n : Nat) (c : Chain (n + 1))
    (pt₁ : PublicTranscript c.1) (pt₂ : PublicTranscript (toSpec n (c.2.2.2 pt₁))) :
    splitPublicTranscript n c (appendPublicTranscript n c pt₁ pt₂) = ⟨pt₁, pt₂⟩ :=
  PublicTranscript.split_append _ _ _ _

/-! ## Output family -/

/-- Lift a family on remaining chains to a family on `PublicTranscript` of the
flattened `Oracle.Spec`. At `Chain 0`, returns `Family ⟨⟩`. At `Chain (n + 1)`,
uses `PublicTranscript.liftAppend` to expose the native append structure of the
flattened public transcript. -/
def outputFamily
    (Family : {n : Nat} → Chain n → Type) :
    (n : Nat) → (c : Chain n) → PublicTranscript (toSpec n c) → Type
  | 0, c, _ => Family c
  | n + 1, ⟨spec, _, _, cont⟩, pt =>
      PublicTranscript.liftAppend spec (fun pt₁ => toSpec n (cont pt₁))
        (fun pt₁ pt₂ => outputFamily Family n (cont pt₁) pt₂) pt

/-- Extract the terminal value selected by a full public transcript.

This is the canonical eliminator for `outputFamily`: callers that only care
about the final state no longer need to hand-roll recursive splitting of the
flattened public transcript. -/
def terminalOutput
    (Family : {n : Nat} → Chain n → Type) :
    (n : Nat) → (c : Chain n) →
      (pt : PublicTranscript (toSpec n c)) →
        outputFamily Family n c pt → Family (n := 0) ⟨⟩
  | 0, _, _, out => out
  | n + 1, ⟨spec, _, _, cont⟩, pt, out =>
      let split := PublicTranscript.split spec (fun pt₁ => toSpec n (cont pt₁)) pt
      terminalOutput Family n (cont split.1) split.2
        (PublicTranscript.unliftAppend spec (fun pt₁ => toSpec n (cont pt₁))
          (fun pt₁ pt₂ => outputFamily Family n (cont pt₁) pt₂) pt out)

/-! ## Prover composition -/

namespace Prover

/-- Per-node prover handlers for a concrete `Chain`.

The handlers follow the actual continuation tree of one chain, so a protocol
does not need to provide a single round-step function that works for every
possible `Chain (k + 1)`. -/
def RoundSteps {m : Type → Type} [Monad m]
    (State : {k : Nat} → Chain k → Type) :
    (n : Nat) → (c : Chain n) → Type 1
  | 0, _ => PUnit
  | n + 1, c =>
      ((state : State c) →
        m
          (Interaction.Spec.StrategyOver (pairedSyntax m)
            Interaction.TwoParty.Participant.focal
            c.1.toInteractionSpec (c.1.toSpecRoles c.2.1)
            (fun tr => State (c.2.2.2 (c.1.projectPublic tr))))) ×
      ((pt : PublicTranscript c.1) → RoundSteps (m := m) State n (c.2.2.2 pt))

/-- Compose prover handlers attached to one concrete chain. -/
def comp
    {m : Type → Type} [Monad m]
    (State : {k : Nat} → Chain k → Type) :
    (n : Nat) → (c : Chain n) → State c → RoundSteps (m := m) State n c →
    m
      (Interaction.Spec.StrategyOver (pairedSyntax m)
        Interaction.TwoParty.Participant.focal
        (toSpec n c).toInteractionSpec
        ((toSpec n c).toSpecRoles (toRoles n c))
        (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr)))
  | 0, _, state, _ => pure state
  | n + 1, ⟨spec, roles, _od, cont⟩, state, steps => do
      let strat ← steps.1 state
      Prover.compAux spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        (Mid := fun tr₁ => State (cont (spec.projectPublic tr₁)))
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁) pt₂)
        strat
        (fun tr₁ state' =>
          comp (m := m) State n (cont (spec.projectPublic tr₁)) state'
            (steps.2 (spec.projectPublic tr₁)))

end Prover

/-! ## Verifier composition -/

namespace Verifier

/-- Per-node verifier handlers for a concrete `Chain`.

This is the verifier analogue of `Prover.RoundSteps`: every continuation carries
the handlers for that exact continuation, so callers do not need to define a
round verifier for unrelated chain shapes. -/
def RoundSteps
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (State : {k : Nat} → Chain k → Type) :
    (n : Nat) → (c : Chain n) → Type 1
  | 0, _ => PUnit
  | n + 1, c =>
      ((state : State c) →
        Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
          c.1.toInteractionSpec
          (RoleDecoration.withMonads (c.1.toSpecRoles c.2.1)
            (c.1.toMonadDecoration oSpec OStmtIn c.2.1 c.2.2.1 []ₒ))
          (fun tr => State (c.2.2.2 (c.1.projectPublic tr)))) ×
      ((pt : PublicTranscript c.1) → RoundSteps (oSpec := oSpec) (OStmtIn := OStmtIn)
        State n (c.2.2.2 pt))

/-- Compose verifier handlers attached to one concrete chain. -/
def comp
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (State : {k : Nat} → Chain k → Type) :
    (n : Nat) → (c : Chain n) → State c → RoundSteps (oSpec := oSpec)
      (OStmtIn := OStmtIn) State n c →
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      (toSpec n c).toInteractionSpec
      (RoleDecoration.withMonads ((toSpec n c).toSpecRoles (toRoles n c))
        ((toSpec n c).toMonadDecoration oSpec OStmtIn (toRoles n c) (toOracleDeco n c) []ₒ))
      (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr))
  | 0, _, state, _ => state
  | n + 1, ⟨spec, roles, od, cont⟩, state, steps =>
      Verifier.compAux (OStmtIn := OStmtIn)
        spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))
        []ₒ
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁) pt₂)
        (steps.1 state)
        (fun tr₁ state' =>
          let pt₁ := spec.projectPublic tr₁
          let accSpec' := (Spec.accumulatedSpec spec od tr₁ []ₒ).2
          Counterpart.liftAcc
            (toSpec n (cont pt₁)) (toRoles n (cont pt₁)) (toOracleDeco n (cont pt₁))
            []ₒ accSpec' (fun q => q.elim)
            (comp (oSpec := oSpec) (OStmtIn := OStmtIn)
              State n (cont pt₁) state' (steps.2 pt₁)))

end Verifier

end Chain

end Spec

/-! ## Reduction.ofChain -/

/-- Compose per-node prover and verifier handlers attached to one concrete
`Chain` into a full `Oracle.Reduction`.

The prover and verifier each receive their own state family indexed by the
remaining chain. Round steps consume the current state and return the state for
the public-transcript-selected continuation. At the end of the chain, caller
provided result functions turn the terminal prover state into honest prover
outputs, and the terminal verifier state into the verifier's local output
statement. -/
def Reduction.ofChain
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {WitnessIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {n : Nat}
    {c : SharedIn → Spec.Chain n}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) →
        (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
          ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    (ProverState : (shared : SharedIn) → {k : Nat} → Spec.Chain k → Type)
    (VerifierState : (shared : SharedIn) → {k : Nat} → Spec.Chain k → Type)
    (proverInit : (shared : SharedIn) →
      StatementWithOracles StatementIn OStatementIn shared → WitnessIn shared →
        ProverState shared (c shared))
    (verifierInit : (shared : SharedIn) →
      StatementIn shared → VerifierState shared (c shared))
    (proverSteps : (shared : SharedIn) →
      Spec.Chain.Prover.RoundSteps (m := OracleComp oSpec) (ProverState shared) n (c shared))
    (verifierSteps : (shared : SharedIn) →
      Spec.Chain.Verifier.RoundSteps (oSpec := oSpec) (OStmtIn := OStatementIn shared)
        (VerifierState shared) n (c shared))
    (proverStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        Spec.Chain.outputFamily (ProverState shared) n (c shared) pt →
        StatementOut shared pt)
    (verifierStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        Spec.Chain.outputFamily (VerifierState shared) n (c shared) pt →
        StatementOut shared pt)
    (oStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        Spec.Chain.outputFamily (ProverState shared) n (c shared) pt →
        ∀ i, OStatementOut shared pt i)
    (witResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        Spec.Chain.outputFamily (ProverState shared) n (c shared) pt →
        WitnessOut shared pt)
    (simulate : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        QueryImpl [OStatementOut shared pt]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Spec.Chain.toSpec n (c shared)).toOracleSpec
                (Spec.Chain.toOracleDeco n (c shared)) pt))) :
    Reduction oSpec SharedIn
      (fun shared => Spec.Chain.toSpec n (c shared))
      (fun shared => Spec.Chain.toRoles n (c shared))
      (fun shared => Spec.Chain.toOracleDeco n (c shared))
      StatementIn OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut where
  prover shared sWithOracles w := do
    let strat ← Spec.Chain.Prover.comp (ProverState shared)
      n (c shared) (proverInit shared sWithOracles w) (proverSteps shared)
    let strat' :=
      Interaction.TwoParty.Focal.mapOutput
        (fun tr proverState =>
          let pt := (Spec.Chain.toSpec n (c shared)).projectPublic tr
          (⟨⟨proverStmtResult shared pt proverState,
                oStmtResult shared pt proverState⟩,
              witResult shared pt proverState⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => StatementOut shared pt)
                (fun _ => OStatementOut shared pt) shared)
              (WitnessOut shared pt)))
        strat
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (Spec.Chain.toSpec n (c shared)).toInteractionSpec
        ((Spec.Chain.toSpec n (c shared)).toSpecRoles (Spec.Chain.toRoles n (c shared)))
        strat'
  verifier := {
    toFun := fun shared stmtIn =>
      Interaction.Spec.ShapeOver.mapOutput counterpartMonadicShape
        (agent := PUnit.unit)
        (spec := (Spec.Chain.toSpec n (c shared)).toInteractionSpec)
        (ctxs := RoleDecoration.withMonads
          ((Spec.Chain.toSpec n (c shared)).toSpecRoles (Spec.Chain.toRoles n (c shared)))
          ((Spec.Chain.toSpec n (c shared)).toMonadDecoration oSpec (OStatementIn shared)
            (Spec.Chain.toRoles n (c shared)) (Spec.Chain.toOracleDeco n (c shared)) []ₒ))
        (fun tr verifierState =>
          let pt := (Spec.Chain.toSpec n (c shared)).projectPublic tr
          verifierStmtResult shared pt verifierState)
        (Spec.Chain.Verifier.comp (oSpec := oSpec)
          (OStmtIn := OStatementIn shared) (VerifierState shared)
          n (c shared) (verifierInit shared stmtIn) (verifierSteps shared))
    simulate := simulate
  }

namespace Spec

/-! ## Indexed chains -/

/-- A chain whose nodes are indexed by a caller-chosen protocol position.

Unlike `Chain n`, an indexed chain remembers more than the number of remaining
nodes. This is useful for heterogeneous protocols whose round-local state is
naturally indexed by a phase position: each continuation returns the next
position together with the remaining chain at that position. -/
def IndexedChain (Idx : Type) : Nat → Idx → Type 1
  | 0, _ => PUnit
  | n + 1, _ =>
      (spec : Oracle.Spec) × (_ : RoleDeco spec) ×
      (_ : OracleDeco spec) ×
      (PublicTranscript spec → (idx' : Idx) × IndexedChain Idx n idx')

namespace IndexedChain

/-- Flatten an indexed chain into a concrete `Oracle.Spec`. -/
def toSpec {Idx : Type} :
    (n : Nat) → {idx : Idx} → IndexedChain Idx n idx → Oracle.Spec
  | 0, _, _ => .done
  | n + 1, _, ⟨spec, _, _, cont⟩ =>
      spec.append (fun pt => toSpec n (cont pt).2)

/-- Flatten role decorations along an indexed chain. -/
def toRoles {Idx : Type} :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) → RoleDeco (toSpec n c)
  | 0, _, _ => ⟨⟩
  | n + 1, _, ⟨spec, roles, _, cont⟩ =>
      RoleDeco.append spec (fun pt => toSpec n (cont pt).2)
        roles (fun pt => toRoles n (cont pt).2)

/-- Flatten oracle decorations along an indexed chain. -/
def toOracleDeco {Idx : Type} :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) → OracleDeco (toSpec n c)
  | 0, _, _ => ⟨⟩
  | n + 1, _, ⟨spec, _, od, cont⟩ =>
      OracleDeco.append spec (fun pt => toSpec n (cont pt).2)
        od (fun pt => toOracleDeco n (cont pt).2)

/-- Lift an index family to a family over full public transcripts. -/
def outputFamily {Idx : Type}
    (Family : Idx → Type) :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) →
      PublicTranscript (toSpec n c) → Type
  | 0, idx, _, _ => Family idx
  | n + 1, _, ⟨spec, _, _, cont⟩, pt =>
      PublicTranscript.liftAppend spec (fun pt₁ => toSpec n (cont pt₁).2)
        (fun pt₁ pt₂ => outputFamily Family n (cont pt₁).2 pt₂) pt

/-- Extract the terminal index and value selected by a full public transcript. -/
def terminalOutput {Idx : Type}
    (Family : Idx → Type) :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) →
      (pt : PublicTranscript (toSpec n c)) →
        outputFamily Family n c pt → (idx' : Idx) × Family idx'
  | 0, idx, _, _, out => ⟨idx, out⟩
  | n + 1, _, ⟨spec, _, _, cont⟩, pt, out =>
      let split := PublicTranscript.split spec (fun pt₁ => toSpec n (cont pt₁).2) pt
      terminalOutput Family n (cont split.1).2 split.2
        (PublicTranscript.unliftAppend spec (fun pt₁ => toSpec n (cont pt₁).2)
          (fun pt₁ pt₂ => outputFamily Family n (cont pt₁).2 pt₂) pt out)

namespace Prover

/-- Per-node prover handlers for an indexed chain. -/
def RoundSteps {Idx : Type} {m : Type → Type} [Monad m]
    (State : Idx → Type) :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) → Type 1
  | 0, _, _ => PUnit
  | n + 1, idx, c =>
      ((state : State idx) →
        m
          (Interaction.Spec.StrategyOver (pairedSyntax m)
            Interaction.TwoParty.Participant.focal
            c.1.toInteractionSpec (c.1.toSpecRoles c.2.1)
            (fun tr => State (c.2.2.2 (c.1.projectPublic tr)).1))) ×
      ((pt : PublicTranscript c.1) → RoundSteps (m := m) State n (c.2.2.2 pt).2)

/-- Compose prover handlers attached to one indexed chain. -/
def comp {Idx : Type}
    {m : Type → Type} [Monad m]
    (State : Idx → Type) :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) → State idx →
    RoundSteps (m := m) State n c →
    m
      (Interaction.Spec.StrategyOver (pairedSyntax m)
        Interaction.TwoParty.Participant.focal
        (toSpec n c).toInteractionSpec
        ((toSpec n c).toSpecRoles (toRoles n c))
        (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr)))
  | 0, _, _, state, _ => pure state
  | n + 1, _, ⟨spec, roles, _od, cont⟩, state, steps => do
      let strat ← steps.1 state
      Prover.compAux spec (fun pt => toSpec n (cont pt).2)
        roles (fun pt => toRoles n (cont pt).2)
        (Mid := fun tr₁ => State (cont (spec.projectPublic tr₁)).1)
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁).2 pt₂)
        strat
        (fun tr₁ state' =>
          comp (m := m) State n (cont (spec.projectPublic tr₁)).2 state'
            (steps.2 (spec.projectPublic tr₁)))

end Prover

namespace Verifier

/-- Per-node verifier handlers for an indexed chain. -/
def RoundSteps {Idx : Type}
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (State : Idx → Type) :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) → Type 1
  | 0, _, _ => PUnit
  | n + 1, idx, c =>
      ((state : State idx) →
        Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
          c.1.toInteractionSpec
          (RoleDecoration.withMonads (c.1.toSpecRoles c.2.1)
            (c.1.toMonadDecoration oSpec OStmtIn c.2.1 c.2.2.1 []ₒ))
          (fun tr => State (c.2.2.2 (c.1.projectPublic tr)).1)) ×
      ((pt : PublicTranscript c.1) → RoundSteps (oSpec := oSpec) (OStmtIn := OStmtIn)
        State n (c.2.2.2 pt).2)

/-- Compose verifier handlers attached to one indexed chain. -/
def comp {Idx : Type}
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (State : Idx → Type) :
    (n : Nat) → {idx : Idx} → (c : IndexedChain Idx n idx) → State idx →
    RoundSteps (oSpec := oSpec) (OStmtIn := OStmtIn) State n c →
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      (toSpec n c).toInteractionSpec
      (RoleDecoration.withMonads ((toSpec n c).toSpecRoles (toRoles n c))
        ((toSpec n c).toMonadDecoration oSpec OStmtIn (toRoles n c) (toOracleDeco n c) []ₒ))
      (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr))
  | 0, _, _, state, _ => state
  | n + 1, _, ⟨spec, roles, od, cont⟩, state, steps =>
      Verifier.compAux (OStmtIn := OStmtIn)
        spec (fun pt => toSpec n (cont pt).2)
        roles (fun pt => toRoles n (cont pt).2)
        od (fun pt => toOracleDeco n (cont pt).2)
        []ₒ
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁).2 pt₂)
        (steps.1 state)
        (fun tr₁ state' =>
          let pt₁ := spec.projectPublic tr₁
          let accSpec' := (Spec.accumulatedSpec spec od tr₁ []ₒ).2
          Counterpart.liftAcc
            (toSpec n (cont pt₁).2) (toRoles n (cont pt₁).2) (toOracleDeco n (cont pt₁).2)
            []ₒ accSpec' (fun q => q.elim)
            (comp (oSpec := oSpec) (OStmtIn := OStmtIn)
              State n (cont pt₁).2 state' (steps.2 pt₁)))

end Verifier

end IndexedChain

/-! ## Terminal-indexed chains -/

/-- An indexed chain with both its starting and terminal indices in the type.

`IndexedChain` is enough when the next round's state is indexed by the
transcript-selected successor. `PathChain` additionally records the terminal
index, so its terminal eliminator returns `Family finish` directly instead of
an existential terminal index. This is the right shape for protocols whose
final output type depends on the known last stage. -/
inductive PathChain (Idx : Type) : Nat → Idx → Idx → Type 1 where
  | nil {idx : Idx} : PathChain Idx 0 idx idx
  | cons {n : Nat} {idx finish : Idx}
      (spec : Oracle.Spec) (roles : RoleDeco spec) (od : OracleDeco spec)
      (nextIdx : PublicTranscript spec → Idx)
      (cont : (pt : PublicTranscript spec) → PathChain Idx n (nextIdx pt) finish) :
      PathChain Idx (n + 1) idx finish

namespace PathChain

/-- Flatten a terminal-indexed chain into a concrete `Oracle.Spec`. -/
def toSpec {Idx : Type} :
    (n : Nat) → {idx finish : Idx} → PathChain Idx n idx finish → Oracle.Spec
  | 0, _, _, .nil => .done
  | n + 1, _, _, .cons spec _ _ _ cont =>
      spec.append (fun pt => toSpec n (cont pt))

/-- Flatten role decorations along a terminal-indexed chain. -/
def toRoles {Idx : Type} :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) → RoleDeco (toSpec n c)
  | 0, _, _, .nil => ⟨⟩
  | n + 1, _, _, .cons spec roles _ _ cont =>
      RoleDeco.append spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))

/-- Flatten oracle decorations along a terminal-indexed chain. -/
def toOracleDeco {Idx : Type} :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) → OracleDeco (toSpec n c)
  | 0, _, _, .nil => ⟨⟩
  | n + 1, _, _, .cons spec _ od _ cont =>
      OracleDeco.append spec (fun pt => toSpec n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))

/-- Lift an index family to a family over full public transcripts, with a known
terminal index. -/
def outputFamily {Idx : Type}
    (Family : Idx → Type) :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) →
      PublicTranscript (toSpec n c) → Type
  | 0, _, finish, .nil, _ => Family finish
  | n + 1, _, _, .cons spec _ _ _ cont, pt =>
      PublicTranscript.liftAppend spec (fun pt₁ => toSpec n (cont pt₁))
        (fun pt₁ pt₂ => outputFamily Family n (cont pt₁) pt₂) pt

/-- Extract the terminal value selected by a full public transcript. -/
def terminalOutput {Idx : Type}
    (Family : Idx → Type) :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) →
      (pt : PublicTranscript (toSpec n c)) →
        outputFamily Family n c pt → Family finish
  | 0, _, _, .nil, _, out => out
  | n + 1, _, _, .cons spec _ _ _ cont, pt, out =>
      let split := PublicTranscript.split spec (fun pt₁ => toSpec n (cont pt₁)) pt
      terminalOutput Family n (cont split.1) split.2
        (PublicTranscript.unliftAppend spec (fun pt₁ => toSpec n (cont pt₁))
          (fun pt₁ pt₂ => outputFamily Family n (cont pt₁) pt₂) pt out)

namespace Prover

/-- Per-node prover handlers for a terminal-indexed chain. -/
def RoundSteps {Idx : Type} {m : Type → Type} [Monad m]
    (State : Idx → Type) :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) → Type 1
  | 0, _, _, .nil => PUnit
  | n + 1, idx, _, .cons spec roles _ nextIdx cont =>
      ((state : State idx) →
        m
          (Interaction.Spec.StrategyOver (pairedSyntax m)
            Interaction.TwoParty.Participant.focal
            spec.toInteractionSpec (spec.toSpecRoles roles)
            (fun tr => State (nextIdx (spec.projectPublic tr))))) ×
      ((pt : PublicTranscript spec) → RoundSteps (m := m) State n (cont pt))

/-- Compose prover handlers attached to one terminal-indexed chain. -/
def comp {Idx : Type}
    {m : Type → Type} [Monad m]
    (State : Idx → Type) :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) → State idx →
    RoundSteps (m := m) State n c →
    m
      (Interaction.Spec.StrategyOver (pairedSyntax m)
        Interaction.TwoParty.Participant.focal
        (toSpec n c).toInteractionSpec
        ((toSpec n c).toSpecRoles (toRoles n c))
        (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr)))
  | 0, _, _, .nil, state, _ => pure state
  | n + 1, _, _, .cons spec roles _ nextIdx cont, state, steps => do
      let strat ← steps.1 state
      Prover.compAux spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        (Mid := fun tr₁ => State (nextIdx (spec.projectPublic tr₁)))
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁) pt₂)
        strat
        (fun tr₁ state' =>
          comp (m := m) State n (cont (spec.projectPublic tr₁)) state'
            (steps.2 (spec.projectPublic tr₁)))

end Prover

namespace Verifier

/-- Per-node verifier handlers for a terminal-indexed chain. -/
def RoundSteps {Idx : Type}
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (State : Idx → Type) :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) → Type 1
  | 0, _, _, .nil => PUnit
  | n + 1, idx, _, .cons spec roles od nextIdx cont =>
      ((state : State idx) →
        Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
          spec.toInteractionSpec
          (RoleDecoration.withMonads (spec.toSpecRoles roles)
            (spec.toMonadDecoration oSpec OStmtIn roles od []ₒ))
          (fun tr => State (nextIdx (spec.projectPublic tr)))) ×
      ((pt : PublicTranscript spec) → RoundSteps (oSpec := oSpec) (OStmtIn := OStmtIn)
        State n (cont pt))

/-- Compose verifier handlers attached to one terminal-indexed chain. -/
def comp {Idx : Type}
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (State : Idx → Type) :
    (n : Nat) → {idx finish : Idx} → (c : PathChain Idx n idx finish) → State idx →
    RoundSteps (oSpec := oSpec) (OStmtIn := OStmtIn) State n c →
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      (toSpec n c).toInteractionSpec
      (RoleDecoration.withMonads ((toSpec n c).toSpecRoles (toRoles n c))
        ((toSpec n c).toMonadDecoration oSpec OStmtIn (toRoles n c) (toOracleDeco n c) []ₒ))
      (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr))
  | 0, _, _, .nil, state, _ => state
  | n + 1, _, _, .cons spec roles od _ cont, state, steps =>
      Verifier.compAux (OStmtIn := OStmtIn)
        spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))
        []ₒ
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁) pt₂)
        (steps.1 state)
        (fun tr₁ state' =>
          let pt₁ := spec.projectPublic tr₁
          let accSpec' := (Spec.accumulatedSpec spec od tr₁ []ₒ).2
          Counterpart.liftAcc
            (toSpec n (cont pt₁)) (toRoles n (cont pt₁)) (toOracleDeco n (cont pt₁))
            []ₒ accSpec' (fun q => q.elim)
            (comp (oSpec := oSpec) (OStmtIn := OStmtIn)
              State n (cont pt₁) state' (steps.2 pt₁)))

end Verifier

end PathChain

end Spec

/-! ## Reduction.ofIndexedChain -/

/-- Compose indexed-chain prover and verifier handlers into a full
`Oracle.Reduction`.

This is the indexed analogue of `Reduction.ofChain`: the chain carries a
caller-chosen protocol position at every continuation, and party state is
indexed by that position rather than only by the number of remaining rounds. -/
def Reduction.ofIndexedChain
    {Idx : Type}
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {WitnessIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {n : Nat}
    {idx : SharedIn → Idx}
    {c : (shared : SharedIn) → Spec.IndexedChain Idx n (idx shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) →
        (pt : Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared))) →
          ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared)) → Type}
    (ProverState : (shared : SharedIn) → Idx → Type)
    (VerifierState : (shared : SharedIn) → Idx → Type)
    (proverInit : (shared : SharedIn) →
      StatementWithOracles StatementIn OStatementIn shared → WitnessIn shared →
        ProverState shared (idx shared))
    (verifierInit : (shared : SharedIn) →
      StatementIn shared → VerifierState shared (idx shared))
    (proverSteps : (shared : SharedIn) →
      Spec.IndexedChain.Prover.RoundSteps (m := OracleComp oSpec)
        (ProverState shared) n (c shared))
    (verifierSteps : (shared : SharedIn) →
      Spec.IndexedChain.Verifier.RoundSteps (oSpec := oSpec) (OStmtIn := OStatementIn shared)
        (VerifierState shared) n (c shared))
    (proverStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared))) →
        Spec.IndexedChain.outputFamily (ProverState shared) n (c shared) pt →
        StatementOut shared pt)
    (verifierStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared))) →
        Spec.IndexedChain.outputFamily (VerifierState shared) n (c shared) pt →
        StatementOut shared pt)
    (oStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared))) →
        Spec.IndexedChain.outputFamily (ProverState shared) n (c shared) pt →
        ∀ i, OStatementOut shared pt i)
    (witResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared))) →
        Spec.IndexedChain.outputFamily (ProverState shared) n (c shared) pt →
        WitnessOut shared pt)
    (simulate : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.IndexedChain.toSpec n (c shared))) →
        QueryImpl [OStatementOut shared pt]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Spec.IndexedChain.toSpec n (c shared)).toOracleSpec
                (Spec.IndexedChain.toOracleDeco n (c shared)) pt))) :
    Reduction oSpec SharedIn
      (fun shared => Spec.IndexedChain.toSpec n (c shared))
      (fun shared => Spec.IndexedChain.toRoles n (c shared))
      (fun shared => Spec.IndexedChain.toOracleDeco n (c shared))
      StatementIn OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut where
  prover shared sWithOracles w := do
    let strat ← Spec.IndexedChain.Prover.comp (ProverState shared)
      n (c shared) (proverInit shared sWithOracles w) (proverSteps shared)
    let strat' :=
      Interaction.TwoParty.Focal.mapOutput
        (fun tr proverState =>
          let pt := (Spec.IndexedChain.toSpec n (c shared)).projectPublic tr
          (⟨⟨proverStmtResult shared pt proverState,
                oStmtResult shared pt proverState⟩,
              witResult shared pt proverState⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => StatementOut shared pt)
                (fun _ => OStatementOut shared pt)
                shared)
              (WitnessOut shared pt)))
        strat
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (Spec.IndexedChain.toSpec n (c shared)).toInteractionSpec
        ((Spec.IndexedChain.toSpec n (c shared)).toSpecRoles
          (Spec.IndexedChain.toRoles n (c shared)))
        strat'
  verifier := {
    toFun := fun shared stmtIn =>
      Interaction.Spec.ShapeOver.mapOutput counterpartMonadicShape
        (agent := PUnit.unit)
        (spec := (Spec.IndexedChain.toSpec n (c shared)).toInteractionSpec)
        (ctxs := RoleDecoration.withMonads
          ((Spec.IndexedChain.toSpec n (c shared)).toSpecRoles
            (Spec.IndexedChain.toRoles n (c shared)))
          ((Spec.IndexedChain.toSpec n (c shared)).toMonadDecoration oSpec (OStatementIn shared)
            (Spec.IndexedChain.toRoles n (c shared)) (Spec.IndexedChain.toOracleDeco n (c shared))
            []ₒ))
        (fun tr verifierState =>
          let pt := (Spec.IndexedChain.toSpec n (c shared)).projectPublic tr
          verifierStmtResult shared pt verifierState)
        (Spec.IndexedChain.Verifier.comp (oSpec := oSpec)
          (OStmtIn := OStatementIn shared) (VerifierState shared)
          n (c shared) (verifierInit shared stmtIn) (verifierSteps shared))
    simulate := simulate
  }

/-! ## Reduction.ofPathChain -/

/-- Compose terminal-indexed chain prover and verifier handlers into a full
`Oracle.Reduction`.

This is the endpoint-aware analogue of `Reduction.ofIndexedChain`: the chain
remembers both its starting index and its terminal index, so callers can use
`PathChain.terminalOutput` to recover a terminal state at the known final
position. -/
def Reduction.ofPathChain
    {Idx : Type}
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {WitnessIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {n : Nat}
    {idx finish : SharedIn → Idx}
    {c : (shared : SharedIn) → Spec.PathChain Idx n (idx shared) (finish shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) →
        (pt : Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared))) →
          ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared)) → Type}
    (ProverState : (shared : SharedIn) → Idx → Type)
    (VerifierState : (shared : SharedIn) → Idx → Type)
    (proverInit : (shared : SharedIn) →
      StatementWithOracles StatementIn OStatementIn shared → WitnessIn shared →
        ProverState shared (idx shared))
    (verifierInit : (shared : SharedIn) →
      StatementIn shared → VerifierState shared (idx shared))
    (proverSteps : (shared : SharedIn) →
      Spec.PathChain.Prover.RoundSteps (m := OracleComp oSpec)
        (ProverState shared) n (c shared))
    (verifierSteps : (shared : SharedIn) →
      Spec.PathChain.Verifier.RoundSteps (oSpec := oSpec) (OStmtIn := OStatementIn shared)
        (VerifierState shared) n (c shared))
    (proverStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared))) →
        Spec.PathChain.outputFamily (ProverState shared) n (c shared) pt →
        StatementOut shared pt)
    (verifierStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared))) →
        Spec.PathChain.outputFamily (VerifierState shared) n (c shared) pt →
        StatementOut shared pt)
    (oStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared))) →
        Spec.PathChain.outputFamily (ProverState shared) n (c shared) pt →
        ∀ i, OStatementOut shared pt i)
    (witResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared))) →
        Spec.PathChain.outputFamily (ProverState shared) n (c shared) pt →
        WitnessOut shared pt)
    (simulate : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.PathChain.toSpec n (c shared))) →
        QueryImpl [OStatementOut shared pt]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Spec.PathChain.toSpec n (c shared)).toOracleSpec
                (Spec.PathChain.toOracleDeco n (c shared)) pt))) :
    Reduction oSpec SharedIn
      (fun shared => Spec.PathChain.toSpec n (c shared))
      (fun shared => Spec.PathChain.toRoles n (c shared))
      (fun shared => Spec.PathChain.toOracleDeco n (c shared))
      StatementIn OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut where
  prover shared sWithOracles w := do
    let strat ← Spec.PathChain.Prover.comp (ProverState shared)
      n (c shared) (proverInit shared sWithOracles w) (proverSteps shared)
    let strat' :=
      Interaction.TwoParty.Focal.mapOutput
        (fun tr proverState =>
          let pt := (Spec.PathChain.toSpec n (c shared)).projectPublic tr
          (⟨⟨proverStmtResult shared pt proverState,
                oStmtResult shared pt proverState⟩,
              witResult shared pt proverState⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => StatementOut shared pt)
                (fun _ => OStatementOut shared pt)
                shared)
              (WitnessOut shared pt)))
        strat
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (Spec.PathChain.toSpec n (c shared)).toInteractionSpec
        ((Spec.PathChain.toSpec n (c shared)).toSpecRoles
          (Spec.PathChain.toRoles n (c shared)))
        strat'
  verifier := {
    toFun := fun shared stmtIn =>
      Interaction.Spec.ShapeOver.mapOutput counterpartMonadicShape
        (agent := PUnit.unit)
        (spec := (Spec.PathChain.toSpec n (c shared)).toInteractionSpec)
        (ctxs := RoleDecoration.withMonads
          ((Spec.PathChain.toSpec n (c shared)).toSpecRoles
            (Spec.PathChain.toRoles n (c shared)))
          ((Spec.PathChain.toSpec n (c shared)).toMonadDecoration oSpec (OStatementIn shared)
            (Spec.PathChain.toRoles n (c shared)) (Spec.PathChain.toOracleDeco n (c shared))
            []ₒ))
        (fun tr verifierState =>
          let pt := (Spec.PathChain.toSpec n (c shared)).projectPublic tr
          verifierStmtResult shared pt verifierState)
        (Spec.PathChain.Verifier.comp (oSpec := oSpec)
          (OStmtIn := OStatementIn shared) (VerifierState shared)
          n (c shared) (verifierInit shared stmtIn) (verifierSteps shared))
    simulate := simulate
  }

end Interaction.Oracle


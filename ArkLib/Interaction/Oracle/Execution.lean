/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Access
public import ArkLib.Interaction.Reduction

/-!
# Oracle strategies and single-run execution

The prover uses PolyFun's ordinary runtime strategy and can remember concrete messages. The
verifier uses `StrategyOver` on the structural oracle tree: its oracle-node continuation takes
only the unique structural branch, never the concrete payload. Queries at public nodes, after
oracle receives, and at terminal leaves use the canonically accumulated signature from `Access`.

`Verifier.toCounterpart` interprets this restricted authoring language into the ordinary PolyFun
counterpart. Only this runtime adapter receives oracle payloads, to extend the pure read handler.
`executeStrategies` calls `TwoParty.run` and then executes the returned terminal action once.
The erasure equation is an equality of open `OracleComp` programs; no commutative ambient handler
is assumed and no probability semantics is introduced here.

Verifier effects run at the precise ownership boundary of the ordinary paired runner: after a
prover-owned move, before emitting a verifier-owned move, and at termination. This is not an
arbitrary reschedulable local program, a logged view, a resumable artifact, or a security theorem.
See `docs/design/01c-access-execution-contract.md`.
-/

@[expose] public section

universe u v w

namespace Interaction.Oracle

open OracleComp OracleSpec TwoParty
open PFunctor.FreeM.Displayed (Decoration)

namespace Verifier

/-- Role, interface, and pre-move query signature at a structural node. The interface describes
post-receive access; the context contains no concrete oracle payload or source handler. -/
@[reducible]
def Context : Oracle.Position.{u} → Type (u + 1) :=
  fun position => TypeTree.RoleContext position ×
    TypeTree.OracleInterfaceContext.{u, u} position × PFunctor.{u, u}

/-- The canonical combined role/access decoration. Access grows only in the continuation of an
oracle send; callers do not supply an arbitrary access annotation to the strategy package. -/
def decorate :
    (tree : Oracle.TypeTree.{u}) → tree.RoleDecoration → tree.OracleDecoration →
    PFunctor.{u, u} → Decoration Context tree
  | .done, _, _, _ => ⟨⟩
  | .public _ rest, roles, oracles, initial =>
      ⟨⟨roles.1, PUnit.unit, initial⟩, fun move =>
        decorate (rest move) (roles.2 move) (oracles.2 move) initial⟩
  | .oracle _ rest, roles, oracles, initial =>
      ⟨⟨PUnit.unit, oracles.1, initial⟩, fun marker =>
        decorate (rest marker) (roles.2 marker) (oracles.2 marker)
          (Access.extend initial oracles.1)⟩

/-- The access component of the combined decoration is exactly AR-3A's canonical builder. -/
theorem decorate_access :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor.{u, u}) →
    Decoration.map (fun _ data => data.2.2) tree (decorate tree roles oracles initial) =
      TypeTree.AccessDecoration.build tree oracles (OracleSpec.ofPFunctor initial)
  | .done, _, _, _ => rfl
  | .public _ rest, roles, oracles, initial => by
      change (initial, fun move =>
        Decoration.map (fun _ data => data.2.2) (rest move)
          (decorate (rest move) (roles.2 move) (oracles.2 move) initial)) = _
      congr 1
      funext move
      exact decorate_access (rest move) (roles.2 move) (oracles.2 move) initial
  | .oracle _ rest, roles, oracles, initial => by
      change (initial, fun marker =>
        Decoration.map (fun _ data => data.2.2) (rest marker)
          (decorate (rest marker) (roles.2 marker) (oracles.2 marker)
            (Access.extend initial oracles.1))) = _
      congr 1
      funext marker
      exact decorate_access (rest marker) (roles.2 marker) (oracles.2 marker)
        (Access.extend initial oracles.1)

/-- Verifier-local syntax over the structural, not runtime, lens. Oracle-receive effects run over
the extended signature, but their continuation is indexed by `PUnit`, never the concrete payload.
Public-sender effects run after receipt; public-receiver effects run before the selected move. -/
def localSyntax {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    SyntaxOver (PFunctor.Lens.id TypeTree.basePFunctor) PUnit.{u + 1} Context where
  Node := fun _ position data (Cont : position.Branch → Type u) =>
    match position with
    | .public Moves =>
        match data.1 with
        | .sender => (move : Moves) →
            OracleComp (ambient + OracleSpec.ofPFunctor data.2.2) (Cont move)
        | .receiver =>
            OracleComp (ambient + OracleSpec.ofPFunctor data.2.2) ((move : Moves) × Cont move)
    | .oracle _ =>
        OracleComp (ambient + OracleSpec.ofPFunctor (Access.extend data.2.2 data.2.1))
          (Cont PUnit.unit)

/-- Oracle-aware verifier strategy. Its output family depends only on public structural choices,
while its terminal action may query every resource accumulated along those choices. -/
abbrev Strategy {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (Out : tree.BranchPath → Type u) :=
  StrategyOver (localSyntax ambient) PUnit.unit tree (decorate tree roles oracles initial)
    (fun path => OracleComp
      (ambient + OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path)) (Out path))

/-- Supply arbitrary input/earlier-message behavior while leaving ambient effects uninterpreted. -/
def readImpl {ι : Type u} (ambient : OracleSpec.{u, u} ι) (access : PFunctor.{u, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor access) Id) :
    QueryImpl (ambient + OracleSpec.ofPFunctor access) (OracleComp ambient) :=
  QueryImpl.add (QueryImpl.id' ambient)
    (show QueryImpl (OracleSpec.ofPFunctor access) (OracleComp ambient) from
      fun q => pure (impl q))

@[simp]
theorem readImpl_ambient {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (access : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor access) Id)
    (q : ambient.Domain) :
    readImpl ambient access impl (.inl q) = QueryImpl.id' ambient q :=
  rfl

@[simp]
theorem readImpl_source {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (access : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor access) Id)
    (q : access.A) :
    readImpl ambient access impl (.inr q) = pure (impl q) :=
  rfl

/-- Interpret a safe oracle verifier as a runtime counterpart. The counterpart's leaf is still a
terminal action: translating the strategy does not execute that action or add a protocol round. -/
def toCounterpart {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor.{u, u}) →
    QueryImpl (OracleSpec.ofPFunctor initial) Id →
    (Out : tree.BranchPath → Type u) → Strategy ambient tree roles oracles initial Out →
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) Participant.counterpart
      tree.toTypeTree (TypeTree.RoleDecoration.toTypeTreeRoles tree roles)
      (fun path => OracleComp ambient
        (Out (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath))
  | .done, _, _, initial, impl, _, verifier =>
      simulateQ (readImpl ambient initial impl) verifier
  | .public _ rest, ⟨.sender, roles⟩, oracles, initial, impl, Out, verifier =>
      fun move => do
        let next ← simulateQ (readImpl ambient initial impl) (verifier move)
        return toCounterpart ambient (rest move) (roles move) (oracles.2 move) initial impl
          (fun path => Out ⟨move, path⟩) next
  | .public _ rest, ⟨.receiver, roles⟩, oracles, initial, impl, Out, verifier => do
      let ⟨move, next⟩ ← simulateQ (readImpl ambient initial impl) verifier
      return ⟨move, toCounterpart ambient (rest move) (roles move) (oracles.2 move)
        initial impl (fun path => Out ⟨move, path⟩) next⟩
  | .oracle _ rest, roles, oracles, initial, impl, Out, verifier =>
      fun message => do
        let extended := Access.extend initial oracles.1
        let extendedImpl := Access.extendImpl initial oracles.1 impl message
        let next ← simulateQ (readImpl ambient extended extendedImpl) verifier
        return toCounterpart ambient (rest PUnit.unit) (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
          extended extendedImpl (fun path => Out ⟨PUnit.unit, path⟩) next


/-- Equality of source handlers is respected extensionally by the execution adapter. -/
theorem toCounterpart_congr_impl {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (left right : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (h : ∀ q, left q = right q) (Out : tree.BranchPath → Type u)
    (verifier : Strategy ambient tree roles oracles initial Out) :
    toCounterpart ambient tree roles oracles initial left Out verifier =
      toCounterpart ambient tree roles oracles initial right Out verifier := by
  have same : left = right := funext h
  rw [same]

/-- An oracle receive can distinguish messages only through their declared answers. This is a
local behavioral theorem for every verifier strategy, not a faithfulness assumption on messages. -/
theorem toCounterpart_oracle_eq_of_answer_eq {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (Messages : Type u) (rest : PUnit.{u + 1} → Oracle.TypeTree.{u})
    (roles : TypeTree.RoleDecoration (.oracle Messages rest))
    (oracles : TypeTree.OracleDecoration (.oracle Messages rest)) (initial : PFunctor.{u, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Out : TypeTree.BranchPath (.oracle Messages rest) → Type u)
    (verifier : Strategy ambient (.oracle Messages rest) roles oracles initial Out)
    (left right : Messages)
    (h : ∀ q, @OracleInterface.answer _ oracles.1 left q =
      @OracleInterface.answer _ oracles.1 right q) :
    toCounterpart ambient (.oracle Messages rest) roles oracles initial impl Out verifier left =
      toCounterpart ambient (.oracle Messages rest) roles oracles initial impl Out verifier
        right := by
  have same : Access.extendImpl initial oracles.1 impl left =
      Access.extendImpl initial oracles.1 impl right := by
    funext q
    cases q with
    | inl q => rfl
    | inr q => exact h q
  simp only [toCounterpart, same]
  rfl

end Verifier

namespace Prover

/-- A prover is an ordinary PolyFun focal strategy on the runtime tree. Unlike the verifier, it
may remember concrete oracle messages; its private terminal output may depend on the full path. -/
abbrev Strategy {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration)
    (Out : tree.ExecutionPath → Type u) :=
  StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) Participant.focal
    tree.toTypeTree (TypeTree.RoleDecoration.toTypeTreeRoles tree roles)
    (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath path))

end Prover

/-- Execute the ordinary paired runner, then the terminal verifier action exactly once. All
ambient queries remain in the returned open program; stateful interpreters preserve their order. -/
def executeStrategies {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type u} {OutV : tree.BranchPath → Type u}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) :
    OracleComp ambient ((path : tree.ExecutionPath) × OutP path × OutV path.toBranchPath) := do
  let result ← TwoParty.run tree.toTypeTree (TypeTree.RoleDecoration.toTypeTreeRoles tree roles)
    prover (Verifier.toCounterpart ambient tree roles oracles initial impl OutV verifier)
  let out ← result.2.2
  return ⟨TypeTree.ExecutionPath.ofTypeTreePath result.1, result.2.1, out⟩

/-- Erasure of the actual exported executor to the existing runner and one terminal bind. This is
an open-program equation, not an equality obtained only after choosing a commutative handler. -/
theorem executeStrategies_eq_run {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type u} {OutV : tree.BranchPath → Type u}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) :
    executeStrategies ambient tree roles oracles initial impl prover verifier = (do
      let result ← TwoParty.run tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles tree roles) prover
        (Verifier.toCounterpart ambient tree roles oracles initial impl OutV verifier)
      let out ← result.2.2
      return ⟨TypeTree.ExecutionPath.ofTypeTreePath result.1, result.2.1, out⟩) :=
  rfl

/-- Project only the public structural path and verifier result. This intentionally is not named a
verifier local view: it does not contain the verifier's ordered query/answer observations. -/
def publicResult {tree : Oracle.TypeTree.{u}}
    {OutP : tree.ExecutionPath → Type u} {OutV : tree.BranchPath → Type u}
    (result : (path : tree.ExecutionPath) × OutP path × OutV path.toBranchPath) :
    (path : tree.BranchPath) × OutV path :=
  ⟨result.1.toBranchPath, result.2.2⟩

/-- A small statement/witness wrapper around oracle strategies. The verifier is built from the
public statement only, never from the input oracle implementation or the prover's private witness.
Families of these packages can depend on shared public parameters. -/
structure Reduction {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (protocol : Oracle.Protocol.{u}) (initial : PFunctor.{u, u})
    (StatementIn : Type v) (WitnessIn : Type w)
    (OutP : protocol.tree.ExecutionPath → Type u)
    (OutV : protocol.tree.BranchPath → Type u) where
  /-- Prover setup followed by an ordinary runtime strategy. -/
  prover : StatementIn → WitnessIn → OracleComp ambient
    (Prover.Strategy ambient protocol.tree protocol.roles OutP)
  /-- Public-input-only verifier authoring. -/
  verifier : StatementIn → Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles
    initial OutV

/-- Execute the package with arbitrary pure input behavior. This is single-run semantics, not
run-derived claim closing or a sequential security theorem. -/
def Reduction.execute {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {StatementIn : Type v} {WitnessIn : Type w}
    {OutP : protocol.tree.ExecutionPath → Type u} {OutV : protocol.tree.BranchPath → Type u}
    (reduction : Reduction ambient protocol initial StatementIn WitnessIn OutP OutV)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (stmt : StatementIn) (wit : WitnessIn) :
    OracleComp ambient
      ((path : protocol.tree.ExecutionPath) × OutP path × OutV path.toBranchPath) := do
  let prover ← reduction.prover stmt wit
  executeStrategies ambient protocol.tree protocol.roles protocol.oracles initial impl prover
    (reduction.verifier stmt)

end Interaction.Oracle

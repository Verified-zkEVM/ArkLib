/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import all PolyFun.Interaction.Basic.StrategyOver
import all PolyFun.Interaction.TwoParty.Strategy

public import ArkLib.Interaction.Oracle.Access
public import ArkLib.Interaction.Oracle.RunSources
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

/-- Functorial continuation maps for the restricted local syntax. They preserve the query
signature, public role, and oracle payload visibility at every node. -/
def localShape {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    ShapeOver (PFunctor.Lens.id TypeTree.basePFunctor) PUnit.{u + 1} Context where
  toSyntaxOver := localSyntax ambient
  map := fun {_} {position} {data} {_} {_} f node =>
    match position, data with
    | .public _, ⟨.sender, _, _⟩ => fun move => f move <$> node move
    | .public _, ⟨.receiver, _, _⟩ => (fun ⟨move, next⟩ => ⟨move, f move next⟩) <$> node
    | .oracle _, _ => f PUnit.unit <$> node

/-- A restricted verifier fragment with ordinary leaf values. Its node effects and authoring
visibility are the same as completed verifiers; leaf values have no implicit terminal execution. -/
abbrev Fragment {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (Out : tree.BranchPath → Type u) :=
  StrategyOver (localSyntax ambient) PUnit.unit tree (decorate tree roles oracles initial) Out

/-- Map ordinary fragment leaves while retaining every existing node effect. -/
def Fragment.mapOutput {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    {tree : Oracle.TypeTree.{u}} {roles : tree.RoleDecoration} {oracles : tree.OracleDecoration}
    {initial : PFunctor.{u, u}} {A B : tree.BranchPath → Type u}
    (f : (path : tree.BranchPath) → A path → B path)
    (verifier : Fragment ambient tree roles oracles initial A) :
    Fragment ambient tree roles oracles initial B :=
  ShapeOver.mapOutput (localShape ambient) (decorate tree roles oracles initial) f verifier

/-- A completed verifier is a fragment whose leaf returns the final query action. The executor
runs that action exactly once after the paired interaction has terminated. -/
abbrev Strategy {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (Out : tree.BranchPath → Type u) :=
  Fragment ambient tree roles oracles initial (fun path => OracleComp
    (ambient + OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path)) (Out path))

/-- Supply arbitrary input/earlier-message behavior while leaving ambient effects uninterpreted. -/
def liftAccessImpl {ι : Type u} (ambient : OracleSpec.{u, u} ι) (access : PFunctor.{u, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor access) Id) :
    QueryImpl (ambient + OracleSpec.ofPFunctor access) (OracleComp ambient) :=
  QueryImpl.add (QueryImpl.id' ambient)
    (show QueryImpl (OracleSpec.ofPFunctor access) (OracleComp ambient) from
      fun q => pure (impl q))

@[simp]
theorem liftAccessImpl_ambient {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (access : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor access) Id)
    (q : ambient.Domain) :
    liftAccessImpl ambient access impl (.inl q) = QueryImpl.id' ambient q :=
  rfl

@[simp]
theorem liftAccessImpl_source {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (access : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor access) Id)
    (q : access.A) :
    liftAccessImpl ambient access impl (.inr q) = pure (impl q) :=
  rfl

/-- The shared interpreter for restricted fragments. Only this adapter sees concrete oracle
messages. `finish` interprets a leaf using the actual accumulated handler; it is interpreter data,
never a parameter available to verifier authoring. Node effects keep their existing schedule. -/
def toCounterpartWith {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor.{u, u}) →
    QueryImpl (OracleSpec.ofPFunctor initial) Id →
    (Leaf Out : tree.BranchPath → Type u) →
    ((path : tree.BranchPath) →
      QueryImpl (OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path)) Id →
      Leaf path → Out path) → Fragment ambient tree roles oracles initial Leaf →
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) Participant.counterpart
      tree.toTypeTree (TypeTree.RoleDecoration.toTypeTreeRoles tree roles)
      (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
  | .done, _, _, _, impl, _, _, finish, verifier => finish PUnit.unit impl verifier
  | .public _ rest, ⟨.sender, roles⟩, oracles, initial, impl, Leaf, Out, finish, verifier =>
      fun move => do
        let next ← simulateQ (liftAccessImpl ambient initial impl) (verifier move)
        return toCounterpartWith ambient (rest move) (roles move) (oracles.2 move) initial impl
          (fun path => Leaf ⟨move, path⟩) (fun path => Out ⟨move, path⟩)
          (fun path => finish ⟨move, path⟩) next
  | .public _ rest, ⟨.receiver, roles⟩, oracles, initial, impl, Leaf, Out, finish, verifier => do
      let ⟨move, next⟩ ← simulateQ (liftAccessImpl ambient initial impl) verifier
      return ⟨move, toCounterpartWith ambient (rest move) (roles move) (oracles.2 move)
        initial impl (fun path => Leaf ⟨move, path⟩) (fun path => Out ⟨move, path⟩)
        (fun path => finish ⟨move, path⟩) next⟩
  | .oracle _ rest, roles, oracles, initial, impl, Leaf, Out, finish, verifier =>
      fun message => do
        let extended := Access.extend initial oracles.1
        let extendedImpl := Access.extendImpl initial oracles.1 impl message
        let next ← simulateQ (liftAccessImpl ambient extended extendedImpl) verifier
        return toCounterpartWith ambient (rest PUnit.unit) (roles.2 PUnit.unit)
          (oracles.2 PUnit.unit) extended extendedImpl
          (fun path => Leaf ⟨PUnit.unit, path⟩) (fun path => Out ⟨PUnit.unit, path⟩)
          (fun path => finish ⟨PUnit.unit, path⟩) next

set_option backward.isDefEq.respectTransparency false in
/-- Mapping fragment leaves changes only the interpreter's finish handler. Every node keeps
its original query program and ownership boundary. -/
theorem toCounterpartWith_mapOutput {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor.{u, u}) →
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) →
    (A B Out : tree.BranchPath → Type u) →
    (f : (path : tree.BranchPath) → A path → B path) →
    (finish : (path : tree.BranchPath) →
      QueryImpl (OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path)) Id →
      B path → Out path) → (verifier : Fragment ambient tree roles oracles initial A) →
    toCounterpartWith ambient tree roles oracles initial impl B Out finish
      (Fragment.mapOutput ambient f verifier) =
    toCounterpartWith ambient tree roles oracles initial impl A Out
      (fun path impl out => finish path impl (f path out)) verifier
  | .done, _, _, _, _, _, _, _, _, _, _ => rfl
  | .public Moves rest, ⟨.sender, roles⟩, oracles, initial, impl, A, B, Out, f, finish,
      verifier => by
      funext move
      change Moves at move
      simp only [Fragment.mapOutput, ShapeOver.mapOutput, localShape, decorate,
        toCounterpartWith]
      rw [simulateQ_map, bind_map_left]
      apply bind_congr
      intro next
      congr 1
      exact toCounterpartWith_mapOutput ambient (rest move) (roles move) (oracles.2 move)
        initial impl (fun path => A ⟨move, path⟩) (fun path => B ⟨move, path⟩)
        (fun path => Out ⟨move, path⟩) (fun path => f ⟨move, path⟩)
        (fun path => finish ⟨move, path⟩) next
  | .public Moves rest, ⟨.receiver, roles⟩, oracles, initial, impl, A, B, Out, f, finish,
      verifier => by
      let resultType := (move : Moves) ×
        StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
          Participant.counterpart (rest move).toTypeTree
          (TypeTree.RoleDecoration.toTypeTreeRoles (rest move) (roles move))
          (fun path => Out ⟨move, (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath⟩)
      let step : ((move : Moves) × Fragment ambient (rest move) (roles move)
          (oracles.2 move) initial (fun path => A ⟨move, path⟩)) →
          ((move : Moves) × Fragment ambient (rest move) (roles move)
          (oracles.2 move) initial (fun path => B ⟨move, path⟩)) := fun next =>
        ⟨next.1, Fragment.mapOutput ambient (fun path => f ⟨next.1, path⟩) next.2⟩
      change (simulateQ (liftAccessImpl ambient initial impl) (step <$> verifier) >>= fun next =>
        pure (⟨next.1, toCounterpartWith ambient (rest next.1) (roles next.1)
          (oracles.2 next.1) initial impl (fun path => B ⟨next.1, path⟩)
          (fun path => Out ⟨next.1, path⟩) (fun path => finish ⟨next.1, path⟩)
          next.2⟩ : resultType)) = _
      rw [simulateQ_map, bind_map_left]
      apply bind_congr
      intro ⟨move, next⟩
      apply congrArg pure
      apply congrArg (Sigma.mk move)
      exact toCounterpartWith_mapOutput ambient (rest move) (roles move) (oracles.2 move)
        initial impl (fun path => A ⟨move, path⟩) (fun path => B ⟨move, path⟩)
        (fun path => Out ⟨move, path⟩) (fun path => f ⟨move, path⟩)
        (fun path => finish ⟨move, path⟩) next
  | .oracle Messages rest, roles, oracles, initial, impl, A, B, Out, f, finish, verifier => by
      funext message
      change Messages at message
      let step := Fragment.mapOutput ambient (fun path => f ⟨PUnit.unit, path⟩)
        (roles := roles.2 PUnit.unit) (oracles := oracles.2 PUnit.unit)
        (initial := Access.extend initial oracles.1)
      change (simulateQ (liftAccessImpl ambient (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)) (step <$> verifier) >>= fun next =>
        pure (toCounterpartWith ambient (rest PUnit.unit) (roles.2 PUnit.unit)
          (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)
          (fun path => B ⟨PUnit.unit, path⟩) (fun path => Out ⟨PUnit.unit, path⟩)
          (fun path => finish ⟨PUnit.unit, path⟩) next)) = _
      rw [simulateQ_map, bind_map_left]
      apply bind_congr
      intro next
      apply congrArg pure
      exact toCounterpartWith_mapOutput ambient (rest PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl message)
        (fun path => A ⟨PUnit.unit, path⟩) (fun path => B ⟨PUnit.unit, path⟩)
        (fun path => Out ⟨PUnit.unit, path⟩) (fun path => f ⟨PUnit.unit, path⟩)
        (fun path => finish ⟨PUnit.unit, path⟩) next


/-- Interpret a value fragment as an ordinary counterpart, returning its boundary value directly. -/
def toCounterpartValue {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Out : tree.BranchPath → Type u) (verifier : Fragment ambient tree roles oracles initial Out) :=
  toCounterpartWith ambient tree roles oracles initial impl Out Out (fun _ _ out => out) verifier

/-- A finish handler uses precisely the source handler extracted from the runtime path.
This is an ordinary output map of the value interpreter, so it adds no node effects. -/
theorem toCounterpartWith_finish_eq_mapOutput {ι : Type u}
    (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor.{u, u}) →
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) →
    (Leaf Out : tree.BranchPath → Type u) →
    (finish : (path : tree.BranchPath) →
      QueryImpl (OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path)) Id →
      Leaf path → Out path) → (verifier : Fragment ambient tree roles oracles initial Leaf) →
    toCounterpartWith ambient tree roles oracles initial impl Leaf Out finish verifier =
      StrategyOver.TwoParty.Counterpart.mapOutput (fun path leaf =>
        finish (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath
          ((TypeTree.ExecutionPath.ofTypeTreePath path).closingImpl oracles initial impl) leaf)
        (toCounterpartValue ambient tree roles oracles initial impl Leaf verifier)
  | .done, _, _, _, _, _, _, _, _ => rfl
  | .public Moves rest, ⟨.sender, roles⟩, oracles, initial, impl, Leaf, Out, finish, verifier => by
      apply funext
      intro move
      change Moves at move
      change (do
        let next ← simulateQ (liftAccessImpl ambient initial impl) (verifier move)
        pure (toCounterpartWith ambient (rest move) (roles move) (oracles.2 move) initial impl
          (fun p => Leaf ⟨move, p⟩) (fun p => Out ⟨move, p⟩)
          (fun p => finish ⟨move, p⟩) next)) =
        StrategyOver.TwoParty.Counterpart.mapOutput (fun p leaf =>
          finish ⟨move, (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath⟩
            ((TypeTree.ExecutionPath.ofTypeTreePath p).closingImpl (oracles.2 move) initial impl)
            leaf) <$> (do
          let next ← simulateQ (liftAccessImpl ambient initial impl) (verifier move)
          pure (toCounterpartValue ambient (rest move) (roles move) (oracles.2 move) initial impl
            (fun p => Leaf ⟨move, p⟩) next))
      rw [map_bind]
      simp only [map_pure]
      congr 1
      funext next
      congr 1
      exact toCounterpartWith_finish_eq_mapOutput ambient (rest move) (roles move)
        (oracles.2 move) initial impl (fun p => Leaf ⟨move, p⟩) (fun p => Out ⟨move, p⟩)
        (fun p => finish ⟨move, p⟩) next
  | .public Moves rest, ⟨.receiver, roles⟩, oracles, initial, impl, Leaf, Out, finish,
      verifier => by
      let resultType (Result : (TypeTree.public Moves rest).BranchPath → Type u) :=
        (move : Moves) × StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
          Participant.counterpart (rest move).toTypeTree
          (TypeTree.RoleDecoration.toTypeTreeRoles (rest move) (roles move))
          (fun p => Result ⟨move, (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath⟩)
      change (do
        let ⟨move, next⟩ ← simulateQ (liftAccessImpl ambient initial impl) verifier
        pure (⟨move, toCounterpartWith ambient (rest move) (roles move) (oracles.2 move)
          initial impl (fun p => Leaf ⟨move, p⟩) (fun p => Out ⟨move, p⟩)
          (fun p => finish ⟨move, p⟩) next⟩ : resultType Out)) =
        (fun (result : resultType Leaf) => (⟨result.1,
          StrategyOver.TwoParty.Counterpart.mapOutput (fun p leaf =>
          finish ⟨result.1, (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath⟩
            ((TypeTree.ExecutionPath.ofTypeTreePath p).closingImpl (oracles.2 result.1)
              initial impl) leaf) result.2⟩ : resultType Out)) <$> (do
          let ⟨move, next⟩ ← simulateQ (liftAccessImpl ambient initial impl) verifier
          pure (⟨move, toCounterpartValue ambient (rest move) (roles move) (oracles.2 move)
            initial impl (fun p => Leaf ⟨move, p⟩) next⟩ : resultType Leaf))
      rw [map_bind]
      simp only [map_pure]
      congr 1
      funext next
      rcases next with ⟨move, next⟩
      congr 2
      exact toCounterpartWith_finish_eq_mapOutput ambient (rest move) (roles move)
        (oracles.2 move) initial impl (fun p => Leaf ⟨move, p⟩) (fun p => Out ⟨move, p⟩)
        (fun p => finish ⟨move, p⟩) next
  | .oracle Messages rest, roles, oracles, initial, impl, Leaf, Out, finish, verifier => by
      apply funext
      intro message
      change Messages at message
      change (do
        let next ← simulateQ (liftAccessImpl ambient (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)) verifier
        pure (toCounterpartWith ambient (rest PUnit.unit) (roles.2 PUnit.unit)
          (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)
          (fun p => Leaf ⟨PUnit.unit, p⟩) (fun p => Out ⟨PUnit.unit, p⟩)
          (fun p => finish ⟨PUnit.unit, p⟩) next)) =
        StrategyOver.TwoParty.Counterpart.mapOutput (fun p leaf =>
          finish ⟨PUnit.unit, (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath⟩
            ((TypeTree.ExecutionPath.ofTypeTreePath p).closingImpl (oracles.2 PUnit.unit)
              (Access.extend initial oracles.1) (Access.extendImpl initial oracles.1 impl message))
            leaf) <$> (do
          let next ← simulateQ (liftAccessImpl ambient (Access.extend initial oracles.1)
            (Access.extendImpl initial oracles.1 impl message)) verifier
          pure (toCounterpartValue ambient (rest PUnit.unit) (roles.2 PUnit.unit)
            (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
            (Access.extendImpl initial oracles.1 impl message)
            (fun p => Leaf ⟨PUnit.unit, p⟩) next))
      rw [map_bind]
      simp only [map_pure]
      congr 1
      funext next
      congr 1
      exact toCounterpartWith_finish_eq_mapOutput ambient (rest PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl message)
        (fun p => Leaf ⟨PUnit.unit, p⟩) (fun p => Out ⟨PUnit.unit, p⟩)
        (fun p => finish ⟨PUnit.unit, p⟩) next


/-- Interpret a completed verifier with the shared adapter. Its leaf is a terminal action;
translation neither executes the action nor inserts an extra protocol round. -/
def toCounterpart {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Out : tree.BranchPath → Type u) (verifier : Strategy ambient tree roles oracles initial Out) :=
  toCounterpartWith ambient tree roles oracles initial impl _ (fun path => OracleComp ambient
    (Out path)) (fun path impl action => simulateQ
      (liftAccessImpl ambient (TypeTree.accessAfter tree oracles initial path) impl) action)
    verifier

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
  simp only [toCounterpart, toCounterpartWith, same]
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

/-- At a terminal node the actual executor runs the final verifier action once. -/
theorem executeStrategies_done {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : TypeTree.done.ExecutionPath → Type u}
    {OutV : TypeTree.done.BranchPath → Type u}
    (prover : Prover.Strategy ambient .done PUnit.unit OutP)
    (verifier : Verifier.Strategy ambient .done PUnit.unit PUnit.unit initial OutV) :
    executeStrategies ambient .done PUnit.unit PUnit.unit initial impl prover verifier = (do
      let out ← simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier
      return ⟨PUnit.unit, prover, out⟩) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A prover public move runs before the verifier's actual receive effect and the continuation. -/
theorem executeStrategies_public_sender {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (roles : (move : Moves) → (rest move).RoleDecoration)
    (oracles : (TypeTree.public Moves rest).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : (TypeTree.public Moves rest).ExecutionPath → Type u}
    {OutV : (TypeTree.public Moves rest).BranchPath → Type u}
    (prover : Prover.Strategy ambient (.public Moves rest) ⟨.sender, roles⟩ OutP)
    (verifier : Verifier.Strategy ambient (.public Moves rest) ⟨.sender, roles⟩ oracles
      initial OutV) :
    executeStrategies ambient (.public Moves rest) ⟨.sender, roles⟩ oracles initial impl
      prover verifier = (do
        let chosen ← prover
        let next ← simulateQ (Verifier.liftAccessImpl ambient initial impl) (verifier chosen.1)
        let result ← executeStrategies ambient (rest chosen.1) (roles chosen.1)
          (oracles.2 chosen.1) initial impl
          (OutP := fun path => OutP ⟨chosen.1, path⟩)
          (OutV := fun path => OutV ⟨chosen.1, path⟩) chosen.2 next
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) := by
  simp only [executeStrategies, Verifier.toCounterpart, Verifier.toCounterpartWith,
    TypeTree.toTypeTree_public, TypeTree.RoleDecoration.toTypeTreeRoles_public,
    TwoParty.run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, TwoParty.participantProfile,
    TwoParty.collectParticipantOutputs, bind_assoc, pure_bind]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A verifier public move runs before the prover's actual response and the continuation. -/
theorem executeStrategies_public_receiver {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    {Moves : Type u} {rest : Moves → Oracle.TypeTree.{u}}
    (roles : (move : Moves) → (rest move).RoleDecoration)
    (oracles : (TypeTree.public Moves rest).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : (TypeTree.public Moves rest).ExecutionPath → Type u}
    {OutV : (TypeTree.public Moves rest).BranchPath → Type u}
    (prover : Prover.Strategy ambient (.public Moves rest) ⟨.receiver, roles⟩ OutP)
    (verifier : Verifier.Strategy ambient (.public Moves rest) ⟨.receiver, roles⟩ oracles
      initial OutV) :
    executeStrategies ambient (.public Moves rest) ⟨.receiver, roles⟩ oracles initial impl
      prover verifier = (do
        let chosen ← simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier
        let next ← prover chosen.1
        let result ← executeStrategies ambient (rest chosen.1) (roles chosen.1)
          (oracles.2 chosen.1) initial impl
          (OutP := fun path => OutP ⟨chosen.1, path⟩)
          (OutV := fun path => OutV ⟨chosen.1, path⟩) next chosen.2
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) := by
  simp only [executeStrategies, Verifier.toCounterpart, Verifier.toCounterpartWith,
    TypeTree.toTypeTree_public, TypeTree.RoleDecoration.toTypeTreeRoles_public,
    TwoParty.run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, TwoParty.participantProfile,
    TwoParty.collectParticipantOutputs, bind_assoc, pure_bind]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An oracle send retains the concrete realization and extends the actual closing handler. -/
theorem executeStrategies_oracle {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    {Messages : Type u} {rest : PUnit.{u + 1} → Oracle.TypeTree.{u}}
    (roles : (TypeTree.oracle Messages rest).RoleDecoration)
    (oracles : (TypeTree.oracle Messages rest).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : (TypeTree.oracle Messages rest).ExecutionPath → Type u}
    {OutV : (TypeTree.oracle Messages rest).BranchPath → Type u}
    (prover : Prover.Strategy ambient (.oracle Messages rest) roles OutP)
    (verifier : Verifier.Strategy ambient (.oracle Messages rest) roles oracles initial OutV) :
    executeStrategies ambient (.oracle Messages rest) roles oracles initial impl
      prover verifier = (do
        let chosen ← prover
        let next ← simulateQ
          (Verifier.liftAccessImpl ambient (Access.extend initial oracles.1)
            (Access.extendImpl initial oracles.1 impl chosen.1)) verifier
        let result ← executeStrategies ambient (rest PUnit.unit) (roles.2 PUnit.unit)
          (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl chosen.1)
          (OutP := fun path => OutP ⟨chosen.1, path⟩)
          (OutV := fun path => OutV ⟨PUnit.unit, path⟩) chosen.2 next
        return ⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩) := by
  simp only [executeStrategies, Verifier.toCounterpart, Verifier.toCounterpartWith,
    TypeTree.toTypeTree_oracle, TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
    TwoParty.run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, TwoParty.participantProfile,
    TwoParty.collectParticipantOutputs, bind_assoc, pure_bind]
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

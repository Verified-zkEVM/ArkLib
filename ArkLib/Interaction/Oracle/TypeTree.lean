/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.TypeTree

/-!
# Oracle interaction type trees

This file refines PolyFun's generic `Interaction.TypeTree` with two node positions:

* `.public Moves` records a public move that selects the next subtree;
* `.oracle Messages` records an opaque oracle message while exposing only a `PUnit` structural
  branch.

The runtime lens turns both positions into ordinary PolyFun move nodes. Consequently,
`BranchPath` records only structural choices, while `ExecutionPath` retains every concrete runtime
message. This module contains shape and path data only; roles and oracle interfaces belong to the
next layer.
-/

universe u v

namespace Interaction.Oracle

/-! ## Polynomial substrate -/

/-- The two node positions in an oracle interaction tree.

A public move controls the continuation. An oracle message is retained at runtime, but its
structural branch is the unique `PUnit` value. -/
inductive Position : Type (u + 1) where
  | «public» : (Moves : Type u) → Position
  | «oracle» : (Messages : Type u) → Position

namespace Position

/-- The structural branch type selected by an oracle-tree position. -/
@[reducible]
def Branch : Position.{u} → Type u
  | .public Moves => Moves
  | .oracle _ => PUnit

end Position

namespace TypeTree

/-- The polynomial generating oracle interaction type trees. -/
@[reducible]
def basePFunctor : PFunctor.{u + 1, u} where
  A := Position
  B := Position.Branch

end TypeTree

/-- A dependent interaction tree distinguishing public moves from opaque oracle messages. -/
abbrev TypeTree : Type (u + 1) :=
  PFunctor.FreeM TypeTree.basePFunctor.{u} PUnit.{u + 1}

namespace TypeTree

/-! ## Constructors and elimination -/

/-- Terminal oracle interaction tree. -/
@[match_pattern, reducible]
def done : TypeTree := PFunctor.FreeM.pure PUnit.unit

/-- Public node whose concrete move selects the continuation. -/
@[match_pattern, reducible]
def «public» (Moves : Type u) (rest : Moves → TypeTree) : TypeTree :=
  PFunctor.FreeM.liftBind (.public Moves) rest

/-- Oracle node whose concrete message cannot affect the structural continuation. -/
@[match_pattern, reducible]
def «oracle» (Messages : Type u) (rest : PUnit.{u + 1} → TypeTree) : TypeTree :=
  PFunctor.FreeM.liftBind (.oracle Messages) rest

/-- Cases eliminator exposing the `done`, `public`, and `oracle` tree shapes. -/
@[elab_as_elim, cases_eliminator]
def casesOn {motive : TypeTree.{u} → Sort v}
    (tree : TypeTree)
    (done : motive TypeTree.done)
    («public» : (Moves : Type u) → (rest : Moves → TypeTree) →
      motive (TypeTree.public Moves rest))
    («oracle» : (Messages : Type u) → (rest : PUnit.{u + 1} → TypeTree) →
      motive (TypeTree.oracle Messages rest)) :
    motive tree :=
  match tree with
  | .done => done
  | .public Moves rest => «public» Moves rest
  | .oracle Messages rest => «oracle» Messages rest

/-- Structural recursor exposing induction hypotheses for every continuation. -/
@[elab_as_elim, induction_eliminator]
def recOn {motive : TypeTree.{u} → Sort v}
    (tree : TypeTree)
    (done : motive TypeTree.done)
    («public» : (Moves : Type u) → (rest : Moves → TypeTree) →
      ((move : Moves) → motive (rest move)) → motive (TypeTree.public Moves rest))
    («oracle» : (Messages : Type u) → (rest : PUnit.{u + 1} → TypeTree) →
      motive (rest PUnit.unit) → motive (TypeTree.oracle Messages rest)) :
    motive tree :=
  match tree with
  | .done => done
  | .public Moves rest =>
      «public» Moves rest (fun move => recOn (rest move) done «public» «oracle»)
  | .oracle Messages rest =>
      «oracle» Messages rest (recOn (rest PUnit.unit) done «public» «oracle»)

/-! ## Runtime lens -/

/-- Expose an oracle interaction tree as a generic runtime `Interaction.TypeTree`.

Both positions carry their concrete message type at runtime. The backwards direction is identity
at public nodes and forgets an oracle payload to the unique structural branch. -/
def runtimeLens : PFunctor.Lens basePFunctor _root_.Interaction.TypeTree.basePFunctor where
  toFunA
    | .public Moves => Moves
    | .oracle Messages => Messages
  toFunB
    | .public _, move => move
    | .oracle _, _ => PUnit.unit

/-- Erase the public/oracle distinction to the generic runtime type tree. -/
def toTypeTree (tree : TypeTree) : _root_.Interaction.TypeTree :=
  tree.mapLens runtimeLens

@[simp]
theorem toTypeTree_done : TypeTree.done.toTypeTree = _root_.Interaction.TypeTree.done :=
  rfl

@[simp]
theorem toTypeTree_public (Moves : Type u) (rest : Moves → TypeTree) :
    (TypeTree.public Moves rest).toTypeTree =
      _root_.Interaction.TypeTree.node Moves (fun move => (rest move).toTypeTree) :=
  rfl

@[simp]
theorem toTypeTree_oracle (Messages : Type u) (rest : PUnit.{u + 1} → TypeTree) :
    (TypeTree.oracle Messages rest).toTypeTree =
      _root_.Interaction.TypeTree.node Messages (fun _ => (rest PUnit.unit).toTypeTree) :=
  rfl

/-! ## Structural and runtime paths -/

/-- Complete structural choices through an oracle interaction tree. -/
abbrev BranchPath (tree : TypeTree.{u}) : Type u :=
  PFunctor.FreeM.Path tree

/-- Complete concrete runtime messages through an oracle interaction tree. -/
abbrev ExecutionPath (tree : TypeTree.{u}) : Type u :=
  PFunctor.FreeM.PathAlong runtimeLens tree

namespace ExecutionPath

/-- View an execution path as a path through the erased runtime type tree. -/
def toTypeTreePath {tree : TypeTree.{u}} (path : ExecutionPath tree) :
    _root_.Interaction.TypeTree.Path tree.toTypeTree :=
  PFunctor.FreeM.pathAlongToMapLensPath runtimeLens tree path

/-- Recover an execution path from a path through the erased runtime type tree. -/
def ofTypeTreePath {tree : TypeTree.{u}}
    (path : _root_.Interaction.TypeTree.Path tree.toTypeTree) : ExecutionPath tree :=
  PFunctor.FreeM.mapLensPathToPathAlong runtimeLens tree path

/-- Forget opaque oracle payloads while preserving public structural choices. -/
def toBranchPath {tree : TypeTree.{u}} (path : ExecutionPath tree) : BranchPath tree :=
  PFunctor.FreeM.projectPathAlong runtimeLens tree path

@[simp]
theorem toTypeTreePath_ofTypeTreePath {tree : TypeTree.{u}}
    (path : _root_.Interaction.TypeTree.Path tree.toTypeTree) :
    (ofTypeTreePath path).toTypeTreePath = path :=
  PFunctor.FreeM.pathAlongToMapLensPath_toPathAlong runtimeLens tree path

@[simp]
theorem ofTypeTreePath_toTypeTreePath {tree : TypeTree.{u}} (path : ExecutionPath tree) :
    ofTypeTreePath path.toTypeTreePath = path :=
  PFunctor.FreeM.mapLensPathToPathAlong_toMapLensPath runtimeLens tree path

@[simp]
theorem toBranchPath_done (path : ExecutionPath TypeTree.done) :
    path.toBranchPath = PUnit.unit :=
  rfl

@[simp]
theorem toBranchPath_public (Moves : Type u) (rest : Moves → TypeTree)
    (path : ExecutionPath (TypeTree.public Moves rest)) :
    path.toBranchPath = ⟨path.1, ExecutionPath.toBranchPath path.2⟩ :=
  rfl

@[simp]
theorem toBranchPath_oracle (Messages : Type u) (rest : PUnit.{u + 1} → TypeTree)
    (path : ExecutionPath (TypeTree.oracle Messages rest)) :
    path.toBranchPath = ⟨PUnit.unit, ExecutionPath.toBranchPath path.2⟩ :=
  rfl

end ExecutionPath

end TypeTree
end Interaction.Oracle

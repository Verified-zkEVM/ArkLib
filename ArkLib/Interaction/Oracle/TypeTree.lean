/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.Interaction.Basic.TypeTree

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

@[expose] public section

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

@[simp]
theorem runtimeLens_toFunA_public (Moves : Type u) :
    runtimeLens.toFunA (.public Moves) = Moves :=
  rfl

@[simp]
theorem runtimeLens_toFunA_oracle (Messages : Type u) :
    runtimeLens.toFunA (.oracle Messages) = Messages :=
  rfl

@[simp]
theorem runtimeLens_toFunB_public (Moves : Type u) (move : Moves) :
    runtimeLens.toFunB (.public Moves) move = move :=
  rfl

@[simp]
theorem runtimeLens_toFunB_oracle (Messages : Type u) (message : Messages) :
    runtimeLens.toFunB (.oracle Messages) message = PUnit.unit :=
  rfl

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

/-- Public projection respects dependent append. The suffix is selected by the prefix's public
structural path, while both execution paths retain their concrete oracle messages. -/
@[simp]
theorem toBranchPath_append (tree : TypeTree.{u})
    (suffix : BranchPath tree → TypeTree.{u}) (path : ExecutionPath tree)
    (rest : ExecutionPath (suffix path.toBranchPath)) :
    ExecutionPath.toBranchPath
      (PFunctor.FreeM.PathAlong.append runtimeLens tree suffix path rest) =
      PFunctor.FreeM.Path.append tree suffix path.toBranchPath rest.toBranchPath :=
  PFunctor.FreeM.PathAlong.projectPathAlong_append runtimeLens tree suffix path rest

/-- Splitting a concrete append path and then projecting each piece agrees with splitting its
public projection. The suffix stays indexed by the recovered prefix's public choices. -/
theorem toBranchPath_split (tree : TypeTree.{u})
    (suffix : BranchPath tree → TypeTree.{u})
    (path : ExecutionPath (PFunctor.FreeM.append tree suffix)) :
    let pieces := PFunctor.FreeM.PathAlong.split runtimeLens tree suffix path
    PFunctor.FreeM.Path.split tree suffix path.toBranchPath =
      ⟨ExecutionPath.toBranchPath pieces.1, ExecutionPath.toBranchPath pieces.2⟩ := by
  let pieces := PFunctor.FreeM.PathAlong.split runtimeLens tree suffix path
  have h := (PFunctor.FreeM.PathAlong.projectPathAlong_append runtimeLens tree suffix
    pieces.1 pieces.2).symm.trans (congrArg
      (PFunctor.FreeM.projectPathAlong runtimeLens (PFunctor.FreeM.append tree suffix))
      (PFunctor.FreeM.PathAlong.append_split runtimeLens tree suffix path))
  exact (PFunctor.FreeM.Path.split_append tree suffix _ _).symm.trans
    (congrArg (PFunctor.FreeM.Path.split tree suffix) h) |>.symm

end ExecutionPath

/-- Erasing the oracle/public distinction commutes with append. Runtime suffix selection forgets
oracle payloads and uses the prefix's public structural choices. -/
theorem toTypeTree_append : (tree : TypeTree.{u}) →
    (suffix : BranchPath tree → TypeTree.{u}) →
    toTypeTree (PFunctor.FreeM.append tree suffix) =
      PFunctor.FreeM.append tree.toTypeTree (fun path =>
        (suffix (ExecutionPath.ofTypeTreePath path).toBranchPath).toTypeTree)
  | .done, _ => rfl
  | .public Moves rest, suffix => by
      apply congrArg (_root_.Interaction.TypeTree.node Moves)
      funext move
      exact toTypeTree_append (rest move) (fun path => suffix ⟨move, path⟩)
  | .oracle Messages rest, suffix => by
      apply congrArg (_root_.Interaction.TypeTree.node Messages)
      funext message
      exact toTypeTree_append (rest PUnit.unit) (fun path => suffix ⟨PUnit.unit, path⟩)

namespace ExecutionPath

private theorem runtimePath_node_heq {Moves : Type u}
    {left right : Moves → _root_.Interaction.TypeTree}
    (h : ∀ move, left move = right move) (move : Moves)
    {first : _root_.Interaction.TypeTree.Path (left move)}
    {second : _root_.Interaction.TypeTree.Path (right move)} (hpath : HEq first second) :
    HEq (⟨move, first⟩ : _root_.Interaction.TypeTree.Path
      (_root_.Interaction.TypeTree.node Moves left))
      (⟨move, second⟩ : _root_.Interaction.TypeTree.Path
        (_root_.Interaction.TypeTree.node Moves right)) := by
  have same := funext h
  cases same
  cases hpath
  rfl

private theorem toTypeTreePath_append_heq : (tree : TypeTree.{u}) →
    (suffix : BranchPath tree → TypeTree.{u}) →
    (path : _root_.Interaction.TypeTree.Path tree.toTypeTree) →
    (rest : _root_.Interaction.TypeTree.Path
      (suffix (ofTypeTreePath path).toBranchPath).toTypeTree) →
    HEq (ExecutionPath.toTypeTreePath (PFunctor.FreeM.PathAlong.append runtimeLens tree suffix
      (ofTypeTreePath path) (ofTypeTreePath rest)))
      (PFunctor.FreeM.Path.append tree.toTypeTree
        (fun p => (suffix (ofTypeTreePath p).toBranchPath).toTypeTree) path rest)
  | .done, _, path, rest => by
      cases path
      exact heq_of_eq (toTypeTreePath_ofTypeTreePath rest)
  | .public _ branches, suffix, path, rest => by
      apply runtimePath_node_heq
        (fun move => toTypeTree_append (branches move) (fun p => suffix ⟨move, p⟩))
        path.1
      exact toTypeTreePath_append_heq (branches path.1)
        (fun p => suffix ⟨path.1, p⟩) path.2 rest
  | .oracle _ branches, suffix, path, rest => by
      apply runtimePath_node_heq
        (fun _ => toTypeTree_append (branches PUnit.unit) (fun p => suffix ⟨PUnit.unit, p⟩))
        path.1
      exact toTypeTreePath_append_heq (branches PUnit.unit)
        (fun p => suffix ⟨PUnit.unit, p⟩) path.2 rest

/-- Joining runtime paths and then recovering their concrete oracle messages agrees with joining
those messages directly. The cast identifies only the runtime trees proved equal by append. -/
theorem ofTypeTreePath_append (tree : TypeTree.{u})
    (suffix : BranchPath tree → TypeTree.{u})
    (path : _root_.Interaction.TypeTree.Path tree.toTypeTree)
    (rest : _root_.Interaction.TypeTree.Path
      (suffix (ofTypeTreePath path).toBranchPath).toTypeTree) :
    ofTypeTreePath (cast (congrArg _root_.Interaction.TypeTree.Path
      (toTypeTree_append tree suffix).symm)
      (PFunctor.FreeM.Path.append tree.toTypeTree
        (fun p => (suffix (ofTypeTreePath p).toBranchPath).toTypeTree) path rest)) =
      PFunctor.FreeM.PathAlong.append runtimeLens tree suffix
        (ofTypeTreePath path) (ofTypeTreePath rest) := by
  have same := eq_of_heq ((cast_heq (congrArg _root_.Interaction.TypeTree.Path
    (toTypeTree_append tree suffix).symm) _).trans
      (toTypeTreePath_append_heq tree suffix path rest).symm)
  rw [same, ofTypeTreePath_toTypeTreePath]

end ExecutionPath

end TypeTree
end Interaction.Oracle

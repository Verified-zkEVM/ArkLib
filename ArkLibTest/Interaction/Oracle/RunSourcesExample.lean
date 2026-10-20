/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.RunSources

/-! # Realized-source acceptance: retained terminal slots and hidden representations -/

namespace Interaction.Oracle.RunSourcesExample

open Interaction.Oracle.TypeTree

/-- Only the first coordinate can be queried. -/
@[reducible]
def interface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

/-- A public choice followed by two oracle sends, the second immediately before termination. -/
abbrev tree : Oracle.TypeTree :=
  .public Bool fun _ => .oracle (Nat × Nat) fun _ => .oracle (Nat × Nat) fun _ => .done

/-- Both oracle slots use the same query and answer types. -/
def oracles : tree.OracleDecoration :=
  ⟨PUnit.unit, fun _ => ⟨interface, fun _ => ⟨interface, fun _ => PUnit.unit⟩⟩⟩

/-- An arbitrary initial behavior, independently of the two sent objects. -/
abbrev initial : PFunctor := (Unit →ₒ Nat).toPFunctor

/-- An execution with a private coordinate in each message. -/
def path (hidden : Nat) : tree.ExecutionPath :=
  ⟨true, (11, hidden), (19, hidden + 1), PUnit.unit⟩

/-- The final query signature. -/
abbrev finalSpec :=
  OracleSpec.ofPFunctor (accessAfter tree oracles initial (path 0).toBranchPath)

/-- Final access distinguishes the input, first sent, and last sent slots. -/
def readAll : OracleComp
    finalSpec
    (Nat × Nat × Nat) := do
  let old : Nat ← liftM (finalSpec.query (.inl (.inl ())))
  let first : Nat ← liftM (finalSpec.query (.inl (.inr ())))
  let last : Nat ← liftM (finalSpec.query (.inr ()))
  return (old, first, last)

example (hidden : Nat) :
    simulateQ ((path hidden).closingImpl oracles initial (fun _ => 7)) readAll =
      (7, 11, 19) := rfl

example (hidden₁ hidden₂ : Nat) :
    (path hidden₁).closingImpl oracles initial (fun _ => 7) =
      (path hidden₂).closingImpl oracles initial (fun _ => 7) := by
  funext query
  rcases query with (_ | _) | _ <;> rfl

/-- Structural paths through an impossible send do not manufacture a concrete message. -/
example : IsEmpty (OracleMessagesAt (.oracle Empty fun _ => .done)
    ⟨PUnit.unit, PUnit.unit⟩) := by
  change IsEmpty (Empty × PUnit)
  infer_instance

end Interaction.Oracle.RunSourcesExample

/-! ## Dependent append with distinguishable resource slots

A public Bool selects the suffix shape: one oracle send, or a public node followed by two sends.
The concrete messages retain private coordinates, and all same-signature slots remain distinct.
These are laws of the supplied paths, without asserting reachability by an adversary or verifier.
-/

namespace Interaction.Oracle.RunSourcesExample.Append

open Interaction.Oracle.TypeTree
open PFunctor.FreeM.Displayed (Decoration)

abbrev firstTree : Oracle.TypeTree :=
  .public Bool fun _ => .oracle (Nat × Nat) fun _ => .done

@[reducible]
def firstOracles : firstTree.OracleDecoration :=
  ⟨PUnit.unit, fun _ => ⟨interface, fun _ => PUnit.unit⟩⟩

@[reducible]
def secondTree (path : firstTree.BranchPath) : Oracle.TypeTree :=
  match path.1 with
  | true => .oracle (Nat × Nat) fun _ => .done
  | false => .public Unit fun _ =>
      .oracle (Nat × Nat) fun _ => .oracle (Nat × Nat) fun _ => .done

@[reducible]
def secondOracles (path : firstTree.BranchPath) : (secondTree path).OracleDecoration :=
  match path with
  | ⟨true, _⟩ => ⟨interface, fun _ => PUnit.unit⟩
  | ⟨false, _⟩ =>
      ⟨PUnit.unit, fun _ => ⟨interface, fun _ => ⟨interface, fun _ => PUnit.unit⟩⟩⟩


@[reducible]
def firstPath (branch : Bool) (hidden : Nat) : firstTree.ExecutionPath :=
  ⟨branch, (11, hidden), PUnit.unit⟩

@[reducible]
def secondPath (branch : Bool) (hidden : Nat) :
    (secondTree (firstPath branch hidden).toBranchPath).ExecutionPath :=
  match branch with
  | true => ⟨(19, hidden + 1), PUnit.unit⟩
  | false => ⟨(), (23, hidden + 1), (29, hidden + 2), PUnit.unit⟩

def combinedPath (branch : Bool) (hidden : Nat) :
    ExecutionPath (PFunctor.FreeM.append firstTree secondTree) :=
  PFunctor.FreeM.PathAlong.append runtimeLens firstTree secondTree
    (firstPath branch hidden) (secondPath branch hidden)

/-- The prefix challenge is receiver-owned; oracle messages remain implicitly sender-owned. -/
def firstRoles : firstTree.RoleDecoration :=
  ⟨TwoParty.Role.receiver, fun _ => ⟨PUnit.unit, fun _ => PUnit.unit⟩⟩

def secondRoles (path : firstTree.BranchPath) : (secondTree path).RoleDecoration :=
  match path with
  | ⟨true, _⟩ => ⟨PUnit.unit, fun _ => PUnit.unit⟩
  | ⟨false, _⟩ =>
      ⟨TwoParty.Role.sender, fun _ =>
        ⟨PUnit.unit, fun _ => ⟨PUnit.unit, fun _ => PUnit.unit⟩⟩⟩

/-- Runtime erasure retains genuinely different suffix shapes after the public choice. -/
example : TypeTree.toTypeTree (PFunctor.FreeM.append firstTree secondTree) =
    _root_.Interaction.TypeTree.node Bool (fun branch =>
      _root_.Interaction.TypeTree.node (Nat × Nat) (fun _ => match branch with
      | true => _root_.Interaction.TypeTree.node (Nat × Nat) (fun _ => .done)
      | false => _root_.Interaction.TypeTree.node Unit (fun _ =>
          _root_.Interaction.TypeTree.node (Nat × Nat) (fun _ =>
            _root_.Interaction.TypeTree.node (Nat × Nat) (fun _ => .done))))) := by
  apply congrArg (_root_.Interaction.TypeTree.node Bool)
  funext branch
  apply congrArg (_root_.Interaction.TypeTree.node (Nat × Nat))
  funext message
  cases branch <;> rfl

/-- The exported role append law applies to the receiver challenge and both suffix shapes. -/
example :
    cast (congrArg TwoParty.RoleDecoration (toTypeTree_append firstTree secondTree))
      (RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append firstTree secondTree)
        (Decoration.append firstRoles secondRoles)) =
      Decoration.append (RoleDecoration.toTypeTreeRoles firstTree firstRoles) (fun path =>
        RoleDecoration.toTypeTreeRoles
          (secondTree (ExecutionPath.ofTypeTreePath path).toBranchPath)
          (secondRoles (ExecutionPath.ofTypeTreePath path).toBranchPath)) :=
  RoleDecoration.toTypeTreeRoles_append firstTree secondTree firstRoles secondRoles

example :
    (RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append firstTree secondTree)
      (Decoration.append firstRoles secondRoles)).1 = TwoParty.Role.receiver := rfl

example (branch : Bool) :
    ((RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append firstTree secondTree)
      (Decoration.append firstRoles secondRoles)).2 branch).1 = TwoParty.Role.sender := rfl

/-- Concrete append/split round-trips preserve the actual messages, not only the public branch. -/
example (branch : Bool) (hidden : Nat) :
    PFunctor.FreeM.PathAlong.split runtimeLens firstTree secondTree
      (combinedPath branch hidden) = ⟨firstPath branch hidden, secondPath branch hidden⟩ := by
  exact PFunctor.FreeM.PathAlong.split_append runtimeLens firstTree secondTree
    (firstPath branch hidden) (secondPath branch hidden)

/-- Splitting the public projection selects the same dependent suffix as the concrete split. -/
example (branch : Bool) (hidden : Nat) :
    PFunctor.FreeM.Path.split firstTree secondTree (combinedPath branch hidden).toBranchPath =
      ⟨(firstPath branch hidden).toBranchPath, (secondPath branch hidden).toBranchPath⟩ := by
  rw [combinedPath, ExecutionPath.toBranchPath_append, PFunctor.FreeM.Path.split_append]

abbrev secondAccess (branch : Bool) (hidden : Nat) :=
  accessAfter (secondTree (firstPath branch hidden).toBranchPath)
    (secondOracles (firstPath branch hidden).toBranchPath)
    (accessAfter firstTree firstOracles initial (firstPath branch hidden).toBranchPath)
    (secondPath branch hidden).toBranchPath

abbrev secondSpec (branch : Bool) (hidden : Nat) :=
  OracleSpec.ofPFunctor (secondAccess branch hidden)

/-- Query the original resource and each concrete prefix/suffix send, in slot order. -/
def readAll (branch : Bool) (hidden : Nat) :
    OracleComp (secondSpec branch hidden) (List Nat) :=
  match branch with
  | true => do
      let old : Nat ← liftM ((secondSpec true hidden).query (.inl (.inl ())))
      let first : Nat ← liftM ((secondSpec true hidden).query (.inl (.inr ())))
      let last : Nat ← liftM ((secondSpec true hidden).query (.inr ()))
      return [old, first, last]
  | false => do
      let old : Nat ← liftM ((secondSpec false hidden).query (.inl (.inl (.inl ()))))
      let first : Nat ← liftM ((secondSpec false hidden).query (.inl (.inl (.inr ()))))
      let next : Nat ← liftM ((secondSpec false hidden).query (.inl (.inr ())))
      let last : Nat ← liftM ((secondSpec false hidden).query (.inr ()))
      return [old, first, next, last]

/-- Split interpretation independently computes the branch-specific, distinguishable answers. -/
example (branch : Bool) (hidden : Nat) :
    simulateQ ((secondPath branch hidden).closingImpl
      (secondOracles (firstPath branch hidden).toBranchPath)
      (accessAfter firstTree firstOracles initial (firstPath branch hidden).toBranchPath)
      ((firstPath branch hidden).closingImpl firstOracles initial (fun _ => 7)))
      (readAll branch hidden) = if branch then [7, 11, 19] else [7, 11, 23, 29] := by
  cases branch <;> rfl

/-- The exported append query law recovers the same answers from the combined concrete path. -/
example (branch : Bool) (hidden : Nat) :
    simulateQ (cast (congrArg (fun access => QueryImpl (OracleSpec.ofPFunctor access) Id)
      (accessAfter_append_execution firstTree secondTree firstOracles secondOracles initial
        (firstPath branch hidden) (secondPath branch hidden)))
      ((combinedPath branch hidden).closingImpl (Decoration.append firstOracles secondOracles)
        initial (fun _ => 7))) (readAll branch hidden) =
      if branch then [7, 11, 19] else [7, 11, 23, 29] := by
  exact (ExecutionPath.simulateQ_closingImpl_append firstTree secondTree firstOracles
    secondOracles initial (firstPath branch hidden) (secondPath branch hidden)
    (fun _ => 7) (readAll branch hidden)).trans (by cases branch <;> rfl)

/-- Hidden coordinates remain opaque in both suffix shapes; changing them changes no answer. -/
example (branch : Bool) (hidden₁ hidden₂ : Nat) :
    HEq ((combinedPath branch hidden₁).closingImpl
      (Decoration.append firstOracles secondOracles) initial (fun _ => 7))
      ((combinedPath branch hidden₂).closingImpl
        (Decoration.append firstOracles secondOracles) initial (fun _ => 7)) := by
  cases branch <;> apply heq_of_eq <;> funext query
  · rcases query with ((_ | _) | _) | _ <;> rfl
  · rcases query with (_ | _) | _ <;> rfl

end Interaction.Oracle.RunSourcesExample.Append

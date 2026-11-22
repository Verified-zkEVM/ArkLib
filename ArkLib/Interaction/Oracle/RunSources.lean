/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Access
public import ArkLib.Interaction.Oracle.Source

/-!
# Sources of a completed oracle execution

A structural path determines the types of messages, while a concrete execution supplies their
values. Together with arbitrary input behavior these values realize exactly the final accumulated
access signature. No inhabitance or reachability of arbitrary structural paths is assumed.
-/

@[expose] public section

universe u v

namespace Interaction.Oracle.TypeTree

/-- Concrete oracle messages along a structural path; public moves are already in the index. -/
def OracleMessagesAt : (tree : Oracle.TypeTree.{u}) → tree.BranchPath → Type u
  | .done, _ => PUnit
  | .public _ rest, path => OracleMessagesAt (rest path.1) path.2
  | .oracle Messages rest, path => Messages × OracleMessagesAt (rest path.1) path.2

/-- A realized execution provides messages even when arbitrary message types may be empty. -/
def ExecutionPath.oracleMessages : {tree : Oracle.TypeTree.{u}} →
    (path : tree.ExecutionPath) → OracleMessagesAt tree path.toBranchPath
  | .done, _ => PUnit.unit
  | .public _ _, path => ExecutionPath.oracleMessages path.2
  | .oracle _ _, path => ⟨path.1, ExecutionPath.oracleMessages path.2⟩

/-- Interpret final access by extending the input handler with each actual oracle message. -/
def answerAfter : (tree : Oracle.TypeTree.{u}) → (oracles : tree.OracleDecoration.{u, v}) →
    (initial : PFunctor.{v, u}) → (path : tree.BranchPath) →
    QueryImpl (OracleSpec.ofPFunctor initial) Id → OracleMessagesAt tree path →
    QueryImpl (OracleSpec.ofPFunctor (accessAfter tree oracles initial path)) Id
  | .done, _, _, _, impl, _ => impl
  | .public _ rest, oracles, initial, path, impl, messages =>
      answerAfter (rest path.1) (oracles.2 path.1) initial path.2 impl messages
  | .oracle _ rest, oracles, initial, path, impl, messages =>
      answerAfter (rest path.1) (oracles.2 path.1) (Access.extend initial oracles.1) path.2
        (Access.extendImpl initial oracles.1 impl messages.1) messages.2

/-- The canonical extensional source behind final access; its environment contains input behavior
and the messages of this structural branch, never objects for unvisited branches. -/
def sourceAfter (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration.{u, v})
    (initial : PFunctor.{v, u}) (path : tree.BranchPath) :
    SourceCtx (accessAfter tree oracles initial path).A
      (QueryImpl (OracleSpec.ofPFunctor initial) Id × OracleMessagesAt tree path) where
  spec := OracleSpec.ofPFunctor (accessAfter tree oracles initial path)
  impl := fun query env => answerAfter tree oracles initial path env.1 env.2 query

/-- Final source interpretation uses the execution-order handler extension. -/
theorem sourceAfter_handler (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration.{u, v})
    (initial : PFunctor.{v, u}) (path : tree.BranchPath)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (messages : OracleMessagesAt tree path) :
    (sourceAfter tree oracles initial path).handler (impl, messages) =
      answerAfter tree oracles initial path impl messages := rfl

/-- Final source behavior canonically extracted from one concrete path and its input behavior. -/
def ExecutionPath.closingImpl {tree : Oracle.TypeTree.{u}} (path : tree.ExecutionPath)
    (oracles : tree.OracleDecoration.{u, v}) (initial : PFunctor.{v, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) :
    QueryImpl (OracleSpec.ofPFunctor (accessAfter tree oracles initial path.toBranchPath)) Id :=
  answerAfter tree oracles initial path.toBranchPath impl path.oracleMessages

@[simp]
theorem ExecutionPath.closingImpl_done (path : ExecutionPath (.done : Oracle.TypeTree.{u}))
    (oracles : OracleDecoration.{u, v} .done) (initial : PFunctor.{v, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) :
    path.closingImpl oracles initial impl = impl := rfl

@[simp]
theorem ExecutionPath.closingImpl_public (Moves : Type u) (rest : Moves → Oracle.TypeTree.{u})
    (path : ExecutionPath (.public Moves rest))
    (oracles : OracleDecoration.{u, v} (.public Moves rest)) (initial : PFunctor.{v, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) :
    path.closingImpl oracles initial impl =
      ExecutionPath.closingImpl path.2 (oracles.2 path.1) initial impl := rfl

@[simp]
theorem ExecutionPath.closingImpl_oracle (Messages : Type u)
    (rest : PUnit.{u + 1} → Oracle.TypeTree.{u}) (path : ExecutionPath (.oracle Messages rest))
    (oracles : OracleDecoration.{u, v} (.oracle Messages rest)) (initial : PFunctor.{v, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) :
    path.closingImpl oracles initial impl =
      ExecutionPath.closingImpl path.2 (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl path.1) := rfl

/-- The concrete handler of an appended execution is the suffix's handler extended from the
prefix's actual handler. This heterogeneous equality keeps the independently computed signatures
visible; `closingImpl_append` gives the ordinary equality after their canonical identification. -/
private theorem ExecutionPath.closingImpl_append_heq :
    (tree : Oracle.TypeTree.{u}) → (suffix : BranchPath tree → Oracle.TypeTree.{u}) →
    (first : OracleDecoration.{u, v} tree) →
    (second : (p : BranchPath tree) → OracleDecoration.{u, v} (suffix p)) →
    (initial : PFunctor.{v, u}) → (path : ExecutionPath tree) →
    (rest : ExecutionPath (suffix path.toBranchPath)) →
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) →
    HEq (ExecutionPath.closingImpl
      (PFunctor.FreeM.PathAlong.append runtimeLens tree suffix path rest)
      (PFunctor.FreeM.Displayed.Decoration.append first second) initial impl)
      (rest.closingImpl (second path.toBranchPath)
        (accessAfter tree first initial path.toBranchPath) (path.closingImpl first initial impl))
  | .done, _, _, _, _, _, _, _ => HEq.rfl
  | .public _ restTree, suffix, first, second, initial, path, rest, impl =>
      ExecutionPath.closingImpl_append_heq (restTree path.1)
        (fun tail => suffix ⟨path.1, tail⟩) (first.2 path.1)
        (fun tail => second ⟨path.1, tail⟩) initial path.2 rest impl
  | .oracle _ restTree, suffix, first, second, initial, path, rest, impl =>
      ExecutionPath.closingImpl_append_heq (restTree PUnit.unit)
        (fun tail => suffix ⟨PUnit.unit, tail⟩) (first.2 PUnit.unit)
        (fun tail => second ⟨PUnit.unit, tail⟩) (Access.extend initial first.1) path.2 rest
        (Access.extendImpl initial first.1 impl path.1)

/-- Closing append uses the input resources and concrete messages of these same two paths.
The cast only identifies the signatures proved equal by `accessAfter_append_execution`; it does
not replace the handler or forget the messages. -/
theorem ExecutionPath.closingImpl_append (tree : Oracle.TypeTree.{u})
    (suffix : BranchPath tree → Oracle.TypeTree.{u})
    (first : OracleDecoration.{u, v} tree)
    (second : (p : BranchPath tree) → OracleDecoration.{u, v} (suffix p))
    (initial : PFunctor.{v, u}) (path : ExecutionPath tree)
    (rest : ExecutionPath (suffix path.toBranchPath))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) :
    cast (congrArg (fun access => QueryImpl (OracleSpec.ofPFunctor access) Id)
      (accessAfter_append_execution tree suffix first second initial path rest))
      (ExecutionPath.closingImpl
      (PFunctor.FreeM.PathAlong.append runtimeLens tree suffix path rest)
        (PFunctor.FreeM.Displayed.Decoration.append first second) initial impl) =
      rest.closingImpl (second path.toBranchPath)
        (accessAfter tree first initial path.toBranchPath) (path.closingImpl first initial impl) :=
  eq_of_heq ((cast_heq _ _).trans
    (ExecutionPath.closingImpl_append_heq tree suffix first second initial path rest impl))

/-- Every query program receives the same answers from closing the combined execution as from
closing its prefix and then its suffix. Original resources and both fragments' messages keep their
execution-order slots, even when those slots have identical signatures. -/
theorem ExecutionPath.simulateQ_closingImpl_append {α : Type u} (tree : Oracle.TypeTree.{u})
    (suffix : BranchPath tree → Oracle.TypeTree.{u})
    (first : OracleDecoration.{u, v} tree)
    (second : (p : BranchPath tree) → OracleDecoration.{u, v} (suffix p))
    (initial : PFunctor.{v, u}) (path : ExecutionPath tree)
    (rest : ExecutionPath (suffix path.toBranchPath))
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (program : OracleComp (OracleSpec.ofPFunctor (accessAfter (suffix path.toBranchPath)
      (second path.toBranchPath) (accessAfter tree first initial path.toBranchPath)
      rest.toBranchPath)) α) :
    simulateQ (cast (congrArg (fun access => QueryImpl (OracleSpec.ofPFunctor access) Id)
      (accessAfter_append_execution tree suffix first second initial path rest))
      (ExecutionPath.closingImpl
      (PFunctor.FreeM.PathAlong.append runtimeLens tree suffix path rest)
        (PFunctor.FreeM.Displayed.Decoration.append first second) initial impl)) program =
      simulateQ (rest.closingImpl (second path.toBranchPath)
        (accessAfter tree first initial path.toBranchPath) (path.closingImpl first initial impl))
        program := by
  rw [ExecutionPath.closingImpl_append]

end Interaction.Oracle.TypeTree

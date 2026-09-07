/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Access
import ArkLib.Interaction.Oracle.Source

/-!
# Sources of a completed oracle execution

A structural path determines the types of messages, while a concrete execution supplies their
values. Together with arbitrary input behavior these values realize exactly the final accumulated
access signature. No inhabitance or reachability of arbitrary structural paths is assumed.
-/

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
def sourcesAfter (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration.{u, v})
    (initial : PFunctor.{v, u}) (path : tree.BranchPath) :
    SourceCtx (accessAfter tree oracles initial path).A
      (QueryImpl (OracleSpec.ofPFunctor initial) Id × OracleMessagesAt tree path) where
  spec := OracleSpec.ofPFunctor (accessAfter tree oracles initial path)
  impl := fun query env => answerAfter tree oracles initial path env.1 env.2 query

/-- Final source interpretation uses the execution-order handler extension. -/
theorem sourcesAfter_handler (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration.{u, v})
    (initial : PFunctor.{v, u}) (path : tree.BranchPath)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (messages : OracleMessagesAt tree path) :
    (sourcesAfter tree oracles initial path).handler (impl, messages) =
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

end Interaction.Oracle.TypeTree

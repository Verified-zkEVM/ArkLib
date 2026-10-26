/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Data.OracleComp.Vector
import Lean.Compiler.IR

/-! # Finite vector simulation preserves effectful handlers, entry order and empty traversals -/

open OracleComp OracleSpec
open Lean Elab Command
namespace OracleVectorSimulationTest
abbrev spec : OracleSpec (Fin 3) := Fin 3 →ₒ Nat

def entry (i : Fin 3) : OracleComp spec Nat := do
  let a ← liftM (spec.query i)
  if i.val = 1 then return a + 100
  else
    let b ← liftM (spec.query i)
    return a + b

def answer : QueryImpl spec (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return (10 * i.val + 1 : Nat)

def idAnswer : QueryImpl spec Id := fun i => 10 * i.val + 1

def program : OracleComp spec (Vector Nat 3) := Vector.ofFnM entry
def actual : Vector Nat 3 × List Nat := (simulateQ answer program).run [99]
def mapped : Vector Nat 3 × List Nat :=
  (Vector.ofFnM fun i => simulateQ answer (entry i)).run [99]
def deterministic : Vector Nat 3 := simulateQ (r := Id) idAnswer program

theorem effectful_equality : actual = mapped :=
  congrArg (fun run => run.run [99]) (simulateQ_vectorOfFnM answer entry)

theorem deterministic_equality : deterministic = Vector.ofFn (fun i =>
    simulateQ (r := Id) idAnswer (entry i)) := simulateQ_ofFnM idAnswer entry

def empty : OracleComp spec (Vector Nat 0) :=
  Vector.ofFnM (fun i : Fin 0 => (Fin.elim0 i : OracleComp spec Nat))
def emptyResult : Vector Nat 0 × List Nat := (simulateQ answer empty).run [99]

theorem empty_equality : simulateQ answer empty = pure (#v[] : Vector Nat 0) := by
  rw [empty, Vector.ofFnM_zero, simulateQ_pure]

def branching (i : Fin 3) : OracleComp spec Nat := do
  let a ← liftM (spec.query i)
  if a = 0 then return a
  else
    let b ← liftM (spec.query ⟨a % 3, Nat.mod_lt _ (by decide)⟩)
    return a + b

def loggedAnswer : QueryImpl spec Id := fun i => ![0, 5, 4] i
def logged := simulateQ loggedAnswer (Vector.ofFnM branching).withQueryLog
def loggedSummary : Vector Nat 3 × List (Nat × Nat) :=
  (logged.1, logged.2.map fun entry => (entry.1.val, entry.2))

theorem logged_equality : logged =
    (Vector.ofFn (fun i => (simulateQ loggedAnswer (branching i).withQueryLog).1),
      (List.finRange 3).flatMap
        (fun i => (simulateQ loggedAnswer (branching i).withQueryLog).2)) :=
  simulateQ_withQueryLog_ofFnM loggedAnswer branching

theorem empty_logged_equality :
    simulateQ idAnswer empty.withQueryLog = (#v[], []) := by
  rw [empty, simulateQ_withQueryLog_ofFnM]
  rfl

run_cmd do
  unless actual == (#v[2, 111, 42], [99, 0, 0, 1, 2, 2]) do
    throwError "effectful vector simulation lost duplicate requests, order or initial state"
  unless mapped == actual do
    throwError "generic monad morphism vector law changed actual target effects"
  unless deterministic == #v[2, 111, 42] do
    throwError "Id vector simulation changed its entry values"
  unless emptyResult == (#v[], [99]) do
    throwError "empty vector simulation invoked an impossible callback or changed target state"
  unless loggedSummary == (#v[0, 9, 9], [(0, 0), (1, 5), (2, 4), (2, 4), (1, 5)]) do
    throwError "logged traversal lost answer-dependent fanout, repeated queries or response order"
  for name in #[``entry, ``answer, ``idAnswer, ``program, ``actual, ``mapped,
      ``deterministic, ``empty, ``emptyResult, ``branching, ``loggedAnswer,
      ``logged, ``loggedSummary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing vector simulation caller executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``MonadHom.map_vector_ofFnM, ``simulateQ_vectorOfFnM, ``simulateQ_ofFnM,
      ``simulateQ_withQueryLog_ofFnM, ``effectful_equality, ``deterministic_equality,
      ``empty_equality, ``logged_equality, ``empty_logged_equality] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "vector simulation has an unexpected axiom: {name}"
end OracleVectorSimulationTest

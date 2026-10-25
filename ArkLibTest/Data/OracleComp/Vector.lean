/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
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

run_cmd do
  unless actual == (#v[2, 111, 42], [99, 0, 0, 1, 2, 2]) do
    throwError "effectful vector simulation lost duplicate requests, order or initial state"
  unless mapped == actual do
    throwError "generic monad morphism vector law changed actual target effects"
  unless deterministic == #v[2, 111, 42] do
    throwError "Id vector simulation changed its entry values"
  unless emptyResult == (#v[], [99]) do
    throwError "empty vector simulation invoked an impossible callback or changed target state"
  for name in #[``entry, ``answer, ``idAnswer, ``program, ``actual, ``mapped,
      ``deterministic, ``empty, ``emptyResult] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing vector simulation caller executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``MonadHom.map_vector_ofFnM, ``simulateQ_vectorOfFnM, ``simulateQ_ofFnM,
      ``effectful_equality, ``deterministic_equality, ``empty_equality] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "vector simulation has an unexpected axiom: {name}"
end OracleVectorSimulationTest

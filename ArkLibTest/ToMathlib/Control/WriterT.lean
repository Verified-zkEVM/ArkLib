/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.Control.WriterT
import Lean.Compiler.IR

/-! # Append-writer lift laws and ordered base effects -/

namespace AppendWriterLiftTests

universe u v

example {m : Type u → Type v} [Monad m] [LawfulMonad m] {ω : Type u}
    [EmptyCollection ω] [Append ω] (hempty : (∅ : ω) ++ ∅ = ∅) :
    LawfulMonadLift m (WriterT ω m) := WriterT.lawfulMonadLiftAppend hempty

local instance {m : Type → Type} [Monad m] [LawfulMonad m] :
    LawfulMonadLift m (WriterT (List Nat) m) :=
  WriterT.lawfulMonadLiftAppend (by rfl)

example {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (program : m α) (next : α → m β) :
    (liftM (program >>= next) : WriterT (List Nat) m β) =
      ((liftM program : WriterT (List Nat) m α) >>= fun a => liftM (next a)) :=
  LawfulMonadLift.monadLift_bind program next

def advance (amount : Nat) : StateM Nat Nat := do
  modify (· + amount)
  get

def observed : WriterT (List Nat) (StateM Nat) Nat := do
  let first ← liftM (advance 1)
  tell [first]
  let second ← liftM (advance 2)
  tell [second]
  return first + second

/-- This append deliberately has no right identity on nonempty values. -/
structure WeakLog where
  value : Nat
  deriving BEq, Repr

instance : EmptyCollection WeakLog := ⟨⟨0⟩⟩
instance : Append WeakLog := ⟨fun a b => ⟨if a.value = 0 then b.value else a.value+b.value+1⟩⟩

local instance {m : Type → Type} [Monad m] [LawfulMonad m] :
    LawfulMonadLift m (WriterT WeakLog m) :=
  WriterT.lawfulMonadLiftAppend (by rfl)

example : ((⟨1⟩ : WeakLog) ++ ∅).value = 2 := by decide

example {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (program : m α) (next : α → m β) :
    (liftM (program >>= next) : WriterT WeakLog m β) =
      ((liftM program : WriterT WeakLog m α) >>= fun a => liftM (next a)) :=
  LawfulMonadLift.monadLift_bind program next

open Lean Elab Command in
run_cmd do
  unless (observed.run.run 0).run == ((4, [1,3]), 3) do
    throwError "writer lifting changed base effect order or retained logs"
  let emptyLift : WriterT WeakLog (StateM Nat) Nat := liftM (advance 5)
  unless (emptyLift.run.run 7).run == ((12, ⟨0⟩), 12) do
    throwError "weak append lift wrote a nonempty log or lost base state"
  unless (← collectAxioms ``WriterT.lawfulMonadLiftAppend).all
      #[``propext, ``Classical.choice, ``Quot.sound].contains do
    throwError "unexpected append-writer lift axiom"
  unless (Lean.IR.findEnvDecl (← getEnv) ``observed).isSome do
    throwError "missing ordinary writer effect caller IR"

end AppendWriterLiftTests

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Univariate.Raw.Horner
import Mathlib.LinearAlgebra.Matrix.Notation
import Lean.Compiler.IR

/-! # Ordinary seeded Horner clients and operand order -/

open CompPoly.CPolynomial.Raw
namespace SeededHornerTests

example {R : Type} [Semiring R] (p : Array R) (x : R) :
    evalHornerSeeded x p = evalHorner x p := evalHornerSeeded_eq_evalHorner x p

inductive Event where
  | read (index : Nat)
  | mul (left right : Nat)
  | add (left right : Nat)
  deriving BEq, Repr

def traced (p : Array Nat) (x : Nat) : Nat × List Event :=
  (evalHornerM (m := StateM (List Event))
    (fun i => do modify (· ++ [.read i]); pure (p[i]?.getD 0))
    (fun a b => do modify (· ++ [.mul a b]); pure (a * b))
    (fun a b => do modify (· ++ [.add a b]); pure (a + b)) p.size x).run []

def matrixAnswer : Matrix (Fin 2) (Fin 2) Nat :=
  evalHornerSeeded !![0, 1; 1, 1]
    #[!![1, 2; 0, 1], !![0, 1; 3, 0], !![2, 0; 0, 4]]

#eval (show IO _ from do
  unless traced #[2, 3, 5] 7 ==
      (268, [.read 2, .read 1, .mul 5 7, .add 35 3,
        .read 0, .mul 38 7, .add 266 2]) do
    throw (IO.userError "Horner seed, callback order or operand order changed")
  unless traced #[] 7 == (0, []) && traced #[9] 7 == (9, [.read 0]) do
    throw (IO.userError "empty/singleton Horner invoked an extra callback")
  unless evalHornerSeeded 0 #[2, 3, 5, 0] == 2 &&
      evalHornerSeeded 1 #[2, 3, 5, 0] == 10 &&
      evalHornerSeeded 7 #[2, 3, 5, 0] == 268 &&
      evalHornerSeeded 1 (Array.replicate 100000 (1 : Nat)) == 100000 do
    throw (IO.userError "padded, zero/one or long tail-loop evaluation failed")
  unless matrixAnswer 0 0 == 4 && matrixAnswer 0 1 == 5 &&
      matrixAnswer 1 0 == 4 && matrixAnswer 1 1 == 12 do
    throw (IO.userError "noncommutative Horner reversed multiplication operands")
  pure (268, 100000))

open Lean Elab Command in
run_cmd do
  for name in #[``traced, ``matrixAnswer, ``hornerLoopM, ``evalHornerM, ``evalHornerSeeded] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``evalHornerM_congr_read, ``evalHornerSeeded_eq_evalHorner] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"

end SeededHornerTests

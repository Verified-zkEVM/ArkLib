/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToCompPoly.Univariate.ArithmeticHorner
import ArkLib.ProofSystem.Sumcheck.Impl.Representation
import Lean.Compiler.IR

/-! # Shared seeded Horner erasure and exact request profiles -/

open CompPoly OracleComp OracleSpec
namespace ArithmeticHornerTests
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

example (p : Array F) (x : F) :
    simulateQ arithmeticAnswer (Arithmetic.evalHornerProgram p x) =
      CPolynomial.Raw.evalHornerSeeded x p := Arithmetic.simulateQ_evalHornerProgram p x

-- The existing message evaluator keeps its CommSemiring-only public signature.
example {R : Type} [CommSemiring R] (deg : Nat)
    (q : Sumcheck.Impl.Representation.Message R deg) (x : R) :
    Sumcheck.Impl.Representation.evaluate R deg q x =
      CPolynomial.Raw.evalHornerSeeded x q.val.val := rfl

-- An actual reader whose metadata costs vary by index, without a coefficient-array read.
def reader (i : Nat) : OracleComp (ArithmeticSpec ℚ) ℚ :=
  if i = 0 then pure 2 else if i = 1 then do
    Arithmetic.tick
    pure 3
  else do
    Arithmetic.tick
    Arithmetic.tick
    pure 5

def readerValue (i : Nat) : ℚ := if i = 0 then 2 else if i = 1 then 3 else 5

def readerCost (i : Nat) : ArithmeticCost :=
  fun kind => if kind = .metadata then i else 0

theorem profile_reader (i : Fin 3) :
    profileArithmetic (reader i.val) = (readerValue i.val, readerCost i.val) := by
  fin_cases i <;> apply Prod.ext
  all_goals first
    | funext kind; cases kind <;>
        simp [reader, readerCost, arithmeticCost, ArithmeticOp.costKind,
          profileArithmetic_bind, profileArithmetic_map]
    | simp [reader, readerValue, profileArithmetic_bind, profileArithmetic_map]

theorem profile_custom_reader :
    profileArithmetic (Arithmetic.evalHornerWithReadProgram reader 3 7) =
      (CPolynomial.Raw.evalHornerM (m := Id) readerValue
        (fun a b => a * b) (fun a b => a + b) 3 7,
        Arithmetic.hornerCost 3 readerCost) := by
  apply Arithmetic.profileArithmetic_evalHornerWithReadProgram
  intro i hi
  exact profile_reader ⟨i, hi⟩

inductive Event where
  | read (index : Nat)
  | mul (left right : ℚ)
  | add (left right : ℚ)
  | other
  deriving BEq, Repr

def recorder : QueryImpl (ArithmeticSpec ℚ) (StateM (List Event)) := fun op => do
  let event := match op with
    | .coefficientRead _ i => .read i
    | .mul a b => .mul a b
    | .add a b => .add a b
    | _ => .other
  modify (· ++ [event])
  pure (arithmeticAnswer op)

#eval (show IO _ from do
  for p in #[#[], #[9], #[2, 3, 5], #[2, 3, 5, 0]] do
    for x in #[(0 : ℚ), 1, 7] do
      let program := Arithmetic.evalHornerProgram p x
      let (value, cost) := profileArithmetic program
      unless value == CPolynomial.Raw.evalHornerSeeded x p &&
          cost .coefficientRead == p.size && cost .add == p.size - 1 &&
          cost .mul == p.size - 1 && cost .sub == 0 && cost .inv == 0 &&
          cost .eq == 0 && cost .nodeRead == 0 && cost .valueRead == 0 &&
          cost .metadata == 0 do
        throw (IO.userError "seeded Horner exact profile failed")
  let (value, trace) := (simulateQ recorder (Arithmetic.evalHornerProgram #[2, 3, 5] 7)).run []
  unless value == 268 && trace == [.read 2, .read 1, .mul 5 7, .add 35 3,
      .read 0, .mul 38 7, .add 266 2] do
    throw (IO.userError "actual arithmetic interpreter changed seed/read/operand order")
  let (customValue, customCost) :=
    profileArithmetic (Arithmetic.evalHornerWithReadProgram reader 3 7)
  unless customValue == 268 && customCost .metadata == 3 && customCost .add == 2 &&
      customCost .mul == 2 && customCost .coefficientRead == 0 && customCost .inv == 0 do
    throw (IO.userError "generic reader profile lost heterogeneous reader effects")
  pure (value, trace))

open Lean Elab Command in
run_cmd do
  for name in #[``reader, ``recorder, ``Arithmetic.evalHornerWithReadProgram,
      ``Arithmetic.evalHornerProgram] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Arithmetic.profileArithmetic_evalHornerWithReadProgram,
      ``Arithmetic.simulateQ_evalHornerWithReadProgram,
      ``Arithmetic.simulateQ_evalHornerProgram, ``Arithmetic.profileArithmetic_evalHornerProgram,
      ``profile_reader, ``profile_custom_reader, ``Sumcheck.Impl.Representation.evaluate_eq] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"

end ArithmeticHornerTests

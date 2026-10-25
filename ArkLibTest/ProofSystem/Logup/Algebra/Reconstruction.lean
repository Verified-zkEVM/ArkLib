/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Algebra.ArithmeticReconstruction
import Mathlib.Data.ZMod.Basic
import Lean.Compiler.IR

/-! # Shared scalar reconstruction: ring semantics, actual requests, and edge cases -/

open Logup CompPoly OracleComp OracleSpec
namespace ReconstructionTests

instance : Inv Int := ⟨fun _ => 37⟩

def caller {R : Type*} [CommRing R] {n T K : Nat}
    (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R)
    (helper : Fin K → R) : R := reconstruct groups alpha z lambda x value weight helper

def groups : Vector (List (Fin 3)) 2 := #v[[0, 1], [2]]
def value : Fin 3 → Int := ![2, 5, 2]
def weight : Fin 3 → Int := ![3, -4, 1]
def helper : Fin 2 → Int := ![7, -2]
def measured := Reconstruction.program groups (2 : Int) ![3] ![5, 9] ![-1] value weight helper

example : caller groups 2 ![3] ![5, 9] ![-1] value weight helper = -247 := by decide

example {R : Type*} [CommRing R] {n T K : Nat}
    (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R)
    (helper : Fin K → R) : caller groups alpha z lambda x value weight helper =
      reconstructWithKernel groups alpha (MvPolynomial.eqTilde z x)
        lambda value weight helper := reconstruct_eq_reconstructWithKernel _ _ _ _ _ _ _ _

example {R : Type} [CommRing R] [Inv R] [DecidableEq R] {n T K : Nat}
    (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R)
    (helper : Fin K → R) :
    profileArithmetic (Reconstruction.program groups alpha z lambda x value weight helper) =
      (caller groups alpha z lambda x value weight helper, Reconstruction.cost groups n) :=
  Reconstruction.profile_program_reconstruct _ _ _ _ _ _ _ _

inductive Event where
  | add (a b : Int)
  | sub (a b : Int)
  | mul (a b : Int)
  | unexpected
  deriving BEq, Repr

def logged : QueryImpl (ArithmeticSpec Int) (StateM (Array Event)) := fun op => do
  modify (·.push (match op with
    | .add a b => .add a b
    | .sub a b => .sub a b
    | .mul a b => .mul a b
    | _ => .unexpected))
  pure (arithmeticAnswer op)

def binary (x : Fin 2 → ZMod 2) : ZMod 2 :=
  caller #v[[0, 1]] 1 ![0, 1] ![1] x ![0, 1] ![1, 1] ![1]

example : binary ![0, 1] = 0 := by decide
example : binary ![1, 0] = 1 := by decide

-- Nonzero coordinate factors can multiply to zero over a ring with zero divisors.
example : caller #v[[0]] (1 : ZMod 4) ![2, 2] ![1] ![1, 1] ![1] ![2] ![3] = 3 := by
  decide

-- Empty occurrences with nonempty helper groups still contribute to the reconstruction.
example : caller (#v[[], []] : Vector (List (Fin 0)) 2) (0 : Int)
    Fin.elim0 ![3, 5] Fin.elim0 Fin.elim0 Fin.elim0 ![2, 7] = 50 := by decide

open Lean Elab Command in
run_cmd do
  let (result, events) := (simulateQ logged measured).run #[]
  unless result == -247 do throwError "asymmetric scalar reconstruction changed"
  let expected : Array Event := #[
    .sub 1 3, .add 3 3, .sub 6 1, .mul 5 (-1), .add (-2) (-5),
    .sub 2 2, .sub 2 5, .mul 3 (-3), .mul (-4) 0, .add (-9) 0, .mul 0 (-3),
    .mul 7 0, .sub 0 (-9), .mul 5 9, .add 0 7, .add 0 45,
    .sub 2 2, .mul (-2) 0, .sub 0 1, .mul 9 (-1), .add 7 (-2), .add 45 (-9),
    .mul (-7) 36, .add 5 (-252)]
  unless events == expected do throwError "shared circuit actual operand/request order changed"
  let profile := (profileArithmetic measured).2
  for kind in #[ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead,
      .nodeRead, .valueRead, .metadata] do
    let expected := match kind with | .add => 8 | .sub => 7 | .mul => 9 | _ => 0
    unless profile kind == expected do throwError "scalar profile coordinate changed"
  let empty := Reconstruction.program (#v[[], []] : Vector (List (Fin 0)) 2) (0 : Int)
    Fin.elim0 ![3, 5] Fin.elim0 Fin.elim0 Fin.elim0 ![2, 7]
  let (e, ecost) := profileArithmetic empty
  unless e == 50 && ecost .add == 5 && ecost .sub == 2 && ecost .mul == 5 do
    throwError "empty occurrence/nonempty helper circuit or cost changed"
  let kernel := Reconstruction.kernelProgram (fun _ : Fin 0 => (0 : Int)) Fin.elim0
  unless Id.run ((simulateQ logged kernel).run #[]) == (1, #[]) do
    throwError "zero-coordinate kernel issued requests or lost neutral one"
  for name in #[``caller, ``reconstruct, ``Reconstruction.reconstructM,
      ``Reconstruction.program, ``logged, ``binary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing external scalar reconstruction IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``reconstruct_eq_reconstructWithKernel, ``Reconstruction.factorM_id,
      ``Reconstruction.fractionM_id, ``Reconstruction.kernelM_id,
      ``Reconstruction.reconstructM_id, ``Reconstruction.profile_fractionProgram,
      ``Reconstruction.profile_kernelProgram, ``Reconstruction.profile_program,
      ``Reconstruction.profile_program_reconstruct, ``Reconstruction.simulate_program_reconstruct,
      ``eval_batchedPolynomial] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected reconstruction axioms: {name}"
  logInfo "scalar ring/pole/empty/characteristic-two, exact operands/all9 profile checks passed"

#eval profileArithmetic measured |>.1

end ReconstructionTests

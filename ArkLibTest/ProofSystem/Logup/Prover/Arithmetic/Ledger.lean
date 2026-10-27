/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.Arithmetic.Ledger
import ArkLibTest.ProofSystem.Logup.Prover.Default
import Lean.Compiler.IR

/-! # Actual shared-control messages, typed histories and exact primitive-request annotations -/

set_option autoImplicit false
open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
open Logup.Prover.Honest.Accounting
open Lean Elab Command
namespace ArithmeticLedgerTests
abbrev F := ArithmeticStrategyTests.F
abbrev ambient : OracleSpec Unit := Unit →ₒ F
def handler : QueryImpl ambient Id := fun _ => 0

def tag {B E : Type} [CommRing B] [CommRing E] {T K : Nat} : Call B E T K → Nat × Nat
  | .prepare n _ _ _ _ => (0, n)
  | .start n _ _ _ => (1, n)
  | .message r _ _ => (2, r)
  | .fold r _ _ => (3, r)

def traced {n T ell : Nat} (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval F n) (alpha : F)
    (joint : (Fin n → F) × (Fin (T ⌈/⌉ ell) → F)) (choices : Vector (Option F) n) :=
  observeProver ambient handler
    (Logup.Prover.Honest.Accounting.proverWith callInterpreter call_erases (· ++ ·) []
      (RingHom.id F) cfg data ambient) alpha joint choices

def costed {n T ell : Nat} (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval F n) (alpha : F)
    (joint : (Fin n → F) × (Fin (T ⌈/⌉ ell) → F)) (choices : Vector (Option F) n) :=
  observeProver ambient handler
    (Logup.Prover.Honest.Accounting.proverWith costInterpreter cost_erases (· + ·) 0
      (RingHom.id F) cfg data ambient) alpha joint choices

def costedWithInitial {n T ell : Nat} (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval F n) (alpha : F)
    (joint : (Fin n → F) × (Fin (T ⌈/⌉ ell) → F)) (choices : Vector (Option F) n)
    (initial : ArithmeticCost) :=
  observeProver ambient handler
    (Logup.Prover.Honest.Accounting.proverWith costInterpreter cost_erases (· + ·) initial
      (RingHom.id F) cfg data ambient) alpha joint choices

/-- An independently executed prelude can seed the weighted driver's cost annotation. -/
def prefixProgram : OracleComp (ArithmeticSpec F) F := do
  let value ← Arithmetic.valueRead #[2, 7] 1
  let scaled ← Arithmetic.mul value.val 3
  let inverse ← Arithmetic.inv 2
  let result ← Arithmetic.add scaled.val inverse.val
  pure result.val

def plain {n T ell : Nat} (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval F n) (alpha : F)
    (joint : (Fin n → F) × (Fin (T ⌈/⌉ ell) → F)) (choices : Vector (Option F) n) :=
  observeProver ambient handler (Logup.Prover.Honest.prover (RingHom.id F) cfg data ambient)
    alpha joint choices

def cubicJoint : (Fin 1 → F) × (Fin 2 → F) := ((fun _ => 3), ![4, 6])
def twoJoint : (Fin 2 → F) × (Fin 2 → F) := (![3, 7], ![4, 6])
def zeroJoint : (Fin 0 → F) × (Fin 2 → F) := (Fin.elim0, ![4, 6])
def cubic := traced LogupStateTest.cfg LogupStateTest.data 2 cubicJoint #v[some 5]
def cubicAbort := traced LogupStateTest.cfg LogupStateTest.data 0 cubicJoint #v[none]
def two := traced LogupHonestTest.TwoRound.cfg LogupHonestTest.TwoRound.data 5 twoJoint
  #v[some 5, some 9]
def twoAbort := traced LogupHonestTest.TwoRound.cfg LogupHonestTest.TwoRound.data 5 twoJoint
  #v[none, some 9]
def laterAbort := traced LogupHonestTest.TwoRound.cfg LogupHonestTest.TwoRound.data 5 twoJoint
  #v[some 5, none]
def zero := traced LogupHonestTest.ZeroRound.cfg LogupHonestTest.ZeroRound.data 2 zeroJoint #v[]

def foldArguments (calls : List (Call F F 2 2)) : List (Nat × F × Array F) :=
  calls.filterMap fun call => match call with
    | .fold r state point => some (r, point, state.kernel.toArray)
    | _ => none

def messageKernels (calls : List (Call F F 2 2)) : List (Nat × Array F) :=
  calls.filterMap fun call => match call with
    | .message r _ state => some (r, state.kernel.toArray)
    | _ => none

run_cmd do
  unless cubic.2.2.map tag == [(0,1),(1,1),(2,0)] &&
      cubic.2.1.map (fun p => p.val.val) == [#[0,2,10,5]] do
    throwError "terminal successful round executed an unused fold or changed its actual cubic"
  unless cubicAbort.2.2.map tag == [(0,1),(1,1),(2,0)] &&
      cubicAbort.2.1.map (fun p => p.val.val) == [#[13,10,4,7]] do
    throwError "terminal abort changed pole helper/message construction or executed a fold"
  unless zero.2.2.map tag == [(0,0)] && zero.2.1.isEmpty do
    throwError "zero rounds executed an unused private cache or native message"
  unless two.2.2.map tag == [(0,2),(1,2),(2,1),(3,1),(2,0)] &&
      laterAbort.2.2.map tag == [(0,2),(1,2),(2,1),(3,1),(2,0)] &&
      twoAbort.2.2.map tag == [(0,2),(1,2),(2,1)] do
    throwError "typed successful/aborting histories selected the wrong actual call sequence"
  unless foldArguments two.2.2 == [(1,5,#[12,16,3,4])] &&
      messageKernels two.2.2 == [(1,#[12,16,3,4]),(0,#[15,8])] do
    throwError "recorded full call arguments used stale cached tables or the wrong public point"
  for call in two.2.2 do
    if (tag call).1 == 3 then
      let profile := (profileArithmetic call.program).2
      unless profile .add == 14 && profile .sub == 14 && profile .mul == 14 &&
          profile .valueRead == 28 && profile .inv == 0 do
        throwError "actual nonterminal one-product fold profile changed"
  for choices in [#v[some 5, some 9], #v[some 5, none], #v[none, some 9]] do
    let observed := traced LogupHonestTest.TwoRound.cfg LogupHonestTest.TwoRound.data 5
      twoJoint choices
    let measured := costed LogupHonestTest.TwoRound.cfg LogupHonestTest.TwoRound.data 5
      twoJoint choices
    let initial := profileArithmetic prefixProgram
    let seeded := costedWithInitial LogupHonestTest.TwoRound.cfg
      LogupHonestTest.TwoRound.data 5 twoJoint choices initial.2
    unless initial.1 == 13 && seeded.1 == observed.1 &&
        seeded.2.1.map (fun p => p.val.val) == observed.2.1.map (fun p => p.val.val) do
      throwError "nonzero prelude annotation changed weighted retained messages"
    let actual := plain LogupHonestTest.TwoRound.cfg LogupHonestTest.TwoRound.data 5
      twoJoint choices
    unless measured.1 == observed.1 && actual.1 == observed.1 &&
        measured.2.1.map (fun p => p.val.val) == observed.2.1.map (fun p => p.val.val) &&
        actual.2.1.map (fun p => p.val.val) == observed.2.1.map (fun p => p.val.val) do
      throwError "Unit/Cost/List driver interpretations changed actual retained messages"
    unless measured.2.2 .inv == 8 do
      throwError "helpers were recomputed after initialization or inverse requests were hidden"
    for kind in #[ArithmeticCostKind.add,.sub,.mul,.inv,.eq,.coefficientRead,.nodeRead,
        .valueRead,.metadata] do
      unless measured.2.2 kind == charges observed.2.2 kind &&
          seeded.2.2 kind == initial.2 kind + charges observed.2.2 kind do
        throwError "observed profile differs from the prelude and exact selected-program charges"

run_cmd do
  for name in #[``Call.program, ``unitInterpreter, ``costInterpreter, ``callInterpreter,
      ``messageWith, ``nativeWith, ``startWith, ``Logup.Prover.Honest.Accounting.proverWith,
      ``observeNative, ``observeProver, ``charges, ``traced, ``costed, ``plain,
      ``costedWithInitial, ``prefixProgram] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual shared-control/observer compiled IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``unit_erases, ``cost_erases, ``call_erases, ``messageWith_fst,
      ``nativeWith_erases, ``nativeWith_erases_unit, ``startWith_erases_unit,
      ``native_unit_eq, ``start_unit_eq_nativeWith,
      ``prover_unit_eq_honestWith, ``charges_append, ``charges_nil, ``charges_singleton,
      ``observeNative_zero, ``observeNative_one, ``observeNative_succ_succ,
      ``native_cost_eq_charges, ``native_cost_eq_initial_add_charges,
      ``observeProver_with, ``prover_cost_eq_charges, ``prover_cost_eq_initial_add_charges,
      ``Logup.Prover.Honest.prover_eq_honestWith] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected shared-control or actual call-ledger axiom: {name}"
end ArithmeticLedgerTests

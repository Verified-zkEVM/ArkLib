/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Sumcheck.Impl.ArithmeticVerifierChecks
import ArkLibTest.ProofSystem.Sumcheck.Interaction.TerminalCheck
import Lean.Compiler.IR

/-! # Actual shared native sum/comparison control and primitive profiles -/

open CompPoly OracleComp OracleSpec
open Sumcheck.Impl.VerifierChecks
namespace VerifierChecksTests

inductive Event where
  | read (point : Nat)
  | add (left right : Nat)
  | equal (left right : Nat)
  deriving BEq, Repr

def traced (domain : List Nat) (target : Nat) : (Nat × Bool) × List Event :=
  (show StateM (List Event) (Nat × Bool) from do
    let total ← sumM
      (fun x => do modify (· ++ [.read x]); pure (x+2))
      (fun a b => do modify (· ++ [.add a b]); pure (a+b)) domain
    let passed ← equalM (fun a b => do modify (· ++ [.equal a b]); pure (a == b)) total target
    pure (total, passed)).run []

def reader (p : Array ℚ) (x : ℚ) : OracleComp (ArithmeticSpec ℚ) ℚ :=
  Arithmetic.evalHornerProgram p x

def sumHorner (p : Array ℚ) (domain : List ℚ) : OracleComp (ArithmeticSpec ℚ) ℚ :=
  sumProgram (reader p) domain

example {R : Type} [CommSemiring R] [DecidableEq R] (left right : R) :
    (equalM (m := Id) (fun a b => decide (a=b)) left right).run = decide (left=right) := rfl

example {R : Type} [Zero R] [Add R] [Sub R] [Mul R] [Inv R] [DecidableEq R]
    (p : Array R) (domain : List R) :
    profileArithmetic (sumProgram (Arithmetic.evalHornerProgram p) domain) =
      ((sumM (R := R) (m := Id) (fun x => CPolynomial.Raw.evalHornerSeeded (R := R) x p)
        (fun a b => a+b) domain).run,
        sumCost domain (fun _ kind => match kind with
        | .coefficientRead => p.size | .mul | .add => p.size-1 | _ => 0)) := by
  apply profileArithmetic_sumProgram
  intro x _
  exact Arithmetic.profileArithmetic_evalHornerProgram p x

#eval (show IO _ from do
  unless traced [0,1] 5 ==
      ((5,true), [.read 0,.read 1,.add 3 0,.add 2 3,.equal 5 5]) do
    throw (IO.userError "shared sum lost read/head-tail-add order or its final addition to zero")
  unless traced [] 1 == ((0,false), [.equal 0 1]) &&
      traced [1,0,1] 8 == ((8,true),
        [.read 1,.read 0,.read 1,.add 3 0,.add 2 3,.add 3 5,.equal 8 8]) do
    throw (IO.userError "empty/repeated/reversed domain or comparison callback changed")
  for p in #[#[], #[9], #[2,3,5], #[2,3,5,0]] do
    for domain in #[[],[(0 : ℚ)],[0,1],[1,0,1]] do
      let (actual,cost) := profileArithmetic (sumHorner p domain)
      let expected := (domain.map (fun x => CPolynomial.Raw.evalHornerSeeded x p)).sum
      unless actual == expected && cost .coefficientRead == domain.length*p.size &&
          cost .mul == domain.length*(p.size-1) &&
          cost .add == domain.length*(p.size-1)+domain.length && cost .sub == 0 &&
          cost .inv == 0 && cost .eq == 0 && cost .nodeRead == 0 &&
          cost .valueRead == 0 && cost .metadata == 0 do
        throw (IO.userError "sum profile omitted a stored coefficient reader or final +0")
      for target in #[expected,expected+1] do
        let (passed,comparisonCost) := profileArithmetic (equalProgram actual target)
        unless passed == decide (actual=target) && comparisonCost .eq == 1 &&
            comparisonCost .add == 0 && comparisonCost .sub == 0 && comparisonCost .mul == 0 &&
            comparisonCost .inv == 0 && comparisonCost .coefficientRead == 0 &&
            comparisonCost .nodeRead == 0 && comparisonCost .valueRead == 0 &&
            comparisonCost .metadata == 0 do
          throw (IO.userError "shared equality requested an extra arithmetic operation")
  pure (traced [0,1] 5))

open Lean Elab Command in
run_cmd do
  for name in #[``sumM, ``equalM, ``sumProgram, ``equalProgram, ``traced, ``reader, ``sumHorner] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable shared local-check IR: {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  for name in #[``sumM_congr_read,``sumM_id_eq_sum,``simulateQ_sumProgram,
      ``profileArithmetic_sumProgram,``simulateQ_equalProgram,``profileArithmetic_equalProgram,
      ``Sumcheck.Interaction.Native.Core.latestSum_nil,
      ``Sumcheck.Interaction.Native.Core.latestSum_cons,
      ``Sumcheck.Interaction.Native.Core.simulate_latestSum,
      ``Sumcheck.Interaction.Native.Core.execute_succ,
      ``Sumcheck.Interaction.Native.Core.simulate_checkFinalClaim] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected shared local-check axiom: {name}"

end VerifierChecksTests

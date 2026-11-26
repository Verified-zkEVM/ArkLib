/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Sumcheck.VirtualOracle
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import Mathlib.Data.ZMod.Basic

/-! Executable checks of the four-query terminal verifier over a small prime field. -/

namespace SpartanTest.Terminal

open Spartan Spartan.Realization Spartan.Terminal OracleComp OracleSpec

abbrev params : PublicParams := ⟨1, 2, 1, by decide⟩

def publicInput : R1CS.Statement (ZMod 5) params.toSizeR1CS := ![2, 1]

def matrices : ∀ i, R1CS.OracleStatement (ZMod 5) params.toSizeR1CS i
  | .A => fun _ j => if j.val = 0 then 1 else 0
  | .B => fun _ j => if j.val = 2 then 1 else 0
  | .C => fun _ j => if j.val = 1 then 1 else 0

def witness : R1CS.Witness (ZMod 5) params.toSizeR1CS := ![3, 4]

def oracles : ∀ i, OracleStatement (R := ZMod 5) params i
  | .inl i => matrices i
  | .inr _ => witness

def statement : FinalStatement (R := ZMod 5) params where
  input := ⟨(0, ⟨publicInput, 0, ![2], 0⟩),
    (fun | .A => 1 | .B => 2 | .C => 3), 0⟩
  r_y := ![3, 4]
  e := 1

def perturbed : FinalStatement (R := ZMod 5) params := {statement with e := 2}

/-- Execute the actual oracle verifier with the four finite-table oracle interfaces. -/
def accepts (s : FinalStatement (R := ZMod 5) params) : Bool :=
  ((finalVerifier params ([]ₒ)).toVerifier.run (s, oracles) default).run.runEmpty.isSome

example : R1CS.relation (ZMod 5) params.toSizeR1CS publicInput matrices witness := by decide

example : terminalRelation params statement oracles := by
  rw [terminalRelation, ← checkValue_eq]
  decide

example : ¬ terminalRelation params perturbed oracles := by
  rw [terminalRelation, ← checkValue_eq]
  decide

example : (finalVerifier params ([]ₒ)).toVerifier.run (statement, oracles) default =
    pure ((), oracles) := by
  classical
  rw [finalVerifier_run_iff]
  have h : terminalRelation params statement oracles := by
    rw [terminalRelation, ← checkValue_eq]
    decide
  simp only [h, ite_true]

example : (finalVerifier params ([]ₒ)).toVerifier.run (perturbed, oracles) default = failure := by
  classical
  rw [finalVerifier_run_iff]
  have h : ¬ terminalRelation params perturbed oracles := by
    rw [terminalRelation, ← checkValue_eq]
    decide
  simp only [h, ite_false]

/-- info: true -/
#guard_msgs in
#eval accepts statement

/-- info: false -/
#guard_msgs in
#eval accepts perturbed

/-- info: true -/
#guard_msgs in
#eval ((simulateQ (OracleInterface.simOracle0 (OracleStatement (R := ZMod 5) params) oracles)
    (VirtualOracle.first params publicInput (![1] : Fin 1 → ZMod 5)
      statement.r_x)).run ==
  firstEval matrices (R1CS.𝕫 publicInput witness) (![1] : Fin 1 → ZMod 5) statement.r_x)

end SpartanTest.Terminal

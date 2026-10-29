/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Batching.Reduction
import ArkLib.ProofSystem.Spartan.Terminal
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import ArkLib.Data.Probability.Instances
import Mathlib.Algebra.Field.ZMod

/-! Independent row-evaluation batching over a small prime field. -/

namespace SpartanTest.Batching

open Spartan Spartan.Realization Spartan.Batching OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance : SampleableType (ZMod 5) :=
  SampleableType.ofEquiv (ZMod.finEquiv 5).toEquiv

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

def evaluationStatement : Evaluation.Statement (R := ZMod 5) params where
  x := publicInput
  τ := ![1]
  r_x := ![2]
  e := 0

def honestClaims : R1CS.MatrixIdx → ZMod 5
  | .A => 2
  | .B => 3
  | .C => 1

def falseClaims : R1CS.MatrixIdx → ZMod 5
  | .A => 3
  | .B => 3
  | .C => 1

def honestInput : InputStatement (R := ZMod 5) params :=
  (honestClaims, evaluationStatement)

def falseInput : InputStatement (R := ZMod 5) params :=
  (falseClaims, evaluationStatement)

def hidingCoefficients : R1CS.MatrixIdx → ZMod 5
  | .A => 0
  | .B => 1
  | .C => 2

def revealingCoefficients : R1CS.MatrixIdx → ZMod 5
  | .A => 1
  | .B => 0
  | .C => 0

theorem honestClaims_correct :
    Evaluation.outputRelation params evaluationStatement oracles honestClaims := by
  have h : honestClaims = Evaluation.values params evaluationStatement oracles := by decide
  rw [h]
  exact Evaluation.values_correct _ _ _

example : Evaluation.check params evaluationStatement honestClaims := by decide

example (ρ : R1CS.MatrixIdx → ZMod 5) :
    outputRelation params (batch params honestInput ρ) oracles :=
  batchedClaim_complete params honestInput oracles ρ honestClaims_correct

theorem falseClaims_incorrect :
    ¬ Evaluation.outputRelation params evaluationStatement oracles falseClaims := by
  intro h
  have hA := (h .A).trans (rowEval_eq _ _ _).symm
  change (3 : ZMod 5) = 2 at hA
  exact (by decide : (3 : ZMod 5) ≠ 2) hA

example : hidingCoefficients ≠ 0 := by decide

example : outputRelation params (batch params falseInput hidingCoefficients) oracles := by
  rw [outputRelation_iff_collision]
  decide

example : ¬ outputRelation params (batch params falseInput revealingCoefficients) oracles := by
  rw [outputRelation_iff_collision]
  decide

/-- A fixed false row claim is hidden by exactly one fifth of the coefficient vectors. -/
example :
    Pr{let ρ ← $ᵗ (R1CS.MatrixIdx → ZMod 5)}[
      outputRelation params (batch params falseInput ρ) oracles] = (1 : ℝ≥0∞) / 5 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    independent_batch_collision_eq_inv_card params falseInput oracles falseClaims_incorrect

/-- Run the actual verifier, recording its claimed sum and the retained coefficients and tables. -/
def runSummary (s : InputStatement (R := ZMod 5) params)
    (ρ : R1CS.MatrixIdx → ZMod 5) : Option (ℕ × Bool × Bool) :=
  (((oracleVerifier params ([]ₒ)).toVerifier.run (s, oracles)
    (FullTranscript.mk1 (pSpec := pSpec (ZMod 5)) ρ)).run.runEmpty).map fun out =>
      (out.1.c.val, decide (out.1.ρ = ρ),
        decide ((∀ i, out.2 (.inl i) = matrices i) ∧ out.2 (.inr 0) = witness))

/-- info: some (0, true, true) -/
#guard_msgs in
#eval runSummary honestInput hidingCoefficients

/-- info: some (0, true, true) -/
#guard_msgs in
#eval runSummary falseInput hidingCoefficients

/-- info: some (3, true, true) -/
#guard_msgs in
#eval runSummary falseInput revealingCoefficients

private def sampleZero (n : ℕ) : Id (unifSpec.Range n) := pure 0

/-- info: [0, 0, 0] -/
#guard_msgs in
#eval let ρ := simulateQ (r := Id) sampleZero ($ᵗ (R1CS.MatrixIdx → ZMod 5))
  [ρ .A, ρ .B, ρ .C].map ZMod.val

end SpartanTest.Batching

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness
import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolCompleteness
import Mathlib.Algebra.Field.ZMod

/-! # Native continuation and abort regressions

The first prover continuation remembers its sampled coefficient, receives the verifier challenge,
and performs another effect before constructing the second message. A noncommutative interpreter
checks the actual effect order, including the response to a public abort.
-/

open Interaction.Oracle

namespace Sumcheck.Interaction.Native.Test

open OracleComp OracleSpec Polynomial
open MultivariateRound

noncomputable section

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def affine (a b : ZMod 17) : SingleRound.Message (ZMod 17) 1 :=
  ⟨C a * X + C b, Polynomial.mem_degreeLE.mpr
    (degree_add_le_of_degree_le (degree_C_mul_X_le a) (degree_C_le.trans zero_le_one))⟩

abbrev events : OracleSpec (Fin 4) := Fin 4 →ₒ ZMod 17

def event (i : Fin 4) : OracleComp events (ZMod 17) := liftM (events.query i)

/-- The last native response retains a terminal effect on both possible public branches. -/
def lastProver (a b r : ZMod 17) : Prover.Strategy events (protocol (ZMod 17) 1 1).tree
    (protocol (ZMod 17) 1 1).roles (fun _ => Unit) := by
  refine pure ⟨affine (b + a) (a * r + 1), ?_⟩
  intro choice
  cases choice <;> exact do
    let _ ← event 3
    return ()

/-- This is an ordinary native strategy; private memory is captured by its continuations. -/
def adaptive : Prover.Strategy events (protocol (ZMod 17) 1 2).tree
    (protocol (ZMod 17) 1 2).roles (fun _ => Unit) := by
  refine do
    let a ← event 0
    return ⟨affine a 1, ?_⟩
  intro choice
  cases choice with
  | none => exact do
      let _ ← event 2
      return ()
  | some r => exact do
      let b ← event 2
      return lastProver a b r

def original : (polynomialFamily (ZMod 17) 2 1).Behavior := fun _ => (0 : ZMod 17)

def initial : Spec.StatementRound (ZMod 17) 2 0 := ⟨1, Fin.elim0⟩

def record : QueryImpl events (StateM (List (Fin 4))) := fun i => do
  modify (fun seen => seen ++ [i])
  return ![7, 3, 5, 11] i

/-- Run the native strategy directly, without packaging it as a reduction witness. -/
def run (domain : List (ZMod 17)) :=
  execute (ZMod 17) 2 1 events (event 1) domain 2 0 (by decide)
    (polynomialFamily (ZMod 17) 2 1).spec.toPFunctor
    (VirtualOracle.id (polynomialFamily (ZMod 17) 2 1))
    initial original adaptive

set_option backward.isDefEq.respectTransparency false in
/-- The post-challenge prover effects occur at their native positions, including at termination. -/
theorem two_rounds : run [0] = (do
    let a ← event 0
    let r ← event 1
    let b ← event 2
    let s ← event 1
    let _ ← event 3
    return some (⟨⟨(b + a) * s + (a * r + 1), ![r, s]⟩, original⟩ :
      ClosedClaim (FinalStatement (ZMod 17) 2) (polynomialFamily (ZMod 17) 2 1))) := by
  have hvec (r s : ZMod 17) : Fin.snoc (Fin.snoc Fin.elim0 r) s = ![r, s] := by
    funext i
    fin_cases i <;> rfl
  simp [run, execute_succ, execute_zero, adaptive, lastProver, affine, initial, hvec]
  congr 1

/-- A noncommutative handler observes all five effects in the required order. -/
example : (simulateQ record ((fun result => result.map (fun claim => claim.stmt.target)) <$>
    run [0])).run [] = (some 7, [0, 1, 2, 1, 3]) := by
  rw [two_rounds]
  simp [record, event, simulateQ_bind, simulateQ_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Abort executes the prover's response, but neither a challenge nor a later message. -/
theorem abort_response : run [] = (do
    let _ ← event 0
    let _ ← event 2
    return none) := by
  simp [run, execute_succ, adaptive, initial]

example : (simulateQ record (Option.isSome <$> run [])).run [] = (false, [0, 2]) := by
  rw [abort_response]
  simp [record, event, simulateQ_bind, simulateQ_map]
  rfl

/-- Completing the checks does not certify the final oracle relation. -/
example : ¬ outputRelation (ZMod 17) 2 1 ⟨⟨7, ![3, 3]⟩, original⟩ := by
  change (0 : ZMod 17) ≠ 7
  decide

end
end Sumcheck.Interaction.Native.Test

#print axioms Sumcheck.Interaction.Native.execute_soundness
#print axioms Sumcheck.Interaction.Native.execute_support_completeness
#print axioms Sumcheck.Interaction.Native.execute_perfectCompleteness

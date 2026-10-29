/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.ArbitraryRounds
import Mathlib.Data.ZMod.Basic

/-! # Arbitrary-round execution boundary and three-round ordering tests -/

namespace Sumcheck.Interaction.MultivariateRound.ArbitraryTest

open OracleComp OracleSpec Polynomial
open _root_.Interaction.Oracle

noncomputable section

/-- An affine message with its actual degree certificate. -/
def affine (a b : ZMod 17) : SingleRound.Message (ZMod 17) 1 :=
  ⟨C a * X + C b, Polynomial.mem_degreeLE.mpr
    (degree_add_le_of_degree_le (degree_C_mul_X_le a) (degree_C_le.trans zero_le_one))⟩

/-- The retained behavior evaluates an asymmetric three-variable polynomial. -/
def original : (polynomialFamily (ZMod 17) 3 1).Behavior :=
  fun q => q.2 0 + 2 * q.2 1 + 4 * q.2 2

/-- Messages for challenges three, five, seven, obtained from successive partial sums. -/
def messages (i : Fin 3) (_ : Spec.StatementRound (ZMod 17) 3 i.castSucc) :
    SingleRound.Message (ZMod 17) 1 :=
  affine 4 (![12, 10, 13] i)

/-- All challenge phases are externally observable and distinct. -/
abbrev events : OracleSpec (Fin 3) := (Fin 3) →ₒ Unit

/-- Receiver effects run before the corresponding fixed challenge is returned. -/
def challenge (i : Fin 3) (_ : Spec.StatementRound (ZMod 17) 3 i.castSucc) :
    OracleComp events (ZMod 17) := do
  let _ ← liftM (events.query i)
  return ![3, 5, 7] i

/-- The stateful interpreter records the exact receiver order. -/
def record : QueryImpl events (StateM (List (Fin 3))) :=
  fun i => modify (fun seen => seen ++ [i])

/-- The initial Boolean-cube sum of `x₀ + 2x₁ + 4x₂` is twenty-eight, hence eleven. -/
def initial : ClosedClaim (Spec.StatementRound (ZMod 17) 3 0) (polynomialFamily (ZMod 17) 3 1) :=
  ⟨⟨11, Fin.elim0⟩, original⟩

/-- Zero remaining rounds does not invoke messages or challenge programs. -/
example : executeRoundsSampled (ZMod 17) 3 1 events 0 0 (by decide) [0, 1]
    initial messages challenge = pure (some initial) := by
  rfl

/-- Three actual rounds retain the original behavior and the ordered challenge vector. -/
theorem three_rounds :
    executeRoundsSampled (ZMod 17) 3 1 events 0 3 (by decide) [0, 1]
      initial messages challenge = (do
        let _ ← liftM (events.query 0)
        let _ ← liftM (events.query 1)
        let _ ← liftM (events.query 2)
        return some (⟨⟨7, ![3, 5, 7]⟩, original⟩ :
          ClosedClaim (Spec.StatementRound (ZMod 17) 3 3) (polynomialFamily (ZMod 17) 3 1))) := by
  simp only [executeRoundsSampled, OrderedExecution.run, roundStages_run, challenge,
    map_eq_bind_pure_comp,
    bind_assoc, pure_bind]
  have h28 : (28 : ZMod 17) = 11 := by decide
  have h24 : (24 : ZMod 17) = 7 := by decide
  have h30 : (30 : ZMod 17) = 13 := by decide
  have h41 : (41 : ZMod 17) = 7 := by decide
  norm_num [executeCore_eq, messages, affine, initial, acceptedRun_closed, bind_assoc,
    h28, h24, h30, h41]
  simp only [h28, h24, h30, ite_true, acceptedRun_closed]
  norm_num [affine, bind_assoc]
  simp only [h24, ite_true, acceptedRun_closed]
  norm_num [affine, bind_assoc]
  simp only [h30, ite_true, acceptedRun_closed]
  norm_num [affine, bind_assoc]
  rw [h41]
  have hv : Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 (3 : ZMod 17)) 5) 7 =
      ![3, 5, 7] := by decide
  rw [hv]
  rfl

/-- A noncommutative interpreter observes all three receiver phases in their original order. -/
example : (simulateQ record (Option.isSome <$>
    executeRoundsSampled (ZMod 17) 3 1 events 0 3 (by decide) [0, 1]
      initial messages challenge)).run [] = (true, [0, 1, 2]) := by
  rw [three_rounds]
  simp [record, simulateQ_bind, simulateQ_map]
  rfl

/-- Rejection retains the first receiver effect and skips both later challenges. -/
example : (simulateQ record (Option.isSome <$>
    executeRoundsSampled (ZMod 17) 3 1 events 0 3 (by decide) [0, 1]
      { initial with stmt := { initial.stmt with target := 12 } } messages challenge)).run [] =
        (false, [0]) := by
  simp only [executeRoundsSampled, OrderedExecution.run, roundStages_run, challenge,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  norm_num [executeCore_eq, messages, affine, initial, bind_assoc]
  have hbad : (28 : ZMod 17) ≠ 12 := by decide
  simp only [hbad, ite_false, CoreRun.closed]
  simp [record]
  rfl

#print axioms executeRounds_honest
#print axioms closedRelation_last_iff

end
end Sumcheck.Interaction.MultivariateRound.ArbitraryTest

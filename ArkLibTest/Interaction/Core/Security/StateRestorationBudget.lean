/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.StateRestorationBudget
import ArkLibTest.Interaction.Core.Oracle

/-! A two-round state-restoration client with round errors `1/8` and `1/16`. Each round sends a
`Fin 8` oracle; the challenges are drawn from `Fin 8` and `Fin 16`. The verifier accepts when the
first challenge is `0`, returning the second message as the claim and as its output oracle. The
adversary queries a second-round key twice before selecting its transcript, so the restored
execution is charged at most `2 * (1/8) + (1/8 + 1/16) = 7/16`. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec
open Interaction.Core.StateRestoration
open Interaction.Core.OracleTests (emptyFamily)

namespace Interaction.Core.StateRestorationBudgetTests

/-- A sent `Fin 8` answers its single query with itself. -/
@[instance_reducible] def messageInterface : OracleInterface (Fin 8) where
  Query := Unit
  toOC := { spec := fun _ => Fin 8, impl := fun _ => do return (← read) }

/-- The first round: a `Fin 8` oracle message and a `Fin 8` challenge. -/
@[implicit_reducible] def firstRound : Round where
  Message := Fin 8
  Challenge := Fin 8
  interface := messageInterface
  sampleChallenge := inferInstance

/-- The second round: a `Fin 8` oracle message and a `Fin 16` challenge. -/
@[implicit_reducible] def secondRound : Round where
  Message := Fin 8
  Challenge := Fin 16
  interface := messageInterface
  sampleChallenge := inferInstance

@[implicit_reducible] def rounds : List Round := [firstRound, secondRound]

/-- The first round's local error is `1/8`, the second's `1/16`. -/
noncomputable def errors : RoundErrors rounds := fun j : Fin 2 => if j = 0 then 1 / 8 else 1 / 16

/-- The output is one `Fin 8` oracle. -/
@[instance_reducible] def outputFamily : OracleFamily PUnit (fun _ => Fin 8) :=
  singletonFamily messageInterface

/-- The input statement: a number with no input oracles. -/
abbrev Stmt : Type := Nat × (∀ i : PEmpty.{1}, (PEmpty.elim i : Type))

/-- The statement `z` with no input oracles. -/
def stmt (z : Nat) : Stmt := (z, fun i => PEmpty.elim i)

/-- The shape of every completed transcript. -/
abbrev shape : Path (protocol rounds) := ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩

/-- Accept when the first challenge is `0`, reading the second payload as the claim. The output
oracle is the second payload. -/
def verifier : OracleVerifier []ₒ (protocol rounds) Nat (Fin 8) emptyFamily outputFamily where
  decide _ p v := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩
    exact if (show Fin 8 from v.1.2.1) = 0 then
      liftM (([]ₒ + (sumFamily emptyFamily (pathFamily (protocol rounds) shape)).spec).query
        (.inr ⟨.inr (.inr (.inl ⟨⟩)), ()⟩))
    else failure
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩⟩⟩
    exact OracleMap.embedding (sumFamily emptyFamily (pathFamily (protocol rounds) shape))
      (fun _ => .inr (.inr (.inl ⟨⟩)))

/-- The transcript with messages 5 and 7 and challenges `first` and `second`. -/
def path (first : Fin 8) (second : Fin 16) : PathAlong oracleSig (protocol rounds) :=
  ⟨(5 : Fin 8), ⟨first, ⟨(7 : Fin 8), ⟨second, ⟨⟩⟩⟩⟩⟩

def messages : Messages Unit rounds := ⟨(5 : Fin 8), (), (7 : Fin 8), (), PUnit.unit⟩

/-- The second-round key below first message 5 and input 0. -/
def lateKey : Key Stmt Unit rounds :=
  Key.later (5 : Fin 8) () (Key.here (stmt 0) (7 : Fin 8) ())

/-- Query the later round first, twice, before completing the selected transcript. -/
def adversary : OracleComp (oracleSpec Stmt Unit rounds) (Stmt × Messages Unit rounds × Nat) := do
  let _ ← liftM ((oracleSpec Stmt Unit rounds).query lateKey)
  let _ ← liftM ((oracleSpec Stmt Unit rounds).query lateKey)
  pure ⟨stmt 0, messages, 6⟩

-- Row 4 (StateRestorationBudget L182, observation): on first challenge `0` the closed
-- observation returns the second message as the claim and its output oracle.
theorem observation (second : Fin 16) :
    closedTerminalObservation verifier (stmt 0) (path 0 second) = some (7, fun _ => 7) := rfl

-- Row 13 (StateRestorationBudget L305): the observation value.
/-- info: some (7, 7) -/
#guard_msgs in
#eval (closedTerminalObservation verifier (stmt 0) (path 0 1)).map
  (fun claim => ((claim.1 : Nat), (claim.2 ⟨⟩ : Nat)))

-- Row 6 (StateRestorationBudget L235, queryBound): the adversary makes two queries.
theorem queryBound : IsTotalQueryBound adversary 2 := by
  unfold adversary
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by decide, fun _ => ?_⟩
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => trivial⟩

-- Row 8 (StateRestorationBudget L246, max_errors): the largest round error is `1/8`.
theorem max_errors : Finset.univ.sup errors = (1 / 8 : ENNReal) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    fin_cases j <;> norm_num [errors]
  · exact Finset.le_sup (f := errors) (Finset.mem_univ (0 : Fin 2))

-- Row 9 (StateRestorationBudget L253, sum_errors): the round errors sum to `3/16`.
theorem sum_errors : (∑ j, errors j) = (3 / 16 : ENNReal) := by
  change (∑ j : Fin 2, errors j) = _
  rw [Fin.sum_univ_two]
  change (1 / 8 : ENNReal) + 1 / 16 = 3 / 16
  have equality : (1 / 8 : NNReal) + 1 / 16 = 3 / 16 := by norm_num
  simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] using
    congrArg (fun x : NNReal => (x : ENNReal)) equality

-- Row 10, cost half (StateRestorationBudget L261, actual_nonuniform_game_bound): the restored
-- execution is charged at most `7/16` on every branch, the budget the frozen game bound uses.
theorem restoredExecution_charge :
    WorstCaseCostBound (restoredExecution rounds adversary)
      (⟨keyError errors⟩ : CostModel (oracleSpec Stmt Unit rounds) ENNReal) (7 / 16) := by
  have general := restoredExecution_round_cost rounds errors adversary 2 queryBound
  have budget : (2 : Nat) * Finset.univ.sup errors + ∑ j, errors j = (7 / 16 : ENNReal) := by
    rw [max_errors, sum_errors]
    have equality : (2 : NNReal) * (1 / 8) + 3 / 16 = 7 / 16 := by norm_num
    simpa only [Nat.cast_ofNat, ENNReal.coe_add, ENNReal.coe_mul,
      ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
      ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0),
      ENNReal.coe_ofNat, ENNReal.coe_one] using
      congrArg (fun x : NNReal => (x : ENNReal)) equality
  rwa [budget] at general

-- The second-round key is charged the second round's error, which is its challenge node's.
example : keyError errors lateKey = 1 / 16 := by
  change errors (1 : Fin 2) = 1 / 16
  simp [errors]

example : keyError errors lateKey = roundEps errors (keyNode lateKey) :=
  keyError_eq_roundEps errors lateKey

-- Row 11 (StateRestorationBudget L284): `7/16` is strictly below the uniform bound
-- `(2 + rounds.length) * (1/8)`.
example : (7 / 16 : ENNReal) < (2 + rounds.length) * (1 / 8) := by
  have better : (7 / 16 : NNReal) < 4 * (1 / 8) := by norm_num
  have coefficient : (2 : ENNReal) + rounds.length = 4 := by norm_num [rounds]
  rw [coefficient]
  simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one]
    using ENNReal.coe_lt_coe.mpr better

end Interaction.Core.StateRestorationBudgetTests

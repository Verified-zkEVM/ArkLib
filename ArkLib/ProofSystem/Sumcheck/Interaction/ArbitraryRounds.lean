/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Composition
public import ArkLib.ProofSystem.Sumcheck.Interaction.Sequential

/-!
# Arbitrary consecutive Sumcheck rounds

The finite ordered reduction executor owns the iteration. Every round receives the closed
claim produced by the previous actual execution. Message selection uses the current statement;
challenge programs run inside the receiver strategy and may use its complete challenge prefix.
The polynomial witness used for honest messages never replaces a closed oracle at a seam.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- Interfaces for a consecutive interval of valid round indices. -/
abbrev roundInterfaces (start count : ℕ) (bound : start + count ≤ n)
    (j : Fin (count + 1)) : ExecutionInterface where
  Stmt := Spec.StatementRound R n ⟨start + j, by omega⟩
  Index := Unit
  Realization := Spec.OracleStatement R n deg
  oracles := polynomialFamily R n deg
  Private := Unit

variable {ι : Type} (ambient : OracleSpec ι)

/-- Actual receiver-sampled reductions over the declared consecutive interfaces. -/
def roundStages [DecidableEq R] (start count : ℕ) (bound : start + count ≤ n)
    (domain : List R)
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc → Message R deg)
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → OracleComp ambient R)
    (j : Fin count) :
    ClosedStage ambient (roundInterfaces R n deg start count bound j.castSucc)
      (roundInterfaces R n deg start count bound j.succ) where
  protocol := fun _ => protocol R deg
  Witness := fun _ => Message R deg
  OutP := fun _ _ => R × R
  reduction := fun stmt => sampledReduction R n deg ambient ⟨start + j, by omega⟩ domain
    (challenges ⟨start + j, by omega⟩ stmt)
  witness := fun stmt _ => messages ⟨start + j, by omega⟩ stmt
  nextPrivate := fun _ _ _ _ => ()

/-- A stage keeps the challenge program at the receiver phase of its actual execution. -/
theorem roundStages_run [DecidableEq R] (start count : ℕ) (bound : start + count ≤ n)
    (domain : List R)
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc → Message R deg)
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → OracleComp ambient R)
    (j : Fin count)
    (input : (roundInterfaces R n deg start count bound j.castSucc).State) :
    (roundStages R n deg ambient start count bound domain messages challenges j).run input =
      (do
        let r ← challenges ⟨start + j, by omega⟩ input.1.stmt
        let result ← executeCore (reduction R n deg ambient ⟨start + j, by omega⟩ domain r)
          input.1.oracles input.1.stmt (messages ⟨start + j, by omega⟩ input.1.stmt)
        return result.closed.map (fun claim => (claim, ()))) := by
  rw [ClosedStage.run_eq_executeCore]
  change (do
    let result ← executeCore (sampledReduction R n deg ambient ⟨start + j, by omega⟩ domain
      (challenges ⟨start + j, by omega⟩ input.1.stmt))
      input.1.oracles input.1.stmt (messages ⟨start + j, by omega⟩ input.1.stmt)
    return result.closed.map (fun claim => (claim, ()))) = _
  erw [executeCore_sampled_eq]
  simp only [bind_assoc]
  rfl

/-- Execute any valid interval using the common ordered reduction executor. -/
def executeRoundsSampled [DecidableEq R] (start count : ℕ) (bound : start + count ≤ n)
    (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R n ⟨start, by omega⟩) (polynomialFamily R n deg))
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc → Message R deg)
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → OracleComp ambient R) :
    OracleComp ambient (Option
      (ClosedClaim (Spec.StatementRound R n ⟨start + count, by omega⟩)
        (polynomialFamily R n deg))) :=
  Option.map Prod.fst <$> OrderedExecution.run count (roundInterfaces R n deg start count bound)
    (roundStages R n deg ambient start count bound domain messages challenges) (input, ())

/-- Fixed challenges are the pure receiver-program instance of arbitrary-round execution. -/
def executeRounds [DecidableEq R] (start count : ℕ) (bound : start + count ≤ n)
    (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R n ⟨start, by omega⟩) (polynomialFamily R n deg))
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc → Message R deg)
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → R) :
    OracleComp ambient (Option
      (ClosedClaim (Spec.StatementRound R n ⟨start + count, by omega⟩)
        (polynomialFamily R n deg))) :=
  executeRoundsSampled R n deg ambient start count bound domain input messages
    (fun i stmt => pure (challenges i stmt))

/-- An empty interval retains the actual input closed claim, including arbitrary behavior. -/
@[simp]
theorem executeRoundsSampled_zero [DecidableEq R] (start : ℕ) (bound : start + 0 ≤ n)
    (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R n ⟨start, by omega⟩) (polynomialFamily R n deg))
    (messages : (i : Fin n) → Spec.StatementRound R n i.castSucc → Message R deg)
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → OracleComp ambient R) :
    executeRoundsSampled R n deg ambient start 0 bound domain input messages challenges =
      pure (some input) := by
  rfl

/-- A one-round interval is exactly the existing actual sampled single-round execution. -/
theorem executeRoundsSampled_one [DecidableEq R] (i : Fin n) (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R n i.castSucc) (polynomialFamily R n deg))
    (messages : (j : Fin n) → Spec.StatementRound R n j.castSucc → Message R deg)
    (challenges : (j : Fin n) → Spec.StatementRound R n j.castSucc → OracleComp ambient R) :
    executeRoundsSampled R n deg ambient i 1 (by omega) domain input messages challenges =
      CoreRun.closed <$> executeCore
        (sampledReduction R n deg ambient i domain (challenges i input.stmt))
        input.oracles input.stmt (messages i input.stmt) := by
  simp only [executeRoundsSampled, OrderedExecution.run, ClosedStage.run_eq_executeCore,
    roundStages, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext result
  simp only [Function.comp_apply]
  cases result.closed <;> rfl

/-- The common arbitrary-round executor agrees with the existing two-stage sampled client. -/
theorem executeRoundsSampled_two [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R (n + 2) i.castSucc.castSucc)
      (polynomialFamily R (n + 2) deg))
    (messages : (j : Fin (n + 2)) → Spec.StatementRound R (n + 2) j.castSucc → Message R deg)
    (challenges : (j : Fin (n + 2)) →
      Spec.StatementRound R (n + 2) j.castSucc → OracleComp ambient R) :
    executeRoundsSampled R (n + 2) deg ambient i 2 (by omega) domain input messages challenges =
      executeTwoSampled R n deg ambient i domain input.stmt input.oracles
        (messages i.castSucc input.stmt) (messages i.succ)
        (challenges i.castSucc input.stmt) (challenges i.succ) := by
  simp only [executeRoundsSampled, executeTwoSampled, OrderedExecution.run,
    ClosedStage.run_eq_executeCore, roundStages, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext result
  cases result.closed with
  | none => rfl
  | some middle =>
    simp only [Option.map_some, bind_assoc]
    congr 1
    funext second
    simp only [Function.comp_apply]
    cases second.closed <;> rfl

/-- Pure challenge programs recover the existing fixed two-round executor exactly. -/
theorem executeRounds_two [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (input : ClosedClaim (Spec.StatementRound R (n + 2) i.castSucc.castSucc)
      (polynomialFamily R (n + 2) deg))
    (messages : (j : Fin (n + 2)) → Spec.StatementRound R (n + 2) j.castSucc → Message R deg)
    (challenges : (j : Fin (n + 2)) → Spec.StatementRound R (n + 2) j.castSucc → R) :
    executeRounds R (n + 2) deg ambient i 2 (by omega) domain input messages challenges =
      executeTwo R n deg ambient i domain input.stmt input.oracles
        (messages i.castSucc input.stmt) (messages i.succ)
        (challenges i.castSucc input.stmt)
        (challenges i.succ ⟨(messages i.castSucc input.stmt).val.eval
          (challenges i.castSucc input.stmt),
            Fin.snoc input.stmt.challenges (challenges i.castSucc input.stmt)⟩) := by
  rw [executeRounds, executeRoundsSampled_two]
  simp only [executeTwoSampled, executeCore_sampled_eq, pure_bind, executeTwo]
  rw [executeCore_eq]
  split
  · simp only [pure_bind, acceptedRun_closed]
  · rfl

/-- The honest message selector uses its witness only to construct the sent univariate oracle. -/
def honestMessages {m : ℕ} (D : Fin m ↪ R) (p : Spec.OracleStatement R n deg ())
    (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc) : Message R deg :=
  Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges p


/-- An honest sampled stage is a map of its receiver program, with no rejection or new handler. -/
theorem roundStages_honest [DecidableEq R] {m : ℕ} (D : Fin m ↪ R)
    (start count : ℕ) (bound : start + count ≤ n)
    (p : Spec.OracleStatement R n deg ())
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → OracleComp ambient R)
    (j : Fin count)
    (input : (roundInterfaces R n deg start count bound j.castSucc).State)
    (h : ((input.1.stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    (roundStages R n deg ambient start count bound (Finset.univ.map D).toList
      (honestMessages R n deg D p) challenges j).run input =
      (fun r => some (⟨honestNext R n deg D ⟨start + j, by omega⟩ input.1.stmt p r,
        input.1.oracles⟩, ())) <$> challenges ⟨start + j, by omega⟩ input.1.stmt := by
  rw [roundStages_run, map_eq_bind_pure_comp]
  congr 1
  funext r
  erw [executeCore_accepted R n deg ambient ⟨start + j, by omega⟩ input.1.stmt _ _ _ r
    (projected_sum_of_relationRound R n deg D ⟨start + j, by omega⟩ input.1.stmt p h)]
  rfl

/-- Honest execution of any remaining interval accepts from one initial multivariate relation.
The conclusion also records preservation of the original evaluation behavior. -/
theorem executeRounds_honest [DecidableEq R] {m : ℕ} (D : Fin m ↪ R)
    (start count : ℕ) (bound : start + count ≤ n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    ∃ output,
      executeRounds R n deg ambient start count bound (Finset.univ.map D).toList
        ⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩
        (honestMessages R n deg D p) challenges = pure (some output) ∧
      output.oracles = (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p) ∧
      closedRelation R n deg D ⟨start + count, by omega⟩ output := by
  let I := roundInterfaces R n deg start count bound
  let stages := roundStages R n deg ambient start count bound (Finset.univ.map D).toList
    (honestMessages R n deg D p) (fun i stmt => pure (challenges i stmt))
  let Inv : (j : Fin (count + 1)) → (I j).State → Prop := fun j state =>
    state.1.oracles = (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p) ∧
      ((state.1.stmt, fun _ => p), ()) ∈
        Spec.relationRound R n deg D _
  have preserves : ∀ (j : Fin count) (input : (I j.castSucc).State),
      Inv j.castSucc input → ∃ output, (stages j).run input = pure (some output) ∧
        Inv j.succ output := by
    intro j input hin
    rcases input with ⟨⟨current, impl⟩, payload⟩
    rcases hin with ⟨himpl, hcurrent⟩
    change impl = (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p) at himpl
    subst impl
    let i : Fin n := ⟨start + j, by omega⟩
    let r := challenges i current
    refine ⟨(⟨honestNext R n deg D i current p r,
      (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩, ()), ?_, rfl, ?_⟩
    · rw [ClosedStage.run_eq_executeCore]
      change (do
        let result ← executeCore (sampledReduction R n deg ambient i
          (Finset.univ.map D).toList (pure r))
          ((polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)) current
          (honestMessages R n deg D p i current)
        return result.closed.map (fun claim => (claim, ()))) = _
      erw [executeCore_sampled_eq]
      simp only [pure_bind]
      erw [executeCore_accepted R n deg ambient i current _ _ _ r
        (projected_sum_of_relationRound R n deg D i current p hcurrent)]
      rfl
    · exact relationRound_projected_output R n deg D i current p r
  obtain ⟨output, hex, horacles, hrelation⟩ :=
    OrderedExecution.run_preserves count I stages Inv preserves
      (⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩, ()) ⟨rfl, h⟩
  refine ⟨output.1, ?_, horacles, ?_⟩
  · change Option.map Prod.fst <$> OrderedExecution.run count I stages _ = _
    erw [hex]
    rfl
  · rcases output with ⟨⟨last, impl⟩, payload⟩
    change impl = (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p) at horacles
    subst impl
    exact hrelation

/-- The final closed round is precisely evaluation at the full challenge vector. -/
theorem closedRelation_last_iff {m : ℕ} (D : Fin m ↪ R)
    (claim : ClosedClaim (Spec.StatementRound R n (Fin.last n)) (polynomialFamily R n deg)) :
    closedRelation R n deg D (Fin.last n) claim ↔
      claim.oracles ⟨(), claim.stmt.challenges⟩ = claim.stmt.target := by
  unfold closedRelation
  have : IsEmpty (Fin (n - (Fin.last n).val)) := ⟨fun j => by
    have hj := j.isLt
    simp only [Fin.val_last, Nat.sub_self] at hj
    omega⟩
  erw [Fintype.piFinset_of_isEmpty]
  erw [Finset.univ_unique, Finset.sum_singleton]
  have heq : Fin.append claim.stmt.challenges
      (default : Fin (n - (Fin.last n).val) → R) ∘ Fin.cast (by simp) =
        claim.stmt.challenges := by
    funext j
    simp only [Fin.append, Function.comp_apply, Fin.addCases, Fin.val_cast,
      show j.val < (Fin.last n).val from j.isLt, dite_true]
    congr 1
  erw [heq]
  rfl

/-- Completing all remaining rounds yields the original polynomial's full evaluation claim. -/
theorem executeRounds_evaluation [DecidableEq R] {m : ℕ} (D : Fin m ↪ R)
    (start count : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (p : Spec.OracleStatement R n deg ())
    (challenges : (i : Fin n) → Spec.StatementRound R n i.castSucc → R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D _) :
    ∃ output,
      executeRounds R n deg ambient start count finish.le (Finset.univ.map D).toList
        ⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩
        (honestMessages R n deg D p) challenges = pure (some output) ∧
      p.val.eval (output.stmt.challenges ∘ Fin.cast finish.symm) = output.stmt.target := by
  subst n
  obtain ⟨output, hex, horacles, hrel⟩ := executeRounds_honest R (start + count) deg ambient
    D start count (le_refl _) stmt p challenges h
  refine ⟨output, hex, ?_⟩
  have heval := (closedRelation_last_iff R (start + count) deg D output).mp hrel
  erw [horacles] at heval
  exact heval

end
end Sumcheck.Interaction.MultivariateRound

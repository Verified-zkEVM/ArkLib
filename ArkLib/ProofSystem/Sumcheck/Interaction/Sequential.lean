/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateRound

/-!
# Ordered execution of two Sumcheck rounds

This executor binds two actual `executeCore` computations. The first run closes its own
output, and the second receives precisely that statement and oracle behavior. Rejection
short-circuits the suffix. This is sequential execution, not a flattened dependent protocol.
-/

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ) {ι : Type} (ambient : OracleSpec ι)

/-- Execute consecutive rounds, passing the actual closed middle claim to the suffix. -/
def executeTwo [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (impl : (family R (n + 2) deg).Behavior) (first : Message R deg)
    (second : Spec.StatementRound R (n + 2) i.castSucc.succ → Message R deg)
    (r₁ r₂ : R) :
    OracleComp ambient (Option (ClosedClaim
      (Spec.StatementRound R (n + 2) i.succ.succ) (family R (n + 2) deg))) := do
  let run ← executeCore (reduction R (n + 2) deg ambient i.castSucc domain r₁) impl stmt first
  match run.closed with
  | none => return none
  | some middle =>
      CoreRun.closed <$>
        executeCore (reduction R (n + 2) deg ambient i.succ domain r₂)
          middle.oracles middle.stmt (second middle.stmt)

/-- Accepting rounds preserve the full input behavior while extending the challenges in order. -/
theorem executeTwo_accepted [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (impl : (family R (n + 2) deg).Behavior) (first : Message R deg)
    (second : Spec.StatementRound R (n + 2) i.castSucc.succ → Message R deg)
    (r₁ r₂ : R)
    (h₁ : (domain.map (fun x => first.val.eval x)).sum = stmt.target)
    (h₂ : (domain.map (fun x =>
      (second ⟨first.val.eval r₁, Fin.snoc stmt.challenges r₁⟩).val.eval x)).sum =
        first.val.eval r₁) :
    executeTwo R n deg ambient i domain stmt impl first second r₁ r₂ =
      pure (some (⟨⟨(second ⟨first.val.eval r₁, Fin.snoc stmt.challenges r₁⟩).val.eval r₂,
        Fin.snoc (Fin.snoc stmt.challenges r₁) r₂⟩, impl⟩ :
          ClosedClaim (Spec.StatementRound R (n + 2) i.succ.succ) (family R (n + 2) deg))) := by
  rw [executeTwo, executeCore_accepted R (n + 2) deg ambient i.castSucc stmt impl first
    domain r₁ h₁]
  simp only [pure_bind, acceptedRun_closed]
  exact executeCore_closed R (n + 2) deg ambient i.succ _ impl _ domain r₂ h₂

/-- An incorrect first sum rejects without executing a suffix round. -/
theorem executeTwo_rejected [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (impl : (family R (n + 2) deg).Behavior) (first : Message R deg)
    (second : Spec.StatementRound R (n + 2) i.castSucc.succ → Message R deg)
    (r₁ r₂ : R)
    (h : (domain.map (fun x => first.val.eval x)).sum ≠ stmt.target) :
    executeTwo R n deg ambient i domain stmt impl first second r₁ r₂ = pure none := by
  rw [executeTwo, executeCore_eq, if_neg h]
  rfl

/-- A successful prefix cannot turn a rejecting suffix into an accepted final claim. -/
theorem executeTwo_second_rejected [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (impl : (family R (n + 2) deg).Behavior) (first : Message R deg)
    (second : Spec.StatementRound R (n + 2) i.castSucc.succ → Message R deg)
    (r₁ r₂ : R)
    (h₁ : (domain.map (fun x => first.val.eval x)).sum = stmt.target)
    (h₂ : (domain.map (fun x =>
      (second ⟨first.val.eval r₁, Fin.snoc stmt.challenges r₁⟩).val.eval x)).sum ≠
        first.val.eval r₁) :
    executeTwo R n deg ambient i domain stmt impl first second r₁ r₂ = pure none := by
  rw [executeTwo, executeCore_accepted R (n + 2) deg ambient i.castSucc stmt impl first
    domain r₁ h₁]
  simp only [pure_bind, acceptedRun_closed]
  rw [executeCore_eq, if_neg h₂]
  rfl

/-- Two actual sampled stages; the suffix challenge runs only after successful prefix closing. -/
def executeTwoSampled [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (impl : (family R (n + 2) deg).Behavior) (first : Message R deg)
    (second : Spec.StatementRound R (n + 2) i.castSucc.succ → Message R deg)
    (challenge₁ : OracleComp ambient R)
    (challenge₂ : Spec.StatementRound R (n + 2) i.castSucc.succ → OracleComp ambient R) :
    OracleComp ambient (Option (ClosedClaim
      (Spec.StatementRound R (n + 2) i.succ.succ) (family R (n + 2) deg))) := do
  let run ← executeCore (sampledReduction R (n + 2) deg ambient i.castSucc domain challenge₁)
    impl stmt first
  match run.closed with
  | none => return none
  | some middle =>
      CoreRun.closed <$>
        executeCore (sampledReduction R (n + 2) deg ambient i.succ domain
          (challenge₂ middle.stmt)) middle.oracles middle.stmt (second middle.stmt)

/-- Accepted sampled stages execute prefix and suffix challenge programs in that order. -/
theorem executeTwoSampled_accepted [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (impl : (family R (n + 2) deg).Behavior) (first : Message R deg)
    (second : Spec.StatementRound R (n + 2) i.castSucc.succ → Message R deg)
    (challenge₁ : OracleComp ambient R)
    (challenge₂ : Spec.StatementRound R (n + 2) i.castSucc.succ → OracleComp ambient R)
    (h₁ : (domain.map (fun x => first.val.eval x)).sum = stmt.target)
    (h₂ : ∀ r₁, (domain.map (fun x =>
      (second ⟨first.val.eval r₁, Fin.snoc stmt.challenges r₁⟩).val.eval x)).sum =
        first.val.eval r₁) :
    executeTwoSampled R n deg ambient i domain stmt impl first second challenge₁ challenge₂ =
      (do
        let r₁ ← challenge₁
        let middle : Spec.StatementRound R (n + 2) i.castSucc.succ :=
          ⟨first.val.eval r₁, Fin.snoc stmt.challenges r₁⟩
        let r₂ ← challenge₂ middle
        return some (⟨⟨(second middle).val.eval r₂,
          Fin.snoc middle.challenges r₂⟩, impl⟩ :
            ClosedClaim (Spec.StatementRound R (n + 2) i.succ.succ)
              (family R (n + 2) deg))) := by
  simp only [executeTwoSampled, executeCore_sampled_eq, bind_assoc]
  congr 1
  funext r₁
  rw [executeCore_accepted R (n + 2) deg ambient i.castSucc stmt impl first domain r₁ h₁]
  simp only [pure_bind, acceptedRun_closed, map_bind]
  congr 1
  funext r₂
  exact executeCore_closed R (n + 2) deg ambient i.succ _ impl _ domain r₂ (h₂ r₁)

/-- Prefix rejection retains its challenge effect and never executes the suffix challenge. -/
theorem executeTwoSampled_rejected [DecidableEq R] (i : Fin (n + 1)) (domain : List R)
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (impl : (family R (n + 2) deg).Behavior) (first : Message R deg)
    (second : Spec.StatementRound R (n + 2) i.castSucc.succ → Message R deg)
    (challenge₁ : OracleComp ambient R)
    (challenge₂ : Spec.StatementRound R (n + 2) i.castSucc.succ → OracleComp ambient R)
    (h : (domain.map (fun x => first.val.eval x)).sum ≠ stmt.target) :
    executeTwoSampled R n deg ambient i domain stmt impl first second challenge₁ challenge₂ =
      (fun _ => none) <$> challenge₁ := by
  simp only [executeTwoSampled, executeCore_sampled_eq, bind_assoc]
  rw [map_eq_bind_pure_comp]
  congr 1
  funext r₁
  rw [executeCore_eq, if_neg h]
  rfl

/-- Honest two-round execution starts from the multivariate relation, with no second assumption. -/
theorem executeTwo_honest [DecidableEq R] {m : ℕ} (D : Fin m ↪ R) (i : Fin (n + 1))
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (p : Spec.OracleStatement R (n + 2) deg ()) (r₁ r₂ : R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R (n + 2) deg D i.castSucc.castSucc) :
    executeTwo R n deg ambient i (Finset.univ.map D).toList stmt
      ((family R (n + 2) deg).answerData (fun _ => p))
      (Spec.SingleRound.projectedRoundPolynomial R (n + 2) deg D i.castSucc stmt.challenges p)
      (fun middle => Spec.SingleRound.projectedRoundPolynomial R (n + 2) deg D i.succ
        middle.challenges p) r₁ r₂ =
      pure (some (⟨honestNext R (n + 2) deg D i.succ
        (honestNext R (n + 2) deg D i.castSucc stmt p r₁) p r₂,
          (family R (n + 2) deg).answerData (fun _ => p)⟩ :
            ClosedClaim (Spec.StatementRound R (n + 2) i.succ.succ)
              (family R (n + 2) deg))) := by
  apply executeTwo_accepted
  · exact projected_sum_of_relationRound R (n + 2) deg D i.castSucc stmt p h
  · exact projected_sum_of_relationRound R (n + 2) deg D i.succ _ p
      (relationRound_projected_output R (n + 2) deg D i.castSucc stmt p r₁)

/-- Actual honest sequential execution ends in a claim satisfying the final round relation. -/
theorem executeTwo_complete [DecidableEq R] {m : ℕ} (D : Fin m ↪ R) (i : Fin (n + 1))
    (stmt : Spec.StatementRound R (n + 2) i.castSucc.castSucc)
    (p : Spec.OracleStatement R (n + 2) deg ()) (r₁ r₂ : R)
    (h : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R (n + 2) deg D i.castSucc.castSucc) :
    Option.map (closedRelation R (n + 2) deg D i.succ.succ) <$>
      executeTwo R n deg ambient i (Finset.univ.map D).toList stmt
        ((family R (n + 2) deg).answerData (fun _ => p))
        (Spec.SingleRound.projectedRoundPolynomial R (n + 2) deg D i.castSucc stmt.challenges p)
        (fun middle => Spec.SingleRound.projectedRoundPolynomial R (n + 2) deg D i.succ
          middle.challenges p) r₁ r₂ = pure (some True) := by
  rw [executeTwo_honest R n deg ambient D i stmt p r₁ r₂ h]
  simp only [map_pure, Option.map_some]
  congr 2
  exact propext ⟨fun _ => trivial, fun _ => honestNext_related R (n + 2) deg D i.succ _ p r₂⟩

end
end Sumcheck.Interaction.MultivariateRound

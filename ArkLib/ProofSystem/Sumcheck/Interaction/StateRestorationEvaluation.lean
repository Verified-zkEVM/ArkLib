/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.StateRestorationCertificate
/-!
# Terminal truth for the Sumcheck restoration certificate

The fixed-round path records a field challenge after each degree-bounded message. Evaluation
rejects when any sum check fails, and otherwise retains the final claim about the original
polynomial. The certificate's terminal predicate agrees exactly with this evaluation. The
Unit witness expresses ordinary truth; it does not extract polynomial knowledge.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ENNReal
namespace Sumcheck.Interaction.Restoration
open SingleRound MultivariateRound
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n deg : ℕ)

/-- Evaluate every round sum check along a completed fixed-round path. -/
noncomputable def paddedStatement {m : ℕ} (D : Fin m ↪ F) :
    (count start : ℕ) → (finish : start + count = n) →
    Spec.StatementRound F n ⟨start, by omega⟩ →
    (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath →
    Option (Native.FinalStatement F n)
  | 0, _, _, stmt, _ => some ⟨stmt.target, stmt.challenges ∘ Fin.cast (by simp; omega)⟩
  | count + 1, start, _, stmt, path =>
      if ((Finset.univ.map D).toList.map (fun x => path.1.val.eval x)).sum = stmt.target then
        paddedStatement D count (start + 1) (by omega)
          ⟨path.1.val.eval path.2.1, Fin.snoc stmt.challenges path.2.1⟩ path.2.2
      else none

/-- Every terminal certificate witness is the same ordinary Unit witness. -/
noncomputable def terminalWitnessEquiv {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ()) :
    (count start : ℕ) → (finish : start + count = n) →
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) → (checksPassed : Prop) →
    (path : (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath) →
    Unit ≃
      ((certificate F n deg D p count start finish stmt checksPassed).terminalState path).Witness
  | 0, _, _, _, _, _ => Equiv.refl _
  | count + 1, start, _, stmt, checksPassed, path =>
      terminalWitnessEquiv D p count (start + 1) (by omega)
        ⟨path.1.val.eval path.2.1, Fin.snoc stmt.challenges path.2.1⟩
        (checksPassed ∧
          ((Finset.univ.map D).toList.map (fun x => path.1.val.eval x)).sum = stmt.target)
        path.2.2

/-- Terminal certificate truth is successful evaluation and truth of the retained claim. -/
theorem terminal_holds_iff {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (checksPassed : Prop)
    (path : (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath)
    (w : Unit) :
    ((certificate F n deg D p count start finish stmt checksPassed).terminalState path).holds
      (terminalWitnessEquiv F n deg D p count start finish stmt checksPassed path w) ↔
    checksPassed ∧ ∃ final,
      paddedStatement F n deg D count start finish stmt path = some final ∧
      Native.outputRelation F n deg
        ⟨final, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩ := by
  induction count generalizing start checksPassed with
  | zero =>
      have hs : start = n := by omega
      subst start
      simp only [certificate, terminalWitnessEquiv,
        claimState, paddedStatement, Option.some.injEq, exists_eq_left']
      exact and_congr_right fun _ => closedRelation_last_iff F n deg D _
  | succ count ih =>
      change (((certificate F n deg D p count (start + 1) (by omega)
        ⟨path.1.val.eval path.2.1, Fin.snoc stmt.challenges path.2.1⟩
        (checksPassed ∧
          ((Finset.univ.map D).toList.map (fun x => path.1.val.eval x)).sum =
            stmt.target)).terminalState
          path.2.2).holds _) ↔ _
      simp only [terminalWitnessEquiv]
      erw [ih]
      simp only [paddedStatement]
      split <;> simp_all

/-- The selected messages form an ordinary native prover; public rejection terminates it. -/
def replayProver : (count : ℕ) →
    (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath →
    Prover.Strategy (Unit →ₒ F) (Native.protocol F deg count).tree
      (Native.protocol F deg count).roles (fun _ => Unit)
  | 0, _ => ()
  | count + 1, path => pure ⟨path.1, fun choice => match choice with
    | none => pure ()
    | some _ => pure (replayProver count path.2.2)⟩

/-- The completed path supplies the field coins used by native replay. -/
def replayChallenges : (count : ℕ) →
    (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath → List F
  | 0, _ => []
  | count + 1, path => path.2.1 :: replayChallenges count path.2.2

/-- Replay verifier coins in order; the correspondence theorem supplies enough coins. -/
def challengeReplay : QueryImpl (Unit →ₒ F) (StateT (List F) Id) :=
  fun _ => fun coins => (coins.headD 0, coins.tail)

set_option backward.isDefEq.respectTransparency false in
/-- Native aborting execution and fixed-round evaluation have identical closed outputs
under the same completed challenge path, including the original oracle behavior. -/
theorem replay_execute_eq {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (path : (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath) :
    ((simulateQ (challengeReplay F) (Native.execute F n deg (Unit →ₒ F)
      (liftM ((Unit →ₒ F).query ())) (Finset.univ.map D).toList count start finish
      A originalOracle stmt impl (replayProver F deg count path))).run'
      (replayChallenges F deg count path)) =
      (paddedStatement F n deg D count start finish stmt path).map
        (fun final => ⟨final, originalOracle.eval impl⟩) := by
  induction count generalizing start A with
  | zero =>
      rw [Native.execute_zero]
      rfl
  | succ count ih =>
      rw [Native.execute_succ]
      simp only [replayProver, pure_bind]
      split
      · simp only [simulateQ_bind, simulateQ_query]
        change ((simulateQ (challengeReplay F) (Native.execute F n deg (Unit →ₒ F)
          (liftM ((Unit →ₒ F).query ())) (Finset.univ.map D).toList count (start + 1) (by omega)
          _ _ ⟨path.1.val.eval path.2.1, Fin.snoc stmt.challenges path.2.1⟩ _
          (replayProver F deg count path.2.2))).run' (replayChallenges F deg count path.2.2)) = _
        rw [ih]
        simp only [paddedStatement]
        split
        · rw [VirtualOracle.eval_sumWeaken_extendImpl]
        · contradiction
      · simp only [simulateQ_pure, paddedStatement]
        split
        · contradiction
        · rfl

/-- The actual aborting native verifier, replayed on the selected messages and field coins. -/
noncomputable def nativeReplayOutput {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (path : (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath) :
    Option (ClosedClaim (Native.FinalStatement F n) (polynomialFamily F n deg)) :=
  (simulateQ (challengeReplay F) (Native.execute F n deg (Unit →ₒ F)
    (liftM ((Unit →ₒ F).query ())) (Finset.univ.map D).toList count start finish
    A originalOracle stmt impl (replayProver F deg count path))).run'
    (replayChallenges F deg count path)

/-- The certificate is true exactly when native replay succeeds with a true closed claim.
The source law identifies the retained original oracle with the polynomial in the certificate. -/
theorem terminal_holds_iff_native {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (sourceLaw : originalOracle.eval impl =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (checksPassed : Prop)
    (path : (Security.StateRestoration.protocol (rounds F deg count)).tree.ExecutionPath)
    (w : Unit) :
    ((certificate F n deg D p count start finish stmt checksPassed).terminalState path).holds
      (terminalWitnessEquiv F n deg D p count start finish stmt checksPassed path w) ↔
    checksPassed ∧ ∃ output,
      nativeReplayOutput F n deg D count start finish A originalOracle stmt impl path =
        some output ∧ Native.outputRelation F n deg output := by
  rw [terminal_holds_iff, nativeReplayOutput, replay_execute_eq, sourceLaw]
  cases paddedStatement F n deg D count start finish stmt path <;> simp

end Sumcheck.Interaction.Restoration

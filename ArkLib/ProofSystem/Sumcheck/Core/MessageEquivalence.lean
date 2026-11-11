/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.InterpretedExecution
public import ArkLib.ProofSystem.Sumcheck.Core.IntervalSoundness

/-! # Mathematical specialization of interpreted message verification -/

@[expose] public section

namespace Sumcheck.Core.Interpreted
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {deg : ℕ}

/-- Polynomial evaluation gives exactly the native mathematical message interface. -/
theorem messageInterface_polynomial :
    messageInterface (fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) =
      (inferInstance : OracleInterface R⦃≤ deg⦄[X]) := rfl

/-- The interpreted mathematical tree is the native Sumcheck tree. -/
theorem protocol_polynomial (k : ℕ) :
    protocol R R⦃≤ deg⦄[X] (fun q r => q.val.eval r) k = Sumcheck.Core.protocol R deg k := rfl

/-- Polynomial interpretation gives the native chronological verdict. -/
theorem verdict_polynomial {State : ℕ → Type} {T : Type} (checks : RoundChecks R State)
    (finish : State 0 → T) (k : ℕ) (st : State k)
    (tr : PathAlong oracleSig (Sumcheck.Core.protocol R deg k)) :
    verdict (fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) checks finish k st tr =
      foldVerdict checks finish k st tr := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases tr with ⟨msg, r, rest⟩
    simp only [verdict, foldVerdict, message, challenge, tail, headMessage, headChallenge,
      tailTranscript]
    exact congrArg (fun f => (Sumcheck.Core.roundVerdict (checks k) st msg r).bind f)
      (funext fun mid => ih mid rest)

/-- Polynomial interpretation gives the native fold decision at every round count. -/
theorem decision_polynomial {State : ℕ → Type} {T : Type} (checks : RoundChecks R State)
    (finish : State 0 → T) (k : ℕ) :
    decision (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) checks finish k =
      foldDecision checks finish k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext st p v
    rcases p with ⟨⟨⟩, ⟨⟨⟩, p⟩⟩
    simp only [decision, foldDecision, ih]
    rfl

/-- Interpreted mathematical verification specializes to the native passive fold, with the
same decision, input oracle and output oracle. -/
theorem verifier_polynomial {ι I : Type} (ambient : OracleSpec ι) {A : I → Type}
    (inputs : OracleFamily I A) {State : ℕ → Type} {T : Type} (checks : RoundChecks R State)
    (finish : State 0 → T) (k : ℕ) :
    (verifier (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r)
      ambient inputs checks finish k) = foldVerifier R deg ambient inputs checks finish k := by
  unfold verifier foldVerifier
  rw [decision_polynomial]

end Sumcheck.Core.Interpreted

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interpreted

/-! # Passive folds of round checks

Each check queries only its round polynomial. The verifier runs every interaction before
checking the messages in order, and keeps the input oracle as its output oracle.

The polynomial fold is the interpreted fold of `Interpreted` at polynomial evaluation. Each name
below abbreviates that instance, so the generic laws `Interpreted.simulate_decision`,
`Interpreted.simulate_verifier` and `Interpreted.verifier_run` apply to it unchanged.
-/

@[expose] public section

namespace Sumcheck
open Polynomial PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {deg : ℕ}

/-- The result of a round check answered by its message polynomial. -/
noncomputable abbrev roundVerdict {S T : Type} (check : S → R →
    OptionT (OracleComp (R →ₒ R)) T) (stmt : S) (msg : R⦃≤ deg⦄[X]) (r : R) : Option T :=
  Interpreted.roundVerdict (fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) check stmt msg r

/-- Check all messages in order and retain explicit rejection. -/
noncomputable abbrev foldVerdict {State : ℕ → Type} {T : Type}
    (V : RoundChecks R State) (finish : State 0 → T) :
    (k : ℕ) → State k → Transcript oracleSig (protocol R deg k) → Option T :=
  Interpreted.verdict (fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) V finish

/-- One more round checks the head message, then the remaining rounds from the new state. -/
theorem foldVerdict_succ {State : ℕ → Type} {T : Type} (V : RoundChecks R State)
    (finish : State 0 → T) (k : ℕ) (st : State (k + 1))
    (tr : Transcript oracleSig (protocol R deg (k + 1))) :
    foldVerdict V finish (k + 1) st tr =
      (roundVerdict (V k) st (Interpreted.message tr) (Interpreted.challenge tr)).bind fun mid =>
        foldVerdict V finish k mid (Interpreted.tail tr) := rfl

/-- The final decision queries every round through its own oracle message. -/
abbrev foldDecision {State : ℕ → Type} {T : Type}
    (V : RoundChecks R State) (finish : State 0 → T) :
    (k : ℕ) → State k → (p : Path (protocol R deg k)) → View (protocol R deg k) p →
      OracleComp (oracleMessageSpec (protocol R deg k) p) (Option T) :=
  Interpreted.decision (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r) V finish

/-- A passive verifier that retains its input oracle and checks all messages at the end. -/
abbrev foldVerifier (R : Type) [CommSemiring R] (deg : ℕ) {ι : Type} (ambient : OracleSpec ι)
    (inputs : OracleBundle)
    {State : ℕ → Type} {T : Type} (V : RoundChecks R State) (finish : State 0 → T) (k : ℕ) :
    OracleVerifier ambient (protocol R deg k) (State k) (fun _ => T) inputs
      (fun _ => inputs) :=
  Interpreted.verifier (evaluate := fun (q : R⦃≤ deg⦄[X]) r => q.val.eval r)
    ambient inputs V finish k

end Sumcheck

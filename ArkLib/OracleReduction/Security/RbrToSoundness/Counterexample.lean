/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calgooon
-/
module

public import ArkLib.OracleReduction.Security.RbrToSoundness

/-!
# The union step is false as stated: the executed negative

See `RbrToSoundness.lean`. One flag oracle simulated statefully, the empty protocol, a verifier
that outputs the flag: `rbrSoundness` with every error `0` and `soundness … 0` failing with
probability one.

The counterexample. One oracle with a Boolean input (`true` sets a flag, `false` reads it)
simulated statefully on `σ := Bool` from `init := pure false`; the empty protocol (`!p[]`, no
rounds, so `rbrSoundness` has no challenge round to constrain and holds with every error `0`);
the verifier reads the flag and outputs it; `langIn := ∅`, `langOut := {true}`. The state
function that is `False` everywhere is a `StateFunction`: `toFun_empty` because `langIn = ∅`;
`toFun_next` vacuously (no rounds); `toFun_full` because from a FRESH `init` the flag is `false`
and the verifier outputs `false ∉ {true}` with probability one. But the prover's output step
SETS the flag before the verifier reads it, so in the soundness game the verifier outputs
`true ∈ {true}` with probability one, and `soundness … (∑ i, 0) = soundness … 0` fails.

What breaks is the quantification of `toFun_full`: it speaks of the verifier run from a fresh
draw of `init`, while the soundness game runs the verifier from the oracle state the prover's
queries left behind. `RbrToSoundness.lean` proves the theorem under the ∀-state form of that
clause, and hence whenever `σ` is a subsingleton.
-/

@[expose] public section

namespace ArkLib.RbrToSoundness.Counterexample

open OracleComp OracleSpec ProtocolSpec ArkLib.RbrToSoundness
open scoped NNReal ENNReal ProbabilityTheory

/-- one oracle with a Boolean input: `true` sets the flag, `false` reads it; Boolean answers -/
abbrev flagSpec : OracleSpec Bool := Bool →ₒ Bool

/-- the stateful simulation of the flag: `set` writes `true` and answers `true`; `read` answers
the flag -/
def flagImpl : QueryImpl flagSpec (StateT Bool ProbComp) :=
  fun t => match t with
    | true => do set true; pure true
    | false => get

/-- the verifier of the empty protocol: read the flag, output it -/
def flagVerifier : Verifier flagSpec Unit Bool !p[] where
  verify := fun _ _ => OptionT.lift (liftM (flagSpec.query false))

/-- the prover of the empty protocol: its output step sets the flag and claims `true` -/
def flagProver : Prover flagSpec Unit Unit Bool Unit !p[] where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => Fin.elim0 i.1
  receiveChallenge := fun i => Fin.elim0 i.1
  output := fun _ => do
    let _ ← (liftM (flagSpec.query true) : OracleComp flagSpec Bool)
    pure (true, ())

/-- the verifier's run from the flag `b`: it outputs `b` and leaves the flag alone -/
lemma flagVerifier_run (tr : (!p[] : ProtocolSpec 0).FullTranscript) (b : Bool) :
    (simulateQ flagImpl (flagVerifier.run () tr)).run b = pure (some b, b) := by
  have h : (flagVerifier.run () tr : OracleComp flagSpec (Option Bool)) =
      (liftM (flagSpec.query false) : OracleComp flagSpec Bool) >>= fun a => pure (some a) := rfl
  rw [h, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp [flagImpl]

/-- the same at the transcript type `toFun_full` speaks of (`Transcript (Fin.last 0)`, a `take`
of the spec) -/
lemma flagVerifier_run' (tr : Transcript (Fin.last 0) (!p[] : ProtocolSpec 0)) (b : Bool) :
    (simulateQ flagImpl (flagVerifier.run () tr)).run b = pure (some b, b) :=
  flagVerifier_run tr b

/-- the state function that is false everywhere is a state function for the flag verifier from
a fresh `init` -/
def flagStateFunction :
    flagVerifier.StateFunction (pure false) flagImpl (∅ : Set Unit) ({true} : Set Bool) where
  toFun := fun _ _ _ => False
  toFun_empty := fun _ => by simp
  toFun_next := fun m => Fin.elim0 m
  toFun_full := fun stmt tr _ => by
    cases stmt
    rw [OptionT.prEvent_mk_eq_zero_iff]
    intro x hx
    simp only [pure_bind, StateT.run'_eq, flagVerifier_run', map_pure, mem_support_pure_iff,
      Option.some.injEq] at hx
    subst hx
    simp

/-- round-by-round soundness holds with every error zero: there is no challenge round -/
theorem flag_rbrSoundness :
    flagVerifier.rbrSoundness (pure false) flagImpl ∅ {true} (fun _ => (0 : ℝ≥0)) :=
  ⟨flagStateFunction, fun _ _ _ _ _ _ i => Fin.elim0 i.1⟩

/-- the prefix run of the empty protocol: nothing happens, the flag stays `false` -/
lemma flag_prefixRun :
    prefixRun (pure false) flagImpl () () flagProver (Fin.last 0) =
      (pure ((default, ()), false) :
        ProbComp ((Transcript (Fin.last 0) (!p[] : ProtocolSpec 0) ×
          flagProver.PrvState (Fin.last 0)) × Bool)) :=
  rfl

/-- the prover's output step from the flag `false`: it sets the flag and claims `true` -/
lemma flag_output :
    (simulateQ (flagImpl.addLift challengeQueryImpl :
        QueryImpl (flagSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)
          (StateT Bool ProbComp))
      (liftM (flagProver.output ()) :
        OracleComp (flagSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ'challengeOracleInterface)
          _)).run false =
      pure ((true, ()), true) := by
  rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_left, QueryImpl.liftTarget_self]
  simp only [flagProver, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, flagImpl,
    StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]

/-- the soundness game of the flag prover is deterministic: the verifier reads the flag the
prover set -/
lemma flag_game : soundGame (pure false) flagImpl () () flagProver flagVerifier =
    pure ((default, true, ()), true) := by
  rw [soundGame_eq, fullRun_eq, flag_prefixRun, pure_bind]
  simp only [flag_output, pure_bind, flagVerifier_run]
  rfl

/-- soundness with error `∑ i, 0 = 0` FAILS for the flag verifier -/
theorem flag_not_soundness :
    ¬ flagVerifier.soundness (pure false) flagImpl ∅ {true}
      (∑ i : (!p[] : ProtocolSpec 0).ChallengeIdx, (fun _ => (0 : ℝ≥0)) i) := by
  intro h
  have := h Unit Unit () flagProver () (Set.notMem_empty ())
  change Pr{let x ← soundGame (pure false) flagImpl () () flagProver flagVerifier}[
    x.2 ∈ ({true} : Set Bool)] ≤ _ at this
  rw [flag_game, OptionT.prEvent_eq_run, OptionT.run_pure] at this
  have h0 := le_antisymm (this.trans (by simp)) zero_le
  rw [prEvent_eq_zero_iff] at h0
  exact h0 (some ((default, true, ()), true)) (by rw [mem_support_pure_iff]) (by simp)

/-- **the original statement is false**: `rbrSoundness → soundness (∑ i, ε i)` does not hold for
every `init` and `impl` -/
theorem pin_statement_false :
    ¬ ∀ {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
        [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type}
        (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
        (langIn : Set StmtIn) (langOut : Set StmtOut)
        (verifier : Verifier oSpec StmtIn StmtOut pSpec)
        (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0),
        verifier.rbrSoundness init impl langIn langOut rbrSoundnessError →
          verifier.soundness init impl langIn langOut (∑ i, rbrSoundnessError i) :=
  fun h => flag_not_soundness (h (pure false) flagImpl ∅ {true} flagVerifier (fun _ => 0)
    flag_rbrSoundness)

end ArkLib.RbrToSoundness.Counterexample

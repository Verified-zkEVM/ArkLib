/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.CompositionSoundness
import ArkLibTest.Interaction.Core.Support
import ArkLibTest.Interaction.Core.Oracle.HiddenBitFixture
import VCVio.OracleComp.EvalDist.AnswerMeasure
import VCVio.OracleComp.QueryTracking.CostModel.Simulation
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Guessing a hidden runtime bit

The hidden-bit fixture runs in a persistent runtime that samples the bit once at setup. A prover
commits to a guess before the suffix decision reveals the bit. The append boundary is the prefix
interaction result together with the runtime state and trace, so the prover's continuation and the
runtime history stay correlated in the boundary distribution. The runtime transport theorem
bounds the guessing prover's success by `1/2`. Its averaged premise is proved from the actual
prefix run and the resumed suffix (`guess_integrated`), not from the whole-run probability; the
whole-run calculation is kept as a regression (`guess_average_whole_run`). The pointwise form
also gives `1/2` with a boundary-dependent error, while a uniform pointwise error of `1/2` fails.
A prover that reveals the bit in the seam slot succeeds surely, and the averaged half-error
premise fails for it.

The last section gives the charged ambient histories, the cost and access bounds of the export and
the routed suffix decision, and the import budget of the same experiment.

## Port notes

The rows below restate the old `Oracle/RuntimeSoundness.lean` and `RuntimeQueryBounds.lean` tests.
The passive schedule changes one order and keeps every probability and charge. In the old
hidden-bit trace, the prefix verifier's dummy request comes before the informed prover's reveal.
Under the passive schedule the prefix decision runs after the suffix interaction, so the reveal
comes first: challenge, reveal, dummy request, reveal. The informed prover still succeeds surely
with charge 7, and the guess prover still succeeds with probability `1/2` with charge 4. #1478's
port table records the same disposition for the shared rows:
https://github.com/Verified-zkEVM/ArkLib/blob/b898b53fd23acd06a8f262a48178db800cf0ba6f/docs/design/interaction-layer/port-oracle-access.md#L176-L192
-/

open PFunctor Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Interaction.Core.RuntimeSoundnessTests

open Interaction.Core.HiddenBitFixture

noncomputable section

/-- A final claim: the claimed bit and the output data. -/
abbrev Claim := Bool × (∀ _ : Unit, Bool)
/-- The observation of a run of the composed hidden-bit verifier. -/
abbrev RunOutcome := Outcome oracleSig.{0, 0} bitCombined (fun _ => Nat) (fun _ => Claim)

/-- A final claim is true when its output oracle answers its statement. -/
def TruthFinal (claim : Claim) : Prop := claim.2 () = claim.1
/-- The run returns a true final claim. -/
def Success (obs : RunOutcome) : Prop := obs.2.2.map TruthFinal = some True
/-- The output oracle's answer and the claimed bit, if the run accepts. -/
def Answer (obs : RunOutcome) : Option (Bool × Bool) :=
  obs.2.2.map fun claim => (claim.2 (), claim.1)

/-- The append boundary of a hidden-bit run. -/
abbrev Boundary := RunBoundary oracleSig bitAmbient bitFirst.{0} (fun _ => bitSecond) (fun _ => Nat)

/-- The prefix interaction of a hidden-bit run, up to its append boundary. -/
abbrev prefixRun (prover : Prover oracleSig bitAmbient bitCombined (fun _ => Nat)) :=
  appendPrefixRun (s₂ := fun _ => bitSecond) prover

-- RuntimeSoundness row 2 (`guess_answers`), restated over `OracleVerifier.run`.
/-- At a fixed hidden state the guess prover's run answers `(guess, hidden)`. -/
theorem guess_answers (guess hidden : Bool) (secret : Nat) :
    (fun result => Answer result.1.1) <$>
      bitRuntime.handler.runState (hidden, 0)
        (bitVerifier.run () falseData (guessProver guess secret)).withQueryLog =
    pure (some (guess, hidden)) := by
  cases guess <;> cases hidden <;> kernel_rfl

-- RuntimeSoundness row 1 (`native_success_eq_split`), restated: the split at the prefix
-- interaction boundary, `OracleVerifier.run_eq_bind`, in any runtime.
/-- Success of a run equals success of its prefix interaction followed by the rest of the run. -/
theorem success_eq_split (world : OracleRuntime coinSpec bitFull)
    (prover : Prover oracleSig bitAmbient bitCombined (fun _ => Nat)) :
    Pr{let result ← world.run (bitVerifier.run () falseData prover)}[Success result.output] =
      Pr{let result ← world.run (appendPrefixRun (s₂ := fun _ => bitSecond) prover >>=
        bitVerifier.suffixRun () falseData)}[Success result.output] := by
  rw [OracleVerifier.run_eq_bind]

-- RuntimeSoundness row 3 (`runFrom_guess_answers`), restated.
/-- The same answer through `runFrom`. -/
theorem runFrom_guess_answers (guess hidden : Bool) (secret : Nat) :
    (fun result => Answer result.output) <$>
      bitRuntime.runFrom (hidden, 0) (bitVerifier.run () falseData (guessProver guess secret)) =
    pure (some (guess, hidden)) := by
  have observed := congrArg (fun program => (fun result => Answer result.1) <$> program)
    (bitRuntime.runFrom_observe (hidden, 0)
      (bitVerifier.run () falseData (guessProver guess secret)))
  calc
    _ = _ := by simpa only [Functor.map_map] using observed
    _ = _ := guess_answers guess hidden secret

-- RuntimeSoundness row 4 (`run_guess_answers`), restated.
/-- Through `run`, the answer is `(guess, hidden)` over the sampled bit. -/
theorem run_guess_answers (guess : Bool) (secret : Nat) :
    (fun result => Answer result.output) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
    (fun hidden => some (guess, hidden)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  rw [OracleRuntime.run_eq, map_bind]
  simp only [bitRuntime, bind_assoc, pure_bind]
  simp_rw [runFrom_guess_answers]
  rfl

-- RuntimeSoundness row 5 (`guess_success`), restated.
/-- A fixed guess succeeds with probability `1/2`. -/
theorem guess_success (guess : Bool) (secret : Nat) :
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret))}[
      Success result.output] = 2⁻¹ := by
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{let pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
    (run_guess_answers guess secret)
  simp only [prEvent_map, Answer, Option.map_map, Function.comp_def] at mass
  convert mass.trans ?_ using 1
  · rfl
  · simp only [Option.map_some, Option.some.injEq]
    rw [prEvent_eq_evalDist_of_discrete,
      OracleComp.evalDist_liftM_query_apply (spec := coinSpec) () MeasurableSet.of_discrete]
    have event : {hidden : Bool | (guess = hidden) = True} = {guess} := by
      ext hidden
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, eq_iff_iff, true_iff, eq_comm]
    rw [event, OracleSpec.UniformAnswerMeasure.toMeasure_singleton]
    rfl

/-- Run results carry the discrete measurable space. -/
local instance : MeasurableSpace (RunResult bitRuntime Boundary) := ⊤
/-- The discrete measurable space on run results. -/
local instance : DiscreteMeasurableSpace (RunResult bitRuntime Boundary) := ⟨fun _ => trivial⟩

-- RuntimeSoundness row 6 (`average_success`), restated: the boundary is the prefix interaction
-- result with the runtime state and trace.
/-- Success is the resumed success averaged over the joint boundary. -/
theorem average_success (prover : Prover oracleSig bitAmbient bitCombined (fun _ => Nat)) :
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData prover)}[
      Success result.output] =
    ∫⁻ b, Pr{let result ← bitRuntime.resume b (bitVerifier.suffixRun () falseData)}[
      Success result.output] ∂𝒟[bitRuntime.run (prefixRun prover)] := by
  rw [OracleVerifier.run_eq_bind, bitRuntime.run_bind, prEvent_bind_eq_lintegral_of_discrete]

-- RuntimeSoundness row 7 (`guess_integrated`), whole-run regression: the averaged resumed
-- success equals the whole-run success. `guess_integrated` below proves the half-error premise
-- from the prefix run and the resumed suffix instead, without this calculation.
/-- For a fixed guess, the resumed success averaged over the joint boundary is the whole-run
success `1/2`. -/
theorem guess_average_whole_run (guess : Bool) (secret : Nat) :
    ∫⁻ b, Pr{let result ← bitRuntime.resume b (bitVerifier.suffixRun () falseData)}[
      Success result.output] ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))] =
      2⁻¹ := by
  rw [← average_success, guess_success]

-- RuntimeSoundness row 9 (`informed_answers`), restated.
/-- At a fixed hidden state the informed prover's run answers `(hidden, hidden)`. -/
theorem informed_answers (hidden : Bool) (secret : Nat) :
    (fun result => Answer result.1.1) <$>
      bitRuntime.handler.runState (hidden, 0)
        (bitVerifier.run () falseData (informedProver secret)).withQueryLog =
    pure (some (hidden, hidden)) := by
  cases hidden <;> kernel_rfl

-- RuntimeSoundness row 10 (`runFrom_informed_answers`), restated.
/-- The same answer through `runFrom`. -/
theorem runFrom_informed_answers (hidden : Bool) (secret : Nat) :
    (fun result => Answer result.output) <$>
      bitRuntime.runFrom (hidden, 0) (bitVerifier.run () falseData (informedProver secret)) =
    pure (some (hidden, hidden)) := by
  have observed := congrArg (fun program => (fun result => Answer result.1) <$> program)
    (bitRuntime.runFrom_observe (hidden, 0)
      (bitVerifier.run () falseData (informedProver secret)))
  calc
    _ = _ := by simpa only [Functor.map_map] using observed
    _ = _ := informed_answers hidden secret

-- RuntimeSoundness row 11 (`run_informed_answers`), restated.
/-- Through `run`, the answer is `(hidden, hidden)` over the sampled bit. -/
theorem run_informed_answers (secret : Nat) :
    (fun result => Answer result.output) <$>
      bitRuntime.run (bitVerifier.run () falseData (informedProver secret)) =
    (fun hidden => some (hidden, hidden)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  rw [OracleRuntime.run_eq, map_bind]
  simp only [bitRuntime, bind_assoc, pure_bind]
  simp_rw [runFrom_informed_answers]
  rfl

-- RuntimeSoundness row 12 (`informed_success`), restated.
/-- The informed prover reveals the bit in the seam slot and succeeds surely. -/
theorem informed_success (secret : Nat) :
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (informedProver secret))}[
      Success result.output] = 1 := by
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{let pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
    (run_informed_answers secret)
  simp only [prEvent_map, Answer, Option.map_map, Function.comp_def] at mass
  convert mass.trans ?_ using 1
  · rfl
  · simp only [Option.map_some, eq_self, prEvent_true_eq_evalDist_apply_univ,
      OracleComp.evalDist_apply_univ_eq_one]

-- RuntimeSoundness row 13 (`informed_half_premise_fails`), restated.
/-- The averaged half-error premise fails for reveal-before-commit. -/
theorem informed_half_premise_fails (secret : Nat) :
    ¬ ((∫⁻ b in {_b : RunResult bitRuntime Boundary | ¬ False},
      Pr{let result ← bitRuntime.resume b (bitVerifier.suffixRun () falseData)}[
        Success result.output]
        ∂𝒟[bitRuntime.run (prefixRun (informedProver secret))]) ≤
    ∫⁻ _b in {_b : RunResult bitRuntime Boundary | ¬ False}, (2 : ℝ≥0∞)⁻¹
      ∂𝒟[bitRuntime.run (prefixRun (informedProver secret))]) := by
  simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_univ]
  rw [← average_success, informed_success, lintegral_const,
    OracleComp.evalDist_apply_univ_eq_one, mul_one]
  norm_num

-- RuntimeSoundness row 14 (`prefix_history`), restated: the dummy request moves to the prefix
-- decision at the end of the run, so the boundary state is `(hidden, 0)`; the trace holds the
-- challenge query, since challenges are queries of the run interface.
/-- The guess run's boundary has state `(hidden, 0)` and only the challenge in its trace. -/
theorem prefix_history (guess hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      bitRuntime.handler.runState (hidden, 0)
        (appendPrefixRun (s₂ := fun _ => bitSecond) (guessProver guess secret)).withQueryLog =
    pure ((hidden, 0), ([⟨challengeEntry, ()⟩] : QueryLog bitFull)) := by
  kernel_rfl

-- RuntimeSoundness row 15 (`informed_prefix_history`), restated: the boundary keeps the prover's
-- seam-slot reveal after the challenge. The old boundary also held the prefix decision's dummy
-- request before the reveal; under the passive schedule that request moves to the end of the
-- run (see the port notes).
/-- The informed run's boundary has state `(hidden, 1)` and trace `[challenge, true ↦ hidden]`. -/
theorem informed_prefix_history (hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      bitRuntime.handler.runState (hidden, 0)
        (appendPrefixRun (s₂ := fun _ => bitSecond) (informedProver secret)).withQueryLog =
    pure ((hidden, 1),
      ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull)) := by
  kernel_rfl

-- RuntimeSoundness row 16 (`final_history`), restated: the challenge, then the prefix decision's
-- dummy request and the suffix decision's reveal.
/-- The whole guess run ends in state `(hidden, 2)`. -/
theorem final_history (guess hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      bitRuntime.handler.runState (hidden, 0)
        (bitVerifier.run () falseData (guessProver guess secret)).withQueryLog =
    pure ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull)) := by
  kernel_rfl

-- RuntimeSoundness row 17 (`informed_final_history`), restated: the prover's reveal precedes
-- both decisions. The old trace was dummy request, reveal, reveal; the passive trace is
-- challenge, reveal, dummy request, reveal, with the same final count 3 (see the port notes).
/-- The whole informed run ends in state `(hidden, 3)`. -/
theorem informed_final_history (hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      bitRuntime.handler.runState (hidden, 0)
        (bitVerifier.run () falseData (informedProver secret)).withQueryLog =
    pure ((hidden, 3), ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩, ⟨.inl false, false⟩,
      ⟨.inl true, hidden⟩] : QueryLog bitFull)) := by
  kernel_rfl

-- RuntimeSoundness row 18 (`run_history`).
/-- Lift fixed-state observations of a program through the runtime's setup. -/
theorem run_history {A : Type} (program : OracleComp bitFull A)
    (history : Bool → (Bool × Nat) × QueryLog bitFull)
    (observed : ∀ hidden, (fun result => (result.2, result.1.2)) <$>
      bitRuntime.handler.runState (hidden, 0) program.withQueryLog = pure (history hidden)) :
    (fun result => (result.state, result.trace)) <$> bitRuntime.run program =
    history <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  have fromState hidden : (fun result => (result.state, result.trace)) <$>
      bitRuntime.runFrom (hidden, 0) program = pure (history hidden) := by
    have same := congrArg (fun program => (fun result => (result.2.1, result.2.2)) <$> program)
      (bitRuntime.runFrom_observe (hidden, 0) program)
    calc
      _ = _ := by simpa only [Functor.map_map] using same
      _ = _ := observed hidden
  rw [OracleRuntime.run_eq, map_bind]
  simp only [bitRuntime, bind_assoc, pure_bind]
  simp_rw [fromState]
  rfl

-- RuntimeSoundness row 19 (prefix runtime run), restated as row 14.
/-- The guess run's prefix boundary has state `(hidden, 0)` for the sampled bit and only the
challenge in its trace. -/
theorem prefix_run_history (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace)) <$>
      bitRuntime.run (appendPrefixRun (s₂ := fun _ => bitSecond) (guessProver guess secret)) =
    (fun hidden => ((hidden, 0), ([⟨challengeEntry, ()⟩] : QueryLog bitFull))) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) :=
  run_history _ _ (fun hidden => prefix_history guess hidden secret)

/-- The hidden bit at a guess run's prefix boundary is the setup sample. -/
theorem prefix_hidden (guess : Bool) (secret : Nat) :
    (fun b => b.state.1) <$> bitRuntime.run (prefixRun (guessProver guess secret)) =
      (coinSpec.query () : OracleComp coinSpec Bool) := by
  have h := congrArg (fun program => (fun r => r.1.1) <$> program)
    (prefix_run_history guess secret)
  simpa only [Functor.map_map, id_map'] using h

-- RuntimeSoundness row 7 (`guess_integrated`), proved directly: the prefix run from each
-- hidden state, then the resumed suffix from each of its boundaries. The proof does not use the
-- whole-run probability.
/-- From a fixed hidden state, a guess run's prefix reaches a boundary with that hidden bit, and
the suffix resumed from it answers `(guess, hidden)`. -/
theorem resumed_guess_answers (guess hidden : Bool) (secret : Nat) :
    (fun b => (b.state.1, (fun result => Answer result.output) <$>
        bitRuntime.resume b (bitVerifier.suffixRun () falseData))) <$>
      bitRuntime.runFrom (hidden, 0) (prefixRun (guessProver guess secret)) =
    pure (hidden, pure (some (guess, hidden))) := by
  cases guess <;> cases hidden <;> kernel_rfl

/-- From every possible boundary of a guess run's prefix, the resumed suffix answers
`(guess, hidden)` for the boundary's hidden bit. -/
theorem boundary_resumed_answers (guess : Bool) (secret : Nat)
    (b : RunResult bitRuntime Boundary)
    (hb : b ∈ support (bitRuntime.run (prefixRun (guessProver guess secret)))) :
    (fun result => Answer result.output) <$>
      bitRuntime.resume b (bitVerifier.suffixRun () falseData) =
    pure (some (guess, b.state.1)) := by
  rw [OracleRuntime.run_eq, mem_support_bind_iff] at hb
  obtain ⟨state, hstate, hb⟩ := hb
  simp only [bitRuntime, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hstate
  obtain ⟨hidden, -, rfl⟩ := hstate
  have hpair : (b.state.1, (fun result => Answer result.output) <$>
      bitRuntime.resume b (bitVerifier.suffixRun () falseData)) ∈
      support (pure (hidden, pure (some (guess, hidden))) :
        OracleComp coinSpec (Bool × OracleComp coinSpec (Option (Bool × Bool)))) := by
    rw [← resumed_guess_answers guess hidden secret, support_map]
    exact ⟨b, hb, rfl⟩
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hpair
  rw [hpair.2, hpair.1]

/-- From every possible boundary of a guess run's prefix, the resumed suffix succeeds surely if
the guess matches the boundary's hidden bit, and never otherwise. -/
theorem resumed_guess_success (guess : Bool) (secret : Nat) (b : RunResult bitRuntime Boundary)
    (hb : b ∈ support (bitRuntime.run (prefixRun (guessProver guess secret)))) :
    Pr{let result ← bitRuntime.resume b (bitVerifier.suffixRun () falseData)}[
      Success result.output] = if guess = b.state.1 then 1 else 0 := by
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{let pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
    (boundary_resumed_answers guess secret b hb)
  simp only [prEvent_map] at mass
  calc
    _ = Pr{let pair ←
        (pure (some (guess, b.state.1)) : OracleComp coinSpec (Option (Bool × Bool)))}[
        pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True] := by
      simp only [Answer, Option.map_map, Function.comp_def] at mass
      convert mass using 1
      rfl
    _ = _ := by
      generalize b.state.1 = hidden
      cases guess <;> cases hidden <;> simp

/-- The prefix boundary's hidden bit matches a fixed guess with probability `1/2`. -/
theorem guess_match_probability (guess : Bool) (secret : Nat) :
    Pr{let b ← bitRuntime.run (prefixRun (guessProver guess secret))}[guess = b.state.1] =
      2⁻¹ := by
  have hidden : Pr{let b ← bitRuntime.run (prefixRun (guessProver guess secret))}[
      guess = b.state.1] = Pr{let hidden ← (coinSpec.query () : OracleComp coinSpec Bool)}[
      guess = hidden] := by
    rw [← prefix_hidden guess secret, prEvent_map]
  rw [hidden, prEvent_eq_evalDist_of_discrete,
    OracleComp.evalDist_liftM_query_apply (spec := coinSpec) () MeasurableSet.of_discrete]
  have event : {hidden : Bool | guess = hidden} = {guess} := by
    ext hidden
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, eq_comm]
  rw [event, OracleSpec.UniformAnswerMeasure.toMeasure_singleton]
  rfl

/-- The boundary-dependent error `1` on a matching hidden bit and `0` otherwise integrates to
`1/2` over the prefix boundary. -/
theorem guess_match_integral (guess : Bool) (secret : Nat) :
    ∫⁻ b, (if guess = b.state.1 then (1 : ℝ≥0∞) else 0)
      ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))] = 2⁻¹ := by
  have indicator : (fun b : RunResult bitRuntime Boundary =>
      if guess = b.state.1 then (1 : ℝ≥0∞) else 0) = {b | guess = b.state.1}.indicator 1 := by
    funext b
    simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  rw [indicator, lintegral_indicator_one MeasurableSet.of_discrete,
    ← prEvent_eq_evalDist_of_discrete, guess_match_probability]

/-- The averaged half-error premise holds for a fixed guess. The proof evaluates the resumed
suffix at each boundary of the actual prefix run and integrates over the hidden bit. -/
theorem guess_integrated (guess : Bool) (secret : Nat) :
    (∫⁻ b in {_b : RunResult bitRuntime Boundary | ¬ False},
      Pr{let result ← bitRuntime.resume b (bitVerifier.suffixRun () falseData)}[
        Success result.output]
        ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))]) ≤
    ∫⁻ _b in {_b : RunResult bitRuntime Boundary | ¬ False}, (2 : ℝ≥0∞)⁻¹
      ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))] := by
  simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_univ]
  rw [lintegral_congr_ae (ae_evalDist_of_forall_mem_support _ fun b hb =>
      resumed_guess_success guess secret b hb), guess_match_integral, lintegral_const,
    OracleComp.evalDist_apply_univ_eq_one, mul_one]

-- RuntimeSoundness row 8 (`guess_bound`), restated: `OracleVerifier.append_soundness_runtime`,
-- with the premise from `guess_integrated`.
/-- The runtime composition theorem bounds the guess prover's success by `1/2`. -/
theorem guess_bound (guess : Bool) (secret : Nat) :
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret))}[
      Success result.output] ≤ 2⁻¹ := by
  have bound := OracleVerifier.append_soundness_runtime bitRuntime bitVerifier () falseData
    (guessProver guess secret) (fun _ => False) Success (fun _ => (2 : ℝ≥0∞)⁻¹)
    (guess_integrated guess secret)
  simpa only [not_false_eq_true, Set.ofPred_true, Measure.restrict_univ,
    lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one,
    prEvent_const_of_not _ not_false, zero_add] using bound

/-- The pointwise runtime form gives the same bound with the boundary-dependent error `1` on a
matching hidden bit and `0` otherwise. A uniform pointwise error of `1/2` would fail: the
boundaries with a matching hidden bit have mass `1/2` and resumed success one. -/
theorem guess_bound_ae (guess : Bool) (secret : Nat) :
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret))}[
      Success result.output] ≤ 2⁻¹ := by
  have bound := OracleVerifier.append_soundness_runtime_ae bitRuntime bitVerifier () falseData
    (guessProver guess secret) (fun _ => False) Success
    (fun b => if guess = b.state.1 then 1 else 0)
    (ae_evalDist_of_forall_mem_support _ fun b hb _ =>
      (resumed_guess_success guess secret b hb).le)
  simpa only [not_false_eq_true, Set.ofPred_true, Measure.restrict_univ,
    prEvent_const_of_not _ not_false, zero_add, guess_match_integral] using bound

/-- The uniform pointwise half-error premise fails for a fixed guess, so the hidden-bit example
needs the averaged form. -/
theorem guess_pointwise_half_fails (guess : Bool) (secret : Nat) :
    ¬ ∀ᵐ b ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))],
      Pr{let result ← bitRuntime.resume b (bitVerifier.suffixRun () falseData)}[
        Success result.output] ≤ 2⁻¹ := by
  intro half
  have mismatch : ∀ᵐ b ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))],
      ¬ guess = b.state.1 := by
    filter_upwards [half, ae_evalDist_of_forall_mem_support _ fun b hb =>
      resumed_guess_success guess secret b hb] with b hhalf hsuccess hmatch
    rw [hsuccess] at hhalf
    norm_num [hmatch] at hhalf
  rw [MeasureTheory.ae_iff] at mismatch
  simp only [not_not] at mismatch
  rw [← prEvent_eq_evalDist_of_discrete, guess_match_probability] at mismatch
  norm_num at mismatch

-- RuntimeSoundness row 20 (informed runtime run), restated as row 17, with the passive order.
example (secret : Nat) :
    (fun result => (result.state, result.trace)) <$>
      bitRuntime.run (bitVerifier.run () falseData (informedProver secret)) =
    (fun hidden => ((hidden, 3), ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩,
      ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] : QueryLog bitFull))) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) :=
  run_history _ _ (fun hidden => informed_final_history hidden secret)

/-- The runtime with a fixed hidden bit; only setup changes, never the prover. -/
abbrev fixedRuntime (hidden : Bool) : OracleRuntime coinSpec bitFull :=
  { bitRuntime with setup := pure (hidden, 0) }

-- RuntimeSoundness row 21 (`fixed_guess_success`), restated.
/-- At a fixed hidden bit, a fixed guess succeeds surely or never. -/
theorem fixed_guess_success (guess hidden : Bool) (secret : Nat) :
    Pr{let result ← ((fixedRuntime hidden).run
      (bitVerifier.run () falseData (guessProver guess secret)))}[Success result.output] =
      if guess = hidden then 1 else 0 := by
  rw [OracleRuntime.run_eq]
  simp only [fixedRuntime, pure_bind]
  have observed := (fixedRuntime hidden).runFrom_observe (hidden, 0)
    (bitVerifier.run () falseData (guessProver guess secret))
  have sameState := congrArg (fun program => Pr{let result ← program}[Success result.1]) observed
  simp only [prEvent_map] at sameState
  rw [sameState]
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{let pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
    (guess_answers guess hidden secret)
  simp only [prEvent_map] at mass
  calc
    _ = Pr{let pair ←
        (pure (some (guess, hidden)) : OracleComp coinSpec (Option (Bool × Bool)))}[
        pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True] := by
      simp only [Answer, Option.map_map, Function.comp_def] at mass
      convert mass using 1
      rfl
    _ = _ := by
      cases guess <;> cases hidden <;> simp

-- RuntimeSoundness row 22 (`fixed_hidden_half_fails`), restated.
/-- A matching fixed hidden bit gives success one, so a fixed-state half bound is invalid. -/
theorem fixed_hidden_half_fails (guess : Bool) (secret : Nat) :
    ¬ Pr{let result ← ((fixedRuntime guess).run
      (bitVerifier.run () falseData (guessProver guess secret)))}[Success result.output] ≤
        (2 : ℝ≥0∞)⁻¹ := by
  rw [fixed_guess_success]
  simp only [ite_true]
  norm_num

/-! ## Charged histories, costs and access -/

/-- The suffix decision at a path of the combined protocol, routed through the prefix export. -/
def routedSuffix (p : FreeM.Path bitCombined) (v : View bitCombined p) :=
  simulateQ ((OracleVerifier.suffixRoute bitPrefix () p v).withAmbient bitAmbient)
    (bitSuffix.decide () (FreeM.Path.split bitFirst (fun _ => bitSecond) p).2
      (View.split bitFirst (fun _ => bitSecond) p v).2).run

/-- The routed suffix decision reads the pad from the input, then reveals the bit. -/
theorem routedSuffix_eq (guess : Bool) (v : View bitCombined ⟨⟨⟩, guess, ⟨⟩⟩) :
    routedSuffix ⟨⟨⟩, guess, ⟨⟩⟩ v = (do
      let pad : Bool ← liftM
        ((bitAmbient + (pathBundle bits bitCombined ⟨⟨⟩, guess, ⟨⟩⟩).spec).query
          (.inr (.inl ⟨(), ()⟩)))
      let hidden : Bool ← liftM
        ((bitAmbient + (pathBundle bits bitCombined ⟨⟨⟩, guess, ⟨⟩⟩).spec).query (.inl true))
      pure (some (hidden ^^ pad))) := by
  rfl

/-- The decision bundle of the combined protocol at a path. -/
abbrev combinedBundle (p : FreeM.Path bitCombined) :=
  (pathBundle bits bitCombined p).spec

/-- Every bundle query costs 2. -/
def bundleQueryCost {I : Type} (spec : OracleSpec I) : CostModel spec Nat := ⟨fun _ => 2⟩

/-- A reveal costs 3, a dummy request 1, and a bundle query 2. -/
def rawCost {I : Type} (spec : OracleSpec I) : CostModel (bitAmbient + spec) Nat :=
  ⟨fun | .inl request => if request then 3 else 1 | .inr _ => 2⟩

/-- Ambient requests must be reveals; bundle queries are unrestricted. -/
def rawAllowed {I : Type} (spec : OracleSpec I) : (bitAmbient + spec).Domain → Prop
  | .inl request => request = true
  | .inr _ => True

/-- Each setup sample costs 1. -/
def importCost : CostModel coinSpec Nat := ⟨fun _ => 1⟩

/-- Each export query makes one input query, of cost 2. -/
theorem export_budget (p : FreeM.Path bitFirst) (v : View bitFirst p) (q) :
    WorstCaseCostBound ((bitPrefix.outputMap () p v).impl q) (bundleQueryCost _) 2 :=
  worstCaseCostBound_query _ (bundleQueryCost _)

/-- The routed suffix decision costs at most 5: the pad query 2 and the reveal 3. -/
theorem routed_suffix_budget (p : FreeM.Path bitCombined) (v : View bitCombined p) :
    WorstCaseCostBound (routedSuffix p v) (rawCost (combinedBundle p)) 5 := by
  rcases p with ⟨⟨⟩, guess, ⟨⟩⟩
  rw [routedSuffix_eq]
  exact WorstCaseCostBound.bind (A := 2) (B := 3) (worstCaseCostBound_query _ (rawCost _))
    (fun _ => WorstCaseCostBound.bind (A := 3) (B := 0) (worstCaseCostBound_query _ (rawCost _))
      (fun _ => (worstCaseCostBound_pure _ _ _).2 le_rfl))

/-- The routed suffix decision makes only reveal requests. -/
theorem routed_suffix_access (p : FreeM.Path bitCombined) (v : View bitCombined p) :
    AllQueriesSatisfy (routedSuffix p v) (rawAllowed (combinedBundle p)) := by
  rcases p with ⟨⟨⟩, guess, ⟨⟩⟩
  rw [routedSuffix_eq]
  apply allQueriesSatisfy_bind
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · intro _
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr rfl
    · exact fun _ => allQueriesSatisfy_pure _ _

/-- The guess run ends in state `(hidden, 2)` with ambient charge 4. -/
theorem actual_history (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
    (fun hidden => ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] :
        QueryLog bitFull), 4))
      <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  kernel_rfl

/-- The informed run ends in state `(hidden, 3)` with ambient charge 7. -/
theorem informed_actual_history (secret : Nat) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (informedProver secret)) =
    (fun hidden => ((hidden, 3),
      ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩, ⟨.inl false, false⟩,
        ⟨.inl true, hidden⟩] :
        QueryLog bitFull), 7)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  kernel_rfl

/-- The whole run samples the import once. -/
theorem import_budget (guess : Bool) (secret : Nat) :
    WorstCaseCostBound (bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)))
      importCost 1 := by
  apply (worstCaseCostBound_map_iff _
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) importCost 1).mp
  rw [actual_history]
  exact (worstCaseCostBound_map_iff _ _ importCost 1).mpr (worstCaseCostBound_query () importCost)

-- RuntimeQueryBounds row 12 (`native_split_history`), restated: the split at the prefix
-- interaction boundary, with both decisions after the suffix interaction.
/-- The split run has the same state, trace and charge as the run. -/
theorem split_history (prover : Prover oracleSig bitAmbient bitCombined (fun _ => Nat)) :
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData prover) =
    (fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (appendPrefixRun (s₂ := fun _ => bitSecond) prover >>=
        bitVerifier.suffixRun () falseData) := by
  rw [OracleVerifier.run_eq_bind]

/-- The prefix exports its input and its decision makes one dummy request. -/
theorem prefix_returns_export :
    (∀ p v, bitPrefix.outputMap () p v =
      OracleMap.fst _ _) ∧
    ∀ v, bitPrefix.decide () ⟨⟨⟩, ⟨⟩⟩ v = (do
      let _ ← liftM ((bitAmbient + firstBundle.spec).query (.inl false))
      pure () : OptionT (OracleComp (bitAmbient + firstBundle.spec)) Unit) :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

-- RuntimeQueryBounds row 16 (`fixed_native_resource_bounds`), restated: "for every boundary"
-- ranges over the paths and views of the combined protocol. The source-name and source-access
-- conjuncts are redundant: oracle family indices are the names, and bundle access is
-- fixed by the decision's type.
/-- The export identity, the export and routed-suffix costs, the ambient access of the routed
suffix, the import budget, the charged history and the `1/2` bound hold together. -/
theorem fixed_cost_bounds (guess : Bool) (secret : Nat) :
    ((∀ p v, bitPrefix.outputMap () p v =
      OracleMap.fst _ _) ∧
    ∀ v, bitPrefix.decide () ⟨⟨⟩, ⟨⟩⟩ v = (do
      let _ ← liftM ((bitAmbient + firstBundle.spec).query (.inl false))
      pure () : OptionT (OracleComp (bitAmbient + firstBundle.spec)) Unit)) ∧
    (∀ (p : FreeM.Path bitCombined) (v : View bitCombined p),
      (∀ q, WorstCaseCostBound ((bitPrefix.outputMap () (FreeM.Path.split bitFirst
        (fun _ => bitSecond) p).1 (View.split bitFirst (fun _ => bitSecond) p v).1).impl q)
        (bundleQueryCost _) 2) ∧
      AllQueriesSatisfy (routedSuffix p v) (rawAllowed (combinedBundle p)) ∧
      WorstCaseCostBound (routedSuffix p v) (rawCost (combinedBundle p)) 5) ∧
    WorstCaseCostBound (bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)))
      importCost 1 ∧
    ((fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret)) =
    (fun hidden => ((hidden, 2),
      ([⟨challengeEntry, ()⟩, ⟨.inl false, false⟩, ⟨.inl true, hidden⟩] :
        QueryLog bitFull), 4))
      <$> (coinSpec.query () : OracleComp coinSpec Bool)) ∧
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (guessProver guess secret))}[
      Success result.output] ≤ 2⁻¹ :=
  ⟨prefix_returns_export, fun p v => ⟨export_budget _ _, routed_suffix_access p v,
    routed_suffix_budget p v⟩, import_budget guess secret, actual_history guess secret,
    guess_bound guess secret⟩

-- RuntimeQueryBounds row 17 (`informed_cost_does_not_give_half`), restated: the trace order
-- follows the informed prover's seam-slot reveal, so the reveal now precedes the dummy request.
-- Charge 7 and success one are unchanged (see the port notes).
/-- The informed prover has ambient charge 7 and success one. -/
theorem informed_cost_does_not_give_half (secret : Nat) :
    ((fun result => (result.state, result.trace, bitCharge result.trace.fst)) <$>
      bitRuntime.run (bitVerifier.run () falseData (informedProver secret)) =
    (fun hidden => ((hidden, 3),
      ([⟨challengeEntry, ()⟩, ⟨.inl true, hidden⟩, ⟨.inl false, false⟩,
        ⟨.inl true, hidden⟩] :
        QueryLog bitFull), 7)) <$> (coinSpec.query () : OracleComp coinSpec Bool)) ∧
    Pr{let result ← bitRuntime.run (bitVerifier.run () falseData (informedProver secret))}[
      Success result.output] = 1 :=
  ⟨informed_actual_history secret, informed_success secret⟩

end

end Interaction.Core.RuntimeSoundnessTests

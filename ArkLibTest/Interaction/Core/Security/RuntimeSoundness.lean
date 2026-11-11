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
runtime history stay correlated in the boundary distribution. The runtime form of composition
soundness bounds the guessing prover's success by `1/2`; a prover that reveals the bit in the seam
slot succeeds surely, and the averaged half-error premise fails for it.

The last section gives the charged ambient histories, the cost and access bounds of the export and
the routed suffix decision, and the import budget of the same experiment.
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
abbrev Obs := Observation oracleSig bitCombined (fun _ => Nat) Claim

/-- A final claim is true when its output oracle answers its statement. -/
def TruthFinal (claim : Claim) : Prop := claim.2 () = claim.1
/-- The run returns a true final claim. -/
def Success (obs : Obs) : Prop := obs.2.2.map TruthFinal = some True
/-- The output oracle's answer and the claimed bit, if the run accepts. -/
def Answer (obs : Obs) : Option (Bool × Bool) := obs.2.2.map fun claim => (claim.2 (), claim.1)

/-- The append boundary of a hidden-bit run. -/
abbrev Boundary := RunBoundary oracleSig bitAmbient bitFirst (fun _ => bitSecond) (fun _ => Nat)

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

-- RuntimeSoundness row 7 (`guess_integrated`), restated.
/-- The averaged half-error premise holds for a fixed guess. -/
theorem guess_integrated (guess : Bool) (secret : Nat) :
    (∫⁻ b in {_b : RunResult bitRuntime Boundary | ¬ False},
      Pr{let result ← bitRuntime.resume b (bitVerifier.suffixRun () falseData)}[
        Success result.output]
        ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))]) ≤
    ∫⁻ _b in {_b : RunResult bitRuntime Boundary | ¬ False}, (2 : ℝ≥0∞)⁻¹
      ∂𝒟[bitRuntime.run (prefixRun (guessProver guess secret))] := by
  simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_univ]
  rw [← average_success, guess_success, lintegral_const,
    OracleComp.evalDist_apply_univ_eq_one, mul_one]

-- RuntimeSoundness row 8 (`guess_bound`), restated: `OracleVerifier.append_soundness_runtime`.
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
-- seam-slot reveal after the challenge.
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
-- both decisions.
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
example (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace)) <$>
      bitRuntime.run (appendPrefixRun (s₂ := fun _ => bitSecond) (guessProver guess secret)) =
    (fun hidden => ((hidden, 0), ([⟨challengeEntry, ()⟩] : QueryLog bitFull))) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) :=
  run_history _ _ (fun hidden => prefix_history guess hidden secret)

-- RuntimeSoundness row 20 (informed runtime run), restated as row 17.
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
      let pad : Bool ← liftM ((bitAmbient + (sumFamily bits (pathFamily bitCombined
        ⟨⟨⟩, guess, ⟨⟩⟩)).spec).query (.inr ⟨.inl (), ()⟩))
      let hidden : Bool ← liftM ((bitAmbient + (sumFamily bits (pathFamily bitCombined
        ⟨⟨⟩, guess, ⟨⟩⟩)).spec).query (.inl true))
      pure (some (hidden ^^ pad))) := by
  rfl

/-- The decision resources of the combined protocol at a path. -/
abbrev combinedResources (p : FreeM.Path bitCombined) :=
  (sumFamily bits (pathFamily bitCombined p)).spec

/-- Every resource query costs 2. -/
def resourceCost {I : Type} (spec : OracleSpec I) : CostModel spec Nat := ⟨fun _ => 2⟩

/-- A reveal costs 3, a dummy request 1, and a resource query 2. -/
def rawCost {I : Type} (spec : OracleSpec I) : CostModel (bitAmbient + spec) Nat :=
  ⟨fun | .inl request => if request then 3 else 1 | .inr _ => 2⟩

/-- Ambient requests must be reveals; resource queries are unrestricted. -/
def rawAllowed {I : Type} (spec : OracleSpec I) : (bitAmbient + spec).Domain → Prop
  | .inl request => request = true
  | .inr _ => True

/-- Each setup sample costs 1. -/
def importCost : CostModel coinSpec Nat := ⟨fun _ => 1⟩

/-- Each export query makes one input query, of cost 2. -/
theorem export_budget (p : FreeM.Path bitFirst) (v : View bitFirst p) (q) :
    WorstCaseCostBound ((bitPrefix.outputMap () p v).impl q) (resourceCost _) 2 :=
  worstCaseCostBound_query _ (resourceCost _)

/-- The routed suffix decision costs at most 5: the pad query 2 and the reveal 3. -/
theorem routed_suffix_budget (p : FreeM.Path bitCombined) (v : View bitCombined p) :
    WorstCaseCostBound (routedSuffix p v) (rawCost (combinedResources p)) 5 := by
  rcases p with ⟨⟨⟩, guess, ⟨⟩⟩
  rw [routedSuffix_eq]
  exact WorstCaseCostBound.bind (A := 2) (B := 3) (worstCaseCostBound_query _ (rawCost _))
    (fun _ => WorstCaseCostBound.bind (A := 3) (B := 0) (worstCaseCostBound_query _ (rawCost _))
      (fun _ => (worstCaseCostBound_pure _ _ _).2 le_rfl))

/-- The routed suffix decision makes only reveal requests. -/
theorem routed_suffix_access (p : FreeM.Path bitCombined) (v : View bitCombined p) :
    AllQueriesSatisfy (routedSuffix p v) (rawAllowed (combinedResources p)) := by
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
      OracleMap.embedding (sumFamily bits (pathFamily bitFirst p)) .inl) ∧
    ∀ v, bitPrefix.decide () ⟨⟨⟩, ⟨⟩⟩ v = (do
      let _ ← liftM ((bitAmbient + firstResources.spec).query (.inl false))
      pure () : OptionT (OracleComp (bitAmbient + firstResources.spec)) Unit) :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

-- RuntimeQueryBounds row 16 (`fixed_native_resource_bounds`), restated: "for every boundary"
-- ranges over the paths and views of the combined protocol. The source-name and source-access
-- conjuncts are redundant: oracle family indices are the names, and resource access is
-- fixed by the decision's type.
/-- The export identity, the export and routed-suffix costs, the ambient access of the routed
suffix, the import budget, the charged history and the `1/2` bound hold together. -/
theorem fixed_resource_bounds (guess : Bool) (secret : Nat) :
    ((∀ p v, bitPrefix.outputMap () p v =
      OracleMap.embedding (sumFamily bits (pathFamily bitFirst p)) .inl) ∧
    ∀ v, bitPrefix.decide () ⟨⟨⟩, ⟨⟩⟩ v = (do
      let _ ← liftM ((bitAmbient + firstResources.spec).query (.inl false))
      pure () : OptionT (OracleComp (bitAmbient + firstResources.spec)) Unit)) ∧
    (∀ (p : FreeM.Path bitCombined) (v : View bitCombined p),
      (∀ q, WorstCaseCostBound ((bitPrefix.outputMap () (FreeM.Path.split bitFirst
        (fun _ => bitSecond) p).1 (View.split bitFirst (fun _ => bitSecond) p v).1).impl q)
        (resourceCost _) 2) ∧
      AllQueriesSatisfy (routedSuffix p v) (rawAllowed (combinedResources p)) ∧
      WorstCaseCostBound (routedSuffix p v) (rawCost (combinedResources p)) 5) ∧
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
-- follows the informed prover's seam-slot reveal.
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

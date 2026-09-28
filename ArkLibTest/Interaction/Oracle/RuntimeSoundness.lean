/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.RuntimeSoundness
import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Guessing a hidden runtime bit

The source input is deterministic and independent of runtime state. A native prover commits to a
bit before the verifier reveals the hidden bit. The actual native prefix continuation and runtime
history remain correlated in the theorem's joint boundary distribution.
-/

namespace Interaction.Oracle.RuntimeSoundnessTest

open OracleComp OracleSpec MeasureTheory
open PFunctor.FreeM.Displayed (Decoration)
open scoped ENNReal

noncomputable section

/-- `false` requests a dummy response; `true` reveals the retained bit. -/
abbrev ambient : OracleSpec Bool := Bool →ₒ Bool
abbrev inputSpec : OracleSpec Unit := Unit →ₒ Bool

def inputImpl : QueryImpl inputSpec Id := fun _ => false

@[reducible]
def boolInterface : OracleInterface Bool where
  Query := Unit
  toOC.spec := Unit →ₒ Bool
  toOC.impl _ := read

abbrev family : OracleFamily Unit (fun _ => Bool) := ⟨fun _ => boolInterface⟩
abbrev firstProtocol : Protocol := .public .receiver Unit fun _ => .done
abbrev secondProtocol : Protocol := .public .sender Bool fun _ => .done
abbrev combined : Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun _ => secondProtocol.tree),
    Decoration.append firstProtocol.roles (fun _ => secondProtocol.roles),
    Decoration.append firstProtocol.oracles (fun _ => secondProtocol.oracles)⟩

/-- The exported capability queries only the total deterministic input source. -/
def exported : VirtualOracle inputSpec family := ⟨fun _ => liftM (inputSpec.query ())⟩

/-- Reception returns an actual exported capability, without consulting runtime state. -/
def firstVerifier : Verifier.Fragment ambient firstProtocol.tree firstProtocol.roles
    firstProtocol.oracles inputSpec.toPFunctor
    (fun p => OpenClaim
      (ofPFunctor (firstProtocol.tree.accessAfter firstProtocol.oracles inputSpec.toPFunctor p))
      Unit family) := by
  change OracleComp (ambient + inputSpec) ((_move : Unit) × OpenClaim inputSpec Unit family)
  exact do
    let _ : Bool ← liftM ((ambient + inputSpec).query (.inl false))
    return ⟨(), ⟨(), exported⟩⟩

/-- The guess is received before the source query and hidden-bit revelation. -/
def secondVerifier (_ : firstProtocol.tree.BranchPath) (_ : Unit) :
    Verifier.Strategy ambient secondProtocol.tree secondProtocol.roles secondProtocol.oracles
      family.spec.toPFunctor
      (fun p => Option (OpenClaim
        (ofPFunctor
          (secondProtocol.tree.accessAfter secondProtocol.oracles family.spec.toPFunctor p))
        Bool family)) := by
  change Bool → OracleComp (ambient + family.spec)
    (OracleComp (ambient + family.spec) (Option (OpenClaim family.spec Bool family)))
  exact fun guess => pure (do
    let pad : Bool ← liftM ((ambient + family.spec).query (.inr ⟨(), ()⟩))
    let hidden : Bool ← liftM ((ambient + family.spec).query (.inl true))
    return some ⟨hidden ^^ pad, ⟨fun _ => pure (guess ^^ pad)⟩⟩)

/-- Both the final statement and actual output-oracle answer are retained. -/
def verifier : Verifier.Strategy ambient combined.tree combined.roles combined.oracles
    inputSpec.toPFunctor
    (TerminalClaim combined inputSpec.toPFunctor (fun _ => Bool) (fun _ => family)) :=
  Verifier.appendExported ambient firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor
    (fun _ => Unit) (fun _ _ => Bool) (fun _ => family)
    (fun _ => Bool) (fun _ _ => Bool) (fun _ => family) firstVerifier secondVerifier

/-- A fixed whole prover commits its guess after the prefix message. The verifier's dummy query
reveals nothing. -/
def prover (guess : Bool) (secret : Nat) :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat) :=
  fun _ => pure (pure ⟨guess, secret⟩)

/-- The contrasting prover learns the bit through an allowed query before choosing its guess. -/
def informedProver (secret : Nat) :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat) := fun _ => do
  let hidden : Bool ← liftM (ambient.query true)
  return pure ⟨hidden, secret⟩

/-- Hidden state is initialized once; neither prover is given it as an authoring argument. -/
abbrev runtime : OracleRuntime coinSpec ambient where
  State := Bool × Nat
  setup := do
    let hidden : Bool ← liftM (coinSpec.query ())
    return (hidden, 0)
  handler := fun request state => pure (if request then state.1 else false, (state.1, state.2 + 1))

/-- Equality compares the final observable oracle answer with the verifier's target bit. -/
abbrev TruthFinal (_ : combined.tree.BranchPath) (claim : ClosedClaim Bool family) : Prop :=
  claim.oracles ⟨(), ()⟩ = claim.stmt

abbrev Boundary := ExportedBoundary ambient firstProtocol.tree (fun _ => secondProtocol.tree)
  (fun _ => secondProtocol.roles) firstProtocol.oracles inputSpec.toPFunctor
  (fun _ => Unit) (fun _ _ => Bool) (fun _ => family) (fun _ => Nat)

abbrev prefixProgram
    (native : Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat)) :=
  exportedPrefixRun ambient firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles inputSpec.toPFunctor inputImpl
    (fun _ => Unit) (fun _ _ => Bool) (fun _ => family) (fun _ => Nat) native firstVerifier

abbrev nextProgram (b : Boundary) :=
  (fun result => (⟨PFunctor.FreeM.Path.append firstProtocol.tree (fun _ => secondProtocol.tree)
    (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1, result.2⟩ :
    (_branch : combined.tree.BranchPath) × Option (ClosedClaim Bool family))) <$>
    exportedSuffixRun ambient firstProtocol.tree (fun _ => secondProtocol.tree)
      (fun _ => secondProtocol.roles) firstProtocol.oracles (fun _ => secondProtocol.oracles)
      inputSpec.toPFunctor inputImpl (fun _ => Unit) (fun _ _ => Bool) (fun _ => family)
      (fun _ => Bool) (fun _ _ => Bool) (fun _ => family) (fun _ => Nat) secondVerifier b

def Success (result : (_branch : combined.tree.BranchPath) × Option (ClosedClaim Bool family)) :
    Prop := result.2.map (TruthFinal result.1) = some True

abbrev Answer (result :
    (_branch : combined.tree.BranchPath) × Option (ClosedClaim Bool family)) :=
  result.2.map fun claim => ((claim.oracles ⟨(), ()⟩ : Bool), claim.stmt)

lemma native_success_eq_split (native :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat))
    (world : OracleRuntime coinSpec ambient) :
    Pr{result ← (executeStrategiesWithRuntime world inputImpl native verifier)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] =
    Pr{result ← (world.run (prefixProgram native >>= nextProgram))}[Success result.output] := by
  have same := executeStrategiesWithRuntime_appendExported_prEvent ambient
    firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor inputImpl
    (fun _ => Unit) (fun _ _ => Bool) (fun _ => family)
    (fun _ => Bool) (fun _ _ => Bool) (fun _ => family) (fun _ => Nat)
    native firstVerifier secondVerifier world TruthFinal
  simp only [verifier]
  rw [same]
  delta nextProgram
  simp only [prefixProgram, Success, map_eq_pure_bind]

lemma guess_answers (guess hidden : Bool) (secret : Nat) :
    (fun result => Answer result.1.1) <$>
      runtime.handler.runState (hidden, 0)
        (prefixProgram (prover guess secret) >>= nextProgram).withQueryLog =
    pure (some (guess, hidden)) := by
  generalize execution : runtime.handler.runState (hidden, 0)
    (prefixProgram (prover guess secret) >>= nextProgram).withQueryLog = observed
  conv at execution => lhs; whnf
  subst execution
  cases guess <;> cases hidden <;> rfl

lemma runFrom_guess_answers (guess hidden : Bool) (secret : Nat) :
    (fun result => Answer result.output) <$>
      runtime.runFrom (hidden, 0) (prefixProgram (prover guess secret) >>= nextProgram) =
    pure (some (guess, hidden)) := by
  have observed := congrArg (fun program => (fun result => Answer result.1) <$> program)
    (runtime.runFrom_observe (hidden, 0) (prefixProgram (prover guess secret) >>= nextProgram))
  calc
    _ = _ := by simpa only [Functor.map_map] using observed
    _ = _ := guess_answers guess hidden secret

lemma run_guess_answers (guess : Bool) (secret : Nat) :
    (fun result => Answer result.output) <$>
      runtime.run (prefixProgram (prover guess secret) >>= nextProgram) =
    (fun hidden => some (guess, hidden)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  rw [OracleRuntime.run_eq, map_bind]
  simp only [runtime, bind_assoc, pure_bind]
  simp_rw [runFrom_guess_answers]
  rfl

lemma guess_success (guess : Bool) (secret : Nat) :
    Pr{result ← (executeStrategiesWithRuntime runtime inputImpl
      (prover guess secret) verifier)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] =
    (2 : ENNReal)⁻¹ := by
  rw [native_success_eq_split]
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
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
    rw [event, OracleSpec.IsUniformMeasureSpec.toMeasure_singleton]
    rfl

local instance : MeasurableSpace (RunResult runtime Boundary) := ⊤

lemma average_success (native :
    Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat)) :
    Pr{result ← (executeStrategiesWithRuntime runtime inputImpl native verifier)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] =
    ∫⁻ b, Pr{result ← runtime.resume b nextProgram}[Success result.output]
      ∂𝒟[runtime.run (prefixProgram native)] := by
  rw [native_success_eq_split, runtime.run_bind, prEvent_bind_eq_lintegral_of_discrete]

/-- The averaged premise holds although a matching fixed hidden bit gives conditional success
one. -/
lemma guess_integrated (guess : Bool) (secret : Nat) :
    (∫⁻ b in {_b : RunResult runtime Boundary | ¬ False},
      Pr{result ← runtime.resume b nextProgram}[Success result.output]
        ∂𝒟[runtime.run (prefixProgram (prover guess secret))]) ≤
    ∫⁻ _b in {_b : RunResult runtime Boundary | ¬ False},
      (2 : ENNReal)⁻¹ ∂𝒟[runtime.run (prefixProgram (prover guess secret))] := by
  simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_univ]
  rw [← average_success, guess_success, lintegral_const,
    OracleComp.evalDist_apply_univ_eq_one, mul_one]

/-- Apply the main native theorem to the actual exported continuation, with no exceptional event. -/
lemma guess_bound (guess : Bool) (secret : Nat) :
    Pr{result ← (executeStrategiesWithRuntime runtime inputImpl
      (prover guess secret) verifier)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] ≤
    (2 : ENNReal)⁻¹ := by
  have bound := executeStrategiesWithRuntime_appendExported_soundness ambient
    firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor inputImpl
    (fun _ => Unit) (fun _ _ => Bool) (fun _ => family)
    (fun _ => Bool) (fun _ _ => Bool) (fun _ => family) (fun _ => Nat)
    (prover guess secret) firstVerifier secondVerifier runtime (fun _ => False) TruthFinal
    (fun _ => (2 : ENNReal)⁻¹)
  dsimp only at bound
  have premise := guess_integrated guess secret
  simp only [prefixProgram, Success] at premise
  have result := bound premise
  simpa only [verifier, not_false_eq_true, Set.ofPred_true, Measure.restrict_univ,
    lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one,
    prEvent_const_of_not _ not_false, zero_add] using result


lemma informed_answers (hidden : Bool) (secret : Nat) :
    (fun result => Answer result.1.1) <$>
      runtime.handler.runState (hidden, 0)
        (prefixProgram (informedProver secret) >>= nextProgram).withQueryLog =
    pure (some (hidden, hidden)) := by
  generalize execution : runtime.handler.runState (hidden, 0)
    (prefixProgram (informedProver secret) >>= nextProgram).withQueryLog = observed
  conv at execution => lhs; whnf
  subst execution
  cases hidden <;> rfl

lemma runFrom_informed_answers (hidden : Bool) (secret : Nat) :
    (fun result => Answer result.output) <$>
      runtime.runFrom (hidden, 0) (prefixProgram (informedProver secret) >>= nextProgram) =
    pure (some (hidden, hidden)) := by
  have observed := congrArg (fun program => (fun result => Answer result.1) <$> program)
    (runtime.runFrom_observe (hidden, 0)
      (prefixProgram (informedProver secret) >>= nextProgram))
  calc
    _ = _ := by simpa only [Functor.map_map] using observed
    _ = _ := informed_answers hidden secret

lemma run_informed_answers (secret : Nat) :
    (fun result => Answer result.output) <$>
      runtime.run (prefixProgram (informedProver secret) >>= nextProgram) =
    (fun hidden => some (hidden, hidden)) <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  rw [OracleRuntime.run_eq, map_bind]
  simp only [runtime, bind_assoc, pure_bind]
  simp_rw [runFrom_informed_answers]
  rfl

/-- A fixed whole native prover can learn through an oracle query before its commitment. -/
lemma informed_success (secret : Nat) :
    Pr{result ← (executeStrategiesWithRuntime runtime inputImpl
      (informedProver secret) verifier)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] =
    1 := by
  rw [native_success_eq_split]
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{pair ← program}[pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True])
    (run_informed_answers secret)
  simp only [prEvent_map, Answer, Option.map_map, Function.comp_def] at mass
  convert mass.trans ?_ using 1
  · rfl
  · simp only [Option.map_some, eq_self, prEvent_true_eq_evalDist_apply_univ,
      OracleComp.evalDist_apply_univ_eq_one]

/-- The averaged half-error premise fails for reveal-before-commit; no runtime-security transfer
can erase this correlation. -/
lemma informed_half_premise_fails (secret : Nat) :
    ¬ ((∫⁻ b in {_b : RunResult runtime Boundary | ¬ False},
      Pr{result ← runtime.resume b nextProgram}[Success result.output]
        ∂𝒟[runtime.run (prefixProgram (informedProver secret))]) ≤
    ∫⁻ _b in {_b : RunResult runtime Boundary | ¬ False},
      (2 : ENNReal)⁻¹ ∂𝒟[runtime.run (prefixProgram (informedProver secret))]) := by
  simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_univ]
  rw [← average_success, informed_success, lintegral_const,
    OracleComp.evalDist_apply_univ_eq_one, mul_one]
  norm_num

/-- The actual prefix runtime state and ordered answers remain in the joint boundary. -/
lemma prefix_history (guess hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      runtime.handler.runState (hidden, 0) (prefixProgram (prover guess secret)).withQueryLog =
    pure ((hidden, 1), ([⟨false, false⟩] : OracleSpec.QueryLog ambient)) := by
  generalize execution : runtime.handler.runState (hidden, 0)
    (prefixProgram (prover guess secret)).withQueryLog = observed
  conv at execution => lhs; whnf
  subst execution
  cases guess <;> cases hidden <;> rfl

lemma informed_prefix_history (hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      runtime.handler.runState (hidden, 0) (prefixProgram (informedProver secret)).withQueryLog =
    pure ((hidden, 2), ([⟨false, false⟩, ⟨true, hidden⟩] :
      OracleSpec.QueryLog ambient)) := by
  generalize execution : runtime.handler.runState (hidden, 0)
    (prefixProgram (informedProver secret)).withQueryLog = observed
  conv at execution => lhs; whnf
  subst execution
  cases hidden <;> rfl

lemma final_history (guess hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      runtime.handler.runState (hidden, 0)
        (prefixProgram (prover guess secret) >>= nextProgram).withQueryLog =
    pure ((hidden, 2), ([⟨false, false⟩, ⟨true, hidden⟩] :
      OracleSpec.QueryLog ambient)) := by
  generalize execution : runtime.handler.runState (hidden, 0)
    (prefixProgram (prover guess secret) >>= nextProgram).withQueryLog = observed
  conv at execution => lhs; whnf
  subst execution
  cases guess <;> cases hidden <;> rfl

lemma informed_final_history (hidden : Bool) (secret : Nat) :
    (fun result => (result.2, result.1.2)) <$>
      runtime.handler.runState (hidden, 0)
        (prefixProgram (informedProver secret) >>= nextProgram).withQueryLog =
    pure ((hidden, 3), ([⟨false, false⟩, ⟨true, hidden⟩, ⟨true, hidden⟩] :
      OracleSpec.QueryLog ambient)) := by
  generalize execution : runtime.handler.runState (hidden, 0)
    (prefixProgram (informedProver secret) >>= nextProgram).withQueryLog = observed
  conv at execution => lhs; whnf
  subst execution
  cases hidden <;> rfl

/-- Lift handler observations through actual initialization, without authoring from hidden state. -/
lemma run_history {A : Type} (program : OracleComp ambient A)
    (history : Bool → (Bool × Nat) × OracleSpec.QueryLog ambient)
    (observed : ∀ hidden, (fun result => (result.2, result.1.2)) <$>
      runtime.handler.runState (hidden, 0) program.withQueryLog = pure (history hidden)) :
    (fun result => (result.state, result.trace)) <$> runtime.run program =
    history <$> (coinSpec.query () : OracleComp coinSpec Bool) := by
  have fromState hidden : (fun result => (result.state, result.trace)) <$>
      runtime.runFrom (hidden, 0) program = pure (history hidden) := by
    have same := congrArg (fun program => (fun result => (result.2.1, result.2.2)) <$> program)
      (runtime.runFrom_observe (hidden, 0) program)
    calc
      _ = _ := by simpa only [Functor.map_map] using same
      _ = _ := observed hidden
  rw [OracleRuntime.run_eq, map_bind]
  simp only [runtime, bind_assoc, pure_bind]
  simp_rw [fromState]
  rfl

example (guess : Bool) (secret : Nat) :
    (fun result => (result.state, result.trace)) <$>
      runtime.run (prefixProgram (prover guess secret)) =
    (fun hidden => ((hidden, 1),
      ([⟨false, false⟩] : OracleSpec.QueryLog ambient))) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) :=
  run_history _ _ (fun hidden => prefix_history guess hidden secret)

example (secret : Nat) :
    (fun result => (result.state, result.trace)) <$>
      runtime.run (prefixProgram (informedProver secret) >>= nextProgram) =
    (fun hidden => ((hidden, 3),
      ([⟨false, false⟩, ⟨true, hidden⟩, ⟨true, hidden⟩] : OracleSpec.QueryLog ambient))) <$>
      (coinSpec.query () : OracleComp coinSpec Bool) :=
  run_history _ _ (fun hidden => informed_final_history hidden secret)

/-- This analytic fixed-state experiment changes only initialization, never the native prover. -/
private abbrev fixedRuntime (hidden : Bool) : OracleRuntime coinSpec ambient :=
  { runtime with setup := pure (hidden, 0) }

/-- At a fixed hidden state, one of the two fixed guesses succeeds surely. All probabilities are
under the base import semantics; this is not a lawful fixed-state `StateT` distribution. -/
lemma fixed_guess_success (guess hidden : Bool) (secret : Nat) :
    Pr{result ← (executeStrategiesWithRuntime (fixedRuntime hidden)
      inputImpl (prover guess secret) verifier)}[
        result.output.core.closed.map
          (TruthFinal result.output.core.path.toBranchPath) = some True] =
      if guess = hidden then 1 else 0 := by
  rw [native_success_eq_split]
  rw [OracleRuntime.run_eq]
  simp only [fixedRuntime, pure_bind]
  have observed := (fixedRuntime hidden).runFrom_observe (hidden, 0)
    (prefixProgram (prover guess secret) >>= nextProgram)
  have sameState := congrArg (fun program => Pr{result ← program}[Success result.1]) observed
  simp only [prEvent_map] at sameState
  rw [sameState]
  let answer := fun result :
      (_branch : combined.tree.BranchPath) × Option (ClosedClaim Bool family) =>
    result.2.map fun claim => ((claim.oracles ⟨(), ()⟩ : Bool), claim.stmt)
  have computed : (fun result => answer result.1.1) <$>
      runtime.handler.runState (hidden, 0)
        (prefixProgram (prover guess secret) >>= nextProgram).withQueryLog =
      pure (some (guess, hidden)) := by
    generalize execution : runtime.handler.runState (hidden, 0)
      (prefixProgram (prover guess secret) >>= nextProgram).withQueryLog = observed
    conv at execution => lhs; whnf
    subst execution
    cases guess <;> cases hidden <;> rfl
  have mass := congrArg (fun program : OracleComp coinSpec (Option (Bool × Bool)) =>
    Pr{pair ← program}[
    pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True]) computed
  simp only [prEvent_map] at mass
  calc
    _ = Pr{pair ← (pure (some (guess, hidden)) : OracleComp coinSpec (Option (Bool × Bool)))}[
        pair.map (fun pair : Bool × Bool => pair.1 = pair.2) = some True] := by
      simp only [answer, Option.map_map, Function.comp_def] at mass
      convert mass using 1
      rfl
    _ = _ := by
      cases guess <;> cases hidden <;> simp

/-- An analytic matching hidden state has success one, so a fixed-state half bound is invalid. -/
lemma fixed_hidden_half_fails (guess : Bool) (secret : Nat) :
    ¬ Pr{result ← (executeStrategiesWithRuntime (fixedRuntime guess)
      inputImpl (prover guess secret) verifier)}[
        result.output.core.closed.map
          (TruthFinal result.output.core.path.toBranchPath) = some True] ≤ (2 : ENNReal)⁻¹ := by
  rw [fixed_guess_success]
  simp only [ite_true]
  norm_num

end

end Interaction.Oracle.RuntimeSoundnessTest

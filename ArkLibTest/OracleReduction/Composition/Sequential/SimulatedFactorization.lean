/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman, ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
import ArkLibTest.OracleReduction.Composition.Sequential.RawExecutionCounterexample

/-!
# Simulated factorization beyond the structural seam condition

The raw-order counterexample from Richard Goodman's PR #643 also gives a positive test for the
factorization interface from his PR #635. Implementing its ambient query by a pure response erases
that effect, so the simulated programs agree although the raw programs differ. The factorization
completeness theorem applies without a pure left output or message-opening right protocol.
-/

namespace ArkLib.AppendRunNecessity
open OracleComp OracleSpec ProtocolSpec

local instance : ∀ i, SampleableType (pS1.Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i
local instance : ∀ i, SampleableType (pS2.Challenge i) := fun ⟨⟨0, _⟩, _⟩ =>
  inferInstanceAs (SampleableType Bool)
local instance : ∀ i, SampleableType ((pS1 ++ₚ pS2).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := pS1) (pSpec₂ := pS2)

local instance : VerifierOnly pS2 := { verifier_first' := rfl }
local instance : VerifierOnly (pS1 ++ₚ pS2) := { verifier_first' := rfl }

/-- The ambient query has no simulated effect and always returns `false`. -/
def pureImpl : QueryImpl oS (StateT Unit ProbComp) := fun _ => pure false

/-- The raw counterexample factors after this ambient simulation, including its full result. -/
theorem simulated_factorization :
    simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := pS1 ++ₚ pS2)) :
      QueryImpl _ (StateT Unit ProbComp)) ((P1.append P2).run () ()) = (do
        let r₁ ← simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := pS1)) :
          QueryImpl _ (StateT Unit ProbComp)) (P1.run () ())
        let r₂ ← simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := pS2)) :
          QueryImpl _ (StateT Unit ProbComp)) (P2.run r₁.2.1 r₁.2.2)
        pure (r₁.1 ++ₜ r₂.1, r₂.2)) := by
  simp only [Prover.run_of_verifier_first]
  dsimp only [Prover.append, P1, P2]
  simp only [Prover.run, Prover.runToRound,pure_bind,
    liftM_pure, liftComp_eq_liftM, liftM_bind, bind_assoc]
  simp only [Fin.val_zero, Nat.not_lt_zero, dite_false, dite_true,
    Nat.reduceEqDiff, eq_mpr_eq_cast, cast_eq, Fin.reduceLast, Fin.induction, Fin.induction.go,
      liftM_pure, pure_bind]
  dsimp only [id]
  simp only [pure_bind, bind_assoc, simulateQ_bind, simulateQ_pure]
  simp only [QueryImpl.addLift_def, PFunctor.Handler.liftTarget_self,
    QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_add_liftM_right]
  simp only [HasQuery.instOfMonadLift_query, getChallenge,
    simulateQ_spec_query, pureImpl]
  change (do
    let c ← (liftM ($ᵗ Bool) : StateT Unit ProbComp Bool)
    let _ ← simulateQ (pureImpl.addLift (challengeQueryImpl (pSpec := pS1 ++ₚ pS2)) :
      QueryImpl _ (StateT Unit ProbComp))
      (liftM (do let _ ← (query (spec := oS) () : OracleComp oS Bool)
                 pure (fun _ : Bool => ())) : OracleComp _ (Bool → Unit))
    pure ((show (pS1 ++ₚ pS2).FullTranscript from fun ⟨0, _⟩ => c), (), ())) =
      (do
        let _ ← (pure false : StateT Unit ProbComp Bool)
        let c ← (liftM ($ᵗ Bool) : StateT Unit ProbComp Bool)
        pure (FullTranscript.append (pSpec₁ := pS1) (pSpec₂ := pS2)
          default (fun i => match i with | ⟨0, _⟩ => c), (), ()))
  simp only [QueryImpl.addLift_def, PFunctor.Handler.liftTarget_self,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_bind, simulateQ_pure,
    HasQuery.instOfMonadLift_query, simulateQ_spec_query, pureImpl, pure_bind]
  congr 1
  funext c
  change (pure ((show (pS1 ++ₚ pS2).FullTranscript from fun ⟨0, _⟩ => c), (), ()) :
    StateT Unit ProbComp _) = pure
      (FullTranscript.append (pSpec₁ := pS1) (pSpec₂ := pS2)
        default (fun i => match i with | ⟨0, _⟩ => c), (), ())
  congr 1
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

/-- Pure verification of the effectful-output first prover. -/
def R1 : Reduction oS Unit Unit Unit Unit pS1 := ⟨P1, ⟨fun _ _ => pure ()⟩⟩
/-- Pure verification of the challenge-opening second prover. -/
def R2 : Reduction oS Unit Unit Unit Unit pS2 := ⟨P2, ⟨fun _ _ => pure ()⟩⟩
/-- Deterministic verifier data for the first stage. -/
def V1 : R1.verifier.PureForm := ⟨fun _ _ => (), fun _ _ => rfl⟩
/-- Deterministic verifier data for the second stage. -/
def V2 : R2.verifier.PureForm := ⟨fun _ _ => (), fun _ _ => rfl⟩

/-- The supplied program equality holds for every input and starting state. -/
theorem beyondSeam_factorization : P1.SimulatedAppendFactorization P2 pureImpl := by
  intro stmt wit s
  cases stmt
  cases wit
  exact congrArg (fun x => x.run s) simulated_factorization

/-- The first stage is perfectly complete from every initial-state distribution. -/
theorem first_complete (start : ProbComp Unit) :
    R1.perfectCompleteness start pureImpl Set.univ Set.univ := by
  rw [Reduction.perfectCompleteness, Reduction.completeness_iff_of_pure_verifier R1 V1]
  intro stmt wit h
  simp

/-- The second stage is perfectly complete from every initial-state distribution. -/
theorem second_complete (start : ProbComp Unit) :
    R2.perfectCompleteness start pureImpl Set.univ Set.univ := by
  rw [Reduction.perfectCompleteness, Reduction.completeness_iff_of_pure_verifier R2 V2]
  intro stmt wit h
  simp

/-- The factorization interface proves completeness outside the structural seam restriction. -/
theorem beyondSeam_complete (start : ProbComp Unit) :
    (R1.append R2).perfectCompleteness start pureImpl Set.univ Set.univ :=
  Reduction.append_perfectCompleteness_of_proverFactorization R1 R2 V1 V2
    beyondSeam_factorization (first_complete start) second_complete

/-- The handoff output issues an ambient query and cannot have a pure-output certificate. -/
theorem output_not_pure : ¬ P1.OutputIsPure := by
  rintro ⟨out, hout⟩
  have h := hout ()
  change PFunctor.FreeM.liftBind _ _ = PFunctor.FreeM.pure _ at h
  cases h

/-- Neither disjunct of the structural seam condition applies to this pair. -/
theorem seam_fails : ¬ (∀ hn : 0 < 1,
    P1.OutputIsPure ∨ pS2.dir ⟨0, hn⟩ = .P_to_V) := by
  intro h
  rcases h (by decide) with hp | hm
  · exact output_not_pure hp
  · cases hm
end ArkLib.AppendRunNecessity
/--
info: 'ArkLib.AppendRunNecessity.simulated_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.simulated_factorization

/--
info: 'ArkLib.AppendRunNecessity.beyondSeam_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.beyondSeam_factorization

/--
info: 'ArkLib.AppendRunNecessity.first_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.first_complete

/--
info: 'ArkLib.AppendRunNecessity.second_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.second_complete

/--
info: 'ArkLib.AppendRunNecessity.beyondSeam_complete' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.beyondSeam_complete

/--
info: 'ArkLib.AppendRunNecessity.output_not_pure' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.output_not_pure

/--
info: 'ArkLib.AppendRunNecessity.seam_fails' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.seam_fails

/--
info: 'Prover.simulatedAppendFactorization_of_seam' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Prover.simulatedAppendFactorization_of_seam

/--
info: 'Reduction.append_completeness_of_proverFactorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.append_completeness_of_proverFactorization

/--
info: 'Reduction.append_perfectCompleteness_of_proverFactorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.append_perfectCompleteness_of_proverFactorization

/--
info: 'Reduction.append_completeness_of_guarded_proverFactorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.append_completeness_of_guarded_proverFactorization

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.LiftContext

/-!
# Context lifting on a concrete reduction

The inner reduction checks that a natural number is even and passes it on. The outer reduction
carries a Boolean tag beside the number, which the lens passes through unchanged. Perfect
completeness and soundness with error `0` of the outer reduction come from the transfers.
-/

open PFunctor PFunctor.FreeM Interaction OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Interaction.LiftContextTests

abbrev zero : Protocol := .pure ⟨⟩

/-- Even numbers, with the trivial witness. -/
@[instance_reducible] def evenInput : StatementProblem ℕ where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ n _ := n % 2 = 0
  rel_admissible _ _ _ _ := trivial

/-- Tagged numbers whose number is even, with the trivial witness. -/
@[instance_reducible] def taggedInput : StatementProblem (ℕ × Bool) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ x _ := x.1 % 2 = 0
  rel_admissible _ _ _ _ := trivial

abbrev evenOutput : PathProblem zero (fun _ => ℕ) := evenInput.toPathProblem zero

abbrev taggedOutput : PathProblem zero (fun _ => ℕ × Bool) := taggedInput.toPathProblem zero

/-- Accept an even number and return it. -/
def evenVerifier : Verifier emptySpec zero ℕ (fun _ => ℕ) where
  decide n _ _ := if n % 2 = 0 then pure n else failure

/-- The honest prover returns its statement. -/
def evenReduction : Reduction emptySpec zero ℕ Unit (fun _ => ℕ) (fun _ => ℕ) where
  prover n _ := (pure n : OracleComp emptySpec ℕ)
  verifier := evenVerifier

/-- Keep the tag beside the number. -/
def tagLens : ContextLens plainSig zero (ℕ × Bool) ℕ Unit Unit (fun _ => ℕ × Bool) (fun _ => ℕ)
    (fun _ => ℕ × Bool) (fun _ => ℕ) where
  stmt := { proj := Prod.fst, lift x _ t := (t, x.2) }
  wit := { proj _ w := w, lift x _ _ o := (o, x.2) }

def taggedReduction : Reduction emptySpec zero (ℕ × Bool) Unit (fun _ => ℕ × Bool)
    (fun _ => ℕ × Bool) :=
  evenReduction.liftContext tagLens

def init : ProbComp Unit := pure ()

def impl : QueryImpl emptySpec (StateT Unit ProbComp) := fun q => q.elim

def challenges : QueryImpl (challengeSpec plainSig zero) ProbComp := fun c => c.val.elim

/-! ### The inner reduction -/

theorem evenReduction_runOutcome (n : ℕ) (w : Unit) (h : n % 2 = 0) :
    evenReduction.runOutcome n w =
      (pure ⟨⟨⟩, n, some n⟩ : OracleComp (emptySpec + challengeSpec plainSig zero) _) := by
  simp only [Reduction.runOutcome, Verifier.run, TwoParty.Lens.run, Prover.simulate, evenReduction,
    evenVerifier, simulateQ_pure, h, ↓reduceIte, OptionT.run_pure, liftComp_eq_liftM,
    _root_.liftM_pure, LawfulMonad.bind_pure_comp, LawfulApplicative.map_pure]
  erw [TwoParty.Lens.runWith_done]
  simp only [TwoParty.Lens.Schedule.seq, Displayed.pure_eq, sampler, samplerEnd,
    LawfulMonad.bind_pure_comp, LawfulMonad.pure_bind, Functor.map_map]
  rfl

theorem evenReduction_completeness :
    evenReduction.completeness init impl challenges evenInput evenOutput (fun _ o => o)
      (fun _ _ _ => ()) (fun _ w => w) 0 := by
  let : MeasurableSpace (Outcome plainSig zero (fun _ => ℕ) (fun _ => ℕ)) := ⊤
  refine ⟨MeasurableSpace.measurableSet_top, fun n w (h : n % 2 = 0) => ?_⟩
  change 1 - 0 ≤ 𝒟[experiment init impl challenges (evenReduction.runOutcome n w)] _
  rw [evenReduction_runOutcome n w h]
  rw [← prEvent_eq_evalDist_of_discrete, prEvent_eq_one_of_forall_mem_support]
  · simp
  · intro obs hobs
    have hobs := support_experiment_subset _ _ _ _ hobs
    simp only [support_pure, Set.mem_singleton_iff] at hobs
    subst hobs
    exact ⟨n, rfl, rfl, h⟩

theorem evenVerifier_soundness :
    evenVerifier.soundness init impl challenges evenInput evenOutput 0 := by
  rw [Verifier.soundness_iff_soundnessUsing]
  intro Out n _ hlang p
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun obs hobs => ?_)
  rintro ⟨t, ht, -⟩
  obtain ⟨v, hv⟩ :=
    evenVerifier.compatible_of_mem_support_run n p (support_experiment_subset _ _ _ _ hobs) ht
  have hodd : ¬ n % 2 = 0 := fun h => hlang ⟨(), h⟩
  simp [evenVerifier, hodd] at hv

/-! ### The lifted reduction, through the transfers -/

theorem tagLens_isSound :
    tagLens.stmt.IsSound taggedInput evenInput taggedOutput evenOutput evenVerifier.Compatible where
  proj_sound _ _ hlang := ⟨trivial, fun ⟨w, hw⟩ => hlang ⟨w, hw⟩⟩
  lift_sound _ _ _ _ _ _ := fun ⟨w, hw⟩ => ⟨w, hw⟩

theorem tagLens_isComplete :
    tagLens.IsComplete taggedInput evenInput (fun _ w => w) (fun _ w => w)
      (OutputJudgement.ofOutcome taggedOutput (fun _ o => o) (fun _ _ _ => ())).honest
      (OutputJudgement.ofOutcome evenOutput (fun _ o => o) (fun _ _ _ => ())).honest
      evenReduction.verifier.Compatible where
  proj_complete _ w h := ⟨w, h, rfl⟩
  lift_complete x _ _ _ o t _ := by
    rintro ⟨t', ht', ho, hrel⟩
    cases ht'
    exact ⟨(t, x.2), rfl, congrArg (·, x.2) ho, hrel⟩

/-- Perfect completeness of the lifted reduction, from the inner one. -/
theorem taggedReduction_completeness :
    taggedReduction.completeness init impl challenges taggedInput taggedOutput (fun _ o => o)
      (fun _ _ _ => ()) (fun _ w => w) 0 :=
  Reduction.liftContext_completeness tagLens evenReduction init impl challenges
    tagLens_isComplete evenReduction_completeness

/-- Soundness with error `0` of the lifted verifier, from the inner one. -/
theorem taggedVerifier_soundness :
    taggedReduction.verifier.soundness init impl challenges taggedInput taggedOutput 0 :=
  Verifier.liftContext_soundness tagLens.stmt evenVerifier init impl challenges tagLens_isSound
    evenVerifier_soundness

/-- The lifted run is the inner run with the tag attached. -/
example (n : ℕ) (b : Bool) (h : n % 2 = 0) :
    taggedReduction.runOutcome (n, b) () =
      (pure ⟨⟨⟩, (n, b), some (n, b)⟩ :
        OracleComp (emptySpec + challengeSpec plainSig zero) _) := by
  rw [taggedReduction, Reduction.liftContext_runOutcome]
  change _ <$> evenReduction.runOutcome n () = _
  rw [evenReduction_runOutcome n () h]
  rfl

end Interaction.LiftContextTests

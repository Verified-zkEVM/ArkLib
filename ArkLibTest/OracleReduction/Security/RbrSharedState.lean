/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.Security.ReachableImplications

/-!
# A shared-state obstruction to RBR-to-standard soundness

There are no protocol messages. The prover's output sets a shared bit; the verifier accepts
exactly when that bit is set. The fresh-initial-state terminal obligation sees `false`, whereas
the real execution sees `true`. No admitted implication is imported or used here.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace RbrSharedState

/-- The query parameter requests either setting or reading the shared bit. -/
abbrev spec : OracleSpec Bool := Bool →ₒ Bool

/-- Setting the bit returns its new value; reading leaves it unchanged. -/
def impl : QueryImpl spec (StateT Bool ProbComp) := fun setTrue => do
  if setTrue then set true
  get

/-- The attack happens in the prover output, even though the protocol has zero rounds. -/
def prover : Prover spec Unit Unit Unit Unit !p[] where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun _ => do
    let _ ← (query (spec := spec) true : OracleComp spec Bool)
    pure ((), ())

/-- Accept if and only if the shared bit has been set. -/
def verifier : Verifier spec Unit Unit !p[] where
  verify := fun _ _ => OptionT.mk do
    let bit ← (query (spec := spec) false : OracleComp spec Bool)
    pure (if bit then some () else none)

@[simp] private theorem run_lift {α : Type} {ι : Type} {o : OracleSpec ι}
    (comp : OracleComp spec α) :
    (liftM comp : OptionT (OracleComp (spec + o)) α).run =
      some <$> (liftM comp : OracleComp (spec + o) α) := by
  rw [← monadLift_liftM_OptionT]
  change (OptionT.lift (liftM comp : OracleComp (spec + o) α)).run = _
  rw [OptionT.run_lift]
  exact (map_eq_bind_pure_comp _ _ _).symm

@[simp] private theorem simulate_query {ι : Type} {o : OracleSpec ι}
    (other : QueryImpl o (StateT Bool ProbComp)) (bit : Bool) :
    simulateQ (impl + other)
      (liftM (liftM (spec.query bit) : OracleComp spec Bool) : OracleComp (spec + o) Bool) =
      impl bit := by
  rw [← liftComp_eq_liftM]
  simp only [liftComp_query, OracleQuery.cont_query, id_map]
  exact QueryImpl.simulateQ_add_liftM_query_left impl other bit

/-- Fresh initialization rejects every transcript, so the always-false state is valid. -/
def stateFunction : verifier.StateFunction (pure false) impl ∅ Set.univ where
  toFun := fun _ _ _ => False
  toFun_empty := by simp
  toFun_next := fun m => nomatch m
  toFun_full := by
    intro stmt tr _
    simp [↓OptionT.prEvent_mk, verifier, Verifier.run, OptionT.mk, impl]

/-- With no challenges, the RBR bounds are vacuous. -/
theorem rbr_soundness : verifier.rbrSoundness (pure false) impl ∅ Set.univ (fun _ => 0) := by
  refine ⟨stateFunction, ?_⟩
  intro stmt hstmt WitIn WitOut wit adv i
  exact Fin.elim0 i.1

/-- Even the extractor-aware RBR premises hold: the terminal check starts at `false`. -/
theorem rbr_knowledgeSoundness :
    verifier.rbrKnowledgeSoundness (pure false) impl
      (∅ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) (fun _ => 0) := by
  let extractor : Extractor.RoundByRound spec Unit Unit Unit !p[] (fun _ => Unit) :=
    { eqIn := rfl
      extractMid := fun m => nomatch m
      extractOut := fun _ _ _ => () }
  let kSF : verifier.KnowledgeStateFunction (pure false) impl ∅ Set.univ extractor :=
    { toFun := fun _ _ _ _ => False
      toFun_empty := by intros; simp
      toFun_next := fun m => nomatch m
      toFun_full := by
        intro stmt tr wit h
        have hz := stateFunction.toFun_full stmt tr (fun h => h)
        exact (ne_of_gt h) hz }
  refine ⟨fun _ => Unit, extractor, kSF, ?_⟩
  intro stmt wit adv i
  exact Fin.elim0 i.1

/-- The real game accepts with probability one, contradicting the claimed zero standard error. -/
theorem not_soundness : ¬ verifier.soundness (pure false) impl ∅ Set.univ 0 := by
  let : ∀ i, OracleInterface ((!p[]).Challenge i) := challengeOracleInterface
  intro h
  have hbad := h Unit Unit () prover () (by simp)
  have hexec : ((Reduction.mk prover verifier).run () ()).run = (do
      let _ ← liftComp (query (spec := spec) true : OracleComp spec Bool) _
      let bit ← liftComp (query (spec := spec) false : OracleComp spec Bool) _
      pure (if bit then some ((default, (), ()), ()) else none)) := by
    simp only [ChallengeIdx, Challenge, Reduction.run, Prover.run, Fin.reduceLast, prover,
      Nat.reduceAdd, Fin.isValue, MessageIdx, Message, HasQuery.instOfMonadLift_query, verifier,
      Prover.runToRound, Fin.induction_zero, bind_pure_comp, liftM_map, Functor.map_map, pure_bind,
      monadLift_liftM_OptionT, Verifier.run, OptionT.run_mk, bind_map_left, OptionT.run_bind,
      Option.elimM, run_lift, OptionT.run_map, Option.elim_some, liftComp_eq_liftM]
    simp only [map_eq_bind_pure_comp]
    apply bind_congr
    intro _
    apply bind_congr
    intro bit
    cases bit <;> rfl
  change Pr{let result ← (OptionT.mk
    ((simulateQ (impl.addLift challengeQueryImpl :
      QueryImpl (spec + [(!p[]).Challenge]ₒ) (StateT Bool ProbComp))
      ((Reduction.mk prover verifier).run () ()).run).run' false))}[result.2 ∈ Set.univ] ≤ 0
    at hbad
  rw [hexec] at hbad
  simp [↓OptionT.prEvent_mk, impl, QueryImpl.addLift_def] at hbad

/-- The reachable-state condition excludes the shared-bit attack. -/
theorem not_reachableOutputCompatible :
    ¬ verifier.ReachableOutputCompatible (pure false) impl := by
  intro h
  apply not_soundness
  simpa using Verifier.rbrSoundness_implies_soundness_of_compatible
    (pure false) impl ∅ Set.univ verifier h (fun _ => 0) rbr_soundness

end RbrSharedState

/-- info: 'RbrSharedState.rbr_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RbrSharedState.rbr_soundness

/-- info: 'RbrSharedState.not_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RbrSharedState.not_soundness

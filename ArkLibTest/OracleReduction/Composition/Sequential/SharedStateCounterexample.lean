/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Basic

/-!
# Why fixed-initial-state completeness does not compose

The first prover sets the shared Boolean state to `true` while sending its only message.
Its output and both verifiers are pure and return `false`. The second prover has no messages
and reads the shared state in its output. Starting separately at `false`, both reductions
are perfectly complete for the universal relations. Appending them leaves the shared state
at `true`, so the prover and verifier outputs disagree.

These proofs use only execution definitions, never an admitted composition theorem.
-/

open OracleComp OracleSpec ProtocolSpec

namespace AppendStateCounterexample

/-- A query either sets the shared bit or reads it. -/
abbrev spec : OracleSpec Bool := Bool →ₒ Bool

/-- One prover message and no challenges. -/
abbrev pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Unit]⟩

instance : ∀ i, SampleableType (pSpec.Challenge i) := fun ⟨0, h⟩ => nomatch h

instance : ∀ i, SampleableType ((pSpec ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := pSpec) (pSpec₂ := !p[])

/-- `true` sets the bit; both query forms return its current value. -/
def impl : QueryImpl spec (StateT Bool ProbComp) := fun setTrue => do
  if setTrue then set true
  get

/-- The first stage changes state while sending its message, then outputs `false`. -/
def first : Reduction spec Unit Unit Bool Unit pSpec where
  prover := {
    PrvState := fun _ => Unit
    input := fun _ => ()
    sendMessage := fun ⟨0, _⟩ _ => do
      let _ ← (query (spec := spec) true : OracleComp spec Bool)
      pure ((), ())
    receiveChallenge := fun ⟨0, h⟩ => nomatch h
    output := fun _ => pure (false, ()) }
  verifier := ⟨fun _ _ => pure false⟩

/-- The second prover reads the shared bit; its verifier always outputs `false`. -/
def second : Reduction spec Bool Unit Bool Unit !p[] where
  prover := {
    PrvState := fun _ => Unit
    input := fun _ => ()
    sendMessage := fun i => nomatch i
    receiveChallenge := fun i => nomatch i
    output := fun _ => do return (← (query (spec := spec) false : OracleComp spec Bool), ()) }
  verifier := ⟨fun _ _ => pure false⟩

instance : first.prover.OutputIsPure := ⟨_, fun _ => rfl⟩
instance : first.verifier.IsPure := ⟨_, fun _ _ => rfl⟩
instance : second.verifier.IsPure := ⟨_, fun _ _ => rfl⟩

@[simp] private theorem run_lift {α : Type} {ι : Type} {o : OracleSpec ι}
    (oa : OracleComp spec α) :
    (liftM oa : OptionT (OracleComp (spec + o)) α).run =
      some <$> (liftM oa : OracleComp (spec + o) α) := by
  rw [← monadLift_liftM_OptionT]
  change (OptionT.lift (liftM oa : OracleComp (spec + o) α)).run = _
  rw [OptionT.run_lift]
  exact (map_eq_bind_pure_comp _ _ _).symm

@[simp] private theorem simulate_query {ι : Type} {o : OracleSpec ι}
    (other : QueryImpl o (StateT Bool ProbComp)) (b : Bool) :
    simulateQ (impl + other)
      (liftM (liftM (spec.query b) : OracleComp spec Bool) : OracleComp (spec + o) Bool) =
      impl b := by
  rw [← liftComp_eq_liftM]
  simp only [liftComp_query, OracleQuery.cont_query, id_map]
  exact QueryImpl.simulateQ_add_liftM_query_left impl other b

/-- The first reduction is perfectly complete from the designated initial state. -/
theorem first_perfectCompleteness :
    first.perfectCompleteness (pure false) impl Set.univ Set.univ := by
  classical
  intro stmt wit h
  simp [first, Reduction.run, Prover.run, Prover.runToRound, Prover.processRound,
    Verifier.run, monadLift_liftM_OptionT, OptionT.probFailure_eq]

/-- The second reduction is perfectly complete when separately initialized at `false`. -/
theorem second_perfectCompleteness :
    second.perfectCompleteness (pure false) impl Set.univ Set.univ := by
  classical
  intro stmt wit h
  simp [second, Reduction.run, Prover.run, Prover.runToRound, Verifier.run, impl,
    monadLift_liftM_OptionT, OptionT.probFailure_eq]

/-- Fixed-initial-state component completeness does not imply appended completeness,
even with pure left prover output and pure verifiers. -/
theorem not_append_perfectCompleteness :
    ¬ (first.append second).perfectCompleteness (pure false) impl Set.univ Set.univ := by
  classical
  let : DecidableEq
      (Option (((pSpec ++ₚ !p[]).FullTranscript × Bool × Unit) × Bool) × Bool) :=
    Classical.typeDecidableEq _
  intro h
  have hbad := h () () (by trivial)
  dsimp only [Reduction.run, Reduction.append] at hbad
  -- Keep the concrete execution normalization explicit before inspecting its result.
  simp only [Nat.add_zero, ChallengeIdx, Fin.vcons_fin_zero, Nat.reduceAdd, Fin.vappend_zero,
    Challenge, QueryImpl.addLift_def, PFunctor.Handler.liftTarget_self, Prover.run,
    Fin.reduceLast, first, Fin.isValue, MessageIdx, Fin.vcons_of_one, Message,
    HasQuery.instOfMonadLift_query, second, Prover.append, Function.comp_apply, Fin.cast_eq_self,
    eq_mpr_eq_cast, Fin.val_eq_zero, Order.lt_one_iff, zero_add, Order.lt_two_iff, Std.le_refl,
    Fin.eta, zero_le, eq_mp_eq_cast, zero_ne_one, Fin.reduceFinMk, Fin.succ_mk, Fin.mk_one,
    Fin.castSucc_mk, ↓dreduceDIte, add_zero, Prover.runToRound, Fin.induction_one',
    Prover.processRound, Fin.castSucc_zero, Fin.succ_zero_eq_one, ↓reduceDIte, bind_pure_comp,
    cast_eq, pure_bind, liftM_map, Functor.map_map, bind_map_left, liftM_bind,
    monadLift_liftM_OptionT, Verifier.run, Verifier.append, map_pure, OptionT.run_pure,
    liftM_pure, Option.getM_some, map_bind, OptionT.run_bind, run_lift, OptionT.run_map,
    Option.map_some, Option.elimM_map, Option.elim_some, simulateQ_bind, simulateQ_map,
    simulate_query, impl, ↓reduceIte, StateT.run'_eq, StateT.run_bind,
    StateT.run_map, StateT.run_get, Set.mem_univ, true_and, ENNReal.coe_zero, tsub_zero,
    ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff', OptionT.probFailure_eq,
    OptionT.run_mk, probFailure_of_liftM_PMF, probOutput_eq_zero_iff', finSupport_map,
    Finset.mem_image, reduceCtorEq, and_false, exists_false, not_false_eq_true,
    OptionT.mem_finSupport_iff, Option.some.injEq, Prod.exists, Bool.exists_bool,
    forall_exists_index, Prod.forall, Prod.mk.injEq, Bool.false_eq, Bool.forall_bool, and_true,
    Bool.true_eq_false, or_self, IsEmpty.forall_iff, implies_true, Subsingleton.forall₂_iff,
    imp_false, not_or, not_and] at hbad
  simp only [Fin.isValue, Fin.append, Fin.addCases, Nat.add_zero, Fin.coe_ofNat_eq_mod,
    Nat.mod_succ, Order.lt_two_iff, Std.le_refl, ↓dreduceDIte, Fin.reduceCastLT,
    Fin.castAdd_zero, Fin.cast_eq_self, id_eq, liftM_map, simulateQ_map, simulate_query, impl,
    ↓reduceIte, LawfulMonadStateOf.set_bind_get, bind_pure_comp, Functor.map_map, StateT.run_map,
    StateT.run_set, map_pure, Subsingleton.forall₂_iff] at hbad
  let tr : (pSpec ++ₚ !p[]).FullTranscript := fun ⟨0, _⟩ => ()
  apply (hbad tr ()).2
  · change (((), ()), true) ∈
      finSupport (pure (((), ()), true) : ProbComp ((Unit × Unit) × Bool))
    simp
  · apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · rfl

end AppendStateCounterexample

/--
info: 'AppendStateCounterexample.first_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AppendStateCounterexample.first_perfectCompleteness

/--
info: 'AppendStateCounterexample.second_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AppendStateCounterexample.second_perfectCompleteness

/--
info: 'AppendStateCounterexample.not_append_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AppendStateCounterexample.not_append_perfectCompleteness

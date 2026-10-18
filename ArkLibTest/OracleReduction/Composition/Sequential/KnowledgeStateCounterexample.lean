/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Execution
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Fresh initialization does not justify shared-state knowledge composition

The examples below use a total Boolean-state oracle and empty message protocols.
They do not invoke any admitted security implication or composition contract.
-/

open OracleComp OracleSpec ProtocolSpec QueryImpl
open scoped NNReal

namespace KnowledgeStateCounterexample

/-- A request either sets the shared bit or reads it. -/
abbrev spec : OracleSpec Bool := Bool →ₒ Bool

/-- Total deterministic state interpretation. -/
def impl : QueryImpl spec (StateT Bool ProbComp) := fun write => do
  if write then set true
  get

/-- No communication. -/
abbrev wire : ProtocolSpec 0 := !p[]

local instance : ∀ i, OracleInterface (wire.Challenge i) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ i, SampleableType ((wire ++ₚ wire).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (pSpec₁ := wire) (pSpec₂ := wire)

/-- The first verifier changes the state, without producing a related intermediate output. -/
def first : Verifier spec Unit Unit wire := ⟨fun _ _ => OptionT.mk do
  let _ ← (query (spec := spec) true : OracleComp spec Bool)
  pure (some ())⟩

/-- The second verifier accepts exactly when the shared bit has been set. -/
def second : Verifier spec Unit Unit wire := ⟨fun _ _ => OptionT.mk do
  let flag ← (query (spec := spec) false : OracleComp spec Bool)
  pure (if flag then some () else none)⟩

/-- The only possible intermediate witness is trivial. -/
def extractor : Extractor.RoundByRound spec Unit Unit Unit wire (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ _ => ()

/-- The first component has no related output, so its knowledge state is always false. -/
def firstState : first.KnowledgeStateFunction (pure false) impl ∅ ∅ extractor where
  toFun := fun _ _ _ _ => False
  toFun_empty := by simp
  toFun_next := fun i => Fin.elim0 i
  toFun_full := by simp

/-- The first component satisfies the existing RBR definition with no error. -/
theorem first_secure : first.rbrKnowledgeSoundnessAveraged (pure false) impl
    (∅ : Set (Unit × Unit)) (∅ : Set (Unit × Unit)) 0 :=
  ⟨_, extractor, firstState, fun _ _ _ i => Fin.elim0 i.1⟩

/-- From the original initialization the second verifier rejects. -/
theorem second_fresh (stmt : Unit) (tr : wire.FullTranscript) :
    (simulateQ impl (second.run stmt tr)).run' false = pure none := by
    rfl

/-- Fresh-state terminal validity is vacuous for the second verifier. -/
def secondState : second.KnowledgeStateFunction (pure false) impl
    (∅ : Set (Unit × Unit)) Set.univ extractor where
  toFun := fun _ _ _ _ => False
  toFun_empty := by simp
  toFun_next := fun i => Fin.elim0 i
  toFun_full := by
    intro stmt tr wit h
    change Pr{let _ ← (OptionT.mk (pure none) : OptionT ProbComp Unit)}[True] > 0 at h
    simp at h

/-- The existing definition certifies the second component at zero error too. -/
theorem second_secure : second.rbrKnowledgeSoundnessAveraged (pure false) impl
    (∅ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) 0 :=
  ⟨_, extractor, secondState, fun _ _ _ i => Fin.elim0 i.1⟩

/-- Sequential verification carries the written bit into the second verifier. -/
theorem composed_accepts (stmt : Unit) (tr : (wire ++ₚ wire).FullTranscript) :
    (simulateQ impl ((first.append second).run stmt tr)).run' false = pure (some ()) := by
  rfl

/-- No knowledge-state certificate can explain this zero-message false-to-true reduction. -/
theorem composed_not_secure : ¬ (first.append second).rbrKnowledgeSoundnessAveraged
    (pure false) impl (∅ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) 0 := by
  rintro ⟨W, E, S, _⟩
  let tr : (wire ++ₚ wire).FullTranscript := fun i => Fin.elim0 i
  have hlast := S.toFun_full () tr () (by
    change Pr{let _ ← (pure () : OptionT ProbComp Unit)}[True] > 0
    simp)
  have htr : tr = (default : Transcript 0 (wire ++ₚ wire)) := by
    funext i
    exact Fin.elim0 i
  have hfirst := (S.toFun_empty () (E.extractOut () tr ())).mpr (by
    simpa only [Nat.reduceAdd, htr, Fin.reduceLast] using hlast)
  exact hfirst

/-- The same two components through the actual n-ary sequential constructor. -/
def sequence : Verifier spec Unit Unit (ProtocolSpec.seqCompose (fun _ : Fin 2 => wire)) :=
  Verifier.seqCompose (fun _ => Unit) (fun i : Fin 2 => if i = 0 then first else second)

local instance : ∀ i, SampleableType
    ((ProtocolSpec.seqCompose (fun _ : Fin 2 => wire)).Challenge i) :=
  fun i => Fin.elim0 i.1

/-- N-ary composition also retains the shared bit, instead of restarting the second verifier. -/
theorem sequence_accepts (tr : (ProtocolSpec.seqCompose (fun _ : Fin 2 => wire)).FullTranscript) :
    (simulateQ impl (sequence.run () tr)).run' false = pure (some ()) := by
  rfl

/-- The n-ary constructor cannot have the claimed zero-error fresh-state certificate either. -/
theorem sequence_not_secure : ¬ sequence.rbrKnowledgeSoundnessAveraged
    (pure false) impl (∅ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) 0 := by
  rintro ⟨W, E, S, _⟩
  let tr : (ProtocolSpec.seqCompose (fun _ : Fin 2 => wire)).FullTranscript :=
    fun i => Fin.elim0 i
  have hlast := S.toFun_full () tr () (by
    change Pr{let _ ← (pure () : OptionT ProbComp Unit)}[True] > 0
    simp)
  have htr : tr = (default : Transcript 0 (ProtocolSpec.seqCompose (fun _ : Fin 2 => wire))) := by
    funext i
    exact Fin.elim0 i
  have hfirst := (S.toFun_empty () (E.extractOut () tr ())).mpr (by
    simpa only [Fin.vsum_succ, Fin.vsum_zero, Function.comp_apply,
      Nat.reduceAdd, htr, Fin.reduceLast] using hlast)
  exact hfirst

/-- A zero-message prover can still modify the ambient oracle during its output computation. -/
def malicious : Prover spec Unit Unit Unit Unit wire where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => Fin.elim0 i.1
  receiveChallenge := fun i => Fin.elim0 i.1
  output := fun _ => do
    let _ ← (query (spec := spec) true : OracleComp spec Bool)
    pure ((), ())

/-- The same fresh-state RBR certificate does not imply plain knowledge soundness. -/
theorem second_not_plain : ¬ second.knowledgeSoundness (pure false) impl
    (∅ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) 0 := by
  rintro ⟨E, hE⟩
  have h := hE () () malicious
  have hr : (Reduction.runWithLog () () ⟨malicious, second⟩).run = (do
      let a ← (query (spec := spec + [wire.Challenge]ₒ) (Sum.inl true) :
        OracleComp (spec + [wire.Challenge]ₒ) Bool)
      let b ← (query (spec := spec + [wire.Challenge]ₒ) (Sum.inl false) :
        OracleComp (spec + [wire.Challenge]ₒ) Bool)
      pure (if b then some (((default, ((), ())), ()),
        ([⟨Sum.inl true, a⟩], [⟨false, b⟩])) else none)) := by
    change (PFunctor.FreeM.liftBind (Sum.inl true) _ :
      OracleComp (spec + [wire.Challenge]ₒ) _) = _
    congr 1
    funext a
    change (PFunctor.FreeM.liftBind (Sum.inl false) _ :
      OracleComp (spec + [wire.Challenge]ₒ) _) = _
    congr 1
    funext b
    cases b <;> rfl
  simp only [Set.mem_empty_iff_false, not_false_eq_true, implies_true, Set.mem_univ,
    and_self, ENNReal.coe_zero] at h
  let q : OracleComp (spec + [wire.Challenge]ₒ) (Option Unit) :=
    liftComp ((E () () default [⟨true, true⟩] [⟨false, true⟩]).run)
      (spec + [wire.Challenge]ₒ)
  simp only [pure_bind, OptionT.run_bind, OptionT.run_pure, StateT.run'_eq] at h
  rw [hr] at h
  simp only [simulateQ_bind, QueryImpl.addLift_def, Option.elimM_bind,
    Option.elimM_pure, StateT.run_bind] at h
  simp only [HasQuery.instOfMonadLift_query, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, QueryImpl.add_apply_inl,
    QueryImpl.liftTarget_apply, monadLift_self, impl, StateT.run_bind, StateT.run_get,
    StateT.run_set, pure_bind, ite_true, Bool.false_eq_true, ite_false,
    Option.elim_some] at h
  have hex : (liftM ((E () () default [⟨true, true⟩] [⟨false, true⟩]).run) :
      OptionT (OracleComp (spec + [wire.Challenge]ₒ)) (Option Unit)).run =
        some <$> q := by
    rw [← monadLift_liftM_OptionT]
    simp only [OptionT.run_monadLift, monadLift_eq_self]
    rfl
  change Pr{let _ ← (OptionT.mk ((simulateQ
    (impl.addLift (challengeQueryImpl (pSpec := wire)))
      (Option.elimM
        (liftM ((E () () default [⟨true, true⟩] [⟨false, true⟩]).run) :
          OptionT (OracleComp (spec + [wire.Challenge]ₒ)) (Option Unit)).run
        (pure none) (fun z => pure (some ((), z, (), ())))) :
          StateT Bool ProbComp (Option (Unit × Option Unit × Unit × Unit))).run' true) :
      OptionT ProbComp (Unit × Option Unit × Unit × Unit))}[True] ≤ 0 at h
  rw [hex] at h
  simp only [Option.elimM_map, Option.elim_some, bind_pure_comp,
    simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at h
  change Pr{let _ ← (OptionT.mk
    ((fun z : Option Unit × Bool => some ((), z.1, (), ())) <$>
      ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := wire))) q :
        StateT Bool ProbComp (Option Unit)) true)) :
        OptionT ProbComp (Unit × Option Unit × Unit × Unit))}[True] ≤ 0 at h
  simp only [ChallengeIdx, Challenge, addLift_def, PFunctor.Handler.liftTarget_self,
    bind_pure_comp, _root_.evalDist_map_const, OptionT.evalDist_apply_univ,
    OptionT.run_mk, evalDist_apply_setOf, probEvent_map, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.dirac_apply_singleton_true, ↓reduceIte, smul_eq_mul, mul_one,
    nonpos_iff_eq_zero, probEvent_eq_zero_iff, MonadAttach.mem_support, Function.comp_apply,
    Option.isSome_some, not_true_eq_false, imp_false, Prod.forall, Bool.forall_bool] at h
  obtain ⟨⟨a, b⟩, hb⟩ := OracleComp.support_nonempty
    ((simulateQ (impl.addLift (challengeQueryImpl (pSpec := wire))) q :
      StateT Bool ProbComp (Option Unit)) true)
  cases b with
  | false => exact (h a).1 hb
  | true => exact (h a).2 hb

/-- Changing the input witness type cannot preserve an arbitrary intermediate witness family. -/
theorem same_family_lift_impossible :
    ¬ Nonempty (Extractor.RoundByRound spec Unit Bool Unit wire (fun _ => Unit)) := by
  rintro ⟨E⟩
  have h := Nat.card_congr (Equiv.cast E.eqIn)
  norm_num at h

end KnowledgeStateCounterexample

/-- info: 'KnowledgeStateCounterexample.composed_not_secure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KnowledgeStateCounterexample.composed_not_secure

/-- info: 'KnowledgeStateCounterexample.sequence_not_secure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KnowledgeStateCounterexample.sequence_not_secure

/-- info: 'KnowledgeStateCounterexample.first_secure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KnowledgeStateCounterexample.first_secure

/-- info: 'KnowledgeStateCounterexample.second_secure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KnowledgeStateCounterexample.second_secure

/-- info: 'KnowledgeStateCounterexample.second_not_plain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KnowledgeStateCounterexample.second_not_plain

/-- info: 'KnowledgeStateCounterexample.same_family_lift_impossible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KnowledgeStateCounterexample.same_family_lift_impossible

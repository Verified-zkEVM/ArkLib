/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.Ordinary

/-!
# Bridges for ordinary adaptive argument security

Size bounds can be enforced either by the verifier or by the failure event. These identities
preserve the adversary, oracle state, query budget, and named extractor. They connect the
parameterized Boolean interfaces to the generic adaptive argument predicates.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped ProbabilityTheory

namespace NARG

/-- Restricting acceptance by instance size equals restricting the false-acceptance event. -/
theorem soundnessExperiment_restrictSize_failureProb_eq
    {ι State Statement String : Type} {spec : OracleSpec ι}
      (init : ProbComp State) (impl : QueryImpl spec (StateT State ProbComp))
      (V : NARG.Verifier spec Statement String)
      (P : NARG.Prover spec Statement String)
    (size : Statement → ℕ) (n : ℕ) (language : Set Statement) :
    Pr{let out ← NARG.soundnessExperiment init impl (V.restrictSize size n) P}[
      NARG.soundnessFailureEvent language out] =
    Pr{let out ← NARG.soundnessExperiment init impl V P}[
      NARG.soundnessFailureEventSizeBounded size n language out] := by
    have hExperiment :
      NARG.soundnessExperiment init impl (V.restrictSize size n) P =
        (fun out => out.map (fun r => (r.1, decide (size r.1 ≤ n) && r.2))) <$>
          NARG.soundnessExperiment init impl V P := by
      have h : (do
          let ⟨x, π⟩ ← P
          let b ← (V.restrictSize size n).verify x (Fin.cons π (fun i => i.elim0))
          return (x, b) : OptionT (OracleComp (spec + unifSpec)) (Statement × Bool)) =
          (fun r : Statement × Bool => (r.1, decide (size r.1 ≤ n) && r.2)) <$> (do
            let ⟨x, π⟩ ← P
            let b ← V.verify x (Fin.cons π (fun i => i.elim0))
            return (x, b) : OptionT (OracleComp (spec + unifSpec)) (Statement × Bool)) := by
        simp [_root_.Verifier.restrictSize, map_bind]
      simp only [NARG.soundnessExperiment_eq]
      rw [h]
      have hmap {α β : Type} (f : α → β) (m : OptionT (OracleComp (spec + unifSpec)) α) :
          simulateQ (impl.addLift (QueryImpl.id' unifSpec) :
                QueryImpl _ (StateT State ProbComp))
            (f <$> m : OptionT _ β) =
            Option.map f <$>
              simulateQ (impl.addLift (QueryImpl.id' unifSpec) :
                QueryImpl _ (StateT State ProbComp))
                m := by
        rw [← simulateQ_map]
        congr 1
        apply OptionT.ext
        rw [OptionT.run_map]
        rfl
      rw [hmap]
      simp only [StateT.run'_eq, StateT.run_map, map_bind, Functor.map_map]
    have events (out : Option (Statement × Bool)) :
        NARG.soundnessFailureEvent language
          (out.map (fun r => (r.1, decide (size r.1 ≤ n) && r.2))) ↔
        NARG.soundnessFailureEventSizeBounded size n language out := by
      cases out with
      | none => simp [NARG.soundnessFailureEvent,
          NARG.soundnessFailureEventSizeBounded, nargSoundFailEvent]
      | some out =>
        rcases out with ⟨x, b⟩
        simp [NARG.soundnessFailureEventSizeBounded, NARG.soundnessFailureEvent,
          nargSoundFailEvent,
          and_assoc, and_left_comm, and_comm]
    simp only [hExperiment, prEvent_map, events]

/-- Restricting acceptance by instance size equals restricting the extraction-failure event. -/
theorem knowledgeSoundnessExperiment_restrictSize_failureProb_eq
    {ι State Statement Witness String : Type} {spec : OracleSpec ι}
    (init : ProbComp State) (impl : QueryImpl spec (StateT State ProbComp))
    (V : NARG.Verifier spec Statement String)
    (P : NARG.Prover spec Statement String)
    (extractor : NARG.Extractor spec Statement Witness String)
    (size : Statement → ℕ) (n : ℕ) (relation : Set (Statement × Witness)) :
    Pr{let out ← (NARG.knowledgeSoundnessExperiment init impl
      (V.restrictSize size n) extractor P)}[NARG.knowledgeSoundnessFailureEvent relation out] =
    Pr{let out ← NARG.knowledgeSoundnessExperiment init impl V extractor P}[
      NARG.knowledgeSoundnessFailureEventSizeBounded size n relation out] := by
  have hExperiment :
      NARG.knowledgeSoundnessExperiment init impl (V.restrictSize size n) extractor P =
      (fun r => (r.1, r.2.1, r.2.2.map (fun b => decide (size r.1 ≤ n) && b))) <$>
        NARG.knowledgeSoundnessExperiment init impl V extractor P := by
    have hlog (x : Statement) (tr : _) :
        ((V.restrictSize size n).verify x tr).run.withQueryLog =
        (fun r => (r.1.map (fun b => decide (size x ≤ n) && b), r.2)) <$>
          (V.verify x tr).run.withQueryLog := by
      simp [_root_.Verifier.restrictSize, OptionT.run_map, withQueryLog, simulateQ_map]
    simp [NARG.knowledgeSoundnessExperiment_eq, hlog, simulateQ_map, simulateQ_bind,
      bind_map_left, StateT.run'_eq, map_bind, Functor.map_map, StateT.run_bind]
  have events (out : Statement × Option Witness × Option Bool) :
      NARG.knowledgeSoundnessFailureEvent relation
        (out.1, out.2.1, out.2.2.map (fun b => decide (size out.1 ≤ n) && b)) ↔
      NARG.knowledgeSoundnessFailureEventSizeBounded size n relation out := by
    rcases out with ⟨x, w, b⟩
    cases w <;> cases b <;>
      simp [NARG.knowledgeSoundnessFailureEventSizeBounded,
          NARG.knowledgeSoundnessFailureEvent,
        nargKSFailEvent, and_assoc, and_left_comm, and_comm]
  simp only [hExperiment, prEvent_map, events]

/-- Adding private verifier randomness commutes with an instance-size acceptance guard. -/
theorem Verifier.ofPublic_restrictSize {ι Statement String : Type} {spec : OracleSpec ι}
    (V : NonInteractiveVerifier String spec Statement Bool) (size : Statement → ℕ) (n : ℕ) :
    Verifier.ofPublic (V.restrictSize size n) = (Verifier.ofPublic V).restrictSize size n := by
  ext x tr
  apply OptionT.ext
  simp [Verifier.ofPublic, _root_.Verifier.liftOracles, _root_.Verifier.restrictSize,
    OptionT.run_map]

section Families

variable {ι State String : ℕ → ℕ → Type} {Statement Witness : Type}
  (spec : ∀ sec n, OracleSpec (ι sec n))
  (init : ∀ sec n, ProbComp (State sec n))
  (impl : ∀ sec n, QueryImpl (spec sec n) (StateT (State sec n) ProbComp))
  (V : ∀ sec n, NonInteractiveVerifier (String sec n) (spec sec n) Statement Bool)

/-- Parameterized ordinary soundness is the generic bounded adaptive contract, with the
instance-size condition enforced by the verifier. Both sides count the same public queries. -/
theorem adaptiveSoundness_ofPublic_iff (language : Set Statement) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) :
    adaptiveSoundness spec init impl (fun sec n => Verifier.ofPublic (V sec n))
      language size error ↔
    ∀ sec n t, ((V sec n).restrictSize size n).adaptiveNARGSoundnessQueryBounded
      (init sec n) (impl sec n) language {true} (fun _ => True) t (error sec n t) := by
  unfold adaptiveSoundness AdaptiveGame.Bounded
    _root_.Verifier.adaptiveNARGSoundnessQueryBounded
  have hEvent : nargSoundFailEvent language {true} = soundnessFailureEvent language := rfl
  simp only [← soundnessExperiment_ofPublic, Verifier.ofPublic_restrictSize,
    hEvent, soundnessExperiment_restrictSize_failureProb_eq]

/-- The ordinary existential contract fixes the same standalone extractor family before all
budgets and adversaries as the generic named-extractor contracts on the right. -/
theorem adaptiveKnowledgeSoundness_ofPublic_iff
    (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) :
    adaptiveKnowledgeSoundness spec init impl (fun sec n => Verifier.ofPublic (V sec n))
      relation size error ↔
    ∃ E : ∀ sec n, Extractor (spec sec n) Statement Witness (String sec n),
      ∀ sec n t, _root_.Verifier.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor
          (init sec n) (impl sec n) privateExtractorImpl
          ((V sec n).restrictSize size n) relation {true}
          (E sec n) (fun _ => True) t (error sec n t) := by
  unfold adaptiveKnowledgeSoundness adaptiveKnowledgeSoundnessWithExtractor AdaptiveGame.Bounded
    _root_.Verifier.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor
  have hEvent : nargKSFailEvent relation {true} = knowledgeSoundnessFailureEvent relation := rfl
  simp only [← knowledgeSoundnessExperiment_ofPublic, Verifier.ofPublic_restrictSize,
    hEvent, knowledgeSoundnessExperiment_restrictSize_failureProb_eq]

end Families

end NARG

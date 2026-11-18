/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.Security.Game
public import ArkLib.Security.PrivateCoins

/-!
# Adaptive NARG soundness and knowledge soundness

The verifier consumes a statement and a proof string directly. These definitions depend only on
oracle computations, so either interaction layer can use them. The public oracle state is shared;
private samples are excluded from query budgets and extractor logs. One named extractor family
is fixed before all budgets and adversaries. No running-time bound is imposed.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped NNReal ProbabilityTheory

/-- False-acceptance event on the NARG soundness experiment output
`Option (StmtIn × StmtOut)`: the prover output a false statement (`x ∉ langIn`) the verifier
accepted into `stmtOut ∈ langOut`. The unbounded and query-bounded predicates use the
same event. -/
def nargSoundFailEvent {StmtIn StmtOut : Type} (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (StmtIn × StmtOut) → Prop
  | some (x, stmtOut) => x ∉ langIn ∧ stmtOut ∈ langOut
  | none => False

/-- Extraction-failure event on the NARG-KS experiment output
`StmtIn × Option WitIn × Option StmtOut`: the verifier accepted into `langOut` yet the extracted
input witness misses `relIn` (or none was produced). No output witness is supplied by the malicious
NARG prover: Definition 3.6 quantifies over the same adversaries producing only a statement and
NARG string `(x, π)` as Definition 3.5. -/
def nargKSFailEvent {StmtIn WitIn StmtOut : Type}
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut) :
    StmtIn × Option WitIn × Option StmtOut → Prop
  | (x, some witIn, some stmtOut) => stmtOut ∈ langOut ∧ (x, witIn) ∉ relIn
  | (_, none, some stmtOut) => stmtOut ∈ langOut
  | _ => False

namespace NARG

/-- A Boolean NARG verifier has the named public oracles and its own private coins.
An internal `none`, like `some false`, denotes rejection. -/
@[ext]
structure Verifier {ι : Type} (publicSpec : OracleSpec ι) (Statement NARGString : Type) where
  verify : Statement → NARGString → OptionT (OracleComp (publicSpec + unifSpec)) Bool

/-- Apply a statement-size guard after the same verifier execution. -/
def Verifier.restrictSize {ι : Type} {publicSpec : OracleSpec ι}
    {Statement NARGString : Type} (V : Verifier publicSpec Statement NARGString)
    (size : Statement → ℕ) (bound : ℕ) : Verifier publicSpec Statement NARGString where
  verify x proof := (fun b => decide (size x ≤ bound) && b) <$> V.verify x proof

/-- A malicious NARG prover chooses a statement and NARG string and has private coins. -/
abbrev Prover {ι : Type} (publicSpec : OracleSpec ι) (Statement NARGString : Type) :=
  OracleComp (publicSpec + unifSpec) (Statement × NARGString)

/-- A non-rewinding NARG extractor receives both public logs and has only private randomness. -/
abbrev Extractor {ι : Type} (publicSpec : OracleSpec ι) (Statement Witness NARGString : Type) :=
  Statement → NARGString → QueryLog publicSpec → QueryLog publicSpec → OptionT ProbComp Witness

/-- The generic backend's handler for an extractor with private randomness only. -/
def privateExtractorImpl {σ : Type} : QueryImpl unifSpec (StateT σ ProbComp) :=
  fun q => StateT.lift ((QueryImpl.id' unifSpec) q)

/-- False acceptance is acceptance of a statement outside the language. -/
def soundnessFailureEvent {Statement : Type} (language : Set Statement) :
    Option (Statement × Bool) → Prop :=
  nargSoundFailEvent language {true}

/-- Extraction failure requires acceptance and either no witness or an invalid witness. -/
def knowledgeSoundnessFailureEvent {Statement Witness : Type}
    (relation : Set (Statement × Witness)) :
    Statement × Option Witness × Option Bool → Prop :=
  nargKSFailEvent relation {true}

/-- Internal verifier failure is rejection, so it cannot cause false acceptance. -/
@[simp] theorem soundnessFailureEvent_none {Statement : Type} (language : Set Statement) :
    ¬ soundnessFailureEvent language none := by
  simp [soundnessFailureEvent, nargSoundFailEvent]

/-- Missing extraction counts as failure whenever the verifier accepts. -/
@[simp] theorem knowledgeSoundnessFailureEvent_missing {Statement Witness : Type}
    (relation : Set (Statement × Witness)) (x : Statement) :
    knowledgeSoundnessFailureEvent relation (x, none, some true) := by
  simp [knowledgeSoundnessFailureEvent, nargKSFailEvent]

/-- Internal verifier failure remains rejection even when extraction also fails. -/
@[simp] theorem knowledgeSoundnessFailureEvent_reject {Statement Witness : Type}
    (relation : Set (Statement × Witness)) (x : Statement) (w : Option Witness) :
    ¬ knowledgeSoundnessFailureEvent relation (x, w, none) := by
  cases w <;> simp [knowledgeSoundnessFailureEvent, nargKSFailEvent]

section

variable {ι : Type} {publicSpec : OracleSpec ι} {σ Statement Witness NARGString : Type}
  (init : ProbComp σ) (impl : QueryImpl publicSpec (StateT σ ProbComp))

/-- Run the probabilistic prover and verifier with the same public-oracle state and independent
private draws. Their use of the same sampling interface shares no sampled values. -/
def soundnessExperiment (V : Verifier publicSpec Statement NARGString)
    (P : Prover publicSpec Statement NARGString) : ProbComp (Option (Statement × Bool)) :=
  AdaptiveGame.run init (impl.addLift (QueryImpl.id' unifSpec)) P
    (fun a => (V.verify a.1 a.2).run)
    (fun a out => out.map (a.1, ·))

/-- Read the NARG soundness experiment as a single optional computation. -/
theorem soundnessExperiment_eq (V : Verifier publicSpec Statement NARGString)
    (P : Prover publicSpec Statement NARGString) :
    soundnessExperiment init impl V P = (do
  (simulateQ (impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp)) (do
    let ⟨x, π⟩ ← P
    let accepted ← V.verify x π
    return (x, accepted) : OptionT (OracleComp (publicSpec + unifSpec))
      (Statement × Bool))).run' (← init)) := by
  unfold soundnessExperiment
  rw [AdaptiveGame.run_eq_runOption]
  rfl

/-- Run the prover and verifier, then `E(𝕩, π, tr_P, tr_V)` with private randomness.
Both parties' private sampling requests are removed from the logs passed to the extractor. -/
def knowledgeSoundnessExperiment (V : Verifier publicSpec Statement NARGString)
    (E : Extractor publicSpec Statement Witness NARGString)
    (P : Prover publicSpec Statement NARGString) :
    ProbComp (Statement × Option Witness × Option Bool) :=
  AdaptiveGame.runWithExtractor init (impl.addLift (QueryImpl.id' unifSpec))
    privateExtractorImpl P.withQueryLog
    (fun a => (V.verify a.1.1 a.1.2).run.withQueryLog)
    (fun a v => E a.1.1 a.1.2 a.2.publicQueries v.2.publicQueries)
    (fun a v w => (a.1.1, w, v.1))

/-- Read the knowledge experiment in terms of the two public logs and a standalone extractor. -/
theorem knowledgeSoundnessExperiment_eq (V : Verifier publicSpec Statement NARGString)
    (E : Extractor publicSpec Statement Witness NARGString)
    (P : Prover publicSpec Statement NARGString) :
    knowledgeSoundnessExperiment init impl V E P = (do
  StateT.run' (do
    let ⟨x, π, logP, accepted, logV⟩ ←
      simulateQ (impl.addLift (QueryImpl.id' unifSpec)) (do
        let ⟨⟨x, π⟩, logP⟩ ← P.withQueryLog
        let ⟨accepted, logV⟩ ←
          (V.verify x π).run.withQueryLog
        return (x, π, logP.publicQueries, accepted, logV.publicQueries))
    let w ← StateT.lift (E x π logP logV).run
    return (x, w, accepted)) (← init)) := by
  have hprivate (p : ProbComp (Option Witness)) :
      simulateQ (privateExtractorImpl (σ := σ)) p = StateT.lift p := by
    change simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT σ ProbComp)) p = _
    rw [simulateQ_liftTarget, simulateQ_id']
    rfl
  simp only [knowledgeSoundnessExperiment, AdaptiveGame.runWithExtractor, AdaptiveGame.execute,
    simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, hprivate]


end

/-- False acceptance of a statement whose size is at most the public instance-size bound. -/
def soundnessFailureEventSizeBounded {Statement : Type}
    (size : Statement → ℕ) (instanceBound : ℕ) (language : Set Statement) :
    Option (Statement × Bool) → Prop
  | none => False
  | some (stmt, accepted) =>
      size stmt ≤ instanceBound ∧ soundnessFailureEvent language (some (stmt, accepted))

/-- The size restriction guards the whole knowledge-failure event, including a missing witness. -/
def knowledgeSoundnessFailureEventSizeBounded {Statement Witness : Type}
    (size : Statement → ℕ) (instanceBound : ℕ) (relation : Set (Statement × Witness))
    (out : Statement × Option Witness × Option Bool) : Prop :=
  size out.1 ≤ instanceBound ∧ knowledgeSoundnessFailureEvent relation out

section Parameterized

variable {ι State NARGString : ℕ → ℕ → Type} {Statement Witness : Type}
  (publicSpec : ∀ securityParam instanceBound, OracleSpec (ι securityParam instanceBound))
  (init : ∀ securityParam instanceBound, ProbComp (State securityParam instanceBound))
  (impl : ∀ securityParam instanceBound, QueryImpl (publicSpec securityParam instanceBound)
    (StateT (State securityParam instanceBound) ProbComp))
  (V : ∀ securityParam instanceBound,
    Verifier (publicSpec securityParam instanceBound) Statement
      (NARGString securityParam instanceBound))

/-- **[snarg-book, Section 9.1]** Adaptive NARG soundness for an oracle distribution indexed by
security parameter and instance-size bound. The error also depends on the public-query budget. -/
def adaptiveSoundness (language : Set Statement) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∀ securityParam instanceBound t, AdaptiveGame.Bounded
    (fun P => P.IsQueryBoundP (publicQuerySelector (fun _ => True)) t)
    (soundnessExperiment (init securityParam instanceBound)
      (impl securityParam instanceBound) (V securityParam instanceBound))
    (soundnessFailureEventSizeBounded size instanceBound language)
    (error securityParam instanceBound t)

/-- The adaptive NARG bound for a supplied extractor family, for all public parameters,
query budgets, and adversaries. The family may use the security parameter and instance-size
bound; no uniform polynomial-time claim is imposed. -/
def adaptiveKnowledgeSoundnessWithExtractor
    (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (E : ∀ securityParam instanceBound,
      Extractor (publicSpec securityParam instanceBound) Statement Witness
        (NARGString securityParam instanceBound))
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∀ securityParam instanceBound t, AdaptiveGame.Bounded
    (fun P => P.IsQueryBoundP (publicQuerySelector fun _ => True) t)
    (knowledgeSoundnessExperiment (init securityParam instanceBound)
      (impl securityParam instanceBound) (V securityParam instanceBound)
      (E securityParam instanceBound))
    (knowledgeSoundnessFailureEventSizeBounded size instanceBound relation)
    (error securityParam instanceBound t)

/-- **[snarg-book, Section 9.1]** One extractor family satisfies
`adaptiveKnowledgeSoundnessWithExtractor`. With no resource bound on the extractor,
classical witness selection gives an extractor from soundness for the relation's language.
See `Verifier.knowledgeSoundness_iff_relationSoundness` for this argument in the ordinary
interactive game. -/
def adaptiveKnowledgeSoundness
    (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∃ E, adaptiveKnowledgeSoundnessWithExtractor publicSpec init impl V relation size E error

end Parameterized

/-! ## Statement-size restrictions -/

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
          let b ← (V.restrictSize size n).verify x π
          return (x, b) : OptionT (OracleComp (spec + unifSpec)) (Statement × Bool)) =
          (fun r : Statement × Bool => (r.1, decide (size r.1 ≤ n) && r.2)) <$> (do
            let ⟨x, π⟩ ← P
            let b ← V.verify x π
            return (x, b) : OptionT (OracleComp (spec + unifSpec)) (Statement × Bool)) := by
        simp [Verifier.restrictSize, map_bind]
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
      simp [Verifier.restrictSize, OptionT.run_map, withQueryLog, simulateQ_map]
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


end NARG

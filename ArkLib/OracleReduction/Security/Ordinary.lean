/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Security.PrivateCoins

/-!
# Ordinary public-coin IP and NARG security

The public security definitions quantify over their full parameter families. Their
experiments and probability identities below support the security proofs. These interfaces
specialize the general reduction games to Boolean acceptance. A public-coin IP
has no ambient oracle; its final decision is deterministic given the statement and transcript.
Its SR adversary and extractor retain private randomness. The SR extractor receives only the
statement, chosen salt, transcript, and SR move-response trace. The adversary supplies no
output witness; the SR game carries the salt separately from the IP statement.

A NARG names its public oracle interface explicitly. Its extractor has private randomness and
the public query logs, with no additional oracle access. The verifier uses the named public
interface and its own private randomness. Both parties' private draws are removed from the
extractor's logs. These are information-theoretic predicates and impose no running-time bound.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace Verifier
variable {ι : Type} {spec : OracleSpec ι} {Statement : Type} {rounds : ℕ}
  {pSpec : ProtocolSpec rounds}
/-- Guard the final Boolean decision by the statement-size bound, after the same execution. -/
def restrictSize (V : Verifier spec Statement Bool pSpec) (size : Statement → ℕ)
    (bound : ℕ) : Verifier spec Statement Bool pSpec where
  verify x tr := (fun b => decide (size x ≤ bound) && b) <$> V.verify x tr
end Verifier

namespace PublicCoinIP

/-- An ordinary public-coin verifier's statement and full transcript determine its final
decision. Both `none` and `some false` mean rejection. -/
abbrev Verifier (Statement : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  _root_.Verifier []ₒ Statement Bool pSpec

/-- The empty interface has a unique handler, with no state effects. -/
def emptyImpl {σ : Type} : QueryImpl []ₒ (StateT σ ProbComp) := fun q => nomatch q

/-- An SR adversary returns `((𝕩, τ), α)`: the statement, chosen salt, and prover messages.
It queries the single-salt challenge oracles and uses private coins. The empty summand is
only the generic backend's interface adapter. -/
abbrev SRProver (Statement : Type) {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover.StateRestoration.Soundness []ₒ unifSpec Statement pSpec (Salt := Salt)

/-- An ordinary non-rewinding SR extractor computes `E(𝕩, τ, T, tr_sr)` from the original
statement, chosen salt, final transcript, and SR move-response trace. It may use private coins
and may fail; it receives no prover handle or private sampling log. -/
abbrev SRExtractor (Statement Witness : Type) {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  Statement → Salt → pSpec.FullTranscript → QueryLog (srChallengeOracle (Statement × Salt) pSpec) →
    OptionT ProbComp Witness

/-- Run an ordinary SR adversary and reconstruct its final transcript using the same
verifier-message functions queried during its moves. -/
def srGame {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : SRProver Statement pSpec (Salt := Salt)) :
    OracleComp (([]ₒ + srChallengeOracle (Statement × Salt) pSpec) + unifSpec)
      (pSpec.FullTranscript × (Statement × Salt)) :=
  srSoundnessGame (Salt := Salt) P

/-- The internal reduction output relation for Boolean acceptance has a dummy witness. -/
def acceptRelation : Set (Bool × Unit) := {result | result.1 ∈ ({true} : Set Bool)}

/-- Add the unique dummy witness required by the generic reduction game. -/
def SRProver.toReduction {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : SRProver Statement pSpec (Salt := Salt)) :
    Prover.StateRestoration.KnowledgeSoundness []ₒ unifSpec Statement Unit pSpec (Salt := Salt) :=
  (fun result => (result.1, result.2, ())) <$> P

/-- Erase the generic game's dummy witness. This does not change any query. -/
def SRProver.ofReduction {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : Prover.StateRestoration.KnowledgeSoundness
      []ₒ unifSpec Statement Unit pSpec (Salt := Salt)) :
    SRProver Statement pSpec (Salt := Salt) :=
  (fun result => (result.1, result.2.1)) <$> P

/-- The dummy output witness carries no information. -/
theorem SRProver.toReduction_ofReduction {Statement Salt : Type} {n : ℕ}
    {pSpec : ProtocolSpec n}
    (P : Prover.StateRestoration.KnowledgeSoundness
      []ₒ unifSpec Statement Unit pSpec (Salt := Salt)) :
    (SRProver.ofReduction P).toReduction = P := by
  unfold Prover.StateRestoration.KnowledgeSoundness at P
  simp only [SRProver.toReduction, SRProver.ofReduction, Functor.map_map]
  have h : (fun result : (Statement × Salt) × pSpec.Messages × Unit =>
      (result.1, result.2.1, ())) = id := by
    funext ⟨x, messages, u⟩
    cases u
    rfl
  rw [h, id_map]

/-- Adapt the ordinary extractor to the general reduction interface. Pass it the statement,
salt, transcript, and SR move-response log, discarding the empty ambient logs and dummy witness. -/
def SRExtractor.toReduction {Statement Witness Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (E : SRExtractor Statement Witness pSpec (Salt := Salt)) :
    Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt) :=
  fun x salt _ transcript log _ => OptionT.mk
    (liftComp (E x salt transcript log.snd).run ([]ₒ + unifSpec))

section

variable {Statement Witness Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (Statement × Salt) pSpec) Id))

/-- Extraction failure for an ordinary SR adversary. The dummy witness is introduced only
inside the general backend; the adversary and extractor interfaces do not expose it. -/
noncomputable def srKnowledgeSoundnessFailureProb (relation : Set (Statement × Witness))
    (V : Verifier Statement pSpec) (E : SRExtractor Statement Witness pSpec (Salt := Salt))
    (P : SRProver Statement pSpec (Salt := Salt)) : ENNReal :=
  _root_.Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt) init emptyImpl
    (QueryImpl.id' unifSpec) E.toReduction relation acceptRelation V P.toReduction

omit [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The same named ordinary extractor works in the general dummy-witness game. -/
theorem srKnowledgeSoundnessQueryBoundedWithExtractor_to_generic
    (relation : Set (Statement × Witness)) (V : Verifier Statement pSpec)
    (E : SRExtractor Statement Witness pSpec (Salt := Salt)) (t : ℕ) (error : ENNReal)
    (h : ∀ P : SRProver Statement pSpec (Salt := Salt),
      P.IsQueryBoundP (publicQuerySelector
        (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt) (oSpec := []ₒ))) t →
      srKnowledgeSoundnessFailureProb (Salt := Salt) init relation V E P ≤ error) :
    _root_.Verifier.StateRestoration.knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt)
      init emptyImpl relation acceptRelation V E.toReduction
      (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)) t error := by
  intro P hP
  unfold Prover.StateRestoration.KnowledgeSoundness at P
  have hBound : (SRProver.ofReduction P).IsQueryBoundP
      (publicQuerySelector (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)
        (oSpec := []ₒ))) t := by
    simpa only [SRProver.ofReduction, isQueryBoundP_map_iff] using hP
  have hResult := h (SRProver.ofReduction P) hBound
  unfold srKnowledgeSoundnessFailureProb at hResult
  erw [SRProver.toReduction_ofReduction] at hResult
  exact hResult

end

section Families

variable {Statement Witness : Type} {Salt : ℕ → ℕ → Type}
  {rounds : ℕ → ℕ → ℕ} {pSpec : ∀ s n, ProtocolSpec (rounds s n)}
  [∀ s n i, SampleableType ((pSpec s n).Challenge i)]
  [DecidableEq Statement] [∀ s n i, DecidableEq ((pSpec s n).Message i)]
  [∀ s n i, DecidableEq ((pSpec s n).Challenge i)]
  (init : ∀ s n, ProbComp
    (QueryImpl (srChallengeOracle (Statement × Salt s n) (pSpec s n)) Id))
  (V : ∀ s n, Verifier Statement (pSpec s n))

/-- **[snarg-book, state-restoration soundness]** SR soundness for every public salt-size
parameter `s`, instance-size bound `n`, and move budget `t`. The salt carrier and challenge
sampler may depend on `s,n`. Guarding the final decision implements the joint event
`size x ≤ n ∧ x ∉ language ∧ accepted`; it does not condition or truncate the game. -/
def srSoundness (language : Set Statement) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∀ s n t, _root_.Verifier.StateRestoration.soundnessQueryBounded (Salt := Salt s n)
    (init s n) emptyImpl language {true} ((V s n).restrictSize size n)
    (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt s n)) t (error s n t)

/-- **[snarg-book, state-restoration knowledge soundness]** One non-rewinding extractor
family precedes all salt-size and instance-size parameters, move budgets, and adversaries.
The parameter `s` indexes the specified salt carrier; no efficiency guarantee is imposed. -/
def srKnowledgeSoundness (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∃ E : ∀ s n, SRExtractor Statement Witness (pSpec s n) (Salt := Salt s n),
    ∀ s n t (P : SRProver Statement (pSpec s n) (Salt := Salt s n)),
      P.IsQueryBoundP (publicQuerySelector
        (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt s n) (oSpec := []ₒ))) t →
      srKnowledgeSoundnessFailureProb (init s n) relation ((V s n).restrictSize size n)
        (E s n) P ≤ error s n t

end Families

end PublicCoinIP

namespace NARG

/-- An ordinary Boolean NARG verifier has the named public oracles and its own private coins.
An internal `none`, like `some false`, denotes rejection. -/
abbrev Verifier {ι : Type} (publicSpec : OracleSpec ι) (Statement NARGString : Type) :=
  NonInteractiveVerifier NARGString (publicSpec + unifSpec) Statement Bool

/-- Embed a verifier that needs no private coins into the ordinary probabilistic interface. -/
def Verifier.ofPublic {ι : Type} {publicSpec : OracleSpec ι}
    {Statement NARGString : Type}
    (V : NonInteractiveVerifier NARGString publicSpec Statement Bool) :
    Verifier publicSpec Statement NARGString :=
  V.liftOracles

/-- A malicious NARG prover chooses a statement and NARG string and has private coins. -/
abbrev Prover {ι : Type} (publicSpec : OracleSpec ι) (Statement NARGString : Type) :=
  OracleComp (publicSpec + unifSpec) (Statement × NARGString)

/-- A non-rewinding NARG extractor receives both public logs and has only private randomness. -/
abbrev Extractor {ι : Type} (publicSpec : OracleSpec ι) (Statement Witness NARGString : Type) :=
  Statement → NARGString → QueryLog publicSpec → QueryLog publicSpec → OptionT ProbComp Witness

/-- Every query to the named public interface contributes to the NARG budget. -/
def countsPublicQuery {ι : Type} : ι → Prop := fun _ => True

instance {ι : Type} : DecidablePred (@countsPublicQuery ι) := fun _ => isTrue trivial

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
    (P : Prover publicSpec Statement NARGString) : ProbComp (Option (Statement × Bool)) := do
  (simulateQ (impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp)) (do
    let ⟨x, π⟩ ← P
    let accepted ← V.verify x (Fin.cons π (fun i => i.elim0))
    return (x, accepted) : OptionT (OracleComp (publicSpec + unifSpec))
      (Statement × Bool))).run' (← init)

/-- Run the prover and verifier, then `E(𝕩, π, tr_P, tr_V)` with private randomness.
Both parties' private sampling requests are removed from the logs passed to the extractor. -/
def knowledgeSoundnessExperiment (V : Verifier publicSpec Statement NARGString)
    (E : Extractor publicSpec Statement Witness NARGString)
    (P : Prover publicSpec Statement NARGString) :
    ProbComp (Statement × Option Witness × Option Bool) := do
  StateT.run' (do
    let ⟨x, π, logP, accepted, logV⟩ ←
      simulateQ (impl.addLift (QueryImpl.id' unifSpec)) (do
        let ⟨⟨x, π⟩, logP⟩ ← P.withQueryLog
        let ⟨accepted, logV⟩ ←
          (V.verify x (Fin.cons π (fun i => i.elim0))).run.withQueryLog
        return (x, π, logP.publicQueries, accepted, logV.publicQueries))
    let w ← StateT.lift (E x π logP logV).run
    return (x, w, accepted)) (← init)

/-- Embedding a public-only verifier preserves its soundness experiment exactly. -/
theorem soundnessExperiment_ofPublic
    (V : NonInteractiveVerifier NARGString publicSpec Statement Bool)
    (P : Prover publicSpec Statement NARGString) :
    soundnessExperiment init impl (Verifier.ofPublic V) P =
      adaptiveNARGSoundnessExp init impl (QueryImpl.id' unifSpec) V P := rfl

/-- Embedding a public-only verifier preserves the knowledge-soundness experiment with a
standalone extractor, including both public-query logs. -/
theorem knowledgeSoundnessExperiment_ofPublic
    (V : NonInteractiveVerifier NARGString publicSpec Statement Bool)
    (E : Extractor publicSpec Statement Witness NARGString)
    (P : Prover publicSpec Statement NARGString) :
    knowledgeSoundnessExperiment init impl (Verifier.ofPublic V) E P =
      adaptiveNARGKnowledgeSoundnessExp init impl (QueryImpl.id' unifSpec)
        privateExtractorImpl V E P := by
  unfold knowledgeSoundnessExperiment adaptiveNARGKnowledgeSoundnessExp
  simp only [Verifier.ofPublic, _root_.Verifier.liftOracles, OptionT.run_mk]
  have hlog (x : Statement) (π : NARGString) :=
    withQueryLog_liftComp_left_of_query (oSpec := publicSpec) (spec₂ := unifSpec) (fun _ => rfl)
      (V.verify x (Fin.cons π (fun i => i.elim0))).run
  simp only [show ∀ x π,
    (liftComp (V.verify x (Fin.cons π (fun i => i.elim0))).run
      (publicSpec + unifSpec)).withQueryLog =
      liftComp (runVerifierWithLog V x π) (publicSpec + unifSpec) >>= fun result =>
        pure (result.1, QueryLog.inl result.2) from hlog]
  simp only [bind_assoc, pure_bind, QueryLog.publicQueries, QueryLog.fst_inl]
  have hprivate (p : ProbComp (Option Witness)) :
      simulateQ (privateExtractorImpl (σ := σ)) p = StateT.lift p := by
    change simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT σ ProbComp)) p = _
    rw [simulateQ_liftTarget, simulateQ_id']
    rfl
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind, hprivate]

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
  ∀ securityParam instanceBound t
      (P : Prover (publicSpec securityParam instanceBound) Statement
        (NARGString securityParam instanceBound)),
    P.IsQueryBoundP (publicQuerySelector countsPublicQuery) t →
    Pr{let out ← (soundnessExperiment (init securityParam instanceBound)
      (impl securityParam instanceBound) (V securityParam instanceBound) P)}[
        soundnessFailureEventSizeBounded size instanceBound language out] ≤
      error securityParam instanceBound t

/-- **[snarg-book, Section 9.1]** One parameterized extractor is chosen before all public
parameters, query budgets, and adversaries. No uniform polynomial-time claim is imposed. -/
def adaptiveKnowledgeSoundness
    (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∃ E : ∀ securityParam instanceBound,
      Extractor (publicSpec securityParam instanceBound) Statement Witness
        (NARGString securityParam instanceBound),
    ∀ securityParam instanceBound t
        (P : Prover (publicSpec securityParam instanceBound) Statement
          (NARGString securityParam instanceBound)),
      P.IsQueryBoundP (publicQuerySelector countsPublicQuery) t →
      Pr{let out ← (knowledgeSoundnessExperiment (init securityParam instanceBound)
        (impl securityParam instanceBound) (V securityParam instanceBound)
        (E securityParam instanceBound) P)}[
          knowledgeSoundnessFailureEventSizeBounded size instanceBound relation out] ≤
        error securityParam instanceBound t

end Parameterized

end NARG

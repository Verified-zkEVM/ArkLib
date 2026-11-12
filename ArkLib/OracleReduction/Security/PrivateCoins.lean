/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Security.StateRestoration
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.QueryTracking.QueryLog
public import ToMathlib.Control.OptionT
public import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Private-sampling preservation in security games

Normalization to `unifSpec` preserves execution, public-query logs and budgets. The adaptive
NARG and state-restoration lemmas transport their security experiments across these adapters.
The core security definitions do not import this proof module. DSFS-specific trace and
extractor transport stays in the DSFS proof modules.
-/

@[expose] public section

open OracleComp OracleSpec

namespace OracleComp

variable {ι κ α σ : Type} {publicSpec : OracleSpec ι} {privateSpec : OracleSpec κ}

/-- Normalization preserves the entire computation, including its public-oracle state. -/
theorem simulateQ_normalizePrivateCoins
    (publicImpl : QueryImpl publicSpec (StateT σ ProbComp))
    (sampler : QueryImpl privateSpec ProbComp) (p : OracleComp (publicSpec + privateSpec) α) :
    simulateQ (publicImpl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp))
      (normalizePrivateCoins sampler p) =
      simulateQ (publicImpl.addLift sampler : QueryImpl _ (StateT σ ProbComp)) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro q
  cases q with
  | inl q =>
    change simulateQ _ (liftComp (liftM (publicSpec.query q) : OracleComp publicSpec _) _) = _
    rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left]
    simp
  | inr q =>
    change simulateQ _ (liftComp (sampler q) _) = _
    rw [QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right, simulateQ_liftTarget]
    simp

/-- A private sampler consumes none of the public-query budget. -/
theorem isQueryBoundP_lift_private (counts : ι → Prop) [DecidablePred counts]
    (p : ProbComp α) :
    (liftComp p (publicSpec + unifSpec)).IsQueryBoundP (publicQuerySelector counts) 0 := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q next ih =>
    rw [liftComp_bind, liftComp_query]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨by simp [publicQuerySelector],
      fun u => by simpa [publicQuerySelector] using ih u⟩

/-- The named private sampler never charges a public query, even when the public spec
also contains `unifSpec`. -/
theorem isQueryBoundP_samplePrivateUniform (α : Type) [SampleableType α]
    (counts : ι → Prop) [DecidablePred counts] :
    (samplePrivateUniform (publicSpec := publicSpec) α).IsQueryBoundP
      (publicQuerySelector counts) 0 :=
  isQueryBoundP_lift_private counts ($ᵗ α)

/-- Compiling private samplers preserves any budget on selected public queries. -/
theorem IsQueryBoundP.normalizePrivateCoins
    (sampler : QueryImpl privateSpec ProbComp) (counts : ι → Prop) [DecidablePred counts]
    {p : OracleComp (publicSpec + privateSpec) α} {n : ℕ}
    (h : p.IsQueryBoundP (publicQuerySelector counts) n) :
    (normalizePrivateCoins sampler p).IsQueryBoundP (publicQuerySelector counts) n := by
  apply h.simulateQ_of_step
  · intro q hq
    cases q with
    | inl q => simp [privateCoinsImpl, publicQuerySelector]
    | inr q => exact False.elim hq
  · intro q hq
    cases q with
    | inl q => simpa [privateCoinsImpl, publicQuerySelector] using hq
    | inr q => exact isQueryBoundP_lift_private counts (sampler q)

/-- The named private sampler contributes no entries to the public transcript. -/
theorem publicQueries_withQueryLog_samplePrivateUniform (α : Type) [SampleableType α] :
    (fun r => (r.1, r.2.fst)) <$>
      (samplePrivateUniform (publicSpec := publicSpec) α).withQueryLog =
    (fun x => (x, ([] : QueryLog publicSpec))) <$> samplePrivateUniform α :=
  fst_withQueryLog_liftComp_right ($ᵗ α)

/-- Normalization preserves the public log even when one private request draws many samples. -/
theorem publicQueries_withQueryLog_normalizePrivateCoins
    (sampler : QueryImpl privateSpec ProbComp) (p : OracleComp (publicSpec + privateSpec) α) :
    (fun r => (r.1, r.2.fst)) <$> (normalizePrivateCoins sampler p).withQueryLog =
      normalizePrivateCoins sampler ((fun r => (r.1, r.2.fst)) <$> p.withQueryLog) := by
  apply withQueryLog_simulateQ_project (privateCoinsImpl sampler) QueryLog.fst QueryLog.fst
    rfl rfl QueryLog.fst_append QueryLog.fst_append
  intro q
  cases q with
  | inl q => simp [privateCoinsImpl, withQueryLog_query, QueryLog.fst]
  | inr q =>
    dsimp only [privateCoinsImpl]
    rw [fst_withQueryLog_liftComp_right]
    rfl

end OracleComp

namespace OracleComp

variable {ι κ α : Type} {a : OracleSpec ι} {b : OracleSpec κ}

/-- Reordering a computation and its handlers preserves the interpreted computation. -/
@[simp]
theorem simulateQ_swapOracles {m : Type → Type} [Monad m] [LawfulMonad m]
    (ha : QueryImpl a m) (hb : QueryImpl b m) (p : OracleComp (a + b) α) :
    simulateQ (hb + ha) p.swapOracles = simulateQ (ha + hb) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  intro q
  cases q <;> simp [QueryImpl.swapOracles]

end OracleComp

/-! ## Adaptive NARG experiments -/

open OracleComp OracleSpec

/-- Execute the prover with private sampling, then verify using only public queries. -/
theorem adaptiveNARGSoundnessExp_eq
    {ι κ : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    adaptiveNARGSoundnessExp init impl privateImpl verifier P = (do
      (do
        let ⟨x, π⟩ ← simulateQ (impl.addLift privateImpl : QueryImpl _ (StateT σ ProbComp)) P
        let output ← simulateQ impl (verifier.verify x (Fin.cons π (fun i => i.elim0))).run
        return output.map (x, ·)).run' (← init)) := by
  simp only [adaptiveNARGSoundnessExp, AdaptiveGame.run, simulateQ_bind, simulateQ_pure,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self, QueryImpl.simulateQ_add_liftComp_left]

/-- A standalone extractor can run after the public-oracle state is discarded. -/
theorem adaptiveNARGKnowledgeSoundnessExp_liftTarget
    {ι κ κE : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {extractorSpec : OracleSpec κE} {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (extractorImpl : QueryImpl extractorSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) WitIn)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExp init impl privateImpl
      (extractorImpl.liftTarget (StateT σ ProbComp)) verifier extractor P = (do
      let ⟨x, π, tr, stmtOut, trV⟩ ←
        (simulateQ (impl.addLift privateImpl : QueryImpl _ (StateT σ ProbComp)) (do
          let ⟨⟨x, π⟩, tr⟩ ← P.withQueryLog
          let ⟨stmtOut, trV⟩ ← liftComp (runVerifierWithLog verifier x π) _
          return (x, π, tr, stmtOut, trV))).run' (← init)
      let witIn ← simulateQ extractorImpl (extractor x π tr.publicQueries trV).run
      return (x, witIn, stmtOut)) := by
  simp only [adaptiveNARGKnowledgeSoundnessExp_eq, simulateQ_liftTarget,
    StateT.run'_bind', StateT.run'_pure']
  simp [StateT.run'_eq, bind_map_left, map_bind]

/-- Embedding a prover without private queries preserves the soundness experiment. -/
theorem adaptiveNARGSoundnessExp_liftComp
    {ι : Type} {oSpec : OracleSpec ι} {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp oSpec (StmtIn × Proof)) :
    adaptiveNARGSoundnessExp init impl (QueryImpl.id' unifSpec) verifier
      (liftCompLeft P) = (do
      (simulateQ impl (do
        let ⟨x, π⟩ ← P
        let stmtOut ← verifier.verify x (Fin.cons π (fun i => i.elim0))
        return (x, stmtOut) : OptionT (OracleComp oSpec) (StmtIn × StmtOut))).run' (← init)) := by
  rw [adaptiveNARGSoundnessExp_eq]
  simp only [liftCompLeft]
  change _ = (do
    (simulateQ impl (do
      let ⟨x, π⟩ ← P
      let stmtOut ← verifier.verify x (Fin.cons π (fun i => i.elim0))
      return (x, stmtOut) : OptionT (OracleComp oSpec) (StmtIn × StmtOut)).run).run' (← init))
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    QueryImpl.simulateQ_add_liftComp_left, StateT.run'_bind', StateT.run'_pure',
    OptionT.liftM_def, OptionT.run_bind, Option.elimM, OptionT.run_lift, OptionT.run_pure,
    bind_assoc, pure_bind, Option.elim_some, simulateQ_bind]
  apply bind_congr
  intro state
  apply bind_congr
  intro proverResult
  apply bind_congr
  intro verifierResult
  cases verifierResult.1 <;> simp

/-- Embedding a prover without private queries preserves its public log and KS experiment. -/
theorem adaptiveNARGKnowledgeSoundnessExp_liftComp
    {ι κE : Type} {oSpec : OracleSpec ι} {extractorSpec : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (extractorImpl : QueryImpl extractorSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) WitIn)
    (P : OracleComp oSpec (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExp init impl (QueryImpl.id' unifSpec)
      (extractorImpl.liftTarget (StateT σ ProbComp)) verifier extractor
      (liftCompLeft P) = (do
      let ⟨x, π, tr, stmtOut, trV⟩ ←
        (simulateQ impl (do
          let ⟨⟨x, π⟩, tr⟩ ← P.withQueryLog
          let ⟨stmtOut, trV⟩ ← runVerifierWithLog verifier x π
          return (x, π, tr, stmtOut, trV))).run' (← init)
      let witIn ← simulateQ extractorImpl (extractor x π tr trV).run
      return (x, witIn, stmtOut)) := by
  rw [adaptiveNARGKnowledgeSoundnessExp_liftTarget]
  unfold liftCompLeft
  rw [withQueryLog_liftComp_left]
  simp only [
    bind_map_left, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left,
    StateT.run'_bind', StateT.run'_pure']
  simp [QueryLog.publicQueries, QueryLog.fst, QueryLog.inl]

/-- Interpreting a standalone extractor beforehand preserves the KS experiment. -/
theorem adaptiveNARGKnowledgeSoundnessExp_simulateExtractor
    {ι κ κE : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {extractorSpec : OracleSpec κE} {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (extractorImpl : QueryImpl extractorSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) WitIn)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExp init impl privateImpl
      ((QueryImpl.id' unifSpec).liftTarget (StateT σ ProbComp)) verifier
      (fun x π tr trV => OptionT.mk (simulateQ extractorImpl (extractor x π tr trV).run)) P =
    adaptiveNARGKnowledgeSoundnessExp init impl privateImpl
      (extractorImpl.liftTarget (StateT σ ProbComp)) verifier extractor P := by
  rw [adaptiveNARGKnowledgeSoundnessExp_liftTarget,
    adaptiveNARGKnowledgeSoundnessExp_liftTarget]
  simp only [OptionT.run_mk, simulateQ_id']

/-! ## State-restoration experiments -/

open OracleComp OracleSpec ProtocolSpec
namespace Verifier.StateRestoration
variable {ι κ : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
  (sampler : QueryImpl privateSpec ProbComp)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem knowledgeSoundnessProverVerifierExp_eq_publicLog
    (V : Verifier oSpec StmtIn StmtOut pSpec) {κ' : Type} {spec : OracleSpec κ'}
    (Q : Prover.StateRestoration.KnowledgeSoundness oSpec spec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessProverVerifierExp (Salt := Salt) V Q = (do
      let ⟨⟨x, messages, witOut⟩, tr⟩ ←
        (fun r : ((StmtIn × Salt) × pSpec.Messages × WitOut) ×
          QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + spec) =>
            (r.1, r.2.publicQueries)) <$> Q.withQueryLog
      let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) x) _
      let ⟨stmtOut, trV⟩ ←
        liftComp (V.run x.1 transcript).run.withQueryLog _
      return (x, witOut, transcript, tr, stmtOut, trV)) := by
  simp only [knowledgeSoundnessProverVerifierExp, withQueryLog, bind_map_left]
  rfl

/-- Compiling a custom sampler preserves the SR soundness experiment. -/
theorem soundnessFailureProb_normalizePrivateCoins (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
    soundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) langIn langOut V
      (normalizePrivateCoins sampler P) =
    soundnessFailureProb (Salt := Salt) init impl sampler langIn langOut V P := by
  simp only [soundnessFailureProb_eq, srSoundnessGame]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  simp only [simulateQ_normalizePrivateCoins]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_add_liftComp_sum_left,
    simulateQ_add_add_liftComp_left, StateT.run'_bind', StateT.run'_pure', map_bind, map_pure]

/-- Compiling a custom sampler preserves SR extraction, including its public-query log. -/
theorem knowledgeSoundnessFailureProb_normalizePrivateCoins
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) E relIn relOut V
      (normalizePrivateCoins sampler P) =
    knowledgeSoundnessFailureProb (Salt := Salt) init impl sampler E relIn relOut V P := by
  simp only [knowledgeSoundnessFailureProb_eq]
  rw [knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt),
    knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt)]
  rw [publicQueries_withQueryLog_normalizePrivateCoins]
  simp only [simulateQ_bind, simulateQ_pure]
  simp only [simulateQ_normalizePrivateCoins]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_map,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left, bind_map_left, bind_assoc,
    pure_bind, StateT.run'_bind', StateT.run'_pure', map_bind, map_pure]

/-- A standard-coin SR soundness premise covers any private sampler with the same move bound. -/
theorem soundnessQueryBounded_apply_sampler
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (error : ENNReal)
    (h : soundnessQueryBounded (Salt := Salt) init impl langIn langOut V (isSrChallengeMove
      (Salt := Salt)) t error) :
    ∀ P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt),
      P.IsQueryBoundP
      (publicQuerySelector (isSrChallengeMove (Salt := Salt) (oSpec := oSpec))) t →
      soundnessFailureProb (Salt := Salt) init impl sampler langIn langOut V P ≤ error := by
  classical
  intro P hP
  rw [← soundnessFailureProb_normalizePrivateCoins (Salt := Salt) init impl sampler]
  apply h
  exact hP.normalizePrivateCoins sampler (isSrChallengeMove (Salt := Salt))

/-- The same SR extractor works after compilation of any custom private prover sampler. -/
theorem knowledgeSoundnessQueryBoundedWithExtractor_apply_sampler
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (error : ENNReal)
    (h : knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init impl relIn relOut V E
      (isSrChallengeMove (Salt := Salt)) t error) :
    ∀ P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt),
      P.IsQueryBoundP
      (publicQuerySelector (isSrChallengeMove (Salt := Salt) (oSpec := oSpec))) t →
      knowledgeSoundnessFailureProb (Salt := Salt) init impl sampler E
        relIn relOut V P ≤ error := by
  classical
  intro P hP
  rw [← knowledgeSoundnessFailureProb_normalizePrivateCoins (Salt := Salt) init impl sampler]
  apply h
  exact hP.normalizePrivateCoins sampler (isSrChallengeMove (Salt := Salt))

end Verifier.StateRestoration

namespace Verifier.StateRestoration

section AmbientSampling

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut Salt : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- Adding a sampling slot to the ambient interface does not strengthen an SR prover:
its samples can all be routed through the private interface. -/
theorem soundnessFailureProb_mergePrivateCoins
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness (oSpec + unifSpec) unifSpec
      StmtIn pSpec (Salt := Salt)) :
    soundnessFailureProb (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec))
      (QueryImpl.id' unifSpec)
      langIn langOut (V.liftOracles (targetSpec := oSpec + unifSpec)) P =
    soundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) langIn langOut V
      P.mergeRight := by
  let challenge := srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)
  have htr (x : StmtIn × Salt) (messages : pSpec.Messages) :=
    simulateQ_deriveTranscriptSR_eq
      ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
        (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) + challenge)
      (impl + challenge) (fun _ => rfl) x messages
  have hmerge := simulateQ_mergeRight impl challenge ((QueryImpl.id' unifSpec).liftTarget _) P
  simp only [soundnessFailureProb_eq, srSoundnessGame]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left]
  simp only [Verifier.liftOracles, Verifier.run]
  rw [hmerge]
  simp only [challenge,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self] at htr
  simp only [htr, OptionT.mk, QueryImpl.simulateQ_add_liftComp_left]
  rfl

/-- A move-bounded SR soundness premise remains valid when private sampling is carried
through an extra ambient slot. The verifier continues to use only its original oracles. -/
theorem soundnessQueryBounded_addPrivateCoins
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (ε : ENNReal)
    (hSR : soundnessQueryBounded (Salt := Salt) init impl langIn langOut V (isSrChallengeMove
      (Salt := Salt)) t ε) :
    soundnessQueryBounded (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec)) langIn langOut
      (V.liftOracles (targetSpec := oSpec + unifSpec)) (isSrChallengeMove (Salt := Salt)) t ε := by
  intro P hP
  change soundnessFailureProb init _ _ langIn langOut _ P ≤ ε
  rw [soundnessFailureProb_mergePrivateCoins (Salt := Salt)]
  apply hSR P.mergeRight
  apply hP.simulateQ_of_step <;> intro q hq <;>
    rcases q with ((q | q) | q) | q <;>
      simp_all [QueryImpl.mergeRight, publicQuerySelector, isSrChallengeMove]

/-- Lift an SR extractor to the temporary ambient sampling interface. Its supplied logs
are projected back to the original public oracles and SR moves. -/
def addPrivateCoinsExtractor
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt)) :
    Extractor.StateRestoration (oSpec + unifSpec) StmtIn WitIn WitOut pSpec (Salt := Salt) :=
  fun x salt w tr log logV => OptionT.mk
    (liftCompLeft (E x salt w tr log.eraseMiddle logV.fst).run)

/-- Merging the prover's two sampling slots preserves the SR extraction-failure probability.
The adapter removes entries from the extra sampling slot before passing the logs to `E`. -/
theorem knowledgeSoundnessFailureProb_mergePrivateCoins
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.KnowledgeSoundness (oSpec + unifSpec) unifSpec
      StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec))
      (QueryImpl.id' unifSpec) (addPrivateCoinsExtractor (Salt := Salt) E) relIn relOut
      (V.liftOracles (targetSpec := oSpec + unifSpec)) P =
    knowledgeSoundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) E relIn relOut V
      P.mergeRight := by
  let challenge := srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)
  have htr (x : StmtIn × Salt) (messages : pSpec.Messages) :=
    simulateQ_deriveTranscriptSR_eq
      ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
        (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) + challenge)
      (impl + challenge) (fun _ => rfl) x messages
  have hlog (x : StmtIn) (tr : pSpec.FullTranscript) :
      (simulateQ loggingOracle
        ((V.liftOracles (targetSpec := oSpec + unifSpec)).run x tr).run).run =
        liftCompLeft (V.run x tr).run.withQueryLog >>= fun z =>
          pure (z.1, QueryLog.inl z.2) :=
    withQueryLog_liftComp_left_of_query (oSpec := oSpec) (spec₂ := unifSpec) (fun _ => rfl)
      (V.run x tr).run
  simp only [knowledgeSoundnessFailureProb_eq]
  rw [knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt) V,
    fst_withQueryLog_mergeRight]
  unfold knowledgeSoundnessProverVerifierExp
  simp only [simulateQ_bind, simulateQ_pure,
    hlog, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left, bind_assoc, pure_bind]
  rw [simulateQ_mergeRight]
  simp only [simulateQ_map, bind_map_left]
  simp only [addPrivateCoinsExtractor, OptionT.run_mk, liftCompLeft,
    QueryImpl.simulateQ_add_liftComp_left]
  simp only [challenge,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self] at htr
  simp only [htr, QueryLog.fst_inl]

/-- The same SR extractor works after routing temporary ambient sampling privately. -/
theorem knowledgeSoundnessQueryBoundedWithExtractor_addPrivateCoins
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (ε : ENNReal)
    (hSR : knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init impl relIn relOut V E
      (isSrChallengeMove (Salt := Salt)) t ε) :
    knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init (impl.addLift (QueryImpl.id'
      unifSpec))
      relIn relOut (V.liftOracles (targetSpec := oSpec + unifSpec))
      (addPrivateCoinsExtractor (Salt := Salt) E) (isSrChallengeMove (Salt := Salt)) t ε := by
  intro P hP
  change knowledgeSoundnessFailureProb init _ _ _ relIn relOut _ P ≤ ε
  rw [knowledgeSoundnessFailureProb_mergePrivateCoins (Salt := Salt)]
  apply hSR P.mergeRight
  apply hP.simulateQ_of_step <;> intro q hq <;>
    rcases q with ((q | q) | q) | q <;>
      simp_all [QueryImpl.mergeRight, publicQuerySelector, isSrChallengeMove]

end AmbientSampling
end Verifier.StateRestoration

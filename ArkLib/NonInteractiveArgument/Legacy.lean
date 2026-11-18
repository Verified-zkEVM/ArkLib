/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.NARG
public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.NonInteractiveArgument.ZeroKnowledge

/-!
# Adapters from legacy OracleReduction interfaces to NARG

These adapters expose a legacy one-message verifier or prover through the protocol-independent
NARG interfaces. Experiment and predicate equivalences preserve the public oracle state,
query budget, and named extractor. Private-coin transport lemmas for the legacy games are
included here. The core NARG modules do not import this adapter.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

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

namespace NARG

/-- Embed a verifier that needs no private coins into the probabilistic interface. -/
def Verifier.ofPublic {ι : Type} {publicSpec : OracleSpec ι}
    {Statement NARGString : Type}
    (V : NonInteractiveVerifier NARGString publicSpec Statement Bool) :
    Verifier publicSpec Statement NARGString where
  verify x proof := (V.liftOracles).verify x (Fin.cons proof (fun i => i.elim0))

section

variable {ι : Type} {publicSpec : OracleSpec ι} {σ Statement Witness NARGString : Type}
  (init : ProbComp σ) (impl : QueryImpl publicSpec (StateT σ ProbComp))

/-- Embedding a public-only verifier preserves its soundness experiment exactly. -/
theorem soundnessExperiment_ofPublic
    (V : NonInteractiveVerifier NARGString publicSpec Statement Bool)
    (P : Prover publicSpec Statement NARGString) :
    soundnessExperiment init impl (Verifier.ofPublic V) P =
      adaptiveNARGSoundnessExp init impl (QueryImpl.id' unifSpec) V P := by
  rw [soundnessExperiment_eq, adaptiveNARGSoundnessExp_eq_option]
  rfl

/-- Embedding a public-only verifier preserves the knowledge-soundness experiment with a
standalone extractor, including both public-query logs. -/
theorem knowledgeSoundnessExperiment_ofPublic
    (V : NonInteractiveVerifier NARGString publicSpec Statement Bool)
    (E : Extractor publicSpec Statement Witness NARGString)
    (P : Prover publicSpec Statement NARGString) :
    knowledgeSoundnessExperiment init impl (Verifier.ofPublic V) E P =
      adaptiveNARGKnowledgeSoundnessExp init impl (QueryImpl.id' unifSpec)
        privateExtractorImpl V E P := by
  simp only [knowledgeSoundnessExperiment_eq, adaptiveNARGKnowledgeSoundnessExp_eq]
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

/-- Adding private verifier randomness commutes with an instance-size acceptance guard. -/
theorem Verifier.ofPublic_restrictSize {ι Statement String : Type} {spec : OracleSpec ι}
    (V : NonInteractiveVerifier String spec Statement Bool) (size : Statement → ℕ) (n : ℕ) :
    Verifier.ofPublic (V.restrictSize size n) = (Verifier.ofPublic V).restrictSize size n := by
  apply Verifier.ext
  funext x proof
  apply OptionT.ext
  simp [Verifier.ofPublic, _root_.Verifier.liftOracles, _root_.Verifier.restrictSize,
    Verifier.restrictSize, OptionT.run_map]

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

namespace Reduction

variable {ιPublic : Type} {publicSpec : OracleSpec ιPublic}
  {StmtIn WitIn Proof : Type}

/-- **[CO25, Definition 7.4]** Expose a one-message ArkLib prover through the prover interface.

The post-protocol output is deliberately not executed: the NARG experiment observes only the
NARG string sent to the verifier. The resulting interface places public oracles before
private sampling. -/
def NonInteractiveProver.toNARGZKProver
    {ιPrivate : Type} {privateSpec : OracleSpec ιPrivate}
    {StmtOut WitOut : Type}
    (prover : NonInteractiveProver Proof (privateSpec + publicSpec)
      StmtIn WitIn StmtOut WitOut) :
    StmtIn → WitIn → OracleComp (publicSpec + privateSpec) Proof :=
  fun stmt wit => OracleComp.swapOracles do
    let state := prover.input (stmt, wit)
    let ⟨proof, _⟩ ← prover.sendMessage ⟨0, rfl⟩ state
    pure proof


end Reduction

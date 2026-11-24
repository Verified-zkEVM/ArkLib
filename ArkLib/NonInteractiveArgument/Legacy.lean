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
NARG interfaces. The experiment equivalences preserve the public oracle state and the named
extractor. Private-coin transport lemmas for the legacy games are included here. The core NARG
modules do not import this adapter.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

/-! ## Adaptive NARG experiments -/

open OracleComp OracleSpec

/-- Execute the prover with uniform private coins, then verify using only public queries. -/
theorem adaptiveNARGSoundnessExp_eq
    {ι : Type} {oSpec : OracleSpec ι} {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp (oSpec + unifSpec) (StmtIn × Proof)) :
    adaptiveNARGSoundnessExp init impl verifier P = (do
      (do
        let ⟨x, π⟩ ← simulateQ
          (impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp)) P
        let output ← simulateQ impl (verifier.verify x (Fin.cons π (fun i => i.elim0))).run
        return output.map (x, ·)).run' (← init)) := by
  simp only [adaptiveNARGSoundnessExp, AdaptiveGame.run, simulateQ_bind, simulateQ_pure,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self, QueryImpl.simulateQ_add_liftComp_left]

/-- A prover with a custom private sampler is a uniform-coin prover: compiling the sampler
gives the soundness experiment in which the original prover samples with `sampler`. -/
theorem adaptiveNARGSoundnessExp_normalizePrivateCoins
    {ι κ : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (sampler : QueryImpl privateSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    adaptiveNARGSoundnessExp init impl verifier (normalizePrivateCoins sampler P) = (do
      (do
        let ⟨x, π⟩ ← simulateQ (impl.addLift sampler : QueryImpl _ (StateT σ ProbComp)) P
        let output ← simulateQ impl (verifier.verify x (Fin.cons π (fun i => i.elim0))).run
        return output.map (x, ·)).run' (← init)) := by
  rw [adaptiveNARGSoundnessExp_eq, simulateQ_normalizePrivateCoins]

private theorem adaptiveNARGKnowledgeSoundnessExp_publicLog
    {ι κ : Type} {oSpec : OracleSpec ι} {spec : OracleSpec κ}
    {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (H : QueryImpl (oSpec + spec) (StateT σ ProbComp))
    (extractorImpl : QueryImpl (oSpec + unifSpec) (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + unifSpec)) WitIn)
    (Q : OracleComp (oSpec + spec) (StmtIn × Proof)) :
    AdaptiveGame.runWithExtractor init H extractorImpl Q.withQueryLog
      (fun a => liftComp (runVerifierWithLog verifier a.1.1 a.1.2) _)
      (fun a v => extractor a.1.1 a.1.2 a.2.publicQueries v.2)
      (fun a v wit => (a.1.1, wit, v.1)) =
    AdaptiveGame.runWithExtractor init H extractorImpl
      ((fun r => (r.1, r.2.publicQueries)) <$> Q.withQueryLog)
      (fun a => liftComp (runVerifierWithLog verifier a.1.1 a.1.2) _)
      (fun a v => extractor a.1.1 a.1.2 a.2 v.2)
      (fun a v wit => (a.1.1, wit, v.1)) := by
  simp only [AdaptiveGame.runWithExtractor, AdaptiveGame.execute, simulateQ_bind, simulateQ_pure,
    bind_assoc, pure_bind, bind_map_left]

/-- A prover with a custom private sampler is a uniform-coin prover for knowledge soundness:
compiling the sampler gives the extraction experiment in which the original prover samples with
`sampler`. The extractor receives the same public query log. -/
theorem adaptiveNARGKnowledgeSoundnessExp_normalizePrivateCoins
    {ι κ : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (sampler : QueryImpl privateSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + unifSpec)) WitIn)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExp init impl verifier extractor
        (normalizePrivateCoins sampler P) =
      AdaptiveGame.runWithExtractor init (impl.addLift sampler)
        (impl.addLift (QueryImpl.id' unifSpec)) P.withQueryLog
        (fun a => liftComp (runVerifierWithLog verifier a.1.1 a.1.2) _)
        (fun a v => extractor a.1.1 a.1.2 a.2.publicQueries v.2)
        (fun a v wit => (a.1.1, wit, v.1)) := by
  rw [adaptiveNARGKnowledgeSoundnessExp, adaptiveNARGKnowledgeSoundnessExp_publicLog,
    adaptiveNARGKnowledgeSoundnessExp_publicLog, publicQueries_withQueryLog_normalizePrivateCoins]
  simp only [AdaptiveGame.runWithExtractor, AdaptiveGame.execute, simulateQ_bind,
    simulateQ_pure]
  simp only [simulateQ_normalizePrivateCoins]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    QueryImpl.simulateQ_add_liftComp_left]

/-- Lift a NARG extractor that makes no public queries to one that may make them. -/
def liftNARGExtractor {ι : Type} {oSpec : OracleSpec ι} {StmtIn Proof WitIn : Type}
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec → OptionT ProbComp WitIn) :
    StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + unifSpec)) WitIn :=
  fun x π logP logV => OptionT.mk (liftComp (extractor x π logP logV).run (oSpec + unifSpec))

/-- An extractor without public queries can run after the public-oracle state is discarded. -/
theorem adaptiveNARGKnowledgeSoundnessExp_liftNARGExtractor
    {ι : Type} {oSpec : OracleSpec ι} {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec → OptionT ProbComp WitIn)
    (P : OracleComp (oSpec + unifSpec) (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExp init impl verifier (liftNARGExtractor extractor) P = (do
      let ⟨x, π, tr, stmtOut, trV⟩ ←
        (simulateQ (impl.addLift (QueryImpl.id' unifSpec) :
            QueryImpl _ (StateT σ ProbComp)) (do
          let ⟨⟨x, π⟩, tr⟩ ← P.withQueryLog
          let ⟨stmtOut, trV⟩ ← liftComp (runVerifierWithLog verifier x π) _
          return (x, π, tr, stmtOut, trV))).run' (← init)
      let witIn ← (extractor x π tr.publicQueries trV).run
      return (x, witIn, stmtOut)) := by
  have hE (x : StmtIn) (π : Proof) (logP logV : QueryLog oSpec) :
      simulateQ (impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp))
        (liftNARGExtractor extractor x π logP logV).run =
        liftM (extractor x π logP logV).run := by
    simp only [liftNARGExtractor, OptionT.run_mk, QueryImpl.addLift_def,
      QueryImpl.simulateQ_add_liftComp_right, simulateQ_liftTarget, simulateQ_id']
  simp only [adaptiveNARGKnowledgeSoundnessExp_eq, hE, StateT.run'_bind', StateT.run'_pure']
  simp [StateT.run'_eq, bind_map_left, map_bind]

/-- Embedding a prover without private queries preserves the soundness experiment. -/
theorem adaptiveNARGSoundnessExp_liftComp
    {ι : Type} {oSpec : OracleSpec ι} {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp oSpec (StmtIn × Proof)) :
    adaptiveNARGSoundnessExp init impl verifier
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
    {ι : Type} {oSpec : OracleSpec ι} {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec → OptionT ProbComp WitIn)
    (P : OracleComp oSpec (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExp init impl verifier (liftNARGExtractor extractor)
      (liftCompLeft P) = (do
      let ⟨x, π, tr, stmtOut, trV⟩ ←
        (simulateQ impl (do
          let ⟨⟨x, π⟩, tr⟩ ← P.withQueryLog
          let ⟨stmtOut, trV⟩ ← runVerifierWithLog verifier x π
          return (x, π, tr, stmtOut, trV))).run' (← init)
      let witIn ← (extractor x π tr trV).run
      return (x, witIn, stmtOut)) := by
  rw [adaptiveNARGKnowledgeSoundnessExp_liftNARGExtractor]
  unfold liftCompLeft
  rw [withQueryLog_liftComp_left]
  simp only [
    bind_map_left, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_left,
    StateT.run'_bind', StateT.run'_pure']
  simp [QueryLog.publicQueries, QueryLog.fst, QueryLog.inl]

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

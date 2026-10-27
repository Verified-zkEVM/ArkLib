/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.OracleReduction.Security.Accumulation
public import VCVio.EvalDist.Monad.Option

/-!
# Soundness from transcript event bounds

Bounds on the actual prover transcript imply ordinary and knowledge soundness when the
verifier rejects outside the bounded event. Deterministic transcript extractors retain their
optional result as a value, so an absent witness counts as extraction failure. The bounds
retain the shared oracle state throughout the actual execution.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
variable {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Expose the prover/verifier boundary in the optional reduction execution. -/
theorem Reduction.run_run_eq_bind
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (reduction.run stmt wit).run = (do
      let pr ← reduction.prover.run stmt wit
      let out ← liftComp (reduction.verifier.run stmt pr.1).run
        (oSpec + [pSpec.Challenge]ₒ)
      pure (out.map (fun v ↦ (pr, v)))) := by
  simp only [Reduction.run, OptionT.run_bind, ← monadLift_liftM_OptionT,
    OptionT.run_monadLift, Option.elimM,
    bind_map_left, Option.elim_some, liftComp_eq_liftM]
  congr 1
  funext pr
  congr 1
  funext out
  cases out <;> rfl

namespace Verifier

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- A transcript-event bound implies ordinary soundness when every transcript outside
the event is rejected outright. The bound and rejection condition are uniform over the
shared oracle state, so no state-reset assumption is used. -/
theorem soundness_of_rejection_event {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (langIn : Set StmtIn) (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (ε : ℝ≥0) (E : StmtIn → pSpec.FullTranscript → Prop)
    (hreject : ∀ stmt ∉ langIn, ∀ tr, ¬ E stmt tr →
      (verifier.run stmt tr).run = pure none)
    (hbound : ∀ (WitIn WitOut : Type) (wit : WitIn)
      (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
      (stmt : StmtIn), stmt ∉ langIn → ∀ os : σ,
      Pr{let x ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (prover.run stmt wit)).run os}[E stmt x.1.1] ≤ ε) :
    verifier.soundness init impl langIn Set.univ ε := by
  classical
  intro WitIn WitOut wit prover stmt hstmt
  dsimp only
  rw [OptionT.prEvent_eq_run]
  apply prEvent_bind_le_of_forall_le_of_support _ _ _
  intro os _
  rw [StateT.run'_eq, prEvent_map, Reduction.run_run_eq_bind, simulateQ_bind, StateT.run_bind]
  refine le_trans ?_ (hbound WitIn WitOut wit prover stmt hstmt os)
  refine prEvent_bind_le_prEvent_of_support
    ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (prover.run stmt wit)).run os)
    _ (fun x ↦ E stmt x.1.1) _ ?_
  intro x _ hx
  have hr := hreject stmt hstmt x.1.1 hx
  simp [hr, simulateQ_pure, StateT.run_pure]

end Verifier

/-- Make a straightline extractor from its optional statement-and-transcript result. -/
def Extractor.Straightline.ofTranscript (e : StmtIn → pSpec.FullTranscript → Option WitIn) :
    Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  fun stmt _ tr _ _ ↦ OptionT.mk (pure (e stmt tr))

private theorem Reduction.ofTranscript_game_eq_map
    {Aux : Type} (R : Reduction oSpec StmtIn Aux StmtOut WitOut pSpec)
    (e : StmtIn → pSpec.FullTranscript → Option WitIn)
    (stmt : StmtIn) (wit : Aux) :
    (do
      let ⟨⟨pr, out⟩, plog, vlog⟩ ← R.runWithLog stmt wit
      let extracted ← liftM
        ((Extractor.Straightline.ofTranscript e) stmt pr.2.2 pr.1 plog.fst vlog).run
      pure (stmt, extracted, out, pr.2.2)) =
    (fun result ↦ (stmt, e stmt result.1.1, result.2, result.1.2.2)) <$> R.run stmt wit := by
  simp only [Extractor.Straightline.ofTranscript, OptionT.run_mk, liftM_pure, bind_pure_comp]
  rw [← Reduction.runWithLog_discard_logs_eq_run]
  simp only [Functor.map_map]
  rfl

/-- A transcript-event bound gives knowledge soundness for the specified deterministic
extractor when every failed extraction outside that event is rejected. The bound is uniform
over input statements, adversarial prover states and shared oracle states. -/
theorem Verifier.knowledgeSoundnessWith_of_transcript_event
    [∀ i, SampleableType (pSpec.Challenge i)] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (e : StmtIn → pSpec.FullTranscript → Option WitIn)
    (ε : NNReal) (E : StmtIn → pSpec.FullTranscript → Prop)
    (hreject : ∀ stmt tr, (∀ p ∈ e stmt tr, (stmt, p) ∉ relIn) → ¬ E stmt tr →
      (V.run stmt tr).run = pure none)
    (hbound : ∀ (Aux : Type) (stmt : StmtIn) (wit : Aux)
      (P : Prover oSpec StmtIn Aux StmtOut WitOut pSpec) (os : σ),
      Pr{let x ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (P.run stmt wit)).run os}[E stmt x.1.1] ≤ ε) :
    V.knowledgeSoundnessWith init impl relIn relOut (Extractor.Straightline.ofTranscript e) ε := by
  intro Aux stmt wit P
  change Pr{let result ← OptionT.mk do
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (do
        let ⟨⟨pr, out⟩, plog, vlog⟩ ← (Reduction.mk P V).runWithLog stmt wit
        let extracted ← liftM
          ((Extractor.Straightline.ofTranscript e) stmt pr.2.2 pr.1 plog.fst vlog).run
        pure (stmt, extracted, out, pr.2.2)).run).run' (← init)}[
      (∀ p ∈ result.2.1, (result.1, p) ∉ relIn) ∧ (result.2.2.1, result.2.2.2) ∈ relOut] ≤ ε
  rw [Reduction.ofTranscript_game_eq_map, OptionT.run_map, simulateQ_map]
  rw [OptionT.prEvent_eq_run]
  apply prEvent_bind_le_of_forall_le_of_support _ _ _
  intro os _
  rw [StateT.run'_eq, prEvent_map, Reduction.run_run_eq_bind,
    simulateQ_bind, StateT.run_map, prEvent_map, StateT.run_bind]
  refine le_trans ?_ (hbound Aux stmt wit P os)
  refine prEvent_bind_le_prEvent_of_support
    ((simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (P.run stmt wit)).run os)
    _ (fun x ↦ E stmt x.1.1) _ ?_
  intro x _ hE
  by_cases hfail : ∀ p ∈ e stmt x.1.1, (stmt, p) ∉ relIn
  · have hr := hreject stmt x.1.1 hfail hE
    simp [hr, simulateQ_pure, StateT.run_pure]
  · simp only [Option.mem_def] at hfail
    rw [bind_pure_comp, simulateQ_map, StateT.run_map, prEvent_map]
    apply prEvent_eq_zero_of_forall_mem_support
    intro a _
    cases a.1 <;> simp [Option.mem_def, hfail]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.OracleReduction.Security.Accumulation
public import VCVio.EvalDist.Monad.Option

/-!
# Soundness from transcript acceptance bounds

A bound on the actual prover transcript implies ordinary soundness whenever rejection
outside the transcript event is the literal failing verifier computation. This avoids
assumptions about correlation with a shared oracle state.
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
  refine (prEvent_bind_le_prEvent_of_support _ _ _ (p := fun x ↦ E stmt x.1.1) ?_).trans
    (hbound WitIn WitOut wit prover stmt hstmt os)
  intro x _ hx
  have hr := hreject stmt hstmt x.1.1 hx
  simp [hr, simulateQ_pure, StateT.run_pure]

end Verifier

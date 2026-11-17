/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Execution.NonInteractive
public import ArkLib.NonInteractiveArgument.FiatShamir.Completeness
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness

/-!
# Completeness with arbitrary error for basic Fiat–Shamir

A shared random oracle preserves the distribution of honest verifier messages. A public salt
changes their keys without changing this distribution.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace CanonicalFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}

/-- Carry a public salt in the input while running the original interactive algorithms. -/
def contextReduction (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Reduction oSpec (StmtIn × Salt) WitIn StmtOut WitOut pSpec where
  prover := contextProver R.prover
  verifier := { verify := fun ctx => R.verifier.verify ctx.1 }

/-- The context adapter leaves interactive execution unchanged. -/
theorem contextReduction_run (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (salt : Salt) (wit : WitIn) :
    ((contextReduction R).run (stmt, salt) wit).run = (R.run stmt wit).run := rfl

variable [VCVCompatible Salt]

/-- The public-salt round executor is the core executor on the statement/salt pair. -/
theorem contextReduction_runToRoundFS
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (salt : Salt) (stmt : StmtIn) (i : Fin (n + 1)) (state : R.prover.PrvState 0) :
    (contextReduction R).prover.runToRoundFS i (stmt, salt) state =
      R.prover.runToRoundFSSalted salt i stmt state := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Expose the honest public-salt execution before interpreting its oracle queries. -/
theorem compileFiatShamir_run_option
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    ((R.compileFiatShamir sampleSalt).run stmt wit).run = (do
      let salt ← liftM sampleSalt
      let (messages, _, st) ← R.prover.runToRoundFSSalted salt (Fin.last n) stmt
        (R.prover.input (stmt, wit))
      let ctx ← liftM (R.prover.output st)
      let tr ← messages.toMessages.deriveTranscriptFS (oSpec := oSpec) (stmt, salt)
      let vr ← liftM (R.verifier.verify stmt tr).run
      pure (vr.map (fun v =>
        ((Fin.cons (salt, messages.toMessages) (fun i => i.elim0), ctx), v))) :
        OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) _).liftComp
          (spec := oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) +
            [(⟨!v[.P_to_V], !v[FSSaltedNARGString pSpec Salt]⟩ :
              ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface)
          (h := ⟨fun q => ⟨Sum.inl q.input, q.cont⟩⟩) := by
  let : ProverOnly
      (⟨!v[.P_to_V], !v[FSSaltedNARGString pSpec Salt]⟩ : ProtocolSpec 1) :=
    { prover_first' := rfl }
  erw [Reduction.run_run_eq_bind,
    Prover.run_of_prover_first stmt wit (R.prover.compileFiatShamir sampleSalt)]
  simp only [Verifier.run, Reduction.compileFiatShamir, Prover.compileFiatShamir,
    Verifier.compileFiatShamir, liftComp_eq_liftM, liftM_bind, liftM_pure,
    bind_assoc, pure_bind]
  simp only [← monadLift_liftM_OptionT, OptionT.run_bind, OptionT.run_monadLift,
    bind_assoc, Option.elimM, bind_map_left, Option.elim_some, monadLift_self, liftM_bind]
  congr 1
  funext salt
  congr 1
  funext x
  rcases x with ⟨messages, stmt', st⟩
  congr 1
  funext ctx
  congr 1
  funext tr
  congr 1
  funext vr
  cases vr <;> simp [Option.getM, funext_iff, Fin.forall_fin_one, MessagesUpTo.toMessages]

set_option backward.isDefEq.respectTransparency false in
/-- Conditioning on the salt identifies the public compiler with the core context compiler. -/
theorem compileFiatShamir_outputs {μ : Type → Type} [Monad μ] [LawfulMonad μ]
    (handler : QueryImpl (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) μ)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    (Option.map (fun x => (x.1.2, x.2))) <$>
      simulateQ (handler + emptyChallengeImpl (FSSaltedNARGString pSpec Salt) μ)
        ((R.compileFiatShamir sampleSalt).run stmt wit).run = (do
      let salt ← simulateQ handler (sampleSalt.liftComp _)
      (Option.map (fun x => (x.1.2, x.2))) <$>
        simulateQ (handler + emptyChallengeImpl pSpec.Messages μ)
          (((contextReduction R).fiatShamir).run (stmt, salt) wit).run) := by
  simp only [compileFiatShamir_run_option, Reduction.fiatShamir_run_option,
    liftComp_eq_liftM, QueryImpl.simulateQ_add_liftM_left, simulateQ_bind,
    simulateQ_pure, map_bind, contextReduction_runToRoundFS, map_pure, Option.map_map]
  rfl

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq (srChallengeOracle (StmtIn × Salt) pSpec).Domain]

local instance : ∀ q : (srChallengeOracle (StmtIn × Salt) pSpec).Domain,
    SampleableType ((srChallengeOracle (StmtIn × Salt) pSpec).Range q) :=
  fun q => inferInstanceAs (SampleableType (pSpec.Challenge q.1))

/-- Shared lazy random functions for the public-salt construction. -/
def randomOracleImpl (impl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      (StateT (Unit × (srChallengeOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp) :=
  FiatShamir.fsRandomOracleImpl (impl.liftTarget (StateT Unit ProbComp))

set_option backward.isDefEq.respectTransparency false in
/-- Conditioning on the salt preserves the initial empty random-oracle cache. -/
theorem compileFiatShamir_randomOracle_split
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    (Option.map (fun x => (x.1.2, x.2))) <$>
      ((simulateQ ((randomOracleImpl impl).addLift challengeQueryImpl : QueryImpl _
        (StateT (Unit × (srChallengeOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
        ((R.compileFiatShamir sampleSalt).run stmt wit).run).run' ((), ∅)) = (do
      let salt ← simulateQ impl sampleSalt
      (Option.map (fun x => (x.1.2, x.2))) <$>
        ((simulateQ ((randomOracleImpl impl).addLift challengeQueryImpl : QueryImpl _
          (StateT (Unit × (srChallengeOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
          (((contextReduction R).fiatShamir).run (stmt, salt) wit).run).run' ((), ∅))) := by
  have hp := compileFiatShamir_outputs (randomOracleImpl impl) R sampleSalt stmt wit
  simp only [addLift_challengeQueryImpl_eq_add_empty (randomOracleImpl impl)]
  have he := congrArg (fun action => action.run' ((), ∅)) hp
  simp only [StateT.run'_eq, StateT.run_map, StateT.run_bind, map_bind,
    Functor.map_map] at he
  rw [show (simulateQ (randomOracleImpl impl) (sampleSalt.liftComp _)).run ((), ∅) =
      (fun salt => (salt, (), (∅ : (srChallengeOracle (StmtIn × Salt) pSpec).QueryCache))) <$>
        simulateQ impl sampleSalt by
    change (simulateQ
      ((impl.liftTarget (StateT Unit ProbComp)).addLift
        (srChallengeOracle (StmtIn × Salt) pSpec).randomOracle : QueryImpl _
          (StateT (Unit × (srChallengeOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
      (liftM sampleSalt)).run ((), ∅) = _
    rw [simulateQ_addLift_run_left]
    simp [simulateQ_liftTarget]] at he
  simpa only [bind_map_left, Function.comp_def, StateT.run'_eq, Functor.map_map] using he

/-- The public-salt compiler preserves the complete honest output distribution. -/
theorem compileFiatShamir_randomOracle_outputs
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    (Option.map (fun x => (x.1.2, x.2))) <$>
      ((simulateQ ((randomOracleImpl impl).addLift challengeQueryImpl : QueryImpl _
        (StateT (Unit × (srChallengeOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
        ((R.compileFiatShamir sampleSalt).run stmt wit).run).run' ((), ∅)) =ᵈ
    (Option.map (fun x => (x.1.2, x.2))) <$>
      ((simulateQ ((impl.liftTarget (StateT Unit ProbComp)).addLift challengeQueryImpl :
        QueryImpl _ (StateT Unit ProbComp)) (R.run stmt wit).run).run' ()) := by
  rw [compileFiatShamir_randomOracle_split]
  let original := (Option.map (fun x => (x.1.2, x.2))) <$>
    ((simulateQ ((impl.liftTarget (StateT Unit ProbComp)).addLift challengeQueryImpl :
      QueryImpl _ (StateT Unit ProbComp)) (R.run stmt wit).run).run' ())
  apply EvalDistEq.trans (my := (do let _ ← simulateQ impl sampleSalt; original))
  · apply EvalDistEq.bind_right
    intro salt
    have h := (contextReduction (Salt := Salt) R).fiatShamir_randomOracle_outputs
      (impl.liftTarget (StateT Unit ProbComp)) (stmt, salt) wit ()
    simpa only [original, randomOracleImpl, StateT.run'_eq, Functor.map_map, Function.comp_def,
      contextReduction_run] using h.map Prod.fst
  · let : MeasurableSpace (Option ((StmtOut × WitOut) × StmtOut)) := ⊤
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)

end CanonicalFS

set_option backward.isDefEq.respectTransparency false in
/-- Basic Fiat–Shamir preserves every completeness error under shared uniform random functions.
The salt sampler uses only the stateless ambient oracles and is called once per NARG string. -/
theorem canonicalFiatShamir_completeness_randomOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut Salt : Type} [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srChallengeOracle (StmtIn × Salt) pSpec).Domain]
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0)
    (h : R.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relIn relOut ε) :
    (R.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srChallengeOracle (StmtIn × Salt) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := StmtIn) (Salt := Salt) impl)
      relIn relOut ε := by
  intro stmt wit hin
  have hd := CanonicalFS.compileFiatShamir_randomOracle_outputs impl R sampleSalt stmt wit
  have hp := hd.prEvent_eq (fun r => r.elim False (fun x =>
    (x.2, x.1.2) ∈ relOut ∧ x.1.1 = x.2))
  have hb := h stmt wit hin
  simp only [OptionT.prEvent_mk, pure_bind] at hb ⊢
  simp only [Functor.map_map, Option.elim_map, Function.comp_def] at hp
  rw [← hp] at hb
  convert hb using 1
  apply congrArg prEvent
  congr 3
  funext q
  rcases q with q | q
  · rfl
  · exact isEmptyElim q.1

/-- Canonical basic Fiat–Shamir preserves arbitrary completeness error at every salt length. -/
theorem fiatShamirSalted_completeness
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut U : Type} [VCVCompatible U] (saltLength : ℕ)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srChallengeOracle (StmtIn × Vector U saltLength) pSpec).Domain]
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0)
    (h : R.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relIn relOut ε) :
    (R.fiatShamirSalted saltLength sampleSalt).completeness
      (pure ((), (∅ : (srChallengeOracle (StmtIn × Vector U saltLength) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := StmtIn)
        (Salt := Vector U saltLength) impl) relIn relOut ε :=
  canonicalFiatShamir_completeness_randomOracle impl R sampleSalt relIn relOut ε h

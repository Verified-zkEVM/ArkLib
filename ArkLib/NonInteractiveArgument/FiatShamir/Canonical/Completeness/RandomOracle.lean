/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.Execution

/-!
# Proof of completeness for canonical Fiat–Shamir in the random-oracle model

A shared random oracle preserves the distribution of honest verifier messages. A public salt
changes their keys without changing this distribution.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace CanonicalFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}

variable [VCVCompatible Salt]

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq (srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain]

local instance : ∀ q : (srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain,
    SampleableType ((srVerifierMessageOracle (StmtIn × Salt) pSpec).Range q) :=
  fun q => inferInstanceAs (SampleableType (pSpec.Challenge q.1))

/-- Shared lazy random functions for the public-salt construction. -/
def randomOracleImpl (impl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
      (StateT (Unit × (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp) :=
  FiatShamir.fsRandomOracleImpl (impl.liftTarget (StateT Unit ProbComp))

/-- Conditioning on the salt preserves the initial empty random-oracle cache. -/
theorem compileFiatShamir_randomOracle_split
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    (Option.map (fun x => (x.1.2, x.2))) <$>
      ((simulateQ ((randomOracleImpl impl).addLift challengeQueryImpl : QueryImpl _
        (StateT (Unit × (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
        ((R.compileFiatShamir sampleSalt).run stmt wit).run).run' ((), ∅)) = (do
      let salt ← simulateQ impl sampleSalt
      (Option.map (fun x => (x.1.2, x.2))) <$>
        ((simulateQ ((randomOracleImpl impl).addLift challengeQueryImpl : QueryImpl _
          (StateT (Unit × (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
          ((R.fiatShamirWithContext (fun x => (x, salt))).run stmt wit).run).run' ((), ∅))) := by
  have hp := compileFiatShamir_outputs (randomOracleImpl impl) R sampleSalt stmt wit
  simp only [addLift_challengeQueryImpl_eq_add_empty (randomOracleImpl impl)]
  have he := congrArg (fun action => action.run' ((), ∅)) hp
  simp only [StateT.run'_eq, StateT.run_map, StateT.run_bind, map_bind,
    Functor.map_map] at he
  rw [show (simulateQ (randomOracleImpl impl) (sampleSalt.liftComp _)).run ((), ∅) =
      (fun salt => (salt, (), (∅ : (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache))) <$>
        simulateQ impl sampleSalt by
    change (simulateQ
      ((impl.liftTarget (StateT Unit ProbComp)).addLift
        (srVerifierMessageOracle (StmtIn × Salt) pSpec).randomOracle : QueryImpl _
          (StateT (Unit × (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
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
        (StateT (Unit × (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache) ProbComp))
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
    have h := R.fiatShamirWithContext_randomOracle_outputs
      (impl.liftTarget (StateT Unit ProbComp)) (fun x => (x, salt)) stmt wit ()
    simpa only [original, randomOracleImpl, StateT.run'_eq, Functor.map_map, Function.comp_def]
      using h.map Prod.fst
  · let : MeasurableSpace (Option ((StmtOut × WitOut) × StmtOut)) := ⊤
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)

end CanonicalFS

/-- Transport interactive completeness along the honest random-oracle execution law. -/
theorem CanonicalFS.completeness_randomOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut Salt : Type} [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain]
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0)
    (h : R.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relIn relOut ε) :
    (R.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache)))
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

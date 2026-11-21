/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.Execution
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Proof of perfect completeness for single-salt Fiat–Shamir

Condition on the fixed challenge table and the sampled salt, then apply the shared
Fiat–Shamir completeness theorem with oracle context `(statement, salt)`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}
  [VCVCompatible Salt] [∀ i, SampleableType (pSpec.Challenge i)]

namespace CanonicalFS

private abbrev fixedImpl (impl : QueryImpl oSpec ProbComp)
    (f : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id) :
    QueryImpl (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) ProbComp :=
  impl + (fun q => pure (f q) : QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) ProbComp)

/-- A sampled fixed table preserves perfect completeness with a stateless ambient handler. -/
theorem perfectCompleteness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (fsInit : ProbComp (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.compileFiatShamir sampleSalt).perfectCompleteness fsInit
      ((impl.liftTarget (StateT (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
        ProbComp)).addLift fsChallengeQueryImpl') relIn relOut := by
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmt wit hin
  rw [OptionT.prEvent_mk_eq_one_iff]
  intro x hx
  simp only [mem_support_bind_iff, StateT.run'_eq, support_map, Set.mem_image] at hx
  obtain ⟨f, _hf, z, hz, rfl⟩ := hx
  rw [simulateQ_readOnly_run (fixed := fun table => fixedImpl impl table +
    emptyChallengeImpl (FSSaltedNARGString pSpec Salt) ProbComp)] at hz
  rotate_left
  · intro q table
    rcases q with (q | q) | q
    · simp [fixedImpl, QueryImpl.addLift_def, QueryImpl.liftTarget]
    · simp [fixedImpl, QueryImpl.addLift_def, QueryImpl.liftTarget, fsChallengeQueryImpl',
        StateT.run]
    · exact isEmptyElim q.1
  obtain ⟨result, hresult, rfl⟩ := mem_support_map_peel _ _ hz
  have hOutput : result.map (fun x => (x.1.2, x.2)) ∈ support
      ((Option.map (fun x => (x.1.2, x.2))) <$>
        simulateQ (fixedImpl impl f + emptyChallengeImpl (FSSaltedNARGString pSpec Salt) ProbComp)
          ((R.compileFiatShamir sampleSalt).run stmt wit).run) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ hresult
  rw [compileFiatShamir_outputs] at hOutput
  obtain ⟨salt, _hsalt, hOutput⟩ := mem_support_bind_peel _ _ hOutput
  obtain ⟨coreResult, hCoreResult, hSame⟩ := mem_support_map_peel _ _ hOutput
  have hCore := fiatShamirWithContext_perfectCompleteness init
    (impl.liftTarget (StateT σ ProbComp)) relIn relOut R (fun x => (x, salt)) h f
  rw [Reduction.perfectCompleteness_eq_prob_one] at hCore
  have hGood := (OptionT.prEvent_mk_eq_one_iff _ _).mp (hCore stmt wit hin)
  obtain ⟨core, hSome, hRel, hAgree⟩ := hGood coreResult (by
    simp only [bind_assoc, pure_bind, mem_support_bind_iff, StateT.run'_eq, support_map,
      Set.mem_image]
    obtain ⟨s, hs⟩ := support_nonempty init
    refine ⟨s, hs, (coreResult, s, f), ?_, rfl⟩
    rw [simulateQ_readOnly_run (fixed := fun state => fixedImpl impl state.2 +
      emptyChallengeImpl pSpec.Messages ProbComp)]
    rotate_left
    · rintro q ⟨s, table⟩
      rcases q with (q | q) | q
      · change (liftM (liftM (impl q) : StateT σ ProbComp _) : StateT _ ProbComp _).run
          (s, table) = (fun x => (x, s, table)) <$> impl q
        rw [StateT.run_liftLeft, StateT.run_monadLift]
        simp only [monadLift_self, bind_pure_comp, Functor.map_map]
      · change (do
          let a ← (pure (table q, table) : ProbComp _)
          pure (a.1, s, a.2)) = (fun x => (x, s, table)) <$> pure (table q)
        simp only [pure_bind, map_pure]
      · exact isEmptyElim q.1
    rw [support_map]
    exact ⟨coreResult, hCoreResult, rfl⟩)
  rw [hSome] at hSame
  cases result with
  | none => simp at hSame
  | some result =>
    refine ⟨result, rfl, ?_⟩
    have hPair : (core.1.2, core.2) = (result.1.2, result.2) := Option.some.inj hSame.symm
    obtain ⟨hOut, hVerdict⟩ := Prod.mk.inj hPair
    change (result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2
    rw [← hOut, ← hVerdict]
    exact ⟨hRel, hAgree⟩

end CanonicalFS

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.Shared
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Construction
public import ArkLib.OracleReduction.Security.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Single-salt Fiat–Shamir completeness proofs

Conditioning on the sampled salt reduces the honest run to the shared context compiler.
The fixed-oracle and random-oracle proofs use this execution law to establish completeness.
The application results carry the random-oracle bound to the honest protocol API and
its byte encoding.

## Main results

* `CanonicalFS.compileFiatShamir_outputs` relates the outputs conditional on the salt to
  those of the shared compiler.
* `CanonicalFS.emptySalt_run_eq` relates the zero-length and unsalted executions after
  erasing the empty salt from the keys and proof.
* `CanonicalFS.perfectCompleteness` and `CanonicalFS.completeness_randomOracle` prove the
  fixed-oracle and lazy random-oracle bounds.
* `CanonicalFS.compileFiatShamir_application_completeness` and
  `CanonicalFS.compileFiatShamirBytes_completeness` prove the application bounds.
-/

@[expose] public section

section Execution

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolSpec

/-- The challenge handler of a one-message, prover-only protocol. -/
def emptyChallengeImpl (Message : Type) (μ : Type → Type) :
    QueryImpl
      ([(⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface) μ :=
  fun q => isEmptyElim q.1

/-- Lifting a random challenge handler adds no behavior to a one-message protocol. -/
theorem addLift_challengeQueryImpl_eq_add_empty
    {ι : Type} {oSpec : OracleSpec ι} {μ : Type → Type} [MonadLiftT ProbComp μ]
    (handler : QueryImpl oSpec μ) (Message : Type)
    [∀ i, SampleableType ((⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge i)] :
    (handler.addLift challengeQueryImpl : QueryImpl
      (oSpec +
        [(⟨!v[.P_to_V], !v[Message]⟩ : ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface) μ) =
      handler + emptyChallengeImpl Message μ := by
  funext q
  rcases q with q | q
  · rfl
  · exact isEmptyElim q.1

end ProtocolSpec

namespace CanonicalFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}

variable [VCVCompatible Salt]

/-- Expose the honest public-salt execution before interpreting its oracle queries. -/
theorem compileFiatShamir_run_option
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    ((R.compileFiatShamir sampleSalt).run stmt wit).run = (do
      let salt ← liftM sampleSalt
      let (messages, _, st) ← R.prover.runToRoundFS (Fin.last n) (stmt, salt)
        (R.prover.input (stmt, wit))
      let ctx ← liftM (R.prover.output st)
      let tr ← messages.toMessages.deriveTranscriptFS (oSpec := oSpec) (stmt, salt)
      let vr ← liftM (R.verifier.verify stmt tr).run
      pure (vr.map (fun v =>
        ((Fin.cons (salt, messages.toMessages) (fun i => i.elim0), ctx), v))) :
        OracleComp (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) _).liftComp
          (spec := oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec)
          ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) +
            [(⟨!v[.P_to_V], !v[FSSaltedNARGString pSpec Salt]⟩ :
              ProtocolSpec 1).Challenge]ₒ'challengeOracleInterface)
          (h := ⟨fun q => ⟨Sum.inl q.input, q.cont⟩⟩) := by
  let : ProverOnly
      (⟨!v[.P_to_V], !v[FSSaltedNARGString pSpec Salt]⟩ : ProtocolSpec 1) :=
    { prover_first' := rfl }
  erw [Reduction.run_run_eq_bind,
    Prover.run_of_prover_first stmt wit (R.prover.compileFiatShamir sampleSalt)]
  simp only [Verifier.run, Reduction.compileFiatShamir, Prover.compileFiatShamir,
    Prover.compileFiatShamirWith, CanonicalFS.compileProof, Verifier.compileFiatShamir,
    fsSaltedVerify, Verifier.verifyFiatShamir,
    liftComp_eq_liftM, liftM_bind, liftM_pure,
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

/-- Conditioning on the salt identifies the public compiler with the core context compiler. -/
theorem compileFiatShamir_outputs {μ : Type → Type} [Monad μ] [LawfulMonad μ]
    (handler : QueryImpl (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) μ)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : StmtIn) (wit : WitIn) :
    (Option.map (fun x => (x.1.2, x.2))) <$>
      simulateQ (handler + emptyChallengeImpl (FSSaltedNARGString pSpec Salt) μ)
        ((R.compileFiatShamir sampleSalt).run stmt wit).run = (do
      let salt ← simulateQ handler (sampleSalt.liftComp _)
      (Option.map (fun x => (x.1.2, x.2))) <$>
        simulateQ (handler + emptyChallengeImpl pSpec.Messages μ)
          ((R.fiatShamirWithContext (fun x => (x, salt))).run stmt wit).run) := by
  simp only [compileFiatShamir_run_option, Reduction.fiatShamirWithContext_run_option,
    liftComp_eq_liftM, QueryImpl.simulateQ_add_liftM_left, simulateQ_bind,
    simulateQ_pure, map_bind, map_pure, Option.map_map]
  rfl

section EmptySalt

variable {U : Type} {μ : Type → Type} [Monad μ] [LawfulMonad μ]

/-- Interpret a verifier-message query carrying an empty salt at its unsalted key. -/
def withEmptySalt (handler : QueryImpl (fsVerifierMessageOracle StmtIn pSpec) μ) :
    QueryImpl (canonicalFSOracle StmtIn pSpec U 0) μ :=
  fun ⟨i, (stmt, _), messages⟩ => handler ⟨i, stmt, messages⟩

variable (base : QueryImpl oSpec μ) (challenge : QueryImpl (fsVerifierMessageOracle StmtIn pSpec) μ)

private theorem runToRoundFS_emptySalt
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : Fin (n + 1)) (stmt : StmtIn) (st : P.PrvState 0) :
    simulateQ (base + withEmptySalt (U := U) challenge)
      (P.runToRoundFS i (stmt, #v[]) st) =
    (fun z => (z.1, (z.2.1, (#v[] : Vector U 0)), z.2.2)) <$>
      simulateQ (base + challenge) (P.runToRoundFS i stmt st) := by
  induction i using Fin.induction with
  | zero =>
    simp only [Prover.runToRoundFS, Fin.induction_zero, simulateQ_pure, map_pure]
  | succ j ih =>
    rw [Prover.runToRoundFS_succ, Prover.runToRoundFS_succ,
      Prover.processRoundFS_bind, Prover.processRoundFS_bind,
      simulateQ_bind, simulateQ_bind, ih, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨messages, context, state⟩
    simp only [Prover.processRoundFS, pure_bind]
    split <;> simp only [simulateQ_bind, QueryImpl.simulateQ_add_liftM_left,
      HasQuery.instOfMonadLift_query, QueryImpl.simulateQ_add_liftM_query_right,
      withEmptySalt, simulateQ_pure, map_bind, map_pure]; rfl

private theorem deriveTranscript_emptySalt
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) :
    simulateQ (base + withEmptySalt (U := U) challenge)
      (messages.deriveTranscriptSRAux (stmt, #v[]) k j) =
    simulateQ (base + challenge) (messages.deriveTranscriptSRAux stmt k j) := by
  induction j using Fin.induction with
  | zero => simp only [MessagesUpTo.deriveTranscriptSRAux_zero, simulateQ_pure]
  | succ j ih =>
    rw [MessagesUpTo.deriveTranscriptSRAux_succ, MessagesUpTo.deriveTranscriptSRAux_succ,
      simulateQ_bind, simulateQ_bind, ih]
    apply bind_congr
    intro tr
    split
    · simp only [simulateQ_bind, simulateQ_pure, HasQuery.instOfMonadLift_query,
        QueryImpl.simulateQ_add_liftM_query_right, withEmptySalt]
      rfl
    · rfl

private theorem deriveFullTranscript_emptySalt
    (stmt : StmtIn) (messages : pSpec.Messages) :
    simulateQ (base + withEmptySalt (U := U) challenge)
      (messages.deriveTranscriptFS (stmt, #v[])) =
    simulateQ (base + challenge) (messages.deriveTranscriptFS stmt) :=
  deriveTranscript_emptySalt base challenge stmt (Fin.last n) messages.asUpTo
    (Fin.last (Fin.last n))

/-- With a pure empty salt, the compiled executions agree under the same ambient handler and
the challenge handler with its keys relabelled. The result forgets the empty salt in the proof.
The target monad can retain arbitrary state and all oracle effects. -/
theorem emptySalt_run_eq [VCVCompatible U]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    (Option.map (fun z => ((z.1.1 0).2, z.1.2, z.2))) <$>
      simulateQ ((base + withEmptySalt (U := U) challenge) +
        emptyChallengeImpl (FiatShamirNARGString pSpec U 0) μ)
        ((R.fiatShamirSalted 0 (pure #v[])).run stmt wit).run =
    (Option.map (fun z => (z.1.1 0, z.1.2, z.2))) <$>
      simulateQ ((base + challenge) + emptyChallengeImpl pSpec.Messages μ)
        (R.fiatShamir.run stmt wit).run := by
  simp only [Reduction.fiatShamirSalted, compileFiatShamir_run_option,
    Reduction.fiatShamir_run_option, liftM_pure, pure_bind, liftComp_eq_liftM,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  rw [runToRoundFS_emptySalt (U := U) base challenge, bind_map_left]
  apply bind_congr
  rintro ⟨messages, context, state⟩
  rw [deriveFullTranscript_emptySalt (U := U) base challenge stmt messages.toMessages]
  simp only [Option.map_map, Function.comp_def, Fin.cons_zero, Messages.fsTranscript]

end EmptySalt

end CanonicalFS

end Execution

section FixedOracle

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

end FixedOracle

section RandomOracle

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

end RandomOracle

section Application

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness Salt U σ : Type}

/-- The typed protocol compiler and compatibility compiler have the same completeness event. -/
theorem InteractiveProtocol.compileFiatShamir_completeness_iff [VCVCompatible Salt]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (init : ProbComp σ)
    (impl : QueryImpl (oSpec + fsVerifierMessageOracle (Statement × Salt) pSpec)
      (StateT σ ProbComp))
    (relation : Set (Statement × Witness)) (ε : ℝ≥0) :
    (P.toReduction.compileFiatShamir sampleSalt).completeness init impl relation acceptRejectRel ε ↔
      (P.compileFiatShamir sampleSalt).completeness init impl relation ε := by
  simp only [Reduction.completeness, NonInteractiveArgument.completeness, OptionT.prEvent_eq_run]
  apply forall_congr'
  intro stmt
  apply forall_congr'
  intro wit
  apply imp_congr_right
  intro _
  rw [CanonicalFS.compileFiatShamir_run_option]
  simp only [liftComp_eq_liftM, QueryImpl.simulateQ_addLift_liftM_left]
  simp [InteractiveProtocol.toReduction,
    InteractiveProver.toReductionProver, InteractiveVerifier.toReductionVerifier,
    NonInteractiveArgument.run, InteractiveProtocol.compileFiatShamir,
    InteractiveProver.compileFiatShamir, InteractiveVerifier.compileFiatShamir,
    acceptRejectRel, OptionT.lift, MessagesUpTo.toMessages]

/-- The typed basic Fiat–Shamir argument preserves arbitrary interactive completeness error. -/
theorem CanonicalFS.compileFiatShamir_application_completeness [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Salt) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec Salt)
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (Statement × Salt) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement) (Salt := Salt) impl)
      relation ε := by
  apply (P.compileFiatShamir_completeness_iff sampleSalt _ _ relation ε).mp
  exact CanonicalFS.completeness_randomOracle impl P.toReduction sampleSalt
    relation acceptRejectRel ε ((P.toReduction_completeness_iff _ _ _ _).mpr h)

/-- Canonical byte serialization adds no completeness error to basic Fiat–Shamir. -/
theorem CanonicalFS.compileFiatShamirBytes_completeness [VCVCompatible U] (saltLength : ℕ)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.compileFiatShamirBytes saltLength serializer sampleSalt).completeness
      (pure ((),
        (∅ : (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement)
        (Salt := Vector U saltLength) impl) relation ε := by
  rw [InteractiveProtocol.compileFiatShamirBytes, NonInteractiveArgument.serialize_completeness_iff]
  exact CanonicalFS.compileFiatShamir_application_completeness P impl sampleSalt relation ε h

end Application

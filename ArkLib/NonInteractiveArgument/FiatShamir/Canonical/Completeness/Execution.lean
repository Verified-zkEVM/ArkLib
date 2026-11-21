/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.Shared
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Construction

/-!
# Conditioning single-salt Fiat–Shamir on the sampled salt

## Main results

* `CanonicalFS.compileFiatShamir_run_option` exposes the oracle computation of the honest run.
* `CanonicalFS.compileFiatShamir_outputs` identifies the outputs conditional on the salt with
  those of the shared compiler using the corresponding oracle context.
* `CanonicalFS.emptySalt_run_eq` identifies the zero-salt compiler with the unsalted compiler
  after erasing the empty salt from the keys and proof.
-/

@[expose] public section

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

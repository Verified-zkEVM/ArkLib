/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.RoundByRound
public import Mathlib.Algebra.BigOperators.Intervals
public import VCVio.EvalDist.Monad.Branch
public import VCVio.EvalDist.Monad.Option

/-!
# Round-by-round soundness implies ordinary soundness

The soundness theorem bounds the actual interpreted native executor by the sum of the local
challenge errors. The prover is an arbitrary native strategy, including probabilistic private
continuations and interpreted effects that fail to return. The ambient interpreter uses VCVio's
existing lawful subprobability semantics; no normalization is assumed.

The uniform corollary gives `count * error`. The initial state law applies only to false inputs,
so the zero-challenge case is covered without imposing initial falsity on true inputs.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree
open scoped ENNReal

namespace Interaction.Oracle.Security

universe v

set_option backward.isDefEq.respectTransparency false in
/-- The actual interpreted native executor can reach a true terminal state from a false current
state with probability at most the sum of its remaining challenge errors.

The embedding retains the concrete authored prefix when restricting to a continuation.
Prover and verifier node effects are the existing native actions; failures remove mass.
The verifier challenge marginal is charged once, and the false successor is bounded by induction.
-/
theorem executeStrategies_state_bound {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (handler : QueryImpl ambient m) {protocol : Protocol} (model : ChallengeModel protocol)
    (state : ExecutionPrefix protocol.tree → Prop) (rank : ExecutionPrefix protocol.tree → ℕ)
    (error : ℕ → ℝ≥0∞) (count : ℕ) (hlocal : LocalSoundness model state rank error)
    (tree : TypeTree) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV)
    (embed : ExecutionPrefix tree → ExecutionPrefix protocol.tree)
    (hprover : ProverPreserves tree roles (fun pfx => state (embed pfx)))
    (hschedule : ChallengeSchedule tree roles (fun pfx => rank (embed pfx)) count)
    (hfresh : FreshVerifier model ambient handler tree roles oracles initial impl OutV
      verifier embed)
    (hfalse : ¬ state (embed (.root tree))) :
    Pr{let result ← (simulateQ handler
      (executeStrategies ambient tree roles oracles initial impl prover verifier))}[
      state (embed (.ofExecutionPath result.1))] ≤
      ∑ j ∈ Finset.Ico (rank (embed (.root tree))) count, error j := by
  induction tree generalizing initial with
  | done =>
    cases roles
    cases oracles
    rw [executeStrategies_done]
    simp only [simulateQ_bind, simulateQ_pure]
    simp only [ExecutionPrefix.ofExecutionPath, hfalse, prEvent_false, zero_le]
  | «public» Moves rest ih =>
    rcases roles with ⟨role, roles⟩
    cases role with
    | sender =>
      rw [executeStrategies_public_sender]
      simp only [simulateQ_bind, simulateQ_pure]
      apply prEvent_bind_le_of_forall_le_of_support
      intro chosen hchosen
      apply prEvent_bind_le_of_forall_le_of_support
      intro next hnext
      have hfalseNext : ¬ state (embed (ExecutionPrefix.prependPublic chosen.1
          (.root (rest chosen.1)))) :=
        fun h => hfalse (hprover.1 rfl chosen.1 h)
      have bound := ih chosen.1 (roles chosen.1) (oracles.2 chosen.1) initial impl
        (OutP := fun path => OutP ⟨chosen.1, path⟩)
        (OutV := fun path => OutV ⟨chosen.1, path⟩)
        chosen.2 next (fun pfx => embed (ExecutionPrefix.prependPublic chosen.1 pfx))
        (hprover.2 chosen.1) (hschedule.2 chosen.1) (hfresh chosen.1 next hnext) hfalseNext
      simpa only [bind_assoc, pure_bind,
        ExecutionPrefix.ofExecutionPath_public, hschedule.1 chosen.1] using bound
    | receiver =>
      rw [executeStrategies_public_receiver]
      simp only [simulateQ_bind, simulateQ_pure]
      let action := simulateQ handler
        (simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier)
      let after := fun chosen : (move : Moves) ×
          Verifier.Strategy ambient (rest move) (roles move) (oracles.2 move) initial
            (fun path => OutV ⟨move, path⟩) =>
        state (embed (ExecutionPrefix.prependPublic chosen.1 (.root (rest chosen.1))))
      obtain ⟨hturn, ⟨encode, heq, hextend⟩, hnext⟩ := hfresh
      have hstep : Pr{let chosen ← action}[after chosen] ≤
          error (rank (embed (.root (.public Moves rest)))) := by
        have h := (RoundByRound.GameFamily.isBounded_iff _ _).mp hlocal
          ⟨embed (.root _), hturn⟩ ()
        change Pr{let result ← model.sample (embed (.root _))}[
          ¬ state (embed (.root _)) ∧ state (model.extend (embed (.root _)) result)] ≤ _ at h
        rw [← heq (fun result =>
          ¬ state (embed (.root _)) ∧ state (model.extend (embed (.root _)) result))] at h
        simpa only [hfalse, not_false_eq_true, true_and, hextend, action, after] using h
      have htail := prEvent_bind_le_prEvent_add_of_support action
        (fun chosen => do
          let next ← simulateQ handler (prover chosen.1)
          let result ← simulateQ handler (executeStrategies ambient (rest chosen.1) (roles chosen.1)
            (oracles.2 chosen.1) initial impl
            (OutP := fun path => OutP ⟨chosen.1, path⟩)
            (OutV := fun path => OutV ⟨chosen.1, path⟩) next chosen.2)
          return (⟨⟨chosen.1, result.1⟩, result.2.1, result.2.2⟩ :
            (path : (TypeTree.public Moves rest).ExecutionPath) ×
              OutP path × OutV path.toBranchPath))
        after (fun result => state (embed (.ofExecutionPath result.1)))
        (ε := ∑ j ∈ Finset.Ico (rank (embed (.root (.public Moves rest))) + 1) count, error j)
        (by
          intro chosen hchosen hfalseNext
          apply prEvent_bind_le_of_forall_le_of_support
          intro next hsupport
          have bound := ih chosen.1 (roles chosen.1) (oracles.2 chosen.1) initial impl
            (OutP := fun path => OutP ⟨chosen.1, path⟩)
            (OutV := fun path => OutV ⟨chosen.1, path⟩)
            next chosen.2 (fun pfx => embed (ExecutionPrefix.prependPublic chosen.1 pfx))
            (hprover.2 chosen.1) (hschedule.2 chosen.1) (hnext chosen hchosen) hfalseNext
          simpa only [bind_assoc, pure_bind,
            ExecutionPrefix.ofExecutionPath_public, hschedule.1.2 chosen.1] using bound)
      exact htail.trans ((add_le_add hstep le_rfl).trans (le_of_eq
        (Finset.sum_eq_sum_Ico_succ_bot hschedule.1.1 error).symm))
  | «oracle» Messages rest ih =>
    rw [executeStrategies_oracle]
    simp only [simulateQ_bind, simulateQ_pure]
    apply prEvent_bind_le_of_forall_le_of_support
    intro chosen hchosen
    apply prEvent_bind_le_of_forall_le_of_support
    intro next hnext
    have hfalseNext : ¬ state (embed (ExecutionPrefix.prependOracle chosen.1
        (.root (rest PUnit.unit)))) :=
      fun h => hfalse (hprover.1 chosen.1 h)
    have bound := ih (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
      (Access.extend initial oracles.1) (Access.extendImpl initial oracles.1 impl chosen.1)
      (OutP := fun path => OutP ⟨chosen.1, path⟩)
      (OutV := fun path => OutV ⟨PUnit.unit, path⟩)
      chosen.2 next (fun pfx => embed (ExecutionPrefix.prependOracle chosen.1 pfx))
      (hprover.2 chosen.1) (hschedule.2 chosen.1) (hfresh chosen.1 next hnext) hfalseNext
    simpa only [bind_assoc, pure_bind,
      ExecutionPrefix.ofExecutionPath_oracle, hschedule.1 chosen.1] using bound

/-- Round-by-round local soundness bounds ordinary soundness of actual native execution. -/
theorem executeStrategies_soundness {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (handler : QueryImpl ambient m) {protocol : Protocol} {input : Prop}
    {output : protocol.tree.ExecutionPath → Prop}
    (certificate : OrdinaryState protocol input output) (model : ChallengeModel protocol)
    (rank : ExecutionPrefix protocol.tree → ℕ) (error : ℕ → ℝ≥0∞) (count : ℕ)
    (hroot : rank (.root protocol.tree) = 0)
    (hschedule : ChallengeSchedule protocol.tree protocol.roles rank count)
    (hlocal : ¬ input → LocalSoundness model certificate.state rank error)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    {OutP : protocol.tree.ExecutionPath → Type} {OutV : protocol.tree.BranchPath → Type}
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles
      initial OutV)
    (hfresh : FreshVerifier model ambient handler protocol.tree protocol.roles protocol.oracles
      initial impl OutV verifier id) (hfalse : ¬ input) :
    Pr{let result ← (simulateQ handler (executeStrategies ambient protocol.tree protocol.roles
      protocol.oracles initial impl prover verifier))}[output result.1] ≤
      ∑ j ∈ Finset.range count, error j := by
  have bound := executeStrategies_state_bound ambient handler model certificate.state rank error
    count (hlocal hfalse) protocol.tree protocol.roles protocol.oracles initial impl prover
    verifier id certificate.prover hschedule hfresh (certificate.initial hfalse)
  have terminal := prEvent_mono
    (simulateQ handler (executeStrategies ambient protocol.tree protocol.roles protocol.oracles
      initial impl prover verifier)) (fun result => output result.1)
    (fun result => certificate.state (.ofExecutionPath result.1))
    (fun result h => certificate.terminal result.1 h)
  exact terminal.trans (by simpa only [id_eq, hroot, Nat.Ico_zero_eq_range] using bound)

/-- The uniform-error corollary is `count * error`, including the zero-challenge case. -/
theorem executeStrategies_soundness_uniform {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (handler : QueryImpl ambient m) {protocol : Protocol} {input : Prop}
    {output : protocol.tree.ExecutionPath → Prop}
    (certificate : OrdinaryState protocol input output) (model : ChallengeModel protocol)
    (rank : ExecutionPrefix protocol.tree → ℕ) (error : ℝ≥0∞) (count : ℕ)
    (hroot : rank (.root protocol.tree) = 0)
    (hschedule : ChallengeSchedule protocol.tree protocol.roles rank count)
    (hlocal : ¬ input → LocalSoundness model certificate.state rank (fun _ => error))
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    {OutP : protocol.tree.ExecutionPath → Type} {OutV : protocol.tree.BranchPath → Type}
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles
      initial OutV)
    (hfresh : FreshVerifier model ambient handler protocol.tree protocol.roles protocol.oracles
      initial impl OutV verifier id) (hfalse : ¬ input) :
    Pr{let result ← (simulateQ handler (executeStrategies ambient protocol.tree protocol.roles
      protocol.oracles initial impl prover verifier))}[output result.1] ≤
      (count : ℝ≥0∞) * error := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    executeStrategies_soundness ambient handler certificate model rank (fun _ => error) count
      hroot hschedule hlocal initial impl prover verifier hfresh hfalse

/-- Averaging the local bound over an author that may fail does not increase its error.

The author returns a small index before the fresh challenge. Mapping that index to a concrete
prefix only accommodates universes; the local hypothesis still covers every authored prefix,
without a reachability or positive-mass restriction. All selected prefixes have the specified
challenge rank, and author failure contributes missing mass. -/
theorem LocalSoundness.random_prefix {protocol : Protocol} {model : ChallengeModel protocol}
    {state : ExecutionPrefix protocol.tree → Prop} {rank : ExecutionPrefix protocol.tree → ℕ}
    {error : ℕ → ℝ≥0∞} (hlocal : LocalSoundness model state rank error) {α : Type}
    (author : OptionT ProbComp α)
    (authoredPrefix : α →
      {pfx : ExecutionPrefix protocol.tree // IsVerifierPrefix protocol.roles pfx})
    (round : ℕ) (hrank : ∀ a, rank (authoredPrefix a).val = round) :
    Pr{let escape ← (author >>= fun a =>
      (fun r => ¬ state (authoredPrefix a).val ∧ state (model.extend (authoredPrefix a).val r)) <$>
        OptionT.lift (model.sample (authoredPrefix a).val))}[escape] ≤ error round := by
  have bound := prEvent_bind_le_of_forall_le author
    (fun a => (fun r => ¬ state (authoredPrefix a).val ∧
      state (model.extend (authoredPrefix a).val r)) <$>
        OptionT.lift (model.sample (authoredPrefix a).val)) id (ε := error round) (by
      intro a
      rw [prEvent_map, OptionT.prEvent_lift]
      have h := (RoundByRound.GameFamily.isBounded_iff _ _).mp hlocal (authoredPrefix a) ()
      simpa only [localGames, hrank, id_eq] using h)
  simpa only [id_eq, bind_pure] using bound

end Interaction.Oracle.Security

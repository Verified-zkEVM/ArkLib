/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.Append.Security

/-!
# Ordinary soundness composition without ambient oracles

In the plain model the only oracle queries are independent protocol challenges. The entire game
is independent of the auxiliary oracle state and its initialization, so both component bounds may
use the same initialization.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {Stmt₁ Stmt₂ Stmt₃ : Type} {m n : ℕ} {pSpec₁ : ProtocolSpec m}
  {pSpec₂ : ProtocolSpec n} [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

private def emptyChallengeImpl : QueryImpl ([]ₒ + [pSpec₁.Challenge]ₒ) ProbComp
  | .inl t => isEmptyElim t
  | .inr t => challengeQueryImpl t

private theorem simulateQ_empty_challenges {α : Type}
    (oa : OracleComp ([]ₒ + [pSpec₁.Challenge]ₒ) α) :
    simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) oa =
      liftM (simulateQ emptyChallengeImpl oa) := by
  rw [← simulateQ_liftTarget]
  congr 1
  funext t
  cases t with
  | inl t => exact isEmptyElim t
  | inr t => rfl

private theorem simulateQ_empty_challenges_run' {α : Type}
    (oa : OracleComp ([]ₒ + [pSpec₁.Challenge]ₒ) α) (s : σ) :
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp)) oa).run' s =
      simulateQ emptyChallengeImpl oa := by
  rw [simulateQ_empty_challenges]
  simp [StateT.run'_eq, StateT.run_monadLift, bind_pure_comp, Functor.map_map]

/-- Without ambient queries, changing the initial oracle state distribution does not change
ordinary soundness. This applies to rejecting and accepting verifiers alike. -/
theorem soundness_empty_init_iff (V : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁)
    (init' : ProbComp σ) {L₁ : Set Stmt₁} {L₂ : Set Stmt₂} {ε : ℝ≥0} :
    V.soundness init impl L₁ L₂ ε ↔ V.soundness init' impl L₁ L₂ ε := by
  unfold soundness
  simp only [simulateQ_empty_challenges_run', OptionT.prEvent_eq_run, OptionT.run_mk,
    map_bind, OracleComp.prEvent_bind_const]

/-- In the plain model, the component soundness bounds may share one initialization. A fallback
is needed only to describe the first verifier's unused output when it rejects. -/
theorem append_soundness_of_empty {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier []ₒ Stmt₂ Stmt₃ pSpec₂)
    (fallback : Stmt₁ → Stmt₂) {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  let := (GuardedForm.ofEmpty V₁ fallback).isGuarded
  exact append_soundness V₁ V₂ h₁ fun s =>
    (soundness_empty_init_iff V₂ (pure s)).mp h₂

end Verifier

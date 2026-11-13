/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.Append.Security

/-!
# Ordinary soundness and knowledge soundness without ambient oracles

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

/-- In the plain model, the component soundness bounds may share one initialization,
even when the intermediate statement type is empty. -/
theorem append_soundness_of_empty {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier []ₒ Stmt₂ Stmt₃ pSpec₂)
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂) :
    (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  classical
  by_cases h : Nonempty Stmt₂
  · let := (GuardedForm.ofEmpty V₁ (fun _ => Classical.choice h)).isGuarded
    exact append_soundness V₁ V₂ h₁ fun s =>
      (soundness_empty_init_iff V₂ (pure s)).mp h₂
  · have hrun (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) : V₁.run stmt tr = pure none := by
      rw [eq_pure_runEmpty (V₁.run stmt tr)]
      congr 1
      cases he : (V₁.run stmt tr).runEmpty with
      | none => rfl
      | some x => exact (h ⟨x⟩).elim
    rw [soundness_iff_run]
    intro Aux Out wit P stmt _
    apply prEvent_bind_le_of_forall_le
    intro z
    have hc : ((V₁.append V₂).run stmt z.1.1).run = pure none := by
      simp only [Verifier.append_run, OptionT.run_bind]
      change ((V₁.run stmt z.1.1.fst).run >>= fun x => _) = _
      rw [hrun]
      rfl
    change Pr{let v ← (simulateQ impl ((V₁.append V₂).run stmt z.1.1).run).run z.2}[
      v.1.elim False (fun v => v ∈ lang₃)] ≤ _
    rw [hc]
    simp


/-- Without ambient queries, changing the initial oracle state distribution leaves the named
knowledge-soundness game unchanged, including its extractor. -/
theorem knowledgeSoundnessWith_empty_init_iff {Wit₁ Wit₂ : Type}
    (V : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁) (init' : ProbComp σ)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {E : Extractor.Straightline []ₒ Stmt₁ Wit₁ Wit₂ pSpec₁} {ε : ℝ≥0} :
    V.knowledgeSoundnessWith init impl rel₁ rel₂ E ε ↔
      V.knowledgeSoundnessWith init' impl rel₁ rel₂ E ε := by
  unfold knowledgeSoundnessWith
  simp only [simulateQ_empty_challenges_run', OptionT.prEvent_eq_run, OptionT.run_mk,
    map_bind, OracleComp.prEvent_bind_const]

/-- In the plain model, pure extractors compose with both component bounds at the same
initialization. The fallback describes the guarded output on rejecting transcripts. -/
theorem append_knowledgeSoundnessWith_of_empty {Wit₁ Wit₂ Wit₃ : Type}
    (V₁ : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier []ₒ Stmt₂ Stmt₃ pSpec₂)
    (fallback : Stmt₁ → Stmt₂)
    (e₁ : Stmt₁ → Wit₂ → pSpec₁.FullTranscript → Option Wit₁)
    (e₂ : Stmt₂ → Wit₃ → pSpec₂.FullTranscript → Option Wit₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundnessWith init impl rel₁ rel₂
      (Extractor.Straightline.ofTranscriptAndOutput e₁) ε₁)
    (h₂ : V₂.knowledgeSoundnessWith init impl rel₂ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput e₂) ε₂) :
    (V₁.append V₂).knowledgeSoundnessWith init impl rel₁ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput
        ((GuardedForm.ofEmpty V₁ fallback).appendExtract e₁ e₂)) (ε₁ + ε₂) :=
  append_knowledgeSoundnessWith (GuardedForm.ofEmpty V₁ fallback) e₁ e₂ h₁ fun s =>
    (knowledgeSoundnessWith_empty_init_iff V₂ (pure s)).mp h₂

/-- Plain-model existential knowledge-soundness composition for pure extractors. Both
component hypotheses use the original initialization. -/
theorem append_knowledgeSoundness_of_empty {Wit₁ Wit₂ Wit₃ : Type}
    (V₁ : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier []ₒ Stmt₂ Stmt₃ pSpec₂)
    (fallback : Stmt₁ → Stmt₂)
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : ∃ e₁, V₁.knowledgeSoundnessWith init impl rel₁ rel₂
      (Extractor.Straightline.ofTranscriptAndOutput e₁) ε₁)
    (h₂ : ∃ e₂, V₂.knowledgeSoundnessWith init impl rel₂ rel₃
      (Extractor.Straightline.ofTranscriptAndOutput e₂) ε₂) :
    (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃ (ε₁ + ε₂) := by
  obtain ⟨e₁, h₁⟩ := h₁
  obtain ⟨e₂, h₂⟩ := h₂
  exact knowledgeSoundness_of_with init impl
    (append_knowledgeSoundnessWith_of_empty V₁ V₂ fallback e₁ e₂ h₁ h₂)

end Verifier

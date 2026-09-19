/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.StateFunction

/-!
# Worst-case round-by-round soundness of sequential composition

Bounding every fixed transcript prefix avoids restricting an arbitrary combined prover to a
component. A pure first verifier determines the intermediate statement at the seam. Its state
function rules out an intermediate statement in the second language whenever a bad transition
can occur in the second component.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Stmt₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- Worst-case round-by-round soundness composes when the first verifier is pure. The
challenge error at each round is inherited from the corresponding component. No assumptions
on an honest prover or on the shared oracle's state transitions are needed. -/
theorem append_rbrSoundnessWorstCase_of_pure_first
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (V : V₁.PureForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundnessWorstCase init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.rbrSoundnessWorstCase init impl lang₂ lang₃ ε₂) :
    (V₁.append V₂).rbrSoundnessWorstCase init impl lang₁ lang₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  classical
  obtain ⟨S₁, h₁⟩ := h₁
  obtain ⟨S₂, h₂⟩ := h₂
  have hVerify : V₁ = ⟨fun stmt tr => pure (V.verify stmt tr)⟩ := by
    cases V₁
    congr 1
    funext stmt tr
    exact V.verify_eq stmt tr
  let S := StateFunction.append init impl V₁ V₂ S₁ S₂ V.verify hVerify
  refine ⟨S, ?_⟩
  intro stmt hstmt i
  obtain ⟨i, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases i with i | i
  · change ∀ tr : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inl i).1.castSucc,
      Pr[fun c => ¬ S _ stmt tr ∧ S _ stmt (tr.concat c) |
        $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))] ≤ _
    intro tr
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    by_cases hnot : ¬ S _ stmt tr
    · obtain ⟨tr₁, hnot₁, hnext⟩ := StateFunction.append_transition_left
        init impl S₁ S₂ V.verify hVerify i.1 stmt tr hnot
      calc
        _ ≤ Pr[fun c => ¬ S₁ i.1.castSucc stmt tr₁ ∧
              S₁ i.1.succ stmt (tr₁.concat (cast (challenge_append_inl i) c)) |
              $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))] :=
          probEvent_mono fun c _ hc => ⟨hnot₁, hnext c hc.2⟩
        _ = Pr[fun c => ¬ S₁ i.1.castSucc stmt tr₁ ∧
              S₁ i.1.succ stmt (tr₁.concat c) | $ᵗ (pSpec₁.Challenge i)] := by
          rw [← uniformSample_challenge_append_inl (pSpec₂ := pSpec₂) i, probEvent_map]
          rfl
        _ ≤ _ := h₁ stmt hstmt i tr₁
    · simp only [hnot, false_and, probEvent_False, zero_le]
  · change ∀ tr : (pSpec₁ ++ₚ pSpec₂).Transcript (ChallengeIdx.inr i).1.castSucc,
      Pr[fun c => ¬ S _ stmt tr ∧ S _ stmt (tr.concat c) |
        $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))] ≤ _
    intro tr
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    by_cases hnot : ¬ S _ stmt tr
    · obtain ⟨stmt₂, hstmt₂, tr₂, hnot₂, hnext⟩ := StateFunction.append_transition_right
        init impl S₁ S₂ V.verify hVerify i.1 stmt tr hnot
      calc
        _ ≤ Pr[fun c => ¬ S₂ i.1.castSucc stmt₂ tr₂ ∧
              S₂ i.1.succ stmt₂ (tr₂.concat (cast (challenge_append_inr i) c)) |
              $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))] :=
          probEvent_mono fun c _ hc => ⟨hnot₂, hnext c hc.2⟩
        _ = Pr[fun c => ¬ S₂ i.1.castSucc stmt₂ tr₂ ∧
              S₂ i.1.succ stmt₂ (tr₂.concat c) | $ᵗ (pSpec₂.Challenge i)] := by
          rw [← uniformSample_challenge_append_inr (pSpec₁ := pSpec₁) i, probEvent_map]
          rfl
        _ ≤ _ := h₂ stmt₂ hstmt₂ i tr₂
    · simp only [hnot, false_and, probEvent_False, zero_le]

/-- The fixed-prefix composition theorem also supplies the prover-averaged round-by-round
soundness contract, with the same per-round errors. -/
theorem append_rbrSoundness_of_worst_case_of_pure_first
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (V : V₁.PureForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundnessWorstCase init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.rbrSoundnessWorstCase init impl lang₂ lang₃ ε₂) :
    (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  rbrSoundnessWorstCase_implies_rbrSoundness init impl
    (append_rbrSoundnessWorstCase_of_pure_first V₁ V₂ V h₁ h₂)

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Stmt₂ Stmt₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [∀ i, OracleInterface (OStmt₃ i)]
  [∀ i, OracleInterface (pSpec₁.Message i)]
  [∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set (Stmt₁ × ∀ i, OStmt₁ i)} {lang₂ : Set (Stmt₂ × ∀ i, OStmt₂ i)}
  {lang₃ : Set (Stmt₃ × ∀ i, OStmt₃ i)}

/-- Oracle verifiers inherit the round-by-round composition theorem through their ordinary
verifier semantics. The fixed-prefix hypotheses and purity concern those converted verifiers. -/
theorem append_rbrSoundness_of_worst_case_of_pure_first
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (V : V₁.toVerifier.PureForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.toVerifier.rbrSoundnessWorstCase init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.toVerifier.rbrSoundnessWorstCase init impl lang₂ lang₃ ε₂) :
    (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrSoundness
  rw [append_toVerifier]
  exact Verifier.append_rbrSoundness_of_worst_case_of_pure_first
    V₁.toVerifier V₂.toVerifier V h₁ h₂

end OracleVerifier

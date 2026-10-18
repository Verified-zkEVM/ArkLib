/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.Composition.Sequential.Append.KnowledgeState
public import ArkLib.OracleReduction.Composition.Sequential.GuardedNary

/-!
# Guarded sequential knowledge soundness

Fixed-prefix knowledge bounds compose without resetting the shared oracle state when the
component verifiers have guarded forms. Errors retain their original component/round indexing.
The prefix-plus-tail theorem only requires the prefix to be guarded; the final verifier may
query the ambient oracle. Converting the resulting RBR certificate to plain knowledge soundness
still requires terminal knowledge at the actual verifier-start state; see `ActualExtraction`.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace ProtocolSpec

/-- Decoding a challenge in the head component returns component zero. -/
theorem seqComposeChallengeIdxToSigma_inl {m : ℕ} {n : Fin (m + 1) → ℕ}
    {pSpec : ∀ i, ProtocolSpec (n i)} (i : (pSpec 0).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₂ := seqCompose (fun j : Fin m => pSpec j.succ)) i) = ⟨0, i⟩ := by
  exact (seqComposeChallengeEquiv pSpec).symm_apply_apply ⟨0, i⟩

/-- Decoding a suffix challenge increments only its component index. -/
theorem seqComposeChallengeIdxToSigma_inr {m : ℕ} {n : Fin (m + 1) → ℕ}
    {pSpec : ∀ i, ProtocolSpec (n i)}
    (i : (ProtocolSpec.seqCompose (fun j : Fin m => pSpec j.succ)).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec) (ChallengeIdx.inr i) =
      ⟨(seqComposeChallengeIdxToSigma i).1.succ, (seqComposeChallengeIdxToSigma i).2⟩ := by
  obtain ⟨⟨j, c⟩, rfl⟩ := (seqComposeChallengeEquiv (fun j : Fin m => pSpec j.succ)).surjective i
  have hdec : seqComposeChallengeIdxToSigma
      (seqComposeChallengeEquiv (fun j : Fin m => pSpec j.succ) ⟨j, c⟩) = ⟨j, c⟩ :=
    (seqComposeChallengeEquiv (fun j : Fin m => pSpec j.succ)).symm_apply_apply ⟨j, c⟩
  rw [hdec]
  change (seqComposeChallengeEquiv pSpec).symm
      (seqComposeChallengeEquiv pSpec ⟨j.succ, c⟩) = _
  exact (seqComposeChallengeEquiv pSpec).symm_apply_apply ⟨j.succ, c⟩

end ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Identity has zero fixed-prefix knowledge error; it has no challenge rounds. -/
theorem id_rbrKnowledgeSoundness {Stmt Wit : Type} (rel : Set (Stmt × Wit)) :
    (Verifier.id : Verifier oSpec Stmt Stmt !p[]).rbrKnowledgeSoundness
      init impl rel rel 0 := by
  refine ⟨_, Extractor.RoundByRound.id, KnowledgeStateFunction.id init impl, ?_⟩
  intro _ i
  exact Fin.elim0 i.1

/-- Guarded component verifiers compose with the original per-component, per-round errors.
The bounds are required at fixed prefixes, not just averaged over a fresh component run. -/
theorem seqCompose_rbrKnowledgeSoundness_of_guarded
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl
      (rel 0) (rel (Fin.last m))
      (fun i => ε (seqComposeChallengeIdxToSigma i).1 (seqComposeChallengeIdxToSigma i).2) := by
  induction m with
  | zero =>
    have herr : (fun i => ε (seqComposeChallengeIdxToSigma i).1
        (seqComposeChallengeIdxToSigma i).2) = 0 := by
      funext i
      exact Fin.elim0 i.1
    rw [herr, seqCompose_zero]
    exact id_rbrKnowledgeSoundness init impl (rel 0)
  | succ m ih =>
    have htail := ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ)
      (fun i => rel i.succ) (fun i => V i.succ) (fun i => G i.succ)
      (fun i => ε i.succ) (fun i => h i.succ)
    have happ := append_rbrKnowledgeSoundness_of_guarded_first init impl
      (G 0) (h 0) htail
    convert happ using 1
    all_goals try rfl
    apply heq_of_eq
    funext i
    obtain ⟨i, rfl⟩ := (ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
      (pSpec₂ := ProtocolSpec.seqCompose (fun j : Fin m => pSpec j.succ))).surjective i
    rcases i with i | i
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
      exact congrArg (fun ij : (j : Fin (m + 1)) × (pSpec j).ChallengeIdx => ε ij.1 ij.2)
        (seqComposeChallengeIdxToSigma_inl (pSpec := pSpec) i)
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
      exact congrArg (fun ij : (j : Fin (m + 1)) × (pSpec j).ChallengeIdx => ε ij.1 ij.2)
        (seqComposeChallengeIdxToSigma_inr (pSpec := pSpec) i)

/-- Fixed-prefix guarded sequential knowledge soundness implies the averaged RBR contract. -/
theorem seqCompose_rbrKnowledgeSoundnessAveraged_of_guarded
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundnessAveraged init impl
      (rel 0) (rel (Fin.last m))
      (fun i => ε (seqComposeChallengeIdxToSigma i).1 (seqComposeChallengeIdxToSigma i).2) :=
  rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged init impl
    (seqCompose_rbrKnowledgeSoundness_of_guarded init impl Stmt Wit rel V G ε h)

/-- A finite guarded prefix may end in an arbitrary verifier, including one that queries the
shared oracle. Only the prefix needs guarded forms; the tail supplies a fixed-prefix bound.
The resulting error retains every original component and tail round bound. -/
theorem seqCompose_append_rbrKnowledgeSoundness_of_guarded_prefix
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (ε i))
    {StmtOut WitOut : Type} {k : ℕ} {tailSpec : ProtocolSpec k}
    [∀ i, SampleableType (tailSpec.Challenge i)]
    (tail : Verifier oSpec (Stmt (Fin.last m)) StmtOut tailSpec)
    (relOut : Set (StmtOut × WitOut)) (εTail : tailSpec.ChallengeIdx → ℝ≥0)
    (hTail : tail.rbrKnowledgeSoundness init impl (rel (Fin.last m)) relOut εTail) :
    ((Verifier.seqCompose Stmt V).append tail).rbrKnowledgeSoundness init impl
      (rel 0) relOut
      (Sum.elim
        (fun i => ε (seqComposeChallengeIdxToSigma i).1 (seqComposeChallengeIdxToSigma i).2)
        εTail ∘ ChallengeIdx.sumEquiv.symm) :=
  append_rbrKnowledgeSoundness_of_guarded_first init impl
    (GuardedForm.seqCompose Stmt V G)
    (seqCompose_rbrKnowledgeSoundness_of_guarded init impl Stmt Wit rel V G ε h) hTail

end Verifier

namespace OracleVerifier

/-- Oracle sequential composition retains fixed-prefix bounds for guarded components. -/
theorem seqCompose_rbrKnowledgeSoundness_of_guarded
    {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : ∀ i, ιₛ i → Type)
    [∀ i j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : ∀ i, OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i))
    (G : ∀ i, (V i).toVerifier.GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).toVerifier.rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (ε i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).toVerifier.rbrKnowledgeSoundness
      init impl (rel 0) (rel (Fin.last m))
      (fun i => ε (seqComposeChallengeIdxToSigma i).1 (seqComposeChallengeIdxToSigma i).2) := by
  rw [seqCompose_toVerifier]
  exact Verifier.seqCompose_rbrKnowledgeSoundness_of_guarded init impl
    (fun i => Stmt i × ∀ j, OStmt i j) Wit rel (fun i => (V i).toVerifier) G ε h

/-- Oracle append preserves fixed-prefix errors when the first underlying verifier is guarded.
The second verifier may use the ambient oracle. -/
theorem append_rbrKnowledgeSoundness_of_guarded_first
    {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
    {ι₁ ι₂ ι₃ : Type} {OStmt₁ : ι₁ → Type} {OStmt₂ : ι₂ → Type} {OStmt₃ : ι₃ → Type}
    [∀ i, OracleInterface (OStmt₁ i)] [∀ i, OracleInterface (OStmt₂ i)]
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, OracleInterface (pSpec₁.Message i)] [∀ i, OracleInterface (pSpec₂.Message i)]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁}
    {V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}
    (G : V₁.toVerifier.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.toVerifier.rbrKnowledgeSoundness init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.toVerifier.rbrKnowledgeSoundness init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).toVerifier.rbrKnowledgeSoundness init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  rw [append_toVerifier]
  exact Verifier.append_rbrKnowledgeSoundness_of_guarded_first init impl G h₁ h₂

/-- Oracle-verifier sequential composition inherits the proved guarded fixed-prefix contract. -/
theorem seqCompose_rbrKnowledgeSoundnessAveraged_of_guarded
    {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : ∀ i, ιₛ i → Type)
    [∀ i j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : ∀ i, OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i))
    (G : ∀ i, (V i).toVerifier.GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).toVerifier.rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (ε i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).rbrKnowledgeSoundnessAveraged init impl
      (rel 0) (rel (Fin.last m))
      (fun i => ε (seqComposeChallengeIdxToSigma i).1 (seqComposeChallengeIdxToSigma i).2) := by
  unfold rbrKnowledgeSoundnessAveraged
  rw [seqCompose_toVerifier]
  exact Verifier.seqCompose_rbrKnowledgeSoundnessAveraged_of_guarded init impl
    (fun i => Stmt i × ∀ j, OStmt i j) Wit rel (fun i => (V i).toVerifier) G ε h

end OracleVerifier

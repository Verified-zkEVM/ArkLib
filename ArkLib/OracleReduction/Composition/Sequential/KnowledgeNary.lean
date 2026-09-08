/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Knowledge
import ArkLib.OracleReduction.Composition.Sequential.GuardedNary

/-!
# Guarded round-by-round knowledge for finite sequential composition

The exact intermediate witness family, extractor, knowledge state, and error are constructed
recursively along the existing verifier `seqCompose`. Every nonempty step uses guarded append;
the empty sequence uses the identity extractor and knowledge state. Component guards remain in
the knowledge state after their respective seams.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier.KnowledgeSeqCompose

variable {ι : Type} {oSpec : OracleSpec ι}

/-- The recursive intermediate witness family, retaining each left component through its seam. -/
def Witness {m : ℕ} (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ}
    (W : ∀ i, Fin (n i + 1) → Type) : Fin (Fin.vsum n + 1) → Type :=
  match m with
  | 0 => fun _ => Wit 0
  | _ + 1 => KnowledgeAppend.Witness (W 0) (Witness (Wit ∘ Fin.succ) (fun i => W i.succ))

/-- The exact append extractor used at every seam of the actual composed verifier. -/
def extractor {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm) (W : ∀ i, Fin (n i + 1) → Type)
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Wit i.succ) (pSpec i) (W i)) :
    Extractor.RoundByRound oSpec (Stmt 0) (Wit 0) (Wit (Fin.last m))
      (ProtocolSpec.seqCompose pSpec) (Witness Wit W) :=
  match m with
  | 0 => Extractor.RoundByRound.id
  | _ + 1 => (E 0).append
      (extractor (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => V i.succ)
        (fun i => G i.succ) (fun i => W i.succ) (fun i => E i.succ)) (G 0).out

/-- The recursive guarded knowledge state for these exact component extractors and states. -/
def state {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm) (W : ∀ i, Fin (n i + 1) → Type)
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Wit i.succ) (pSpec i) (W i))
    (K : ∀ i, (V i).KnowledgeStateFunction init impl (rel i.castSucc) (rel i.succ) (E i)) :
    (Verifier.seqCompose Stmt V).KnowledgeStateFunction init impl
      (rel 0) (rel (Fin.last m)) (extractor Stmt Wit V G W E) := by
  induction m with
  | zero => exact KnowledgeStateFunction.id init impl
  | succ m ih =>
    exact KnowledgeStateFunction.appendGuarded (G 0) (K 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => rel i.succ)
        (fun i => V i.succ) (fun i => G i.succ) (fun i => W i.succ)
        (fun i => E i.succ) (fun i => K i.succ))

/-- The challenge error follows the same first-component/suffix split as actual composition. -/
def error {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0) :
    (ProtocolSpec.seqCompose pSpec).ChallengeIdx → ℝ≥0 :=
  match m with
  | 0 => fun i => Fin.elim0 i.1
  | _ + 1 => Sum.elim (ε 0) (error (fun i => ε i.succ)) ∘
      (ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ))).symm

/-- The recursive error at an embedded component challenge is that component's exact error. -/
theorem error_component {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0) (i : Fin m) (j : (pSpec i).ChallengeIdx) :
    error ε (sigmaChallengeIdxToSeqCompose i j) = ε i j := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases i using Fin.cases with
    | zero =>
      rw [sigmaChallengeIdxToSeqCompose_zero]
      change Sum.elim (ε 0) (error (fun i => ε i.succ))
        ((ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
          (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ))).symm
          (ChallengeIdx.inl j)) = _
      rw [ChallengeIdx.sumEquiv_symm_inl]
      rfl
    | succ i =>
      rw [sigmaChallengeIdxToSeqCompose_succ]
      change Sum.elim (ε 0) (error (fun i => ε i.succ))
        ((ChallengeIdx.sumEquiv (pSpec₁ := pSpec 0)
          (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ))).symm
          (ChallengeIdx.inr (sigmaChallengeIdxToSeqCompose i j))) = _
      rw [ChallengeIdx.sumEquiv_symm_inr]
      exact ih (fun i => ε i.succ) i j

/-- Recursive error selection equals the public component-and-challenge decoding API. -/
theorem error_eq_sigma {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0) :
    error ε = fun k =>
      let ij := seqComposeChallengeIdxToSigma k
      ε ij.1 ij.2 := by
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := (seqComposeChallengeEquiv pSpec).surjective k
  change error ε (seqComposeChallengeEquiv pSpec ⟨i, j⟩) =
    (fun ij : (i : Fin m) × (pSpec i).ChallengeIdx => ε ij.1 ij.2)
      ((seqComposeChallengeEquiv pSpec).symm (seqComposeChallengeEquiv pSpec ⟨i, j⟩))
  rw [Equiv.symm_apply_apply]
  exact error_component ε i j

end Verifier.KnowledgeSeqCompose

namespace Verifier

open KnowledgeSeqCompose

variable {ι : Type} {oSpec : OracleSpec ι}

/-- Guarded finite composition preserves the fixed-prefix knowledge contract for its exact
recursive witness family, extractor, and knowledge state. -/
theorem seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_verifiers
    {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm) (W : ∀ i, Fin (n i + 1) → Type)
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Wit i.succ) (pSpec i) (W i))
    (K : ∀ i, (V i).KnowledgeStateFunction init impl (rel i.castSucc) (rel i.succ) (E i))
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundnessWorstCaseWith init impl
      (rel i.castSucc) (rel i.succ) (W i) (E i) (K i) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundnessWorstCaseWith init impl
      (rel 0) (rel (Fin.last m)) (Witness Wit W) (extractor Stmt Wit V G W E)
      (state Stmt Wit init impl rel V G W E K) (error ε) := by
  induction m with
  | zero => intro _ i; exact Fin.elim0 i.1
  | succ m ih =>
    exact append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first (G 0) (K 0)
      (state (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) init impl (fun i => rel i.succ)
        (fun i => V i.succ) (fun i => G i.succ) (fun i => W i.succ)
        (fun i => E i.succ) (fun i => K i.succ)) (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => rel i.succ)
        (fun i => V i.succ) (fun i => G i.succ) (fun i => W i.succ)
        (fun i => E i.succ) (fun i => K i.succ) (fun i => ε i.succ) (fun i => h i.succ))

/-- The same exact recursively composed objects satisfy the prover-averaged knowledge contract. -/
theorem seqCompose_rbrKnowledgeSoundnessWith_of_worstCase_of_guarded_verifiers
    {m : ℕ} (Stmt Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm) (W : ∀ i, Fin (n i + 1) → Type)
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Wit i.succ) (pSpec i) (W i))
    (K : ∀ i, (V i).KnowledgeStateFunction init impl (rel i.castSucc) (rel i.succ) (E i))
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundnessWorstCaseWith init impl
      (rel i.castSucc) (rel i.succ) (W i) (E i) (K i) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundnessWith init impl
      (rel 0) (rel (Fin.last m)) (Witness Wit W) (extractor Stmt Wit V G W E)
      (state Stmt Wit init impl rel V G W E K) (error ε) :=
  rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
    (seqCompose_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_verifiers
      Stmt Wit init impl rel V G W E K ε h)

end Verifier

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.Composition.Sequential.Append.GuardedRoundByRound

/-!
# Round-by-round knowledge soundness of a finite guarded sequential composition

`Verifier.seqCompose_rbrKnowledgeSoundnessWith_of_guarded`: if every component verifier is
guarded and round-by-round knowledge sound between consecutive relations, so is their
sequential composition. Each combined challenge's error is its component's, through
`seqComposeChallengeIdxToSigma`. The proof iterates the binary
`Verifier.append_rbrKnowledgeSoundnessWith_of_guarded_first`. The error bookkeeping of each
step is `ProtocolSpec.apply_seqComposeChallengeIdxToSigma_eq_sumElim`.

The existential corollary and `OracleVerifier` wrappers are included.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Named round-by-round certificates compose along a finite guarded chain.
The extractor and knowledge state iterate guarded append with a terminal identity; the error
of each combined challenge is its component error under `seqComposeChallengeIdxToSigma`.
Every guard is used, including the last component's guard before the terminal identity. -/
theorem seqCompose_rbrKnowledgeSoundnessWith_of_guarded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    {WitMid : ∀ i, Fin (n i + 1) → Type}
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Wit i.succ) (pSpec i) (WitMid i))
    (K : ∀ i, (V i).KnowledgeStateFunction init impl (rel i.castSucc) (rel i.succ) (E i))
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundnessWith init impl (rel i.castSucc) (rel i.succ)
      (WitMid i) (E i) (K i) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundnessWith init impl (rel 0)
      (rel (Fin.last m)) _ (Extractor.RoundByRound.seqCompose Stmt Wit V G E)
      (KnowledgeStateFunction.seqComposeGuarded Stmt Wit rel V G E K)
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        ε ij.1 ij.2) := by
  induction m with
  | zero => exact fun _ i => Fin.elim0 i.1
  | succ m ih =>
    have htail := ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => rel i.succ)
      (fun i => V i.succ) (fun i => G i.succ) (fun i => E i.succ) (fun i => K i.succ)
      (fun i => ε i.succ) (fun i => h i.succ)
    have happend := append_rbrKnowledgeSoundnessWith_of_guarded_first
      (V 0) _ (G 0) (h 0) htail
    rw [apply_seqComposeChallengeIdxToSigma_eq_sumElim, instSampleableTypeChallengeSeqCompose_succ]
    exact happend

/-- Existential form of `seqCompose_rbrKnowledgeSoundnessWith_of_guarded`. -/
theorem seqCompose_rbrKnowledgeSoundness_of_guarded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl (rel 0)
      (rel (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        ε ij.1 ij.2) := by
  choose WitMid E K h using h
  exact ⟨_, _, _, seqCompose_rbrKnowledgeSoundnessWith_of_guarded
    Stmt Wit rel V G E K ε h⟩

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Oracle chains inherit named guarded certificates through `seqCompose_toVerifier`, with
the same folded extractor, transported knowledge state, and per-component challenge errors. -/
theorem seqCompose_rbrKnowledgeSoundnessWith_of_guarded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type}
    (OStmt : (i : Fin (m + 1)) → ιₛ i → Type) [∀ i j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : ∀ i, OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ)
      (OStmt i.succ) (pSpec i))
    (G : ∀ i, (V i).toVerifier.GuardedForm)
    {WitMid : ∀ i, Fin (n i + 1) → Type}
    (E : ∀ i, Extractor.RoundByRound oSpec (Stmt i.castSucc × ∀ j, OStmt i.castSucc j)
      (Wit i.castSucc) (Wit i.succ) (pSpec i) (WitMid i))
    (K : ∀ i, (V i).toVerifier.KnowledgeStateFunction init impl
      (rel i.castSucc) (rel i.succ) (E i))
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).toVerifier.rbrKnowledgeSoundnessWith init impl (rel i.castSucc)
      (rel i.succ) (WitMid i) (E i) (K i) (ε i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).toVerifier.rbrKnowledgeSoundnessWith init impl
      (rel 0) (rel (Fin.last m)) _
      (Extractor.RoundByRound.seqCompose (fun i => Stmt i × ∀ j, OStmt i j) Wit
        (fun i => (V i).toVerifier) G E)
      (seqComposeKnowledgeStateFunction Stmt OStmt Wit rel V G E K)
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        ε ij.1 ij.2) :=
  Verifier.seqCompose_rbrKnowledgeSoundnessWith_of_guarded
    (fun i => Stmt i × ∀ j, OStmt i j) Wit rel (fun i => (V i).toVerifier) G E K ε h

/-- Existential form of `seqCompose_rbrKnowledgeSoundnessWith_of_guarded`. -/
theorem seqCompose_rbrKnowledgeSoundness_of_guarded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Fin (m + 1) → Type}
    (OStmt : (i : Fin (m + 1)) → ιₛ i → Type) [∀ i j, OracleInterface (OStmt i j)]
    (Wit : Fin (m + 1) → Type) {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, OracleInterface ((pSpec i).Message j)]
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : ∀ i, OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ)
      (OStmt i.succ) (pSpec i))
    (G : ∀ i, (V i).toVerifier.GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).toVerifier.rbrKnowledgeSoundness init impl (rel i.castSucc)
      (rel i.succ) (ε i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).toVerifier.rbrKnowledgeSoundness init impl
      (rel 0) (rel (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        ε ij.1 ij.2) := by
  choose WitMid E K h using h
  exact ⟨_, _, _, seqCompose_rbrKnowledgeSoundnessWith_of_guarded
    Stmt OStmt Wit rel V G E K ε h⟩

end OracleVerifier

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.Composition.Sequential.Append.GuardedRoundByRound

/-!
# Worst-case round-by-round knowledge soundness of a finite guarded sequential composition

`Verifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded`: if every component verifier is
guarded and worst-case round-by-round knowledge sound between consecutive relations, so is their
sequential composition. Each combined challenge's error is its component's, through
`seqComposeChallengeIdxToSigma`. The proof iterates the binary
`Verifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`. The error bookkeeping of each
step is `ProtocolSpec.apply_seqComposeChallengeIdxToSigma_eq_sumElim`.

The averaged corollary and an `OracleVerifier` wrapper are included.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Worst-case round-by-round knowledge soundness of a finite guarded sequential composition.**
If every component verifier is guarded and worst-case round-by-round knowledge sound between
consecutive relations, so is their sequential composition. The error of each combined challenge is
the error of the component challenge it decodes to under `seqComposeChallengeIdxToSigma`. It is the
binary `append_rbrKnowledgeSoundnessWorstCase_of_guarded_first` iterated. Every component's guard
is used, the last one included: `seqCompose` peels the head with `append`, so the last component
is the guarded first factor of `append (V (Fin.last _)) Verifier.id`. -/
theorem seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundnessWorstCase init impl (rel i.castSucc) (rel i.succ) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundnessWorstCase init impl (rel 0)
      (rel (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        ε ij.1 ij.2) := by
  induction m with
  | zero =>
    rw [Verifier.seqCompose_zero]
    exact ⟨_, _, KnowledgeStateFunction.id init impl, fun _ i => Fin.elim0 i.1⟩
  | succ m ih =>
    have := ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => rel i.succ) (fun i => V i.succ)
      (fun i => G i.succ) (fun i => ε i.succ) (fun i => h i.succ)
    have h2 := append_rbrKnowledgeSoundnessWorstCase_of_guarded_first (V 0) _ (G 0) (h 0) this
    rw [apply_seqComposeChallengeIdxToSigma_eq_sumElim, instSampleableTypeChallengeSeqCompose_succ]
    exact h2

/-- The finite guarded composition theorem also supplies the prover-averaged round-by-round
knowledge soundness contract, with the same per-round errors. -/
theorem seqCompose_rbrKnowledgeSoundness_of_worst_case_of_guarded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm)
    (ε : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundnessWorstCase init impl (rel i.castSucc) (rel i.succ) (ε i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl (rel 0) (rel (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        ε ij.1 ij.2) :=
  rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded Stmt Wit rel V G ε h)

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Oracle verifiers inherit the finite guarded composition theorem through their ordinary
verifier semantics. The guards and the component hypotheses concern the converted verifiers. -/
theorem seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded {m : ℕ}
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
    (h : ∀ i, (V i).toVerifier.rbrKnowledgeSoundnessWorstCase init impl (rel i.castSucc)
      (rel i.succ) (ε i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (rel 0) (rel (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        ε ij.1 ij.2) := by
  rw [seqCompose_toVerifier]
  exact Verifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded _ Wit rel _ G ε h

end OracleVerifier

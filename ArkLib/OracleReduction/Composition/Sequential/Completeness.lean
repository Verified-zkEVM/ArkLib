/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.IsPure
public import ArkLib.OracleReduction.Composition.Sequential.Append.Completeness

/-!
# State-aware completeness of a sequence of reductions

This module composes the proved binary completeness theorem. Every component is complete from
all deterministic shared oracle states, so each tail can receive its predecessor's final state.
-/

@[expose] public section

open ProtocolSpec OracleComp
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- A finite sequence of reductions with pure verifier verdicts and pure prover outputs is
complete, with total error bounded by the sum of component errors, provided each component is
complete from every shared oracle state. Prover messages may still make oracle queries. -/
theorem seqCompose_completeness_of_pure
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ) (pSpec i))
    (ε : Fin m → ℝ≥0)
    (hP : ∀ i, (R i).prover.OutputIsPure)
    (hV : ∀ i, (R i).verifier.IsPure)
    (h : ∀ i s, (R i).completeness (pure s) impl (rel i.castSucc) (rel i.succ) (ε i)) :
    (seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
      (∑ i, ε i) := by
  induction m generalizing init impl with
  | zero => simp only [seqCompose_zero]; exact id_perfectCompleteness init impl
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one]
    rw [Fin.sum_univ_succ]
    let := hP 0
    let := hV 0
    let : (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ)
        (fun i => R i.succ)).verifier.IsPure :=
      Verifier.IsPure.seqCompose _ _ (fun i => hV i.succ)
    apply append_completeness_of_pure (R 0)
      (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R i.succ))
    · obtain ⟨f, hf⟩ := (hV 0).is_pure
      exact completeness_of_pure_states (R 0) ⟨f, hf⟩ (h 0)
    · intro s
      exact ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (pure s) impl
        (fun i => rel i.succ) (fun i => R i.succ) (fun i => ε i.succ)
        (fun i => hP i.succ) (fun i => hV i.succ) (fun i => h i.succ)

/-- Perfect completeness of a finite sequence under pure verifier verdicts, pure prover
outputs, and component completeness from every deterministic oracle state. -/
theorem seqCompose_perfectCompleteness_of_pure
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ) (pSpec i))
    (hP : ∀ i, (R i).prover.OutputIsPure)
    (hV : ∀ i, (R i).verifier.IsPure)
    (h : ∀ i s, (R i).perfectCompleteness (pure s) impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  simpa only [perfectCompleteness, Finset.sum_const_zero] using
    seqCompose_completeness_of_pure Stmt Wit init impl rel R (fun _ => 0) hP hV h

end Reduction

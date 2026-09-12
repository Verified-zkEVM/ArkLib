/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.IsPure

/-!
# Guarded completeness of finite sequential composition

Each component has pure prover output and a deterministic verifier that can reject. The suffix
receives its predecessor's actual oracle state; component completeness holds from every state.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}

/-- Guarded verifier forms compose along a finite sequence, retaining all component checks. -/
def GuardedForm.seqCompose {m : ℕ} (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (G : ∀ i, (V i).GuardedForm) : (Verifier.seqCompose Stmt V).GuardedForm := by
  induction m with
  | zero => exact ⟨fun _ _ => true, fun stmt _ => stmt, fun _ _ => rfl⟩
  | succ m ih =>
    exact (G 0).append (ih (Stmt ∘ Fin.succ) (fun i => V i.succ) (fun i => G i.succ))

end Verifier

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- Pure prover outputs and guarded verifiers compose with the sum of the component errors
when every component is complete from every deterministic shared state. -/
theorem seqCompose_completeness_of_guarded_verifiers
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ) (pSpec i))
    (ε : Fin m → ℝ≥0)
    (hP : ∀ i, (R i).prover.OutputIsPure)
    (hV : ∀ i, (R i).verifier.GuardedForm)
    (h : ∀ i s, (R i).completeness (pure s) impl (rel i.castSucc) (rel i.succ) (ε i)) :
    (seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
      (∑ i, ε i) := by
  induction m generalizing init impl with
  | zero => simp only [seqCompose_zero]; exact id_perfectCompleteness init impl
  | succ m ih =>
    simp only [Fin.vsum_succ, seqCompose_succ, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Function.comp_apply, Fin.succ_last, Nat.succ_eq_add_one]
    rw [Fin.sum_univ_succ]
    apply append_completeness_of_guarded_verifiers (R 0)
      (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R i.succ)) (hV 0)
      (Verifier.GuardedForm.seqCompose (Stmt ∘ Fin.succ)
        (fun i => (R i.succ).verifier) (fun i => hV i.succ))
      (fun _ => Or.inl (hP 0))
    · exact completeness_of_guarded_states (R 0) (hV 0) (h 0)
    · intro s
      exact ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (pure s) impl
        (fun i => rel i.succ) (fun i => R i.succ) (fun i => ε i.succ)
        (fun i => hP i.succ) (fun i => hV i.succ) (fun i => h i.succ)

/-- Pure prover outputs and guarded verifiers preserve perfect completeness of a finite sequence
when every component is perfectly complete from every deterministic shared state. -/
theorem seqCompose_perfectCompleteness_of_guarded_verifiers
    {m : ℕ} (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i j, SampleableType ((pSpec i).Challenge j)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ) (pSpec i))
    (hP : ∀ i, (R i).prover.OutputIsPure)
    (hV : ∀ i, (R i).verifier.GuardedForm)
    (h : ∀ i s, (R i).perfectCompleteness (pure s) impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  simpa only [perfectCompleteness, Finset.sum_const_zero] using
    seqCompose_completeness_of_guarded_verifiers Stmt Wit init impl rel R (fun _ => 0) hP hV h

end Reduction

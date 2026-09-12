/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# Composition certificates when the ambient oracle specification is empty

An oracle computation with no possible query has a pure result. A verifier can still reject;
its guarded form uses an input-dependent fallback only to define the unused rejecting verdict.
No global inhabitation assumption on the output statement or oracle family is needed.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace OracleComp

/-- Extract the result of a computation that has no possible oracle query. -/
def runEmpty {α : Type} : OracleComp []ₒ α → α
  | .pure a => a
  | .liftBind t _ => isEmptyElim t

/-- Every computation over the empty specification is exactly its pure result. -/
theorem eq_pure_runEmpty {α : Type} (oa : OracleComp []ₒ α) :
    oa = pure (runEmpty oa) := by
  cases oa with
  | pure a => rfl
  | queryBind t _ => exact isEmptyElim t

end OracleComp

/-- Pure output is automatic when a prover has no ambient oracle to query. -/
instance Prover.instOutputIsPureEmpty
    {Stmt₁ Wit₁ Stmt₂ Wit₂ : Type} {n : ℕ} {p : ProtocolSpec n}
    (P : Prover []ₒ Stmt₁ Wit₁ Stmt₂ Wit₂ p) : P.OutputIsPure :=
  ⟨fun st => (P.output st).runEmpty, fun st => eq_pure_runEmpty (P.output st)⟩

/-- Extract a deterministic guarded verifier form over an empty ambient oracle. The fallback is
used only if verification rejects; it may preserve oracle values from the input statement. -/
def Verifier.GuardedForm.ofEmpty {Stmt₁ Stmt₂ : Type}
    {n : ℕ} {p : ProtocolSpec n} (V : Verifier []ₒ Stmt₁ Stmt₂ p)
    (fallback : Stmt₁ → Stmt₂) : V.GuardedForm where
  check := fun stmt tr => (V.verify stmt tr).run.runEmpty.isSome
  out := fun stmt tr => (V.verify stmt tr).run.runEmpty.getD (fallback stmt)
  verify_eq := by
    intro stmt tr
    apply OptionT.ext
    rw [eq_pure_runEmpty (V.verify stmt tr).run]
    cases h : (V.verify stmt tr).run.runEmpty <;> simp [h]

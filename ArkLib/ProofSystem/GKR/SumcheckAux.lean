/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude(Anthropic)
-/

import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# Sum-check preserves its oracle statement

Sum-check sums a *fixed* polynomial: each round consumes one variable and updates the target,
but the polynomial itself is never modified. This file proves that the oracle statement
component of the prover's output equals the one that went in.

GKR needs this: after running the inner sum-check, the combine step must know the polynomial
it is reasoning about is still `roundPolyFin` rather than an arbitrary polynomial that happens
to typecheck. Without it `Context.Lens.IsComplete.lift_complete` cannot be discharged.

Nothing here is GKR-specific; it belongs upstream in `Sumcheck/Spec/` and lives here only to
keep the GKR development self-contained.
-/

namespace Sumcheck.Spec

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R) (n : ℕ)
variable {ι : Type} (oSpec : OracleSpec ι)
variable [DecidableEq R] [SampleableType R]

omit [SampleableType R] in
/-- The single-round prover leaves the oracle statement untouched.

This is immediate from the shape of `oStmtLens`: its `toFunB` reassembles the output from the
*outer input's* oracle (`oStmt`), ignoring whatever the inner protocol returned. -/
theorem singleRound_prover_run_preserves_oracle (i : Fin n)
    (stmt : StatementRound R n i.castSucc × (∀ j, OracleStatement R n deg j)) (wit : Unit) :
    ∀ x ∈ _root_.support ((SingleRound.reduction R n deg D oSpec i).prover.run stmt wit),
      x.2.1.2 = stmt.2 := by
  intro x hx
  rw [SingleRound.reduction, Reduction.liftContext] at hx
  rw [Prover.liftContext_run] at hx
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨y, _, hxy⟩ := hx
  subst hxy
  rfl

section General

variable {ι' : Type} {oSpec' : OracleSpec ι'}

/-- If every prover in a sequence leaves the second component of its statement untouched, then
so does their sequential composition. Induction on the number of rounds, peeling with
`Prover.seqCompose_succ` and `Prover.append_run`. -/
theorem seqCompose_run_preserves_snd {M : ℕ} (A : Fin (M + 1) → Type) (B : Type)
    {nn : Fin M → ℕ} {pSpec' : ∀ i, ProtocolSpec (nn i)}
    (P : (i : Fin M) → Prover oSpec' (A i.castSucc × B) Unit (A i.succ × B) Unit (pSpec' i))
    (hP : ∀ i s w, ∀ x ∈ _root_.support ((P i).run s w), x.2.1.2 = s.2)
    (stmt : A 0 × B) (wit : Unit) :
    ∀ x ∈ _root_.support
        ((Prover.seqCompose (fun i => A i × B) (fun _ => Unit) P).run stmt wit),
      x.2.1.2 = stmt.2 := by
  induction M with
  | zero =>
      intro x hx
      simp only [Prover.seqCompose_zero, Prover.id, Prover.run, Prover.runToRound,
        bind_pure_comp] at hx
      subst hx
      rfl
  | succ M ih =>
      intro x hx
      rw [Prover.seqCompose_succ] at hx
      erw [Prover.append_run] at hx
      erw [mem_support_bind_iff] at hx
      obtain ⟨⟨tr₁, stmt₂, wit₂⟩, hstep1, hx⟩ := hx
      -- first round preserved the oracle
      have h1 : stmt₂.2 = stmt.2 :=
        hP 0 stmt wit _ (OracleComp.mem_support_of_mem_support_liftComp _ _ _ hstep1)
      erw [mem_support_bind_iff] at hx
      obtain ⟨⟨tr₂, stmt₃, wit₃⟩, hstep2, hx⟩ := hx
      -- the remaining rounds preserved it too, by induction
      have h2 : stmt₃.2 = stmt₂.2 :=
        ih (A ∘ Fin.succ) (fun i => P i.succ) (fun i s w => hP i.succ s w) stmt₂ _
          (OracleComp.mem_support_of_mem_support_liftComp _ _ _ hstep2)
      simp only [] at hx
      subst hx
      exact h2.trans h1

end General

omit [SampleableType R] in
/-- The composed sum-check prover leaves the oracle statement untouched: the polynomial that
comes out is the one that went in. Proved by induction on the number of rounds, using
`Prover.seqCompose_succ` to peel one round at a time. -/
theorem prover_run_preserves_oracle
    (stmt : StatementRound R n 0 × (∀ j, OracleStatement R n deg j)) (wit : Unit) :
    ∀ x ∈ _root_.support ((reduction R deg D n oSpec).prover.run stmt wit),
      x.2.1.2 = stmt.2 :=
  seqCompose_run_preserves_snd
    (A := fun i => StatementRound R n i)
    (B := ∀ j, OracleStatement R n deg j)
    (P := fun i => (SingleRound.reduction R n deg D oSpec i).prover)
    (fun i s w => singleRound_prover_run_preserves_oracle R deg D n oSpec i s w)
    stmt wit

omit [SampleableType R] in
/-- The form GKR consumes: the oracle statement in the prover's half of a `Reduction.run`
result is the one that went in. -/
theorem reduction_run_preserves_oracle
    (stmt : StatementRound R n 0 × (∀ j, OracleStatement R n deg j)) (wit : Unit) :
    ∀ x ∈ _root_.support ((reduction R deg D n oSpec).run stmt wit),
      x.1.2.1.2 = stmt.2 := by
  intro x hx
  rw [Reduction.run] at hx
  erw [mem_support_bind_iff] at hx
  obtain ⟨proverResult, hprover, hx⟩ := hx
  rw [OptionT.support_liftM] at hprover
  have hp : proverResult.2.1.2 = stmt.2 :=
    prover_run_preserves_oracle R deg D n oSpec stmt wit _ hprover
  erw [mem_support_bind_iff] at hx
  obtain ⟨stmtOut, -, hx⟩ := hx
  erw [mem_support_bind_iff] at hx
  obtain ⟨v, -, hx⟩ := hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact hp

end Sumcheck.Spec

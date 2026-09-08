/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.PackedCommitment

/-!
# Exact commitments to packed multilinears

This is the exact-functional specialization of a commitment relation. A fixed collection of
oracle statements determines at most one packed polynomial, and every polynomial has an honest
commitment. The relation is retained by the phase and its downstream opening relation.

Functionality permits a security proof to fix the packed witness before sampling a batching
challenge. List-decoding and collision-escape interfaces require separate security contracts;
they are not instances of this exact specialization without an additional uniqueness theorem.
-/

noncomputable section

namespace RingSwitching.Packing

open MvPolynomial

/-- A packed commitment together with uniqueness for each fixed oracle statement. -/
structure ExactPackedCommitment (P : Type) [CommRing P] (m : ℕ)
    extends PackedCommitment P m where
  /-- Exact binding of the unchanged packed commitment relation. -/
  commitsTo_functional : toPackedCommitment.Functional

instance {P : Type} [CommRing P] {m : ℕ} :
    Coe (ExactPackedCommitment P m) (PackedCommitment P m) := ⟨fun pc => pc.toPackedCommitment⟩

namespace ExactPackedCommitment

variable {P : Type} [CommRing P] {m : ℕ} (pc : ExactPackedCommitment P m)

/-- Honest commitments to different packed polynomials are different oracle collections. -/
theorem commit_injective : Function.Injective pc.commit := by
  intro p p' h
  exact pc.commitsTo_functional (pc.commitsTo_commit p) (h ▸ pc.commitsTo_commit p')

/-- The exact specialization uses the same opening relation as its underlying commitment. -/
abbrev evalRel {C : Type} [CommRing C] [Algebra P C] :=
  pc.toPackedCommitment.evalRel (C := C)

/-- Honest opening coverage is inherited without using functionality. -/
theorem evalRel_honest {C : Type} [CommRing C] [Algebra P C]
    (p : P⦃≤ 1⦄[X Fin m]) (r : Fin m → C) :
    (((r, aeval r p.val), pc.commit p), p) ∈ pc.evalRel :=
  pc.toPackedCommitment.evalRel_honest p r

/-- Honest coverage rules out an empty opening relation. -/
theorem evalRel_nonempty {C : Type} [CommRing C] [Algebra P C] :
    (pc.evalRel (C := C)).Nonempty :=
  pc.toPackedCommitment.evalRel_nonempty

/-- In a nontrivial packed ring, no fixed oracle collection is related to every polynomial. -/
theorem commitsTo_not_top [Nontrivial P] (c : ∀ j, pc.OStmt j) :
    ¬ ∀ p, pc.commitsTo c p := by
  intro h
  have h01 : (⟨MLE fun _ => 0, MLE_mem_restrictDegree _⟩ : P⦃≤ 1⦄[X Fin m]) =
      ⟨MLE fun _ => 1, MLE_mem_restrictDegree _⟩ := pc.commitsTo_functional (h _) (h _)
  have hv := congrArg (fun p : P⦃≤ 1⦄[X Fin m] =>
    eval (((fun _ => 0) : Fin m → Fin 2) : Fin m → P) p.val) h01
  simp only [MLE_eval_zeroOne] at hv
  exact zero_ne_one hv

/-- An explicit commitment whose oracle stores the entire polynomial. -/
def polynomialOracle (P : Type) [CommRing P] (m : ℕ) : ExactPackedCommitment P m where
  ιC := Unit
  OStmt _ := P⦃≤ 1⦄[X Fin m]
  Oᵢ _ := OracleInterface.instDefault
  commitsTo c p := c () = p
  commit p _ := p
  commitsTo_functional h h' := h.symm.trans h'
  commitsTo_commit _ := rfl

end ExactPackedCommitment

end RingSwitching.Packing

end

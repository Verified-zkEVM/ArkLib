/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.OracleReduction.OracleInterface

/-!
# Packed commitment relations

The generic phase layer needs an oracle relation and honest coverage. Functionality is a
separate security premise: list-valued relations can use the same phases, extractors, and
completeness theorems, while randomized separation needs an appropriate additional bound.
-/

noncomputable section

namespace RingSwitching.Packing

open MvPolynomial

/-- Commitment semantics and honest coverage, without a uniqueness requirement. -/
structure PackedCommitment (P : Type) [CommRing P] (m : ℕ) where
  /-- Index of commitment oracle statements. -/
  ιC : Type
  /-- Commitment oracle types. -/
  OStmt : ιC → Type
  /-- Interfaces through which a verifier reads the commitment. -/
  Oᵢ : ∀ i, OracleInterface (OStmt i)
  /-- The relation between an oracle collection and a packed polynomial. -/
  commitsTo : (∀ j, OStmt j) → P⦃≤ 1⦄[X Fin m] → Prop
  /-- Honest commitment, covering every packed polynomial. -/
  commit : P⦃≤ 1⦄[X Fin m] → ∀ j, OStmt j
  /-- The honest commitment satisfies the same relation used by protocol statements. -/
  commitsTo_commit : ∀ p, commitsTo (commit p) p

attribute [instance] PackedCommitment.Oᵢ

namespace PackedCommitment

variable {P : Type} [CommRing P] {m : ℕ} (pc : PackedCommitment P m)

/-- Every fixed oracle collection is compatible with at most one packed polynomial. -/
def Functional : Prop := ∀ {c : ∀ j, pc.OStmt j} {p p' : P⦃≤ 1⦄[X Fin m]},
  pc.commitsTo c p → pc.commitsTo c p' → p = p'

/-- The same-oracle opening relation, allowing evaluation in an algebra of packed coefficients. -/
def evalRel {C : Type} [CommRing C] [Algebra P C] :
    Set (((((Fin m → C) × C) × (∀ j, pc.OStmt j))) × P⦃≤ 1⦄[X Fin m]) :=
  { x | x.1.1.2 = aeval x.1.1.1 x.2.val ∧ pc.commitsTo x.1.2 x.2 }

/-- Every honest commitment has its true opening at every challenge point. -/
theorem evalRel_honest {C : Type} [CommRing C] [Algebra P C]
    (p : P⦃≤ 1⦄[X Fin m]) (r : Fin m → C) :
    (((r, aeval r p.val), pc.commit p), p) ∈ pc.evalRel :=
  ⟨rfl, pc.commitsTo_commit p⟩

/-- Honest coverage rules out an empty opening relation. -/
theorem evalRel_nonempty {C : Type} [CommRing C] [Algebra P C] :
    (pc.evalRel (C := C)).Nonempty :=
  ⟨(((fun _ => 0, aeval (fun _ : Fin m => (0 : C)) (0 : P⦃≤ 1⦄[X Fin m]).val),
      pc.commit 0), 0), pc.evalRel_honest 0 (fun _ => 0)⟩

end PackedCommitment

end RingSwitching.Packing

end

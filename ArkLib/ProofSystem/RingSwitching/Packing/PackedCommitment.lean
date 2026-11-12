/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.OracleReduction.OracleInterface

/-!
# Packed commitment relations

For a packed polynomial p and oracle collection o, `commitsTo o p` specifies compatibility.
Functionality means that o determines p. `Honest` supplies an independent constructor satisfying
`commitsTo (commit p) p`; the protocol and its security statements require only the relation.
-/

@[expose] public section

noncomputable section

namespace RingSwitching.Packing

open MvPolynomial

/-- A packed-polynomial oracle relation, without a uniqueness or coverage requirement. -/
structure PackedCommitment (P : Type) [CommRing P] (m : ℕ) where
  /-- Index of commitment oracle statements. -/
  ιC : Type
  /-- Commitment oracle types. -/
  OStmt : ιC → Type
  /-- Interfaces through which a verifier reads the commitment. -/
  Oᵢ : ∀ i, OracleInterface (OStmt i)
  /-- The relation between an oracle collection and a packed polynomial. -/
  commitsTo : (∀ j, OStmt j) → P⦃≤ 1⦄[X Fin m] → Prop

attribute [instance] PackedCommitment.Oᵢ

namespace PackedCommitment

/-- An honest constructor whose output satisfies the packed-polynomial oracle relation. -/
structure Honest {P : Type} [CommRing P] {m : ℕ} (pc : PackedCommitment P m) where
  /-- Honest commitment to each packed polynomial. -/
  commit : P⦃≤ 1⦄[X Fin m] → ∀ j, pc.OStmt j
  /-- The constructor covers every polynomial under the same oracle relation. -/
  commitsTo_commit : ∀ p, pc.commitsTo (commit p) p

variable {P : Type} [CommRing P] {m : ℕ} (pc : PackedCommitment P m)

/-- Every fixed oracle collection is compatible with at most one packed polynomial. -/
def Functional : Prop := ∀ {c : ∀ j, pc.OStmt j} {p p' : P⦃≤ 1⦄[X Fin m]},
  pc.commitsTo c p → pc.commitsTo c p' → p = p'

/-- The same-oracle opening relation, allowing evaluation in an algebra of packed coefficients. -/
def evalRel {C : Type} [CommRing C] [Algebra P C] :
    Set (((((Fin m → C) × C) × (∀ j, pc.OStmt j))) × P⦃≤ 1⦄[X Fin m]) :=
  { x | x.1.1.2 = aeval x.1.1.1 x.2.val ∧ pc.commitsTo x.1.2 x.2 }

/-- Retain a public context beside an evaluation of the same committed polynomial. -/
def evalRelWithContext (Context : Type) {C : Type} [CommRing C] [Algebra P C] :
    Set (((Context × ((Fin m → C) × C)) × (∀ j, pc.OStmt j)) × P⦃≤ 1⦄[X Fin m]) :=
  {x | ((x.1.1.2, x.1.2), x.2) ∈ pc.evalRel}

/-- Forgetting the retained context gives the original opening relation. -/
theorem evalRelWithContext_iff (Context : Type) {C : Type} [CommRing C] [Algebra P C]
    (ctx : Context) (r : Fin m → C) (v : C) (ost : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    (((ctx, (r, v)), ost), p) ∈ pc.evalRelWithContext Context ↔
      (((r, v), ost), p) ∈ pc.evalRel := Iff.rfl

/-- Every honest commitment has its true opening at every challenge point. -/
theorem mem_evalRel_commit (honest : pc.Honest) {C : Type} [CommRing C] [Algebra P C]
    (p : P⦃≤ 1⦄[X Fin m]) (r : Fin m → C) :
    (((r, aeval r p.val), honest.commit p), p) ∈ pc.evalRel :=
  ⟨rfl, honest.commitsTo_commit p⟩

/-- Honest coverage rules out an empty opening relation. -/
theorem evalRel_nonempty (honest : pc.Honest) {C : Type} [CommRing C] [Algebra P C] :
    (pc.evalRel (C := C)).Nonempty :=
  ⟨(((fun _ => 0, aeval (fun _ : Fin m => (0 : C)) (0 : P⦃≤ 1⦄[X Fin m]).val),
      honest.commit 0), 0), pc.mem_evalRel_commit honest 0 (fun _ => 0)⟩

end PackedCommitment

end RingSwitching.Packing

end

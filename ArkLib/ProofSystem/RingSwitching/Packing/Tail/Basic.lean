/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.MvPolynomial.Hypercube
import ArkLib.ProofSystem.RingSwitching.Packing.PackedCommitment

/-!
# The same-commitment product-sumcheck relation

The public multiplier and the transported packed polynomial are multilinear over the challenge
ring. Their product has individual degree at most two. Every intermediate relation keeps the
original packed polynomial and its original commitment oracle collection.
-/

noncomputable section
namespace RingSwitching.Packing.Tail
open Polynomial MvPolynomial
variable {P C Context : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}

/-- The challenge-algebra product of the multiplier and coefficient-mapped packed polynomial. -/
def productPoly (A : C⦃≤ 1⦄[X Fin m]) (p : P⦃≤ 1⦄[X Fin m]) : C⦃≤ 2⦄[X Fin m] :=
  ⟨A.val * MvPolynomial.map (algebraMap P C) p.val, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    have hA : A.val.degreeOf i ≤ 1 := degreeOf_le_iff.mpr fun _ h => A.property h i
    have hp : (MvPolynomial.map (algebraMap P C) p.val).degreeOf i ≤ 1 :=
      degreeOf_le_iff.mpr fun _ h => p.property (support_map_subset _ _ h) i
    exact (degreeOf_mul_le i _ _).trans (by omega)⟩

/-- Evaluating the product uses coefficient transport for the original packed polynomial. -/
theorem productPoly_eval (A : C⦃≤ 1⦄[X Fin m]) (p : P⦃≤ 1⦄[X Fin m]) (r : Fin m → C) :
    (productPoly A p).val.eval r = A.val.eval r * aeval r p.val := by
  simp [productPoly, MvPolynomial.eval_map, MvPolynomial.aeval_def]

/-- Public context, previously sampled coordinates, and the remaining cube sum claim. -/
structure Statement (Context C : Type) {m : ℕ} (i : Fin (m + 1)) where
  ctx : Context
  challenges : Fin i → C
  target : C

/-- The exact residual-sum relation at a fixed challenge prefix. -/
def rel (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m)
    (i : Fin (m + 1)) :
    Set (((Statement Context C i) × (∀ j, pc.OStmt j)) × P⦃≤ 1⦄[X Fin m]) :=
  {x | x.1.1.target = hypercubeSum m (productPoly (multiplier x.1.1.ctx) x.2).val
      i x.1.1.challenges ∧ pc.commitsTo x.1.2 x.2}

/-- The initial relation is the Boolean cube sum of the challenge-algebra product. -/
theorem rel_zero (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m)
    (ctx : Context) (target : C) (oStmt : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    ((⟨ctx, Fin.elim0, target⟩, oStmt), p) ∈ rel multiplier pc 0 ↔
      target = ∑ y : Fin m → Fin 2,
        (multiplier ctx).val.eval (y : Fin m → C) *
          aeval (y : Fin m → C) p.val ∧ pc.commitsTo oStmt p := by
  change (target = hypercubeSum m (productPoly (multiplier ctx) p).val 0 Fin.elim0) ∧ _ ↔ _
  rw [hypercubeSum_zero]
  simp only [productPoly_eval]

/-- The terminal relation is exactly the public multiplier times the packed opening. -/
theorem rel_last (multiplier : Context → C⦃≤ 1⦄[X Fin m]) (pc : PackedCommitment P m)
    (stmt : Statement Context C (Fin.last m)) (oStmt : ∀ j, pc.OStmt j)
    (p : P⦃≤ 1⦄[X Fin m]) :
    ((stmt, oStmt), p) ∈ rel multiplier pc (Fin.last m) ↔
      stmt.target = (multiplier stmt.ctx).val.eval stmt.challenges *
        aeval stmt.challenges p.val ∧ pc.commitsTo oStmt p := by
  change (_ = hypercubeSum m _ m _) ∧ _ ↔ _
  rw [hypercubeSum_last, productPoly_eval]

/-- The degree-two honest message for any existing round, without an arity typeclass. -/
def roundMessage (i : Fin m) (H : C⦃≤ 2⦄[X Fin m]) (r : Fin i → C) : C⦃≤ 2⦄[X] :=
  match m with
  | 0 => i.elim0
  | _ + 1 => ⟨roundPoly H.val i r,
      Polynomial.mem_degreeLE.mpr (roundPoly_degree_le H.val i r
        (fun j => degreeOf_le_iff.mpr fun _ h => H.property h j))⟩

/-- The honest round message evaluates to the next remaining cube sum. -/
theorem roundMessage_eval (i : Fin m) (H : C⦃≤ 2⦄[X Fin m]) (r : Fin i → C) (c : C) :
    (roundMessage i H r).val.eval c = hypercubeSum m H.val (i + 1) (Fin.snoc r c) := by
  cases m with
  | zero => exact i.elim0
  | succ n => exact roundPoly_eval H.val i r c

/-- The two Boolean values of the honest message add to the previous cube sum. -/
theorem roundMessage_sum (i : Fin m) (H : C⦃≤ 2⦄[X Fin m]) (r : Fin i → C) :
    (roundMessage i H r).val.eval 0 + (roundMessage i H r).val.eval 1 =
      hypercubeSum m H.val i r := by
  rw [roundMessage_eval, roundMessage_eval]
  cases m with
  | zero => exact i.elim0
  | succ n => exact (hypercubeSum_succ H.val i r).symm

end RingSwitching.Packing.Tail

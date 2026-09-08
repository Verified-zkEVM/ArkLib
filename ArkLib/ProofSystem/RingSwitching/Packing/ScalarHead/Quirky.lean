/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Layout
import Mathlib.LinearAlgebra.Lagrange

/-!
# Flock's quirky scalar claim layout

The original table is indexed by retained bits `y`, the extra Boolean coordinate `b`, and skipped
bits `σ`. The skipped bits enumerate distinct univariate interpolation nodes. Its quirky extension
is multilinear in `(y,b)` and is the degree-bounded Lagrange interpolant in the skipped coordinate.
Packing indexes `(σ,b)` in this order. Appendix B.3's reconstruction weights are exactly
`Lσ(ζ) * eq(ρ,b)`; the retained partial evaluations are unchanged.

## References

* [BRW26] Bünz, Benedikt, Ron Rothblum, and William Wang. "Flock: Fast Proving for Batch
  Boolean Computations." Cryptology ePrint Archive, Report 2026/1329. Appendix A, B.3.
-/

noncomputable section

namespace RingSwitching.Packing.ScalarHead

open MvPolynomial

variable {B : Type} [CommRing B] (data : PackingData B) (m ks : ℕ)

/-- The original table order: retained bits, the extra bit, then the skipped index. -/
abbrev QuirkyTable := ((Fin m → Fin 2) × Fin 2) → (Fin ks → Fin 2) → B

/-- The multilinear table section at one fixed skipped index. -/
def quirkySection (t : QuirkyTable (B := B) m ks) (σ : Fin ks → Fin 2) :
    B⦃≤ 1⦄[X Fin (m + 1)] :=
  ⟨MLE (fun z => t ((fun i => z i.castSucc), z (Fin.last m)) σ), MLE_mem_restrictDegree _⟩

/-- The retained component indexed by the pair `(skipped index, extra bit)`. -/
def quirkyComponent (t : QuirkyTable (B := B) m ks) (v : (Fin ks → Fin 2) × Fin 2) :
    B⦃≤ 1⦄[X Fin m] := ⟨MLE (fun y => t (y, v.2) v.1), MLE_mem_restrictDegree _⟩

/-- Component splitting has an exact inverse that reads the same original table entries. -/
def quirkyComponentsEquiv : QuirkyTable (B := B) m ks ≃
    (((Fin ks → Fin 2) × Fin 2) → B⦃≤ 1⦄[X Fin m]) where
  toFun := quirkyComponent m ks
  invFun ps yb σ := eval (yb.1 : Fin m → B) (ps (σ, yb.2)).val
  left_inv t := by
    funext yb σ
    exact MLE_eval_zeroOne _ _
  right_inv ps := by
    funext v
    apply Subtype.ext
    apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (quirkyComponent m ks _ v).property)
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (ps v).property)
    intro y
    exact MLE_eval_zeroOne _ _

/-- Fixing the extra Boolean coordinate yields the component indexed by `(σ,b)`. -/
theorem quirkySection_splitLast (t : QuirkyTable (B := B) m ks)
    (σ : Fin ks → Fin 2) (b : Fin 2) :
    splitLast 1 m (quirkySection m ks t σ) (fun _ => b) = quirkyComponent m ks t (σ, b) := by
  apply Subtype.ext
  dsimp only [splitLast, quirkyComponent]
  congr 1
  funext y
  rw [← cast_append_bool, quirkySection, MLE_eval_zeroOne]
  simp only [Fin.append_right_eq_snoc, Fin.snoc_castSucc, Fin.snoc_last]

variable [hField : Fact (IsField data.E)]

local instance : Field data.E := hField.out.toField

variable (nodes : (Fin ks → Fin 2) ↪ data.E)

/-- The original quirky extension after fixing its multilinear coordinates. -/
def quirkyPolynomial (t : QuirkyTable (B := B) m ks) (r : Fin m → data.E) (ρ : data.E) :
    Polynomial data.E :=
  Lagrange.interpolate Finset.univ nodes
    (fun σ => aeval (Fin.snoc r ρ) (quirkySection m ks t σ).val)

/-- The quirky extension has the required degree below the number of skip points. -/
theorem quirkyPolynomial_degree (t : QuirkyTable (B := B) m ks)
    (r : Fin m → data.E) (ρ : data.E) :
    (quirkyPolynomial data m ks nodes t r ρ).degree < Fintype.card (Fin ks → Fin 2) := by
  simpa [quirkyPolynomial] using
    (Lagrange.degree_interpolate_lt (s := Finset.univ) (fun σ =>
      aeval (Fin.snoc r ρ) (quirkySection m ks t σ).val) nodes.injective.injOn)

/-- At a skip node, the quirky extension is the original multilinear section. -/
theorem quirkyPolynomial_at_node (t : QuirkyTable (B := B) m ks)
    (r : Fin m → data.E) (ρ : data.E) (σ : Fin ks → Fin 2) :
    (quirkyPolynomial data m ks nodes t r ρ).eval (nodes σ) =
      aeval (Fin.snoc r ρ) (quirkySection m ks t σ).val :=
  Lagrange.eval_interpolate_at_node _ nodes.injective.injOn (Finset.mem_univ _)

/-- The original quirky scalar evaluation reads the univariate coordinate at `ζ`. -/
def quirkyEval (t : QuirkyTable (B := B) m ks) (r : Fin m → data.E) (ρ ζ : data.E) : data.E :=
  (quirkyPolynomial data m ks nodes t r ρ).eval ζ

/-- The two packed-coordinate weights are the skipped Lagrange weight and one Boolean weight. -/
def quirkyWeight (ρ ζ : data.E) (v : (Fin ks → Fin 2) × Fin 2) : data.E :=
  (Lagrange.basis Finset.univ nodes v.1).eval ζ *
    eqTilde (fun _ : Fin 1 => (v.2 : data.E)) (fun _ => ρ)

/-- The quirky scalar evaluation reconstructs with the exact Appendix B.3 weights. -/
theorem quirky_reconstruct (t : QuirkyTable (B := B) m ks)
    (r : Fin m → data.E) (ρ ζ : data.E) :
    quirkyEval data m ks nodes t r ρ ζ =
      ∑ v : (Fin ks → Fin 2) × Fin 2,
        quirkyWeight data ks nodes ρ ζ v * aeval r (quirkyComponent m ks t v).val := by
  classical
  simp only [quirkyEval, quirkyPolynomial, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h := aeval_append_splitLast (R := B) 1 m (quirkySection m ks t σ) r (fun _ => ρ)
  rw [Fin.append_right_eq_snoc] at h
  rw [h]
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  change eqTilde (fun _ : Fin 1 => (b : data.E)) (fun _ => ρ) *
    aeval r (splitLast 1 m (quirkySection m ks t σ) (fun _ => b)).val *
      (Lagrange.basis Finset.univ nodes σ).eval ζ = _
  rw [quirkySection_splitLast]
  unfold quirkyWeight
  ring

/-- Flock's original quirky claim, retaining the exact `(σ,b)` packing order. -/
def flockQuirkyLayout
    (index : data.ιP ≃ ((Fin ks → Fin 2) × Fin 2)) : ClaimLayout data m where
  Source := QuirkyTable (B := B) m ks
  Query := (Fin m → data.E) × data.E × data.E
  components := (quirkyComponentsEquiv m ks).trans
    (Equiv.arrowCongr index.symm (Equiv.refl _))
  point q := q.1
  weight q i := quirkyWeight data ks nodes q.2.1 q.2.2 (index i)
  eval q t := quirkyEval data m ks nodes t q.1 q.2.1 q.2.2
  reconstruct q t := by
    rw [quirky_reconstruct]
    exact (index.sum_comp _).symm

end RingSwitching.Packing.ScalarHead

end

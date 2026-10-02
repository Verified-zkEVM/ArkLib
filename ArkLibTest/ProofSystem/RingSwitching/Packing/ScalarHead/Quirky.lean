/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Quirky
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Field.ZMod

/-!
# Flock's quirky layout on a concrete table

The fixture has one retained bit, one extra bit, and one skipped bit whose two values map to the
non-Boolean field nodes `0` and `2` of `ZMod 5`. At the off-grid query `(r, ρ, ζ) = (2, 2, 4)` the
quirky evaluation is computed from the explicit interpolant, the packed reconstruction is computed
term by term from Lagrange, equality, and component values, and both give `2`. Boolean nodes give a
different value, so the node embedding is observable.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.Quirky

open MvPolynomial Module
open RingSwitching.Packing.ScalarHead

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Rank-four packing indexed by `(skipped bit, extra bit)`, opening directly in `ZMod 5`. -/
abbrev quirkyData : PackingData (ZMod 5) where
  P := ((Fin 1 → Fin 2) × Fin 2) → ZMod 5
  E := ZMod 5
  ιP := (Fin 1 → Fin 2) × Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit (ZMod 5)

local instance : Fact (IsField quirkyData.E) := ⟨Field.toIsField (ZMod 5)⟩

/-- The two skipped Boolean indices enumerate field nodes zero and two, not Boolean nodes. -/
def skipNodes : (Fin 1 → Fin 2) ↪ quirkyData.E where
  toFun σ := 2 * (σ 0 : ZMod 5)
  inj' σ τ h := by
    funext i
    fin_cases i
    have he := mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) h
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (σ 0).isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans (τ 0).isLt (by decide))] at hv
    exact Fin.ext hv

/-- The skip node of `σ` is `2σ`. -/
theorem skipNodes_apply (σ : Fin 1 → Fin 2) : skipNodes σ = 2 * (σ 0 : ZMod 5) := rfl

/-- The table `t(y, b, σ) = y + 2σ + 3b`. -/
def quirkySource : QuirkyTable (B := ZMod 5) 1 1 :=
  fun yb σ => (yb.1 0 : ZMod 5) + 2 * (σ 0 : ZMod 5) + 3 * (yb.2 : ZMod 5)

/-- The quirky layout with packed coordinates indexed by `(σ, b)` directly. -/
abbrev quirky := quirkyLayout quirkyData 1 1 skipNodes (Equiv.refl _)

/-- The unusual skipped/extra order selects the table value at its retained Boolean point. -/
theorem quirky_component_order :
    eval (fun _ => (0 : ZMod 5))
      (quirky.components quirkySource ((fun _ => 1), 0)).val = 2 ∧
    eval (fun _ => (0 : ZMod 5))
      (quirky.components quirkySource ((fun _ => 0), 1)).val = 3 := by
  constructor <;>
    change eval (fun _ => (0 : ZMod 5)) (MLE _) = _ <;>
    rw [show (fun _ : Fin 1 => (0 : ZMod 5)) =
      ((fun _ : Fin 1 => (0 : Fin 2)) : Fin 1 → ZMod 5) from rfl, MLE_eval_zeroOne] <;>
    norm_num [quirkySource]

/-- The non-Boolean skip node selects its own section with weight one. -/
theorem quirky_weight_node :
    quirkyWeight quirkyData 1 skipNodes 0 (skipNodes (fun _ => 1)) ((fun _ => 1), 0) = 1 := by
  let : Field quirkyData.E := (show IsField quirkyData.E from Fact.out).toField
  unfold quirkyWeight
  rw [Lagrange.eval_basis_self skipNodes.injective.injOn (Finset.mem_univ _)]
  norm_num [eqTilde, eqPolynomial, singleEqPolynomial]

/-- The skipped index set has exactly the two constant bit functions. -/
theorem univ_bits : (Finset.univ : Finset (Fin 1 → Fin 2)) = {fun _ => 0, fun _ => 1} := by
  decide

/-- A sum over the one-bit cube is the sum of its two points. -/
private theorem sum_one_bit {M : Type*} [AddCommMonoid M] (f : (Fin 1 → Fin 2) → M) :
    ∑ y, f y = f (fun _ => 0) + f (fun _ => 1) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp f, Fin.sum_univ_two]
  rfl

/-- A Lagrange divisor evaluates to any `w` solving its defining linear equation. -/
theorem eval_basisDivisor_of_mul {F : Type*} [Field F] {x y ζ w : F} (hxy : x ≠ y)
    (h : (x - y) * w = ζ - y) : (Lagrange.basisDivisor x y).eval ζ = w := by
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, ← h, inv_mul_cancel_left₀ (sub_ne_zero.mpr hxy)]

/-- On two nodes, the first Lagrange basis polynomial evaluates to any solution `w` of
`(vᵢ - vⱼ) w = ζ - vⱼ`. The field structure is an implicit argument, so a rewrite adopts the
structure in the goal; the quirky layout's field comes from `IsField`, not from `ZMod.instField`. -/
theorem eval_basis_pair_left {ι F : Type*} [DecidableEq ι] {_ : Field F} {i j : ι}
    {v : ι → F} {ζ w : F} (hij : i ≠ j) (hv : v i ≠ v j) (h : (v i - v j) * w = ζ - v j) :
    (Lagrange.basis {i, j} v i).eval ζ = w := by
  rw [Lagrange.basis_pair_left hij]
  exact eval_basisDivisor_of_mul hv h

/-- On two nodes, the second Lagrange basis polynomial evaluates to any solution `w` of
`(vⱼ - vᵢ) w = ζ - vᵢ`. -/
theorem eval_basis_pair_right {ι F : Type*} [DecidableEq ι] {_ : Field F} {i j : ι}
    {v : ι → F} {ζ w : F} (hij : i ≠ j) (hv : v j ≠ v i) (h : (v j - v i) * w = ζ - v i) :
    (Lagrange.basis {i, j} v j).eval ζ = w := by
  rw [Lagrange.basis_pair_right hij]
  exact eval_basisDivisor_of_mul hv h

/-- At `(r, ρ) = (2, 2)` the multilinear section at skip index `σ` is `3 + 2σ`. -/
theorem section_aeval (σ : Fin 1 → Fin 2) :
    aeval (Fin.snoc (fun _ => (2 : quirkyData.E)) (2 : quirkyData.E) : Fin 2 → quirkyData.E)
      (quirkySection 1 1 quirkySource σ).val = 3 + 2 * (σ 0 : ZMod 5) := by
  rw [aeval_multilinear_eq_sum_eqTilde (quirkySection 1 1 quirkySource σ).property]
  simp only [quirkySection, MLE_eval_zeroOne, eqTilde_eq_prod, quirkySource]
  generalize σ 0 = b
  fin_cases b <;> decide

/-- At `r = 2` the retained component `(σ, b)` is `2 + 2σ + 3b`. -/
theorem component_aeval (σ : Fin 1 → Fin 2) (b : Fin 2) :
    aeval (fun _ => (2 : quirkyData.E)) (quirkyComponent 1 1 quirkySource (σ, b)).val =
      2 + 2 * (σ 0 : ZMod 5) + 3 * (b : ZMod 5) := by
  rw [aeval_multilinear_eq_sum_eqTilde (quirkyComponent 1 1 quirkySource (σ, b)).property]
  simp only [quirkyComponent, MLE_eval_zeroOne, eqTilde_eq_prod, quirkySource]
  generalize σ 0 = c
  fin_cases b <;> fin_cases c <;> decide

/-- Off the node grid, the quirky evaluation at `(r, ρ, ζ) = (2, 2, 4)` is `2`: the section
values `3` and `0` at the nodes `0` and `2` interpolate to `3 + X`. -/
theorem quirkyEval_off_grid :
    quirkyEval quirkyData 1 1 skipNodes quirkySource (fun _ => 2) 2 4 = 2 := by
  let : Field quirkyData.E := (show IsField quirkyData.E from Fact.out).toField
  have hinterp : quirkyPolynomial quirkyData 1 1 skipNodes quirkySource (fun _ => 2) 2 =
      Polynomial.X + Polynomial.C 3 := by
    symm
    apply Lagrange.eq_interpolate_of_eval_eq _ skipNodes.injective.injOn
    · rw [Polynomial.degree_X_add_C, Finset.card_univ]
      decide
    · intro σ _
      rw [section_aeval]
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      rw [skipNodes_apply]
      generalize σ 0 = b
      fin_cases b <;> decide
  rw [quirkyEval, hinterp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  decide

/-- The packed reconstruction, computed term by term from Lagrange weights `4, 2` at `ζ = 4`,
equality weights `4, 2` at `ρ = 2`, and component values `2 + 2σ + 3b`, is also `2`. -/
theorem weighted_sum_off_grid :
    ∑ v, quirkyWeight quirkyData 1 skipNodes 2 4 v *
      aeval (fun _ => (2 : quirkyData.E)) (quirkyComponent 1 1 quirkySource v).val = 2 := by
  have hne : (fun _ : Fin 1 => (0 : Fin 2)) ≠ fun _ => 1 := by decide
  simp only [Fintype.sum_prod_type, sum_one_bit, Fin.sum_univ_two, quirkyWeight]
  rw [component_aeval, component_aeval, component_aeval, component_aeval]
  rw [univ_bits, eval_basis_pair_left (w := 4) hne, eval_basis_pair_right (w := 2) hne]
  · simp only [eqTilde_eq_prod]
    decide
  all_goals first
    | exact skipNodes.injective.ne hne
    | exact skipNodes.injective.ne hne.symm
    | (rw [skipNodes_apply, skipNodes_apply]; decide)

/-- Through the layout record, source evaluation and packed reconstruction agree off the grid. -/
theorem quirky_off_grid :
    quirky.eval (fun _ => 2, 2, 4) quirkySource = 2 ∧
      ∑ i, quirky.weight (fun _ => 2, 2, 4) i *
        aeval (quirky.point (fun _ => 2, 2, 4)) (quirky.components quirkySource i).val = 2 :=
  ⟨quirkyEval_off_grid, weighted_sum_off_grid⟩

/-- Boolean skip nodes `0` and `1`, a naive alternative to the field nodes `0` and `2`. -/
def boolNodes : (Fin 1 → Fin 2) ↪ quirkyData.E where
  toFun σ := (σ 0 : ZMod 5)
  inj' σ τ h := by
    funext i
    fin_cases i
    have hv := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (σ 0).isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans (τ 0).isLt (by decide))] at hv
    exact Fin.ext hv

/-- The Boolean node of `σ` is `σ` itself. -/
theorem boolNodes_apply (σ : Fin 1 → Fin 2) : boolNodes σ = (σ 0 : ZMod 5) := rfl

/-- With Boolean nodes the same table and query evaluate to `1` rather than `2`: the section
values `3` and `0` now sit at `0` and `1` and interpolate to `3 + 2X`. -/
theorem quirkyEval_boolNodes :
    quirkyEval quirkyData 1 1 boolNodes quirkySource (fun _ => 2) 2 4 = 1 := by
  let : Field quirkyData.E := (show IsField quirkyData.E from Fact.out).toField
  have hinterp : quirkyPolynomial quirkyData 1 1 boolNodes quirkySource (fun _ => 2) 2 =
      Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := by
    symm
    apply Lagrange.eq_interpolate_of_eval_eq _ boolNodes.injective.injOn
    · rw [Polynomial.degree_linear (by decide), Finset.card_univ]
      decide
    · intro σ _
      rw [section_aeval]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      rw [boolNodes_apply]
      generalize σ 0 = b
      fin_cases b <;> decide
  rw [quirkyEval, hinterp]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  decide

end RingSwitching.Packing.Tests.Quirky

end

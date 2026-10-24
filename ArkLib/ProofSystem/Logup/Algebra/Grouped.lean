/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.Fraction
public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.Polynomial.PartialFractions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.List.Nodup

/-!
# Grouped denominator-cleared lookup constraints

The grouped scalar circuit folds weighted fractions, checks each helper against its folded pair,
and batches the residuals with the multilinear equality kernel. `reconstruct` consumes the scalar
answers at one query point. Its groups and all ring operations are explicit executable data.

The scalar circuit and its polynomial degree bounds work over a commutative ring. Global clearing
uses a field and an explicit finite row set: an exact cover, zero residuals and a zero helper total
force the global cleared polynomial to vanish at the scalar challenge, including at poles.

Mathlib's sparse `MvPolynomial` arithmetic uses classical finite-support coefficient operations.
The three polynomial-view constructors are individually `noncomputable`. Their evaluation agrees
with the executable circuit for arbitrary input and helper polynomials. With multilinear inputs
and groups of size at most `ell`, the batched polynomial has individual degree at most `ell + 2`.
The Boolean-sum identity interpolates the residual tables; those multilinear extensions are
separate from the generally higher-degree residual polynomials.

The grouped circuit is based on the partial-sum construction of [Hab22]. Version information and
the chosen conventions are recorded in `docs/kb/papers/Hab22.md`.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22]
-/

@[expose] public section

open BigOperators MvPolynomial

namespace Logup

variable {R S : Type*} [CommRing R] [CommRing S] {T K n : ℕ}

/-- Fold a group of weighted linear denominators without division. -/
def groupFraction (group : List (Fin T)) (alpha : R) (value weight : Fin T → R) :
    FractionPair R :=
  FractionPair.sum (group.map fun i ↦ ⟨weight i, alpha - value i⟩)

/-- The denominator-cleared local constraint for one helper value. -/
def groupResidual (group : List (Fin T)) (alpha : R) (value weight : Fin T → R)
    (helper : R) : R :=
  let fraction := groupFraction group alpha value weight
  helper * fraction.denominator - fraction.numerator

/-- Reconstruct the batched scalar from retained source answers at one query point. -/
def reconstruct (groups : Vector (List (Fin T)) K) (alpha : R) (z : Fin n → R)
    (lambda : Fin K → R) (x : Fin n → R) (value weight : Fin T → R)
    (helper : Fin K → R) : R :=
  (∑ k, helper k) + eqTilde z x *
    ∑ k, lambda k * groupResidual groups[k.val] alpha value weight (helper k)

/-- A ring homomorphism preserves the grouped fraction fold. -/
theorem map_groupFraction (f : R →+* S) (group : List (Fin T)) (alpha : R)
    (value weight : Fin T → R) :
    FractionPair.map f (groupFraction group alpha value weight) =
      groupFraction group (f alpha) (fun i ↦ f (value i)) (fun i ↦ f (weight i)) := by
  unfold groupFraction
  rw [FractionPair.map_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [FractionPair.map, map_sub]

/-- Ring homomorphisms preserve grouped residuals. -/
theorem map_groupResidual (f : R →+* S) (group : List (Fin T)) (alpha : R)
    (value weight : Fin T → R) (helper : R) :
    f (groupResidual group alpha value weight helper) =
      groupResidual group (f alpha) (fun i ↦ f (value i)) (fun i ↦ f (weight i)) (f helper) := by
  have h := map_groupFraction f group alpha value weight
  have hn := congrArg FractionPair.numerator h
  have hd := congrArg FractionPair.denominator h
  change f (groupFraction group alpha value weight).numerator = _ at hn
  change f (groupFraction group alpha value weight).denominator = _ at hd
  simp only [groupResidual, map_sub, map_mul, hn, hd]

/-- The polynomial view of one denominator-cleared group residual. -/
noncomputable def residualPolynomial (group : List (Fin T)) (alpha : R)
    (value weight : Fin T → MvPolynomial (Fin n) R) (helper : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  groupResidual group (C alpha) value weight helper

/-- The helper sum plus equality-weighted batched residual polynomial. -/
noncomputable def batchedPolynomial (groups : Vector (List (Fin T)) K) (alpha : R)
    (z : Fin n → R) (lambda : Fin K → R)
    (value weight : Fin T → MvPolynomial (Fin n) R)
    (helper : Fin K → MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  (∑ k, helper k) + eqPolynomial z *
    ∑ k, C (lambda k) * residualPolynomial groups[k.val] alpha value weight (helper k)

/-- Polynomial evaluation agrees with scalar residual reconstruction for every helper. -/
theorem eval_residualPolynomial (group : List (Fin T)) (alpha : R)
    (value weight : Fin T → MvPolynomial (Fin n) R) (helper : MvPolynomial (Fin n) R)
    (x : Fin n → R) :
    eval x (residualPolynomial group alpha value weight helper) =
      groupResidual group alpha (fun i ↦ eval x (value i)) (fun i ↦ eval x (weight i))
        (eval x helper) := by
  simpa only [residualPolynomial, eval_C] using
    map_groupResidual (eval x) group (C alpha) value weight helper

/-- Every polynomial realization reconstructs the same scalar at every query point. -/
theorem eval_batchedPolynomial (groups : Vector (List (Fin T)) K) (alpha : R)
    (z : Fin n → R) (lambda : Fin K → R)
    (value weight : Fin T → MvPolynomial (Fin n) R)
    (helper : Fin K → MvPolynomial (Fin n) R) (x : Fin n → R) :
    eval x (batchedPolynomial groups alpha z lambda value weight helper) =
      reconstruct groups alpha z lambda x (fun i ↦ eval x (value i))
        (fun i ↦ eval x (weight i)) (fun k ↦ eval x (helper k)) := by
  simp [batchedPolynomial, reconstruct, eval_residualPolynomial, eqTilde_eq_eval]

/-- Multilinear factors bound both folded individual degrees by the group length. -/
theorem degreeOf_groupFraction_le (group : List (Fin T)) (alpha : R)
    (value weight : Fin T → MvPolynomial (Fin n) R) (j : Fin n)
    (hv : ∀ i, degreeOf j (value i) ≤ 1) (hw : ∀ i, degreeOf j (weight i) ≤ 1) :
    degreeOf j (groupFraction group (C alpha) value weight).numerator ≤ group.length ∧
      degreeOf j (groupFraction group (C alpha) value weight).denominator ≤ group.length := by
  induction group with
  | nil => simp [groupFraction]
  | cons i group ih =>
    have hd : degreeOf j (C alpha - value i) ≤ 1 := by
      apply (degreeOf_sub_le j _ _).trans
      exact max_le (by simp) (hv i)
    simp only [groupFraction, List.map_cons, FractionPair.sum_cons,
      FractionPair.combine_numerator, FractionPair.combine_denominator, List.length_cons]
    constructor
    · apply (degreeOf_add_le j _ _).trans
      apply max_le
      · exact (degreeOf_mul_le j _ _).trans
          ((add_le_add (hw i) ih.2).trans (by omega))
      · exact (degreeOf_mul_le j _ _).trans (add_le_add ih.1 hd)
    · exact (degreeOf_mul_le j _ _).trans
        ((add_le_add hd ih.2).trans (by omega))

/-- A multilinear helper adds at most one to the group degree bound. -/
theorem degreeOf_residualPolynomial_le (group : List (Fin T)) (alpha : R)
    (value weight : Fin T → MvPolynomial (Fin n) R) (helper : MvPolynomial (Fin n) R)
    (j : Fin n) (hv : ∀ i, degreeOf j (value i) ≤ 1)
    (hw : ∀ i, degreeOf j (weight i) ≤ 1) (hh : degreeOf j helper ≤ 1) :
    degreeOf j (residualPolynomial group alpha value weight helper) ≤ group.length + 1 := by
  have hg := degreeOf_groupFraction_le group alpha value weight j hv hw
  unfold residualPolynomial groupResidual
  apply (degreeOf_sub_le j _ _).trans
  apply max_le
  · exact (degreeOf_mul_le j _ _).trans ((add_le_add hh hg.2).trans (by omega))
  · exact hg.1.trans (Nat.le_succ _)

/-- Bounded group sizes give individual degree at most `ell + 2`. -/
theorem degreeOf_batchedPolynomial_le (groups : Vector (List (Fin T)) K) (alpha : R)
    (z : Fin n → R) (lambda : Fin K → R)
    (value weight : Fin T → MvPolynomial (Fin n) R)
    (helper : Fin K → MvPolynomial (Fin n) R) (ell : ℕ)
    (hgroups : ∀ k : Fin K, groups[k.val].length ≤ ell)
    (j : Fin n) (hv : ∀ i, degreeOf j (value i) ≤ 1)
    (hw : ∀ i, degreeOf j (weight i) ≤ 1) (hh : ∀ k, degreeOf j (helper k) ≤ 1) :
    degreeOf j (batchedPolynomial groups alpha z lambda value weight helper) ≤ ell + 2 := by
  have hsum : degreeOf j (∑ k, helper k) ≤ 1 := by
    apply (degreeOf_sum_le j Finset.univ _).trans
    exact Finset.sup_le fun k _ ↦ hh k
  have hweighted : degreeOf j (∑ k, C (lambda k) *
      residualPolynomial groups[k.val] alpha value weight (helper k)) ≤ ell + 1 := by
    apply (degreeOf_sum_le j Finset.univ _).trans
    apply Finset.sup_le
    intro k _
    have hres := degreeOf_residualPolynomial_le groups[k.val] alpha value weight (helper k)
      j hv hw (hh k)
    apply (degreeOf_mul_le j _ _).trans
    simp only [degreeOf_C, zero_add]
    exact hres.trans (Nat.add_le_add_right (hgroups k) 1)
  unfold batchedPolynomial
  apply (degreeOf_add_le j _ _).trans
  apply max_le
  · exact hsum.trans (by omega)
  · exact (degreeOf_mul_le j _ _).trans
      ((add_le_add (eqPolynomial_degreeOf z j) hweighted).trans (by omega))

/-- Multilinear input and helper polynomials produce a bounded batched polynomial. -/
theorem batchedPolynomial_mem_restrictDegree (groups : Vector (List (Fin T)) K)
    (alpha : R) (z : Fin n → R) (lambda : Fin K → R)
    (value weight : Fin T → MvPolynomial (Fin n) R)
    (helper : Fin K → MvPolynomial (Fin n) R) (ell : ℕ)
    (hgroups : ∀ k : Fin K, groups[k.val].length ≤ ell)
    (hv : ∀ i, value i ∈ restrictDegree (Fin n) R 1)
    (hw : ∀ i, weight i ∈ restrictDegree (Fin n) R 1)
    (hh : ∀ k, helper k ∈ restrictDegree (Fin n) R 1) :
    batchedPolynomial groups alpha z lambda value weight helper ∈
      restrictDegree (Fin n) R (ell + 2) := by
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro j
  exact degreeOf_batchedPolynomial_le groups alpha z lambda value weight helper ell hgroups j
    (fun i ↦ (mem_restrictDegree_iff_degreeOf_le _ _).mp (hv i) j)
    (fun i ↦ (mem_restrictDegree_iff_degreeOf_le _ _).mp (hw i) j)
    (fun k ↦ (mem_restrictDegree_iff_degreeOf_le _ _).mp (hh k) j)

/-- Package the batched polynomial with its checked individual-degree bound. -/
noncomputable def boundedBatchedPolynomial (groups : Vector (List (Fin T)) K)
    (alpha : R) (z : Fin n → R) (lambda : Fin K → R) (ell : ℕ)
    (hgroups : ∀ k : Fin K, groups[k.val].length ≤ ell)
    (value weight : Fin T → restrictDegree (Fin n) R 1)
    (helper : Fin K → restrictDegree (Fin n) R 1) : restrictDegree (Fin n) R (ell + 2) :=
  ⟨batchedPolynomial groups alpha z lambda (fun i ↦ (value i).val)
      (fun i ↦ (weight i).val) (fun k ↦ (helper k).val),
    batchedPolynomial_mem_restrictDegree groups alpha z lambda _ _ _ ell hgroups
      (fun i ↦ (value i).property) (fun i ↦ (weight i).property) (fun k ↦ (helper k).property)⟩

/-- Boolean summation batches the multilinear extensions of the residual tables. -/
theorem sum_eval_batchedPolynomial (groups : Vector (List (Fin T)) K) (alpha : R)
    (z : Fin n → R) (lambda : Fin K → R)
    (value weight : Fin T → MvPolynomial (Fin n) R)
    (helper : Fin K → MvPolynomial (Fin n) R) :
    (∑ x : Fin n → Fin 2, eval (x : Fin n → R)
      (batchedPolynomial groups alpha z lambda value weight helper)) =
      (∑ x : Fin n → Fin 2, ∑ k, eval (x : Fin n → R) (helper k)) +
        ∑ k, lambda k * eval z (MLE (fun x : Fin n → Fin 2 ↦ eval (x : Fin n → R)
          (residualPolynomial groups[k.val] alpha value weight (helper k)))) := by
  classical
  simp only [batchedPolynomial, map_add, map_mul, map_sum, eval_C]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ x : Fin n → Fin 2, eval (x : Fin n → R) (eqPolynomial z) *
      ∑ k, lambda k * eval (x : Fin n → R)
        (residualPolynomial groups[k.val] alpha value weight (helper k))) =
        ∑ k, lambda k * ∑ x : Fin n → Fin 2, eval (x : Fin n → R) (eqPolynomial z) *
          eval (x : Fin n → R)
            (residualPolynomial groups[k.val] alpha value weight (helper k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      rw [MLE_eval]
      apply Finset.sum_congr rfl
      intro x _
      rw [← eqTilde_eq_eval, eqTilde_symm]

private theorem vector_toList_eq_finRange_map {α : Type*} (xs : Vector α K) :
    xs.toList = (List.finRange K).map (fun k ↦ xs[k.val]) := by
  have h := congrArg Vector.toList (Vector.ofFn_getElem (xs := xs))
  simpa only [Vector.toList_ofFn, List.ofFn_eq_map] using h.symm

/-- Local residual identities give a global cleared identity over an exact occurrence cover. -/
theorem groupFraction_numerator_eq_helper_sum_mul_denominator
    (groups : Vector (List (Fin T)) K) (alpha : R) (value weight : Fin T → R)
    (helper : Fin K → R) (hcover : groups.toList.flatten.Perm (List.finRange T))
    (hres : ∀ k : Fin K, groupResidual groups[k.val] alpha value weight (helper k) = 0) :
    (groupFraction (List.finRange T) alpha value weight).numerator =
      (∑ k, helper k) * (groupFraction (List.finRange T) alpha value weight).denominator := by
  let term : Fin T → FractionPair R := fun i ↦ ⟨weight i, alpha - value i⟩
  have hgroups := (vector_toList_eq_finRange_map groups).symm
  have hflatten : ((List.finRange K).map (fun k ↦ groups[k.val].map term)).flatten =
      groups.toList.flatten.map term := by
    rw [List.map_flatten, ← hgroups, List.map_map]
    rfl
  have heq := FractionPair.sum_eq_of_perm (hcover.map term)
  have hscale := FractionPair.sum_flatten_numerator_eq_sum_mul_denominator (List.finRange K)
    (fun k ↦ groups[k.val].map term) helper (fun k _ ↦ by
      exact (sub_eq_zero.mp (hres k)).symm)
  rw [hflatten, heq] at hscale
  simpa only [groupFraction, Fin.sum_univ_def] using hscale

/-- Zero local residuals and helper total force the global fraction-fold numerator to vanish. -/
theorem fold_rows_numerator_eq_zero {ρ : Type*}
    (groups : Vector (List (Fin T)) K) (alpha : R) (rows : List ρ)
    (value weight : Fin T → ρ → R) (helper : Fin K → ρ → R)
    (hcover : groups.toList.flatten.Perm (List.finRange T))
    (hres : ∀ row ∈ rows, ∀ k : Fin K, groupResidual groups[k.val] alpha
      (fun i ↦ value i row) (fun i ↦ weight i row) (helper k row) = 0)
    (htotal : (rows.map (fun row ↦ ∑ k, helper k row)).sum = 0) :
    (FractionPair.sum (rows.map (fun row ↦ (List.finRange T).map fun i ↦
      (⟨weight i row, alpha - value i row⟩ : FractionPair R))).flatten).numerator = 0 := by
  apply FractionPair.sum_flatten_numerator_eq_zero rows _ (fun row ↦ ∑ k, helper k row)
  · intro row hrow
    exact groupFraction_numerator_eq_helper_sum_mul_denominator groups alpha
      (fun i ↦ value i row) (fun i ↦ weight i row) (fun k ↦ helper k row) hcover
      (hres row hrow)
  · exact htotal

section Clearing

variable {ρ F : Type*} [DecidableEq ρ] [Field F]

/-- Local grouped table identities force global denominator clearing at the scalar challenge. -/
theorem eval_clearedNumerator_eq_zero_of_groupResidual_eq_zero
    (groups : Vector (List (Fin T)) K) (alpha : F) (rows : Finset ρ)
    (value weight : Fin T → ρ → F) (helper : Fin K → ρ → F)
    (hcover : groups.toList.flatten.Perm (List.finRange T))
    (hres : ∀ row ∈ rows, ∀ k : Fin K, groupResidual groups[k.val] alpha
      (fun i ↦ value i row) (fun i ↦ weight i row) (helper k row) = 0)
    (htotal : ∑ row ∈ rows, ∑ k, helper k row = 0) :
    Polynomial.eval alpha (PartialFractions.clearedNumerator
      (rows.product (Finset.univ : Finset (Fin T)))
      (fun p ↦ value p.2 p.1) (fun p ↦ weight p.2 p.1)) = 0 := by
  classical
  rw [PartialFractions.eval_clearedNumerator_eq_fold_numerator]
  let occurrence : ρ × Fin T → FractionPair F := fun p ↦
    ⟨weight p.2 p.1, alpha - value p.2 p.1⟩
  change (FractionPair.sum
    ((rows.product (Finset.univ : Finset (Fin T))).toList.map occurrence)).numerator = 0
  have hp : (rows.product (Finset.univ : Finset (Fin T))).toList.Perm
      (rows.toList ×ˢ List.finRange T) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      ((Finset.nodup_toList rows).product (List.nodup_finRange T))).mpr
    rintro ⟨row, i⟩
    simp
  rw [FractionPair.sum_eq_of_perm (hp.map occurrence)]
  have hreshape (rs : List ρ) : (rs ×ˢ List.finRange T).map occurrence =
      (rs.map (fun row ↦ (List.finRange T).map fun i ↦
        (⟨weight i row, alpha - value i row⟩ : FractionPair F))).flatten := by
    induction rs with
    | nil => rfl
    | cons row rs ih => simp [List.product_cons, List.map_map, Function.comp_def, occurrence, ih]
  rw [hreshape]
  apply fold_rows_numerator_eq_zero groups alpha rows.toList value weight helper hcover
  · intro row hrow
    exact hres row (Finset.mem_toList.mp hrow)
  · simpa using htotal

end Clearing

end Logup

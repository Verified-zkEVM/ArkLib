/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.ToMathlib.MvPolynomial.OptionRoots
public import ArkLib.ToMathlib.MvPolynomial.PrefixSubstitution
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Sequential Schwartz–Zippel over pairwise-distinct points

Let `S` be a finite subset of a domain `R`. Drawing the coordinates of a point of `Sⁿ` in order
and without replacement, coordinate `i` takes one of the `#S - i` values not used before it. Let
`I` be a set of coordinates and `P i` a polynomial for each `i ∈ I`, and consider the points `x`
at which, for every `i ∈ I`, `P i` is nonzero after substituting `x j` for each `X j` with
`j < i` and zero after substituting `x j` for each `X j` with `j ≤ i`. Given the coordinates
before `i`, the first substitution is a fixed nonzero polynomial and coordinate `i` is one of its
at most `(P i).degreeOf i` roots in `X i`, the later variables staying symbolic. So among the
`(#S).descFactorial n` points with pairwise-distinct coordinates, the number `N` of such points
satisfies

  `N * ∏ i ∈ I, (#S - i) ≤ (∏ i ∈ I, (P i).degreeOf i) * (#S).descFactorial n`,

which is `card_filter_injective_sequential_le`.

## Main statements

* `MvPolynomial.card_filter_injective_sequential_le`: the sequential bound.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

omit [CommRing R] [IsDomain R] in
/-- A set `A` of points of `Rⁿ` such that, for every coordinate `m` and every `x ∈ A`, the points
of `A` that agree with `x` before `m` take at most `b m` values at `m`, has at most `∏ m, b m`
points. -/
private theorem card_le_prod_of_card_image_le {n : ℕ} (A : Finset (Fin n → R)) (b : Fin n → ℕ)
    (hb : ∀ m, ∀ x ∈ A, #({y ∈ A | ∀ j < m, y j = x j}.image fun y ↦ y m) ≤ b m) :
    #A ≤ ∏ m, b m := by
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero]
    exact card_le_one.mpr fun x _ y _ ↦ funext finZeroElim
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, mul_comm]
    have hfib : ∀ z ∈ A.image Fin.init, #{x ∈ A | Fin.init x = z} ≤ b (Fin.last n) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      refine (card_le_card_of_injOn (fun y ↦ y (Fin.last n)) (fun y hy ↦ ?_) ?_).trans
        (hb (Fin.last n) x hx)
      · obtain ⟨hyA, hyx⟩ := mem_filter.mp (mem_coe.mp hy)
        refine mem_coe.mpr (mem_image_of_mem _ (mem_filter.mpr ⟨hyA, fun j hj ↦ ?_⟩))
        obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
        exact congrFun hyx k
      · intro y hy y' hy' h
        rw [← Fin.snoc_init_self y, ← Fin.snoc_init_self y', (mem_filter.mp (mem_coe.mp hy)).2,
          (mem_filter.mp (mem_coe.mp hy')).2]
        exact congrArg _ h
    refine (card_le_mul_card_image A _ hfib).trans
      (Nat.mul_le_mul_left _ (ih _ _ fun m z hz ↦ ?_))
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    refine (card_le_card fun a ha ↦ ?_).trans (hb m.castSucc x hx)
    obtain ⟨z', hz', rfl⟩ := mem_image.mp ha
    obtain ⟨hz'A, hz'x⟩ := mem_filter.mp hz'
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hz'A
    refine mem_image.mpr ⟨y, mem_filter.mpr ⟨hy, fun j hj ↦ ?_⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr (hj.trans (Fin.castSucc_lt_last m)).ne
    exact hz'x k (Fin.castSucc_lt_castSucc_iff.mp hj)

omit [DecidableEq R] in
/-- Let `q ≠ 0` and let `m` be a variable. Every finite set `Y` of `a` such that substituting
`C a` for `X m` in `q`, and keeping the other variables, gives `0` has `#Y ≤ q.degreeOf m`. -/
private theorem card_le_degreeOf_of_aeval_update_eq_zero {σ : Type*} [DecidableEq σ]
    {q : MvPolynomial σ R} (hq : q ≠ 0) (m : σ) (Y : Finset R)
    (hY : ∀ a ∈ Y, aeval (Function.update X m (C a)) q = 0) :
    #Y ≤ q.degreeOf m := by
  classical
  have hφ : Function.Injective
      (aeval (R := R) (X : {j // j ≠ m} → MvPolynomial {j // j ≠ m} R)) := by
    rw [aeval_X_left]
    exact Function.injective_id
  have hdeg := degreeOf_rename_of_injective (p := q) (Equiv.optionSubtypeNe m).symm.injective m
  rw [Equiv.optionSubtypeNe_symm_self] at hdeg
  rw [← hdeg, ← card_image_of_injective Y (C_injective {j // j ≠ m} R)]
  refine card_le_degreeOf_none_of_aeval_eq_zero hφ (fun h ↦ hq (rename_injective _
    (Equiv.injective _) (h.trans (map_zero _).symm))) _ fun b hb ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
  refine rename_injective _ Subtype.val_injective ?_
  rw [map_zero, ← hY a ha, aeval_rename, comp_aeval_apply]
  refine congrArg (fun f ↦ aeval f q) (funext fun j ↦ ?_)
  by_cases hj : j = m
  · subst hj
    simp
  · simp [Equiv.optionSubtypeNe_symm_of_ne hj, Function.update_of_ne hj]

/-- **Sequential Schwartz–Zippel over pairwise-distinct points.** Let `I` be a set of coordinates
and `P i` a polynomial for each `i ∈ I`. Count the points `x` of `Sⁿ` with pairwise-distinct
coordinates such that, for every `i ∈ I`, `P i` is nonzero after substituting `x j` for each `X j`
with `j < i`, and zero after substituting `x j` for each `X j` with `j ≤ i`. Their number `N`
satisfies `N * ∏ i ∈ I, (#S - i) ≤ (∏ i ∈ I, (P i).degreeOf i) * (#S).descFactorial n`. -/
theorem card_filter_injective_sequential_le {n : ℕ} (S : Finset R) (I : Finset (Fin n))
    (P : Fin n → MvPolynomial (Fin n) R) :
    #{x ∈ Fintype.piFinset fun _ ↦ S | Function.Injective x ∧ ∀ i ∈ I,
        aeval (fun j ↦ if j < i then C (x j) else X j) (P i) ≠ 0 ∧
          aeval (fun j ↦ if j ≤ i then C (x j) else X j) (P i) = 0} *
        ∏ i ∈ I, (#S - i) ≤
      (∏ i ∈ I, (P i).degreeOf i) * (#S).descFactorial n := by
  set A := {x ∈ Fintype.piFinset fun _ : Fin n ↦ S | Function.Injective x ∧ ∀ i ∈ I,
    aeval (fun j ↦ if j < i then C (x j) else X j) (P i) ≠ 0 ∧
      aeval (fun j ↦ if j ≤ i then C (x j) else X j) (P i) = 0}
  have hA : #A ≤ ∏ m, if m ∈ I then (P m).degreeOf m else #S - m := by
    refine card_le_prod_of_card_image_le A _ fun m x hx ↦ ?_
    obtain ⟨hxS, hxinj, hxI⟩ := mem_filter.mp hx
    split_ifs with hm
    · refine (card_le_degreeOf_of_aeval_update_eq_zero (hxI m hm).1 m _ fun a ha ↦ ?_).trans
        (degreeOf_aeval_ite_lt_le m (P m))
      obtain ⟨y, hy, rfl⟩ := mem_image.mp ha
      obtain ⟨hyA, hyx⟩ := mem_filter.mp hy
      rw [comp_aeval_apply]
      refine (congrArg (fun f ↦ aeval f (P m)) (funext fun j ↦ ?_)).trans
        ((mem_filter.mp hyA).2.2 m hm).2
      rcases lt_trichotomy j m with hj | rfl | hj
      · simp [hj, hj.le, hyx j hj]
      · simp
      · simp [hj.not_gt, hj.not_ge, Function.update_of_ne hj.ne']
    · calc _ ≤ #(S \ (Iio m).image x) := card_le_card fun a ha ↦ ?_
        _ = #S - m := by
          rw [card_sdiff_of_subset fun _ hb ↦ ?_, card_image_of_injective _ hxinj, Fin.card_Iio]
          obtain ⟨j, -, rfl⟩ := mem_image.mp hb
          exact Fintype.mem_piFinset.mp hxS j
      obtain ⟨y, hy, rfl⟩ := mem_image.mp ha
      obtain ⟨hyA, hyx⟩ := mem_filter.mp hy
      obtain ⟨hyS, hyinj, -⟩ := mem_filter.mp hyA
      refine mem_sdiff.mpr ⟨Fintype.mem_piFinset.mp hyS m, fun hym ↦ ?_⟩
      obtain ⟨j, hj, hjm⟩ := mem_image.mp hym
      rw [mem_Iio] at hj
      exact hj.ne (hyinj ((hyx j hj).trans hjm))
  have key : (∏ m, if m ∈ I then (P m).degreeOf m else #S - m) * ∏ i ∈ I, (#S - i) =
      (∏ i ∈ I, (P i).degreeOf i) * ∏ m : Fin n, (#S - m) := by
    have h1 : ∏ i ∈ I, (#S - i) = ∏ m, if m ∈ I then #S - m else 1 := by
      rw [prod_ite_mem, univ_inter]
    have h2 : ∏ i ∈ I, (P i).degreeOf i = ∏ m, if m ∈ I then (P m).degreeOf m else 1 := by
      rw [prod_ite_mem, univ_inter]
    rw [h1, h2, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun m _ ↦ ?_
    split_ifs <;> simp [mul_comm]
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ #S - i) n, ← Nat.descFactorial_eq_prod_range] at key
  exact key ▸ Nat.mul_le_mul_right _ hA

end MvPolynomial

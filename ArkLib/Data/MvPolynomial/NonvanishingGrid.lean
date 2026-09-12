/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Multivariate.Eval
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Deterministic nonvanishing search on a supplied scalar grid

The executable search visits the Cartesian power of a supplied list, retaining its order.
It does not enumerate the coefficient field. A grid with more distinct scalars than the
polynomial's total degree detects every nonzero polynomial. Applying this to a top homogeneous
part supplies a direction-search leaf; constructing that part and a monic projection is separate.
-/

@[expose] public section

namespace CPoly.NonvanishingGrid

open CPoly CPoly.CMvPolynomial

variable {E : Type*}

/-- Cartesian points in deterministic lexicographic list order; dimension zero has one point. -/
def gridPoints : (n : ℕ) → List E → List (Fin n → E)
  | 0, _ => [Fin.elim0]
  | n + 1, values => values.flatMap fun a =>
      (gridPoints n values).map fun tail => Fin.cons a tail

/-- The executed Cartesian list contains exactly the points whose coordinates are supplied. -/
theorem mem_gridPoints {n : ℕ} (values : List E) (x : Fin n → E) :
    x ∈ gridPoints n values ↔ ∀ i, x i ∈ values := by
  induction n with
  | zero => simp [gridPoints, Subsingleton.elim x Fin.elim0]
  | succ n ih =>
      simp only [gridPoints, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨a, ha, tail, ht, rfl⟩ i
        exact Fin.cases ha (fun j => (ih tail).mp ht j) i
      · intro hx
        exact ⟨x 0, hx 0, Fin.tail x, (ih _).mpr (fun i => hx i.succ), Fin.cons_self_tail x⟩

variable [CommRing E] [BEq E] [LawfulBEq E]

/-- Return the first supplied-grid point where the stored polynomial evaluates nonzero. -/
def selectNonzero {n : ℕ} (p : CMvPolynomial n E) (values : List E) : Option (Fin n → E) :=
  (gridPoints n values).find? fun x => p.eval x != 0

/-- A returned point lies in the requested scalar grid and has nonzero evaluation. -/
theorem selectNonzero_sound {n : ℕ} {p : CMvPolynomial n E} {values : List E}
    {x : Fin n → E} (h : selectNonzero p values = some x) :
    (∀ i, x i ∈ values) ∧ p.eval x ≠ 0 := by
  refine ⟨(mem_gridPoints values x).mp (List.mem_of_find?_eq_some h), ?_⟩
  simpa using (List.find?_eq_some_iff_append.mp h).1

/-- Every point preceding the selected point evaluates to zero. -/
theorem selectNonzero_first {n : ℕ} {p : CMvPolynomial n E} {values : List E}
    {x : Fin n → E} (h : selectNonzero p values = some x) :
    ∃ before after, gridPoints n values = before ++ x :: after ∧
      ∀ y ∈ before, p.eval y = 0 := by
  obtain ⟨_, before, after, heq, hbefore⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨before, after, heq, by simpa using hbefore⟩

/-- Exhaustion means every point of the supplied Cartesian grid evaluates to zero. -/
theorem selectNonzero_eq_none_iff {n : ℕ} (p : CMvPolynomial n E) (values : List E) :
    selectNonzero p values = none ↔
      ∀ x, (∀ i, x i ∈ values) → p.eval x = 0 := by
  simp [selectNonzero, List.find?_eq_none, mem_gridPoints]

/-- More distinct scalars than total degree force the executed search to find a point.
The theorem uses polynomial nonzeroness, not a supplied nonvanishing evaluation witness. -/
theorem selectNonzero_exists [IsDomain E] [DecidableEq E] {n : ℕ}
    (p : CMvPolynomial n E) (values : List E) (hp : p ≠ 0)
    (hdegree : (fromCMvPolynomial p).totalDegree < values.toFinset.card) :
    ∃ x, selectNonzero p values = some x := by
  classical
  cases hs : selectNonzero p values with
  | some x => exact ⟨x, rfl⟩
  | none =>
      have hzero := (selectNonzero_eq_none_iff p values).mp hs
      have hp' : fromCMvPolynomial p ≠ 0 := by
        intro h
        apply hp
        apply eq_iff_fromCMvPolynomial.mpr
        simpa using h
      have hbound := MvPolynomial.schwartz_zippel_totalDegree hp' values.toFinset
      have hfilter :
          {x ∈ Fintype.piFinset (fun _ : Fin n => values.toFinset) |
            MvPolynomial.eval x (fromCMvPolynomial p) = 0} =
          Fintype.piFinset (fun _ : Fin n => values.toFinset) := by
        apply Finset.filter_eq_self.mpr
        intro x hx
        rw [← eval_equiv]
        exact hzero x (fun i => List.mem_toFinset.mp (Fintype.mem_piFinset.mp hx i))
      have hcard : (values.toFinset.card : ℚ≥0) ≠ 0 := by
        exact_mod_cast (Nat.zero_lt_of_lt hdegree).ne'
      rw [hfilter, Fintype.card_piFinset_const, Nat.cast_pow, div_self (pow_ne_zero n hcard)]
        at hbound
      have hlt : (fromCMvPolynomial p).totalDegree / (values.toFinset.card : ℚ≥0) < 1 := by
        apply (div_lt_one (pos_iff_ne_zero.mpr hcard)).mpr
        exact_mod_cast hdegree
      exact False.elim ((not_le_of_gt hlt) hbound)

/-- A distinct scalar prefix longer than total degree makes nonvanishing search succeed. -/
theorem selectNonzero_exists_of_nodup [IsDomain E] {n : ℕ}
    (p : CMvPolynomial n E) (values : List E) (hp : p ≠ 0) (hdistinct : values.Nodup)
    (hdegree : (fromCMvPolynomial p).totalDegree < values.length) :
    ∃ x, selectNonzero p values = some x := by
  classical
  apply selectNonzero_exists p values hp
  simpa [List.toFinset_card_of_nodup hdistinct] using hdegree

end CPoly.NonvanishingGrid

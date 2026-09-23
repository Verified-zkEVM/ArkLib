/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.BidegreeIncidence

open MvPolynomial

namespace BidegreeIncidenceTest

private abbrev R := MvPolynomial (Option Empty) ℚ

private def zeroPoint : Option Empty → ℚ := fun _ ↦ 0

private theorem X_none_mem_bidegree {σ : Type*} :
    (X none : MvPolynomial (Option σ) ℚ) ∈ restrictBidegree σ ℚ 1 1 := by
  rw [mem_restrictBidegree, support_X]
  simp

private theorem one_mem_bidegree {σ : Type*} :
    (1 : MvPolynomial (Option σ) ℚ) ∈ restrictBidegree σ ℚ 1 1 := by
  rw [mem_restrictBidegree, support_one]
  simp

/-- The distinguished variable does not fit in a zero first bidegree bound. -/
example : (X none : MvPolynomial (Option (Fin 1)) ℚ) ∉
    restrictBidegree (Fin 1) ℚ 0 1 := by
  rw [mem_restrictBidegree, support_X]
  simp

/-- A remaining-coordinate variable does not fit in a zero second bidegree bound. -/
example : (X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∉
    restrictBidegree (Fin 1) ℚ 1 0 := by
  rw [mem_restrictBidegree, support_X]
  simp

private theorem span_X_none_ne_top {σ : Type*} :
    Ideal.span {(X none : MvPolynomial (Option σ) ℚ)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  intro h
  simpa using h.map constantCoeff

private theorem X_none_affineDimension_zero {J : Ideal R}
    (hX : (X none : R) ∈ J) : (affineHilbertPolynomial J).natDegree = 0 := by
  have hle := natDegree_affineHilbertPolynomial_le_of_mem
    (X_ne_zero (none : Option Empty)) hX
  have hle' : (affineHilbertPolynomial J).natDegree ≤ 0 := by simpa using hle
  omega

/-- On one variable, the bidegree pullback degree bounds the single point on `X none = 0`. -/
example : (1 : ℚ) ≤ affineDegree
    ((Ideal.span {(X none : R)}).comap (bidegreeMap Empty ℚ 1 1)) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp
    (F := ℚ) (σ := Empty) (a := 1) (b := 1) (n := 0) (A := 0) (L := 0)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num)
    (g := (X none : R)) (s := (1 : R))
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree) (hs := one_mem_bidegree)
    (highCuts := []) (hhigh := by simp)
    (cuts := fun i ↦ Fin.elim0 i) (hcuts := by intro i; exact Fin.elim0 i)
    (excluded := ∅)
    (hterminal := by
      intro J _ _ hX _ hdim _
      have hd := X_none_affineDimension_zero hX
      omega)
    (S := {zeroPoint}) (hS := by
      intro x hx
      have : x = zeroPoint := Finset.mem_singleton.mp hx
      subst x
      simp [zeroPoint])
    (hA := by intro x hx; exact Nat.zero_le _)
  simpa using h

/-- The sharp estimate also applies when `A > n`; then a nonempty point set is impossible. -/
example : (0 : ℚ) ≤ affineDegree
    ((Ideal.span {(X none : R)}).comap (bidegreeMap Empty ℚ 1 1)) *
      (((0 - 0 + 1 : ℕ) : ℚ) / ((1 - 0 + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial (Ideal.span {(X none : R)})).natDegree := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp
    (F := ℚ) (σ := Empty) (a := 1) (b := 1) (n := 0) (A := 1) (L := 0)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num)
    (g := (X none : R)) (s := (0 : R))
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree) (hs := by simp)
    (highCuts := []) (hhigh := by simp)
    (cuts := fun i ↦ Fin.elim0 i) (hcuts := by intro i; exact Fin.elim0 i)
    (excluded := ∅)
    (hterminal := by
      intro J _ hsJ _ _ _ _
      have hfalse : False := hsJ (by simp)
      intro x hx
      exact hfalse.elim)
    (S := ∅) (hS := by simp) (hA := by simp)
  simpa using h

/-- The hybrid bound also counts this point, whose hypersurface has affine dimension zero. -/
example : (1 : ℚ) ≤ affineDegree
    ((Ideal.span {(X none : R)}).comap (bidegreeMap Empty ℚ 1 1)) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_hybrid
    (F := ℚ) (σ := Empty) (a := 1) (b := 1) (n := 0) (A := 0) (L := 0) (k := 0)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num) (hkA := by norm_num)
    (hAn := by norm_num) (g := (X none : R)) (s := (1 : R))
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hgAB := X_none_mem_bidegree) (hs := one_mem_bidegree)
    (highCuts := []) (hhigh := by simp)
    (cuts := fun i ↦ Fin.elim0 i) (hcuts := by intro i; exact Fin.elim0 i)
    (excluded := ∅)
    (hdimension := by
      intro J _ _ hX _ hdim
      have hd := X_none_affineDimension_zero hX
      omega)
    (hterminal := by
      intro J _ _ hX _ hdim _
      have hd := X_none_affineDimension_zero hX
      omega)
    (S := {zeroPoint}) (hS := by
      intro x hx
      have : x = zeroPoint := Finset.mem_singleton.mp hx
      subst x
      simp [zeroPoint])
    (hA := by intro x hx; exact Nat.zero_le _)
  simpa [hybridDimensionSensitiveIncidenceProduct] using h

/-- The one-coordinate mixed-degree specialization gives the first-factor bound. -/
example : (0 : ℚ) ≤ (1 * 1 + 1 * 1 : ℕ) *
    (((0 - 0 + 1 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ)) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_one
    (F := ℚ) (a := 1) (b := 1) (h := 1) (v := 1) (n := 0) (A := 0) (L := 0)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num)
    (g := (X none : MvPolynomial (Option (Fin 1)) ℚ)) (s := (0 : _))
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree) (hgAB := X_none_mem_bidegree)
    (hs := by simp) (highCuts := []) (hhigh := by simp)
    (cuts := fun i ↦ Fin.elim0 i) (hcuts := by intro i; exact Fin.elim0 i)
    (excluded := ∅)
    (hterminal := by
      intro J _ hsJ _ _ _ _
      have hfalse : False := hsJ (by simp)
      intro x hx
      exact hfalse.elim)
    (S := ∅) (hS := by simp) (hA := by simp)
  norm_num at h ⊢

/-- The two-coordinate mixed-degree specialization gives the squared first-factor bound. -/
example : (0 : ℚ) ≤ (1 * 1 ^ 2 + 2 * 1 * 1 * 1 : ℕ) *
    ((((0 - 0 + 1 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ)) ^ 2) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_two
    (F := ℚ) (a := 1) (b := 1) (h := 1) (v := 1) (n := 0) (A := 0) (L := 0)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num)
    (g := (X none : MvPolynomial (Option (Fin 2)) ℚ)) (s := (0 : _))
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree) (hgAB := X_none_mem_bidegree)
    (hs := by simp) (highCuts := []) (hhigh := by simp)
    (cuts := fun i ↦ Fin.elim0 i) (hcuts := by intro i; exact Fin.elim0 i)
    (excluded := ∅)
    (hterminal := by
      intro J _ hsJ _ _ _ _
      have hfalse : False := hsJ (by simp)
      intro x hx
      exact hfalse.elim)
    (S := ∅) (hS := by simp) (hA := by simp)
  norm_num at h ⊢

/-- The two-coordinate hybrid estimate specializes to its first two incidence factors. -/
example : (0 : ℚ) ≤ (1 * 1 ^ 2 + 2 * 1 * 1 * 1 : ℕ) *
    ((((0 - 0 + 1 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ)) *
      (((0 - 0 + 1 : ℕ) : ℚ) / ((0 - 0 + 1 : ℕ) : ℚ))) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_hybrid_two
    (F := ℚ) (a := 1) (b := 1) (h := 1) (v := 1) (n := 0) (A := 0) (L := 0) (k := 0)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num) (hkA := by norm_num)
    (_hAn := by norm_num) (g := (X none : MvPolynomial (Option (Fin 2)) ℚ))
    (s := (0 : _)) (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree) (highCuts := []) (hhigh := by simp)
    (cuts := fun i ↦ Fin.elim0 i) (hcuts := by intro i; exact Fin.elim0 i)
    (excluded := ∅)
    (hdimension := by
      intro J _ hsJ _ _ _
      have hfalse : False := hsJ (by simp)
      exact hfalse.elim)
    (hterminal := by
      intro J _ hsJ _ _ _ _
      have hfalse : False := hsJ (by simp)
      intro x hx
      exact hfalse.elim)
    (S := ∅) (hS := by simp) (hA := by simp)
  norm_num at h ⊢

end BidegreeIncidenceTest

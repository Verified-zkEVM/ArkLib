/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.BidegreeIncidence

/-!
# Acceptance tests for bidegree hypersurface incidence

Concrete examples exercise the sharp and hybrid incidence bounds on rational points, including
the one- and two-coordinate mixed-degree estimates and boundary cases for bidegree restrictions.

## Main statements

* `MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp`: a rational point satisfies
  the sharp estimate on a one-coordinate hypersurface.
* `MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_one` and
  `MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_two`: mixed-degree estimates
  hold for nonempty point sets in one and two coordinates.
* `MvPolynomial.bidegreeHypersurface_incidence_off_excluded_hybrid` and
  `MvPolynomial.bidegreeHypersurface_incidence_off_excluded_hybrid_two`: hybrid bounds hold in
  the empty-coordinate and two-coordinate examples.

## References

* [BCPZZ26]
-/

open MvPolynomial

namespace BidegreeIncidenceTest

noncomputable section

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

private theorem X_some_mem_bidegree {σ : Type*} (i : σ) :
    (X (some i) : MvPolynomial (Option σ) ℚ) ∈ restrictBidegree σ ℚ 1 1 := by
  rw [mem_restrictBidegree, support_X]
  simp

private theorem X_some_add_one_mem_bidegree {σ : Type*} (i : σ) :
    (X (some i) + 1 : MvPolynomial (Option σ) ℚ) ∈ restrictBidegree σ ℚ 1 1 := by
  apply (restrictBidegree σ ℚ 1 1).add_mem
  · exact X_some_mem_bidegree i
  · exact one_mem_bidegree

private theorem affineDimension_zero_fin1 {J : Ideal (MvPolynomial (Option (Fin 1)) ℚ)}
    (hX : ∀ i, (X i : MvPolynomial (Option (Fin 1)) ℚ) ∈ J) :
    (affineHilbertPolynomial J).natDegree = 0 := by
  classical
  have hdim := natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det
    (v := Function.Embedding.refl (Option (Fin 1))) (A := 1) (by simp)
    (fun i ↦ (X i : MvPolynomial (Option (Fin 1)) ℚ)) hX (by
      intro i
      simp [Matrix.one_apply])
  have hdim' : (affineHilbertPolynomial J).natDegree ≤ 0 := by
    simpa [Nat.card_eq_fintype_card] using hdim
  omega

private theorem affineDimension_zero_fin2 {J : Ideal (MvPolynomial (Option (Fin 2)) ℚ)}
    (hX : ∀ i, (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈ J) :
    (affineHilbertPolynomial J).natDegree = 0 := by
  classical
  have hdim := natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det
    (v := Function.Embedding.refl (Option (Fin 2))) (A := 1) (by simp)
    (fun i ↦ (X i : MvPolynomial (Option (Fin 2)) ℚ)) hX (by
      intro i
      simp [Matrix.one_apply])
  have hdim' : (affineHilbertPolynomial J).natDegree ≤ 0 := by
    simpa [Nat.card_eq_fintype_card] using hdim
  omega

private abbrev oneCoordinatePoint : Option (Fin 1) → ℚ := fun _ ↦ 0
private abbrev twoCoordinatePoint : Option (Fin 2) → ℚ := fun _ ↦ 0

private abbrev oneCoordinateWitness : MvPolynomial (Option (Fin 1)) ℚ :=
  X (some 0) + 1
private abbrev twoCoordinateWitness : MvPolynomial (Option (Fin 2)) ℚ :=
  X (some 0) + 1

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

/-- The one-coordinate mixed-degree specialization bounds a genuine point off its open divisor. -/
example : (1 : ℚ) ≤ (1 * 1 + 1 * 1 : ℕ) *
    (((1 - 1 + 1 : ℕ) : ℚ) / ((1 - 1 + 1 : ℕ) : ℚ)) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_one
    (F := ℚ) (a := 1) (b := 1) (h := 1) (v := 1) (n := 1) (A := 1) (L := 1)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num)
    (g := (X none : MvPolynomial (Option (Fin 1)) ℚ)) (s := oneCoordinateWitness)
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree) (hgAB := X_none_mem_bidegree)
    (hs := X_some_add_one_mem_bidegree 0)
    (highCuts := [X (some 0)]) (hhigh := by
      intro f hf
      simp only [List.mem_singleton] at hf
      subst f
      exact X_some_mem_bidegree 0)
    (cuts := fun _ ↦ (X none : MvPolynomial (Option (Fin 1)) ℚ))
    (hcuts := by intro i; exact X_none_mem_bidegree)
    (excluded := ∅)
    (hterminal := by
      intro J _ _ hgJ hhighJ hd _
      have hXsome : (X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈ J :=
        hhighJ _ (by simp)
      have hdim := affineDimension_zero_fin1 (J := J) (by
        intro i
        cases i with
        | none => exact hgJ
        | some i => fin_cases i; exact hXsome)
      omega)
    (S := {oneCoordinatePoint}) (hS := by
      intro x hx
      have hx' : x = oneCoordinatePoint := Finset.mem_singleton.mp hx
      subst x
      refine ⟨by simp [oneCoordinatePoint], by simp [oneCoordinateWitness], ?_, by simp⟩
      intro f hf
      simp only [List.mem_singleton] at hf
      subst f
      simp [oneCoordinatePoint])
    (hA := by
      intro x hx
      have hx' : x = oneCoordinatePoint := Finset.mem_singleton.mp hx
      subst x
      norm_num [oneCoordinatePoint])
  norm_num at h ⊢

/-- The two-coordinate mixed-degree specialization bounds a genuine point outside the excluded
locus. -/
example : (1 : ℚ) ≤ (1 * 1 ^ 2 + 2 * 1 * 1 * 1 : ℕ) *
    ((((1 - 1 + 1 : ℕ) : ℚ) / ((1 - 1 + 1 : ℕ) : ℚ)) ^ 2) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_sharp_two
    (F := ℚ) (a := 1) (b := 1) (h := 1) (v := 1) (n := 1) (A := 1) (L := 1)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num)
    (g := (X none : MvPolynomial (Option (Fin 2)) ℚ)) (s := twoCoordinateWitness)
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree) (hgAB := X_none_mem_bidegree)
    (highCuts := [X (some 0), X (some 1)]) (hhigh := by
      intro f hf
      have hf' : f = X (some 0) ∨ f = X (some 1) := by simpa using hf
      rcases hf' with h0 | h1
      · rw [h0]
        exact X_some_mem_bidegree 0
      · rw [h1]
        exact X_some_mem_bidegree 1)
    (cuts := fun _ ↦ (X none : MvPolynomial (Option (Fin 2)) ℚ))
    (hcuts := by intro i; exact X_none_mem_bidegree)
    (excluded := ∅)
    (hterminal := by
      intro J _ _ hgJ hhighJ hd _
      have hX0 : (X (some 0) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhighJ _ (by simp)
      have hX1 : (X (some 1) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhighJ _ (by simp)
      have hdim := affineDimension_zero_fin2 (J := J) (by
        intro i
        cases i with
        | none => exact hgJ
        | some i => fin_cases i <;> simp_all)
      omega)
    (S := {twoCoordinatePoint}) (hS := by
      intro x hx
      have hx' : x = twoCoordinatePoint := Finset.mem_singleton.mp hx
      subst x
      refine ⟨by simp [twoCoordinatePoint], by simp [twoCoordinateWitness], ?_, by simp⟩
      intro f hf
      have hf' : f = X (some 0) ∨ f = X (some 1) := by simpa using hf
      rcases hf' with h0 | h1
      · rw [h0]
        simp [twoCoordinatePoint]
      · rw [h1]
        simp [twoCoordinatePoint])
    (hA := by
      intro x hx
      have hx' : x = twoCoordinatePoint := Finset.mem_singleton.mp hx
      subst x
      norm_num [twoCoordinatePoint])
  norm_num at h ⊢

/-- The two-coordinate hybrid estimate bounds a genuine point outside the excluded locus. -/
example : (1 : ℚ) ≤ (1 * 1 ^ 2 + 2 * 1 * 1 * 1 : ℕ) *
    ((((1 - 1 + 1 : ℕ) : ℚ) / ((1 - 1 + 1 : ℕ) : ℚ)) *
      (((1 - 1 + 1 : ℕ) : ℚ) / ((1 - 1 + 1 : ℕ) : ℚ))) := by
  have h := MvPolynomial.bidegreeHypersurface_incidence_off_excluded_hybrid_two
    (F := ℚ) (a := 1) (b := 1) (h := 1) (v := 1) (n := 1) (A := 1) (L := 1) (k := 1)
    (ha := by norm_num) (hb := by norm_num) (hLA := by norm_num) (hkA := by norm_num)
    (_hAn := by norm_num) (g := (X none : MvPolynomial (Option (Fin 2)) ℚ))
    (s := twoCoordinateWitness) (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_bidegree)
    (highCuts := [X (some 0), X (some 1)]) (hhigh := by
      intro f hf
      have hf' : f = X (some 0) ∨ f = X (some 1) := by simpa using hf
      rcases hf' with h0 | h1
      · rw [h0]
        exact X_some_mem_bidegree 0
      · rw [h1]
        exact X_some_mem_bidegree 1)
    (cuts := fun _ ↦ (X none : MvPolynomial (Option (Fin 2)) ℚ))
    (hcuts := by intro i; exact X_none_mem_bidegree)
    (excluded := ∅)
    (hdimension := by
      intro J _ _ hgJ hhighJ hd
      have hX0 : (X (some 0) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhighJ _ (by simp)
      have hX1 : (X (some 1) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhighJ _ (by simp)
      have hdim := affineDimension_zero_fin2 (J := J) (by
        intro i
        cases i with
        | none => exact hgJ
        | some i => fin_cases i <;> simp_all)
      omega)
    (hterminal := by
      intro J _ _ hgJ hhighJ hd _
      have hX0 : (X (some 0) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhighJ _ (by simp)
      have hX1 : (X (some 1) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhighJ _ (by simp)
      have hdim := affineDimension_zero_fin2 (J := J) (by
        intro i
        cases i with
        | none => exact hgJ
        | some i => fin_cases i <;> simp_all)
      omega)
    (S := {twoCoordinatePoint}) (hS := by
      intro x hx
      have hx' : x = twoCoordinatePoint := Finset.mem_singleton.mp hx
      subst x
      refine ⟨by simp [twoCoordinatePoint], by simp [twoCoordinateWitness], ?_, by simp⟩
      intro f hf
      have hf' : f = X (some 0) ∨ f = X (some 1) := by simpa using hf
      rcases hf' with h0 | h1
      · rw [h0]
        simp [twoCoordinatePoint]
      · rw [h1]
        simp [twoCoordinatePoint])
    (hA := by
      intro x hx
      have hx' : x = twoCoordinatePoint := Finset.mem_singleton.mp hx
      subst x
      norm_num [twoCoordinatePoint])
  norm_num at h ⊢

end

end BidegreeIncidenceTest

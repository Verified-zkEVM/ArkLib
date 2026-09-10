/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Bezout
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Cuts

/-! # Finite prime families under successive principal-open cuts -/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial
open scoped BigOperators

variable {F σ : Type*} [Field F] [Finite σ]

/-- Retained children after one cut. A cut already in the prime leaves that prime unchanged. -/
def retainedCutChildren (P : Ideal (MvPolynomial σ F)) (s f : MvPolynomial σ F) :
    Finset (Ideal (MvPolynomial σ F)) := by
  classical
  exact if f ∈ P then {P} else (P ⊔ Ideal.span {f}).retainedMinimalPrimes s

/-- Every child produced by one retained cut is prime, contains the parent and the cut,
and remains on the principal open. -/
theorem mem_retainedCutChildren
    {P Q : Ideal (MvPolynomial σ F)} {s f : MvPolynomial σ F}
    (hP : P.IsPrime) (hs : s ∉ P) :
    Q ∈ retainedCutChildren P s f →
      Q.IsPrime ∧ P ≤ Q ∧ f ∈ Q ∧ s ∉ Q := by
  classical
  intro hQ
  by_cases hf : f ∈ P
  · simp only [retainedCutChildren, hf, if_true, Finset.mem_singleton] at hQ
    subst Q
    exact ⟨hP, le_rfl, hf, hs⟩
  · simp only [retainedCutChildren, hf, if_false] at hQ
    have hQ' := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ
    exact ⟨hQ'.1.isPrime, le_sup_left.trans hQ'.1.le,
      hQ'.1.le ((le_sup_right : Ideal.span {f} ≤ P ⊔ Ideal.span {f})
        (Ideal.subset_span (Set.mem_singleton f))), hQ'.2⟩

/-- One retained cut covers every regular parent point satisfying the new equation. -/
theorem exists_mem_retainedCutChildren_of_mem_zeroLocus
    {E : Type*} [Field E] [Algebra F E]
    {P : Ideal (MvPolynomial σ F)} {s f : MvPolynomial σ F} (x : σ → E)
    (hxP : x ∈ zeroLocus E P) (hxf : aeval x f = 0) (hxs : aeval x s ≠ 0) :
    ∃ Q ∈ retainedCutChildren P s f, x ∈ zeroLocus E Q ∧ aeval x s ≠ 0 := by
  classical
  by_cases hf : f ∈ P
  · exact ⟨P, by simp [retainedCutChildren, hf], hxP, hxs⟩
  · obtain ⟨Q, hQ, hxQ, hsQ⟩ :=
      (mem_zeroLocus_and_cut_iff_retained P s f x).mp ⟨hxP, hxf, hxs⟩
    exact ⟨Q, by simpa [retainedCutChildren, hf] using hQ, hxQ, hsQ⟩

/-- The Bezout potential `degree * b^dimension` does not increase under one
retained cut of degree at most `b`. -/
theorem sum_retainedCutChildren_affineDegree_mul_pow_le
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s f : MvPolynomial σ F} (_hs : s ∉ P) {b : ℕ} (hb : 1 ≤ b)
    (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ retainedCutChildren P s f,
        affineDegree Q * (b : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
      affineDegree P * (b : ℚ) ^ (hilbertPolynomial P).natDegree := by
  classical
  by_cases hf : f ∈ P
  · simp [retainedCutChildren, hf]
  · let children := (P ⊔ Ideal.span {f}).retainedMinimalPrimes s
    have hsubset : children ⊆ minimalPrimesFinset (P ⊔ Ideal.span {f}) := by
      intro Q hQ
      exact mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ).1
    have hsum : ∑ Q ∈ children, affineDegree Q ≤ (b : ℚ) * affineDegree P :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun Q _ _ ↦ affineDegree_nonneg Q)).trans
        (principalCut_sum_affineDegree_le hP hf hfdeg)
    have hchild (Q : Ideal (MvPolynomial σ F)) (hQ : Q ∈ children) :
        (hilbertPolynomial Q).natDegree + 1 = (hilbertPolynomial P).natDegree :=
      principalCut_component_hilbertPolynomial_natDegree_add_one hP hf
        ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ).1
    simp only [retainedCutChildren, hf, if_false]
    change (∑ Q ∈ children,
      affineDegree Q * (b : ℚ) ^ (hilbertPolynomial Q).natDegree) ≤ _
    by_cases hd : (hilbertPolynomial P).natDegree = 0
    · have hempty : children = ∅ := by
        ext Q
        simp only [Finset.notMem_empty, iff_false]
        intro hQ
        have := hchild Q hQ
        omega
      rw [hempty]
      simp only [Finset.sum_empty, hd, pow_zero]
      simpa using affineDegree_nonneg P
    have hdpos : 0 < (hilbertPolynomial P).natDegree := Nat.pos_of_ne_zero hd
    calc
      ∑ Q ∈ children, affineDegree Q * (b : ℚ) ^ (hilbertPolynomial Q).natDegree =
          ∑ Q ∈ children, affineDegree Q *
            (b : ℚ) ^ ((hilbertPolynomial P).natDegree - 1) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [show (hilbertPolynomial Q).natDegree =
          (hilbertPolynomial P).natDegree - 1 by have := hchild Q hQ; omega]
      _ = (∑ Q ∈ children, affineDegree Q) *
          (b : ℚ) ^ ((hilbertPolynomial P).natDegree - 1) := by
        rw [Finset.sum_mul]
      _ ≤ ((b : ℚ) * affineDegree P) *
          (b : ℚ) ^ ((hilbertPolynomial P).natDegree - 1) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
      _ = affineDegree P *
          ((b : ℚ) ^ ((hilbertPolynomial P).natDegree - 1) * (b : ℚ)) := by ring
      _ = affineDegree P * (b : ℚ) ^ (hilbertPolynomial P).natDegree := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ (hilbertPolynomial P).natDegree)]

end AffineHilbert

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.CutFamily.Finite

/-! # Cutting finite families of affine prime components -/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial
open scoped BigOperators

variable {F σ : Type*} [Field F] [Finite σ]

private theorem sum_biUnion_le_sum_sum {α β : Type*} [DecidableEq β]
    (S : Finset α) (T : α → Finset β) (w : β → ℚ) (hw : ∀ q, 0 ≤ w q) :
    ∑ q ∈ S.biUnion T, w q ≤ ∑ P ∈ S, ∑ q ∈ T P, w q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert P S hP ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hP]
      have hinter : 0 ≤ ∑ q ∈ T P ∩ S.biUnion T, w q :=
        Finset.sum_nonneg fun q _ ↦ hw q
      have hunion := Finset.sum_union_inter (s₁ := T P) (s₂ := S.biUnion T) (f := w)
      calc
        ∑ q ∈ T P ∪ S.biUnion T, w q ≤
            (∑ q ∈ T P, w q) + ∑ q ∈ S.biUnion T, w q := by linarith
        _ ≤ (∑ q ∈ T P, w q) + ∑ Q ∈ S, ∑ q ∈ T Q, w q :=
          add_le_add_right ih _

/-- Apply one retained cut simultaneously to a finite prime family. -/
def retainedCutFamily (Ps : Finset (Ideal (MvPolynomial σ F)))
    (s f : MvPolynomial σ F) : Finset (Ideal (MvPolynomial σ F)) :=
  Ps.biUnion fun P ↦ retainedCutChildren P s f

/-- A regular point covered by a parent family and satisfying the new cut remains
covered by the retained child family. -/
theorem exists_mem_retainedCutFamily_of_mem_zeroLocus
    {E : Type*} [Field E] [Algebra F E]
    (Ps : Finset (Ideal (MvPolynomial σ F))) {s f : MvPolynomial σ F} (x : σ → E)
    (hx : ∃ P ∈ Ps, x ∈ zeroLocus E P)
    (hxf : aeval x f = 0) (hxs : aeval x s ≠ 0) :
    ∃ Q ∈ retainedCutFamily Ps s f, x ∈ zeroLocus E Q := by
  obtain ⟨P, hP, hxP⟩ := hx
  obtain ⟨Q, hQ, hxQ, _⟩ :=
    exists_mem_retainedCutChildren_of_mem_zeroLocus x hxP hxf hxs
  exact ⟨Q, Finset.mem_biUnion.mpr ⟨P, hP, hQ⟩, hxQ⟩

/-- One simultaneous retained cut does not increase the total Bezout potential
of a finite prime family. -/
theorem sum_retainedCutFamily_affineDegree_mul_pow_le
    (Ps : Finset (Ideal (MvPolynomial σ F)))
    (hprime : ∀ P ∈ Ps, P.IsPrime) {s f : MvPolynomial σ F}
    (hopen : ∀ P ∈ Ps, s ∉ P) {b : ℕ} (hb : 1 ≤ b) (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ retainedCutFamily Ps s f,
        affineDegree Q * (b : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
      ∑ P ∈ Ps, affineDegree P * (b : ℚ) ^ (hilbertPolynomial P).natDegree := by
  let w : Ideal (MvPolynomial σ F) → ℚ := fun Q ↦
    affineDegree Q * (b : ℚ) ^ (hilbertPolynomial Q).natDegree
  calc
    ∑ Q ∈ retainedCutFamily Ps s f, w Q ≤
        ∑ P ∈ Ps, ∑ Q ∈ retainedCutChildren P s f, w Q := by
      exact sum_biUnion_le_sum_sum Ps (fun P ↦ retainedCutChildren P s f) w
        (fun Q ↦ mul_nonneg (affineDegree_nonneg Q) (by positivity))
    _ ≤ ∑ P ∈ Ps, w P := by
      apply Finset.sum_le_sum
      intro P hP
      exact sum_retainedCutChildren_affineDegree_mul_pow_le
        (hprime P hP) (hopen P hP) hb hfdeg

/-- Successively cut a finite prime family, retaining only components on one
fixed principal open. -/
def iteratedRetainedCutFamily (Ps : Finset (Ideal (MvPolynomial σ F)))
    (s : MvPolynomial σ F) : List (MvPolynomial σ F) →
      Finset (Ideal (MvPolynomial σ F))
  | [] => Ps
  | f :: cuts => iteratedRetainedCutFamily (retainedCutFamily Ps s f) s cuts

theorem iteratedRetainedCutFamily_prime_open
    (Ps : Finset (Ideal (MvPolynomial σ F)))
    (hprime : ∀ P ∈ Ps, P.IsPrime) {s : MvPolynomial σ F}
    (hopen : ∀ P ∈ Ps, s ∉ P) (cuts : List (MvPolynomial σ F)) :
    ∀ Q ∈ iteratedRetainedCutFamily Ps s cuts, Q.IsPrime ∧ s ∉ Q := by
  induction cuts generalizing Ps with
  | nil => exact fun Q hQ ↦ ⟨hprime Q hQ, hopen Q hQ⟩
  | cons f cuts ih =>
      apply ih
      · intro Q hQ
        obtain ⟨P, hP, hchild⟩ := Finset.mem_biUnion.mp hQ
        exact (mem_retainedCutChildren (hprime P hP) (hopen P hP) hchild).1
      · intro Q hQ
        obtain ⟨P, hP, hchild⟩ := Finset.mem_biUnion.mp hQ
        exact (mem_retainedCutChildren (hprime P hP) (hopen P hP) hchild).2.2.2

theorem mem_iteratedRetainedCutFamily_contains
    (Ps : Finset (Ideal (MvPolynomial σ F))) {s : MvPolynomial σ F}
    (cuts : List (MvPolynomial σ F)) {Q : Ideal (MvPolynomial σ F)}
    (hQ : Q ∈ iteratedRetainedCutFamily Ps s cuts) :
    ∃ P ∈ Ps, P ≤ Q ∧ ∀ f ∈ cuts, f ∈ Q := by
  induction cuts generalizing Ps with
  | nil => exact ⟨Q, hQ, le_rfl, by simp⟩
  | cons f cuts ih =>
      obtain ⟨R, hR, hRQ, htail⟩ := ih (retainedCutFamily Ps s f) hQ
      obtain ⟨P, hP, hchild⟩ := Finset.mem_biUnion.mp hR
      have hPR : P ≤ R := by
        by_cases hf : f ∈ P
        · simp only [retainedCutChildren, hf, if_true, Finset.mem_singleton] at hchild
          subst R
          exact le_rfl
        · exact le_sup_left.trans
            ((Ideal.mem_retainedMinimalPrimes _ _ _).mp (by
              simpa [retainedCutChildren, hf] using hchild)).1.le
      have hfR : f ∈ R := by
        by_cases hf : f ∈ P
        · exact hPR hf
        · have hminimal := (Ideal.mem_retainedMinimalPrimes _ _ _).mp (by
            simpa [retainedCutChildren, hf] using hchild)
          exact hminimal.1.le
            ((le_sup_right : Ideal.span {f} ≤ P ⊔ Ideal.span {f})
              (Ideal.subset_span (Set.mem_singleton f)))
      refine ⟨P, hP, hPR.trans hRQ, ?_⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hRQ hfR
      · exact htail g hg

theorem exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
    {E : Type*} [Field E] [Algebra F E]
    (Ps : Finset (Ideal (MvPolynomial σ F))) {s : MvPolynomial σ F}
    (cuts : List (MvPolynomial σ F)) (x : σ → E)
    (hx : ∃ P ∈ Ps, x ∈ zeroLocus E P) (hxs : aeval x s ≠ 0)
    (hcuts : ∀ f ∈ cuts, aeval x f = 0) :
    ∃ Q ∈ iteratedRetainedCutFamily Ps s cuts, x ∈ zeroLocus E Q := by
  induction cuts generalizing Ps with
  | nil =>
      change ∃ Q ∈ Ps, x ∈ zeroLocus E Q
      exact hx
  | cons f cuts ih =>
      apply ih (retainedCutFamily Ps s f)
      · exact exists_mem_retainedCutFamily_of_mem_zeroLocus Ps x hx
          (hcuts f (by simp)) hxs
      · intro g hg
        exact hcuts g (by simp [hg])

theorem sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le
    (Ps : Finset (Ideal (MvPolynomial σ F)))
    (hprime : ∀ P ∈ Ps, P.IsPrime) {s : MvPolynomial σ F}
    (hopen : ∀ P ∈ Ps, s ∉ P) {b : ℕ} (hb : 1 ≤ b)
    (cuts : List (MvPolynomial σ F))
    (hdeg : ∀ f ∈ cuts, f.totalDegree ≤ b) :
    ∑ Q ∈ iteratedRetainedCutFamily Ps s cuts,
        affineDegree Q * (b : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
      ∑ P ∈ Ps, affineDegree P * (b : ℚ) ^ (hilbertPolynomial P).natDegree := by
  induction cuts generalizing Ps with
  | nil => exact le_rfl
  | cons f cuts ih =>
      have hnext (Q : Ideal (MvPolynomial σ F))
          (hQ : Q ∈ retainedCutFamily Ps s f) : Q.IsPrime ∧ s ∉ Q := by
        obtain ⟨P, hP, hchild⟩ := Finset.mem_biUnion.mp hQ
        have hmem := mem_retainedCutChildren (hprime P hP) (hopen P hP) hchild
        exact ⟨hmem.1, hmem.2.2.2⟩
      exact (ih (retainedCutFamily Ps s f)
        (fun Q hQ ↦ (hnext Q hQ).1)
        (fun Q hQ ↦ (hnext Q hQ).2)
        (fun g hg ↦ hdeg g (by simp [hg]))).trans
          (sum_retainedCutFamily_affineDegree_mul_pow_le Ps hprime hopen hb
            (hdeg f (by simp)))

/-- Complete singleton-start specification: the iterated family consists of regular
prime components containing the parent and every cut, covers all regular solutions,
and satisfies the global Bezout-potential bound. -/
theorem iteratedRetainedCutFamily_singleton_spec
    {E : Type*} [Field E] [Algebra F E]
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P) {b : ℕ} (hb : 1 ≤ b)
    (cuts : List (MvPolynomial σ F))
    (hdeg : ∀ f ∈ cuts, f.totalDegree ≤ b) :
    let T := iteratedRetainedCutFamily {P} s cuts
    (∀ Q ∈ T, Q.IsPrime ∧ P ≤ Q ∧ s ∉ Q ∧ ∀ f ∈ cuts, f ∈ Q) ∧
      (∑ Q ∈ T, affineDegree Q * (b : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
        affineDegree P * (b : ℚ) ^ (hilbertPolynomial P).natDegree) ∧
      ∀ x : σ → E, x ∈ zeroLocus E P → aeval x s ≠ 0 →
        (∀ f ∈ cuts, aeval x f = 0) → ∃ Q ∈ T, x ∈ zeroLocus E Q := by
  dsimp only
  have hprime : ∀ Q ∈ ({P} : Finset (Ideal (MvPolynomial σ F))), Q.IsPrime := by
    intro Q hQ
    rw [Finset.mem_singleton.mp hQ]
    exact hP
  have hopen : ∀ Q ∈ ({P} : Finset (Ideal (MvPolynomial σ F))), s ∉ Q := by
    intro Q hQ
    rw [Finset.mem_singleton.mp hQ]
    exact hs
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    have hprimeOpen := iteratedRetainedCutFamily_prime_open {P} hprime hopen cuts Q hQ
    obtain ⟨P₀, hP₀, hP₀Q, hcutsQ⟩ :=
      mem_iteratedRetainedCutFamily_contains {P} cuts hQ
    have hP₀eq : P₀ = P := Finset.mem_singleton.mp hP₀
    subst P₀
    exact ⟨hprimeOpen.1, hP₀Q, hprimeOpen.2, hcutsQ⟩
  · simpa using sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le
      {P} hprime hopen hb cuts hdeg
  · intro x hxP hxs hcuts
    apply exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus {P} cuts x
    · exact ⟨P, Finset.mem_singleton_self P, hxP⟩
    · exact hxs
    · exact hcuts

end AffineHilbert

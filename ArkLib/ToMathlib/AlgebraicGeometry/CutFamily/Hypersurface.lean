/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.CutFamily.Iteration
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Excluded

/-!
# Retained cuts of an affine hypersurface

Starting from one nonzero equation, impose finitely many additional equations while
retaining only components meeting a prescribed principal open. The resulting family
has the original hypersurface's degree potential, including in joint challenge/jet space.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- Initial hypersurface components meeting the open defined by `s`. -/
def hypersurfacePrimeFamily (g s : MvPolynomial σ F) :
    Finset (Ideal (MvPolynomial σ F)) :=
  (Ideal.span {g}).retainedMinimalPrimes s

/-- The retained prime family after all additional equations have been imposed. -/
def hypersurfaceCutFamily (g s : MvPolynomial σ F) (cuts : List (MvPolynomial σ F)) :
    Finset (Ideal (MvPolynomial σ F)) :=
  iteratedRetainedCutFamily (hypersurfacePrimeFamily g s) s cuts

/-- Initial components are prime and meet the prescribed open. -/
theorem hypersurfacePrimeFamily_prime_open (g s : MvPolynomial σ F)
    {P : Ideal (MvPolynomial σ F)} (hP : P ∈ hypersurfacePrimeFamily g s) :
    P.IsPrime ∧ s ∉ P := by
  have h := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hP
  exact ⟨h.1.isPrime, h.2⟩

/-- A nonzero hypersurface has codimension one on every retained component. -/
theorem hypersurfacePrimeFamily_dimension (g s : MvPolynomial σ F) (hg : g ≠ 0)
    {P : Ideal (MvPolynomial σ F)} (hP : P ∈ hypersurfacePrimeFamily g s) :
    (hilbertPolynomial P).natDegree = Nat.card σ - 1 := by
  have hminimal := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hP |>.1
  have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
    (P := (⊥ : Ideal (MvPolynomial σ F))) Ideal.isPrime_bot
    (f := g) (by simpa using hg) (by simpa only [bot_sup_eq] using hminimal)
  rw [hilbertPolynomial_bot_natDegree] at hpure
  omega

/-- Initial degree potential is bounded by the degree of the defining equation. -/
theorem hypersurfacePrimeFamily_potential_le (g s : MvPolynomial σ F) (hg : g ≠ 0)
    {v B : ℕ} (hv : g.totalDegree ≤ v) :
    ∑ P ∈ hypersurfacePrimeFamily g s,
      affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree ≤
      (v : ℚ) * (B : ℚ) ^ (Nat.card σ - 1) := by
  have hsum : ∑ P ∈ hypersurfacePrimeFamily g s, affineDegree P ≤ (v : ℚ) := by
    simpa only [hypersurfacePrimeFamily, bot_sup_eq, affineDegree_bot, mul_one] using
      sum_retained_affineDegree_le
        (P := (⊥ : Ideal (MvPolynomial σ F))) Ideal.isPrime_bot
        (s := s) (f := g) (by simpa using hg) hv
  calc
    _ = (∑ P ∈ hypersurfacePrimeFamily g s, affineDegree P) *
        (B : ℚ) ^ (Nat.card σ - 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P hP
      rw [hypersurfacePrimeFamily_dimension g s hg hP]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)

/-- Every final component contains the initial equation and all additional equations. -/
theorem hypersurfaceCutFamily_spec (g s : MvPolynomial σ F)
    (cuts : List (MvPolynomial σ F)) {P : Ideal (MvPolynomial σ F)}
    (hP : P ∈ hypersurfaceCutFamily g s cuts) :
    P.IsPrime ∧ s ∉ P ∧ g ∈ P ∧ ∀ f ∈ cuts, f ∈ P := by
  have hpo := iteratedRetainedCutFamily_prime_open (hypersurfacePrimeFamily g s)
    (fun J hJ ↦ (hypersurfacePrimeFamily_prime_open g s hJ).1)
    (fun J hJ ↦ (hypersurfacePrimeFamily_prime_open g s hJ).2) cuts P hP
  obtain ⟨P₀, hP₀, hle, hcuts⟩ := mem_iteratedRetainedCutFamily_contains
    (hypersurfacePrimeFamily g s) cuts hP
  have hminimal := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hP₀ |>.1
  exact ⟨hpo.1, hpo.2, hle (hminimal.le (Ideal.subset_span (Set.mem_singleton g))), hcuts⟩

/-- Every regular solution of all equations belongs to a retained component. -/
theorem hypersurfaceCutFamily_covers {E : Type*} [Field E] [Algebra F E]
    (g s : MvPolynomial σ F) (cuts : List (MvPolynomial σ F)) (x : σ → E)
    (hg : aeval x g = 0) (hs : aeval x s ≠ 0)
    (hcuts : ∀ f ∈ cuts, aeval x f = 0) :
    ∃ P ∈ hypersurfaceCutFamily g s cuts, x ∈ zeroLocus E P := by
  apply exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
    (hypersurfacePrimeFamily g s) cuts x
  · apply exists_retainedMinimalPrime_of_mem_zeroLocus (Ideal.span {g}) s x _ hs
    change Ideal.span {g} ≤ RingHom.ker (aeval x).toRingHom
    rw [Ideal.span_singleton_le_iff_mem]
    exact hg
  · exact hs
  · exact hcuts

/-- Imposing bounded-degree cuts preserves the hypersurface degree potential. -/
theorem hypersurfaceCutFamily_potential_le (g s : MvPolynomial σ F) (hg : g ≠ 0)
    {v B : ℕ} (hv : g.totalDegree ≤ v) (hB : 1 ≤ B)
    (cuts : List (MvPolynomial σ F)) (hcuts : ∀ f ∈ cuts, f.totalDegree ≤ B) :
    ∑ P ∈ hypersurfaceCutFamily g s cuts,
      affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree ≤
      (v : ℚ) * (B : ℚ) ^ (Nat.card σ - 1) := by
  exact (sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le
    (hypersurfacePrimeFamily g s)
    (fun P hP ↦ (hypersurfacePrimeFamily_prime_open g s hP).1)
    (fun P hP ↦ (hypersurfacePrimeFamily_prime_open g s hP).2)
    hB cuts hcuts).trans (hypersurfacePrimeFamily_potential_le g s hg hv)

/-- Additional equations cannot increase a component's dimension. -/
theorem hypersurfaceCutFamily_dimension_le (g s : MvPolynomial σ F) (hg : g ≠ 0)
    (cuts : List (MvPolynomial σ F)) {P : Ideal (MvPolynomial σ F)}
    (hP : P ∈ hypersurfaceCutFamily g s cuts) :
    (hilbertPolynomial P).natDegree ≤ Nat.card σ - 1 := by
  obtain ⟨P₀, hP₀, hle, _⟩ := mem_iteratedRetainedCutFamily_contains
    (hypersurfacePrimeFamily g s) cuts hP
  exact (hilbertPolynomial_degree_and_leadingCoeff_antitone hle
    (hypersurfaceCutFamily_spec g s cuts hP).1.ne_top).1.trans_eq
    (hypersurfacePrimeFamily_dimension g s hg hP₀)

/-- Agreement incidence on a cut hypersurface, excluding every positive-dimensional
component on which at least `L` agreement equations hold identically. -/
theorem hypersurfaceCutFamily_incidence_off_excluded
    (g s : MvPolynomial σ F) (hg : g ≠ 0) {v B n A L : ℕ}
    (hv : g.totalDegree ≤ v) (hB : 0 < B)
    (highCuts : List (MvPolynomial σ F))
    (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B)
    (cuts : Fin n → MvPolynomial σ F) (hcuts : ∀ i, (cuts i).totalDegree ≤ B)
    (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hterminal : ∀ P : Ideal (MvPolynomial σ F),
      P.IsPrime → s ∉ P → g ∈ P → (∀ f ∈ highCuts, f ∈ P) →
      0 < (hilbertPolynomial P).natDegree →
      L ≤ (cutsInIdeal P cuts).card → principalOpenZeroLocus P s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ (v : ℚ) *
      (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ (Nat.card σ - 1) := by
  classical
  let T := hypersurfaceCutFamily g s highCuts
  let D := Nat.card σ - 1
  let t : ℚ := (n : ℚ) / ((A - L + 1 : ℕ) : ℚ)
  have hden : 0 < A - L + 1 := by omega
  have hdenn : A - L + 1 ≤ n := by omega
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast hden)).2
    simpa using (show ((A - L + 1 : ℕ) : ℚ) ≤ (n : ℚ) by exact_mod_cast hdenn)
  have hratio : (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) = (B : ℚ) * t := by
    dsimp [t]
    push_cast
    ring
  have hcover : S.card ≤ ∑ P ∈ T, (componentPoints S P).card := by
    apply le_trans _ (Finset.card_biUnion_le)
    apply Finset.card_le_card
    intro x hx
    obtain ⟨P, hP, hxP⟩ := hypersurfaceCutFamily_covers g s highCuts x
      (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2.1
    exact Finset.mem_biUnion.mpr ⟨P, hP, by rw [mem_componentPoints]; exact ⟨hx, hxP⟩⟩
  have hcomponent (P : Ideal (MvPolynomial σ F)) (hP : P ∈ T) :
      ((componentPoints S P).card : ℚ) ≤
        affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree * t ^ D := by
    obtain ⟨hp, hs, hgP, hhP⟩ := hypersurfaceCutFamily_spec g s highCuts hP
    have hi := affineAgreementIncidence_bound_off_excluded hp hs cuts hcuts hB hLA
      excluded (fun J hPJ hJ hsJ hdJ hcJ ↦ hterminal J hJ hsJ (hPJ hgP)
        (fun f hf ↦ hPJ (hhP f hf)) hdJ hcJ) (componentPoints S P)
      (fun x hx ↦ by
        rw [mem_componentPoints] at hx
        exact ⟨⟨hx.2, (hS x hx.1).2.1⟩, (hS x hx.1).2.2.2⟩)
      (fun x hx ↦ by rw [mem_componentPoints] at hx; exact hA x hx.1)
    rw [hratio, mul_pow, ← mul_assoc] at hi
    apply hi.trans
    apply mul_le_mul_of_nonneg_left
    · exact pow_le_pow_right₀ ht (hypersurfaceCutFamily_dimension_le g s hg highCuts hP)
    · exact mul_nonneg (affineDegree_nonneg P) (by positivity)
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T, ((componentPoints S P).card : ℚ) := by
      exact_mod_cast hcover
    _ ≤ ∑ P ∈ T,
        affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree * t ^ D :=
      Finset.sum_le_sum hcomponent
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
        t ^ D := by rw [Finset.sum_mul]
    _ ≤ ((v : ℚ) * (B : ℚ) ^ D) * t ^ D :=
      mul_le_mul_of_nonneg_right
        (hypersurfaceCutFamily_potential_le g s hg hv hB highCuts hhigh)
        (by positivity)
    _ = _ := by rw [hratio, mul_pow]; ring

end AffineHilbert

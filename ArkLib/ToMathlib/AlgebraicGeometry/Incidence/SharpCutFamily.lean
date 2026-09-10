/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.CutFamily.Iteration
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Agreement
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpExcluded

/-! # Sharp incidence summation after retained linear cuts -/

@[expose] public section

noncomputable section
open MvPolynomial
open scoped BigOperators
namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- Sum any sharp per-prime off-excluded incidence theorem after imposing a list of
degree-one high cuts on an initial retained prime family. -/
theorem iteratedRetainedCutFamily_incidence_sharp
    (T₀ : Finset (Ideal (MvPolynomial σ F))) (s : MvPolynomial σ F)
    (hprime : ∀ P ∈ T₀, P.IsPrime) (hopen : ∀ P ∈ T₀, s ∉ P)
    {d : ℕ} (hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = d)
    {V t : ℚ} (ht : 1 ≤ t) (hV : ∑ P ∈ T₀, affineDegree P ≤ V)
    (highCuts : List (MvPolynomial σ F))
    (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ 1)
    (S : Finset (σ → F))
    (hcover : ∀ x ∈ S, ∃ P ∈ iteratedRetainedCutFamily T₀ s highCuts,
      x ∈ zeroLocus F P)
    (hperPrime : ∀ P ∈ iteratedRetainedCutFamily T₀ s highCuts,
      ((componentPoints S P).card : ℚ) ≤
        affineDegree P * t ^ (hilbertPolynomial P).natDegree) :
    (S.card : ℚ) ≤ V * t ^ d := by
  classical
  let T := iteratedRetainedCutFamily T₀ s highCuts
  have hTprime : ∀ P ∈ T, P.IsPrime :=
    fun P hP ↦ (iteratedRetainedCutFamily_prime_open T₀ hprime hopen highCuts P hP).1
  have hTdim : ∀ P ∈ T, (hilbertPolynomial P).natDegree ≤ d := by
    intro P hP
    obtain ⟨P₀, hP₀, hle, _⟩ := mem_iteratedRetainedCutFamily_contains T₀ highCuts hP
    exact (hilbertPolynomial_degree_and_leadingCoeff_antitone hle (hTprime P hP).ne_top).1
      |>.trans_eq (hdim P₀ hP₀)
  have hdegree : ∑ P ∈ T, affineDegree P ≤ V := by
    have hp := sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le T₀ hprime hopen
      (show 1 ≤ (1 : ℕ) by omega) highCuts hhigh
    have hV' : ∑ P ∈ T₀, affineDegree P * (1 : ℚ) ^
        (hilbertPolynomial P).natDegree ≤ V := by simpa using hV
    simpa using hp.trans hV'
  have hcard : S.card ≤ ∑ P ∈ T, (componentPoints S P).card := by
    apply le_trans _ Finset.card_biUnion_le
    apply Finset.card_le_card
    intro x hx
    obtain ⟨P, hPT, hxP⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨P, hPT, by rw [mem_componentPoints]; exact ⟨hx, hxP⟩⟩
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T, ((componentPoints S P).card : ℚ) := by exact_mod_cast hcard
    _ ≤ ∑ P ∈ T, affineDegree P * t ^ (hilbertPolynomial P).natDegree :=
      Finset.sum_le_sum hperPrime
    _ ≤ ∑ P ∈ T, affineDegree P * t ^ d := by
      apply Finset.sum_le_sum
      intro P hP
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (hTdim P hP))
        (affineDegree_nonneg P)
    _ = (∑ P ∈ T, affineDegree P) * t ^ d := by rw [Finset.sum_mul]
    _ ≤ V * t ^ d := mul_le_mul_of_nonneg_right hdegree (by positivity)

/-- Sharp off-excluded incidence after imposing degree-one high cuts on an initial
prime family.  The terminal hypothesis is stated for every prime extension of an
initial component, so it applies hereditarily after all retained cuts. -/
theorem iteratedRetainedCutFamily_incidence_off_excluded_sharp
    (T₀ : Finset (Ideal (MvPolynomial σ F))) (s : MvPolynomial σ F)
    (hprime : ∀ P ∈ T₀, P.IsPrime) (hopen : ∀ P ∈ T₀, s ∉ P)
    {d : ℕ} (hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = d)
    {V : ℚ} (hV : ∑ P ∈ T₀, affineDegree P ≤ V)
    (highCuts : List (MvPolynomial σ F))
    (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ 1)
    {n A L b : ℕ}
    (cuts : Fin n → MvPolynomial σ F) (hcuts : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hLA : L ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hterminal : ∀ P ∈ T₀, ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, (∃ P ∈ T₀, x ∈ zeroLocus F P) ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ V *
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
  classical
  let t : ℚ := (((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)
  have hdenNat : 0 < A - L + 1 := by omega
  have hnumNat : A - L + 1 ≤ (n - L + 1) * b := by
    exact (show A - L + 1 ≤ n - L + 1 by omega).trans
      (Nat.le_mul_of_pos_right (n - L + 1) hb)
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (show (0 : ℚ) < (A - L + 1 : ℕ) by exact_mod_cast hdenNat)).2
    simpa only [one_mul] using
      (show ((A - L + 1 : ℕ) : ℚ) ≤ (((n - L + 1) * b : ℕ) : ℚ) by
        exact_mod_cast hnumNat)
  apply iteratedRetainedCutFamily_incidence_sharp T₀ s hprime hopen hdim ht hV
    highCuts hhigh S
  · intro x hx
    exact exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus T₀ highCuts x
      (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2.1
  · intro P hP
    obtain ⟨P₀, hP₀, hP₀P, hhighP⟩ :=
      mem_iteratedRetainedCutFamily_contains T₀ highCuts hP
    have hprimeOpen :=
      iteratedRetainedCutFamily_prime_open T₀ hprime hopen highCuts P hP
    apply affineAgreementIncidence_bound_off_excluded_sharp hprimeOpen.1 hprimeOpen.2
      cuts hcuts hb hLA hAn excluded
    · intro Q hPQ hQ hsQ hdQ hcutsQ
      exact hterminal P₀ hP₀ Q (hP₀P.trans hPQ) hQ hsQ
        (fun f hf ↦ hPQ (hhighP f hf)) hdQ hcutsQ
    · intro x hx
      rw [mem_componentPoints] at hx
      exact ⟨⟨hx.2, (hS x hx.1).2.1⟩, (hS x hx.1).2.2.2⟩
    · intro x hx
      rw [mem_componentPoints] at hx
      exact hA x hx.1

end AffineHilbert

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.HighCutGeometry
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpPrimeFamily
/-!
# Sharp counting of regular Taylor-chart solutions

Agreement at `A` positions gives the incidence ratio `(n-k+1)/(A-k+1)`.
This fixed-word count is shared by list bounds and mutual correlated agreement.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential



open MvPolynomial AffineHilbert
open scoped BigOperators

variable {F : Type*} [Field F] {r : ℕ}

/-- Finite regular high-cut jets obey the sharp ordinary-chart incidence ratio at any
sufficient common Taylor exponent. -/
theorem finite_regularHighCutJets_card_le_sharp_of_exponent
    [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val (τ := τ)) = 0)
    (hA : ∀ jet ∈ S, A ≤ (agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i) (τ := τ))
        jet).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        ((((((n - k + 1) * rationalTaylorCutDegreeBound Q K (τ := τ) : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) ^ r) := by
  classical
  let B := rationalTaylorCutDegreeBound Q K (τ := τ)
  let T := highTaylorPrimeFamily center Q K k (τ := τ)
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) F := fun i ↦
    taylorAgreementEquation center Q K (domain i) (received i) (τ := τ)
  let R : ℚ := (((n - k + 1) * B : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  let t : ℚ := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hinit : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_separant_ne_zero center Q hsep
  have hB : 0 < B := by simp [B, rationalTaylorCutDegreeBound]
  have hcNat : 0 < A - k + 1 := by omega
  have hcn : A - k + 1 ≤ n - k + 1 := by omega
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast hcNat)).2
    simpa only [one_mul] using (show ((A - k + 1 : ℕ) : ℚ) ≤
      ((n - k + 1 : ℕ) : ℚ) by exact_mod_cast hcn)
  have hR : R = (B : ℚ) * t := by
    dsimp only [R, t]
    push_cast
    field_simp
  have hspec := highTaylorPrimeFamily_spec (F := F) (E := F) center Q K k (τ := τ)
  have hcoverNat : S.card ≤
      ∑ P ∈ T, (componentPoints S P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ componentPoints S P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := hspec.2 jet
          (hS jet hjet).1 (hS jet hjet).2.1 (hS jet hjet).2.2
        exact Finset.mem_biUnion.mpr ⟨P, hPT, by
          rw [mem_componentPoints]
          exact ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (componentPoints S P).card := Finset.card_biUnion_le
  have hcover : (S.card : ℚ) ≤
      ∑ P ∈ T, ((componentPoints S P).card : ℚ) := by
    exact_mod_cast hcoverNat
  have hcomponent : ∀ P ∈ T,
      ((componentPoints S P).card : ℚ) ≤
        affineDegree P * R ^ (hilbertPolynomial P).natDegree := by
    intro P hPT
    have hPspec := hspec.1 P hPT
    apply affineAgreementIncidence_bound_sharp hPspec.1 hPspec.2.1
      cuts (fun i ↦ totalDegree_taylorAgreementEquation_le_of_exponent
        center Q hv K τ hτ _ _)
      hB hk hkA hAn (componentPoints S P)
    · intro jet hjet
      rw [mem_componentPoints] at hjet
      exact ⟨hjet.2, (hS jet hjet.1).2.1⟩
    · intro jet hjet
      rw [mem_componentPoints] at hjet
      exact hA jet hjet.1
    · intro U hU jet jet' hjetP hjetS hjetP' hjetS' hzero
      apply eq_of_mem_principalOpen_of_highCuts_of_agreementFinset_of_exponent
        center Q K k τ hτ hK P hPspec.2.2 domain received U hU
        ⟨hjetP, hjetS⟩ ⟨hjetP', hjetS'⟩
      · intro i hi
        exact (hzero i hi).1
      · intro i hi
        exact (hzero i hi).2
  have hpotential := sum_highTaylorPrimeFamily_affineDegree_mul_pow_le_of_exponent
    center Q hsep hv K k τ hτ
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T,
        ((componentPoints S P).card : ℚ) := hcover
    _ ≤ ∑ P ∈ T, affineDegree P * R ^ (hilbertPolynomial P).natDegree :=
      Finset.sum_le_sum hcomponent
    _ = ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          t ^ (hilbertPolynomial P).natDegree := by
      apply Finset.sum_congr rfl
      intro P _
      rw [hR, mul_pow]
      ring
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          t ^ r := by
      apply Finset.sum_le_sum
      intro P hPT
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_right₀ ht
          (highTaylorPrimeFamily_hilbertPolynomial_natDegree_le
            center Q K k (τ := τ) hinit hPT)
      · exact mul_nonneg (affineDegree_nonneg P) (by positivity)
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^
          (hilbertPolynomial P).natDegree) * t ^ r := by rw [Finset.sum_mul]
    _ ≤ (((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) : ℚ) *
          (B : ℚ) ^ r) * t ^ r :=
      mul_le_mul_of_nonneg_right hpotential (by positivity)
    _ = ((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) : ℚ) *
          R ^ r := by
      rw [hR, mul_pow]
      ring

/-- Compatibility form of the sharp chart incidence theorem at exponent `2K`. -/
theorem finite_regularHighCutJets_card_le_sharp
    [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ) (hK : r < K)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Fin (r + 1) → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val) = 0)
    (hA : ∀ jet ∈ S, A ≤ (agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i)) jet).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        ((((((n - k + 1) * rationalTaylorCutDegreeBound Q K : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ))) ^ r) := by
  exact finite_regularHighCutJets_card_le_sharp_of_exponent center Q K k (2 * K)
    (taylorExponentSufficient_two_mul r K) hK hsep hv domain received hk hkA hAn S hS hA

end ReedSolomon.HiddenDerivative

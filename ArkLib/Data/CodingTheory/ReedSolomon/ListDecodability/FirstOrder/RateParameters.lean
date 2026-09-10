/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.RateCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SharpListBound
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.RateLimits
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
/-!
# First-order rate-dependent list bounds

The finite parameter certificate is selected before the block length and received
word. Its equation explains the entire close list. Summing the successive jet
degrees gives the advertised square-sum constant.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

universe u

open Polynomial HiddenDerivative PolynomialDifferential
open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation
open scoped BigOperators

/-- The square sum through the weak total-jet cap. -/
def firstOrderRateSquareSum (μ : ℕ) : ℕ := ∑ j ∈ Finset.range (μ + 1), j ^ 2

/-- The first-order scalar list constant. -/
def firstOrderRateListConstant (δ : ℝ) (μ : ℕ) : ℝ :=
  1 + 2 * firstOrderRateSquareSum μ / δ

/-- Every derivative-cap-sensitive chain is bounded by the full square sum. -/
theorem firstOrderListWeight_le_squareSum {K : ℕ} (hK : 0 < K) (μ M : ℕ) :
    firstOrderListWeight K μ M ≤ 2 * K * firstOrderRateSquareSum μ := by
  induction μ generalizing M with
  | zero => simp [firstOrderListWeight, firstOrderRateSquareSum]
  | succ μ ih =>
    have hsum : firstOrderRateSquareSum (μ + 1) =
        firstOrderRateSquareSum μ + (μ + 1) ^ 2 := by
      exact Finset.sum_range_succ _ _
    rw [hsum]
    cases M with
    | zero =>
      simp only [firstOrderListWeight]
      have h := ih 0
      nlinarith
    | succ M =>
      simp only [firstOrderListWeight]
      have h := ih M
      nlinarith

open Classical in
/-- A first-order certificate gives the rate-first scalar constant for every finite close list. -/
theorem finite_firstOrderRate_list_bound_of_certificate
    {F : Type u} [Field F] {D A m M μ k h n N K : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F) D A m M μ k h domain received
      (fun _ ↦ 0) columns)
    (hK : 1 < K) (hkK : k ≤ K) (hKn : K ≤ n)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hδ : 0 < δ) (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F)
    (S : Finset F[X]) (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℝ) ≤ firstOrderRateListConstant δ μ * n := by
  have hcard := firstOrder_finite_agreement_solutions_card_le_sharp
    domain received columns cert hK hkK hKn hk hkA hAn hchar S hS
  have hcardR : (S.card : ℝ) ≤
      (n : ℝ) * firstOrderListWeight K μ M / (A - k + 1 : ℕ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcard
    simpa only [Rat.cast_natCast, Rat.cast_div, Rat.cast_mul, Nat.cast_mul] using h
  have hn : 0 < n := hk.trans_le (hkK.trans hKn)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (A - k + 1 : ℕ) := by positivity
  have hgap' : δ * (n : ℝ) ≤ (A - k + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_sub hkA, Nat.cast_one]
    linarith
  have hw : (firstOrderListWeight K μ M : ℝ) ≤
      2 * K * firstOrderRateSquareSum μ := by
    exact_mod_cast firstOrderListWeight_le_squareSum (by omega : 0 < K) μ M
  have hraw : (S.card : ℝ) ≤ 2 * K * firstOrderRateSquareSum μ / δ := by
    apply hcardR.trans
    apply (div_le_iff₀ hden).mpr
    have hp := mul_le_mul_of_nonneg_left hgap'
      (by positivity : 0 ≤ 2 * (K : ℝ) * firstOrderRateSquareSum μ / δ)
    have hcancel : (2 * (K : ℝ) * firstOrderRateSquareSum μ / δ) * (δ * n) =
        (n : ℝ) * (2 * K * firstOrderRateSquareSum μ) := by field_simp
    rw [hcancel] at hp
    exact (mul_le_mul_of_nonneg_left hw hn'.le).trans hp
  apply hraw.trans
  have hKn' : (K : ℝ) ≤ n := by exact_mod_cast hKn
  dsimp [firstOrderRateListConstant]
  have h := mul_le_mul_of_nonneg_right hKn'
    (by positivity : 0 ≤ 2 * (firstOrderRateSquareSum μ : ℝ) / δ)
  calc
    _ = (K : ℝ) * (2 * firstOrderRateSquareSum μ / δ) := by ring
    _ ≤ (n : ℝ) * (2 * firstOrderRateSquareSum μ / δ) := h
    _ ≤ _ := by nlinarith

open Classical in
/-- A finite rate choice works uniformly for every admissible code and received word. -/
theorem finite_firstOrderRate_list_bound
    {F : Type u} [Field F] {R a : ℝ} (p : FirstOrderFiniteRateParameters R a)
    (hR : 0 < R) (hRa : R < a)
    {n k A : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ max (k - 1) p.jetDegree < ringChar F)
    (S : Finset F[X]) (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℝ) ≤ firstOrderRateListConstant (a - R) p.jetDegree * n := by
  let K := max k 2
  let D := K - 1
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : 0 < a := hR.trans hRa
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := hkR.trans ((mul_le_mul_of_nonneg_right hRa.le hn'.le).trans haA)
    exact_mod_cast h
  have hKn : K ≤ n := max_le (hkA.trans hAn) hn
  have hD : 0 < D := by dsimp [D, K]; omega
  have hDk : D ≤ k := by dsimp [D, K]; omega
  have hDrate : (D : ℝ) ≤ R * n := (Nat.cast_le.mpr hDk).trans hkR
  have hbudget : 0 < p.multiplicity * A := mul_pos p.multiplicity_pos (hk.trans_le hkA)
  have hμ : 0 < p.jetDegree := by
    apply Nat.lt_ceil.mpr
    have hm : (0 : ℝ) < p.multiplicity := by exact_mod_cast p.multiplicity_pos
    simpa only [Nat.cast_zero] using (show (0 : ℝ) < p.multiplicity * a / R by positivity)
  have hcharK : ringChar F = 0 ∨ max (K - 1) p.jetDegree < ringChar F := by
    apply hchar.imp_right
    intro hc
    have h : K - 1 ≤ max (k - 1) p.jetDegree := by dsimp [K]; omega
    exact (max_le h (le_max_right _ _)).trans_lt hc
  obtain ⟨cert⟩ := exists_firstOrderRate_symbolicCertificate.{u, u} p (k := k) (by omega : 0 < n)
    hD hbudget (by dsimp [D, K]; omega) hDrate haA domain received (fun _ ↦ 0)
  apply finite_firstOrderRate_list_bound_of_certificate (K := K) domain received _ cert
    (by change 1 < max k 2; omega) (le_max_left _ _) hKn hk hkA hAn (sub_pos.mpr hRa) ?_ hcharK S hS
  nlinarith

open Classical in
/-- The same constant controls the complete close list over any admissible field. -/
theorem firstOrderRate_close_list_bound
    {F : Type u} [Field F] {R a : ℝ} (p : FirstOrderFiniteRateParameters R a)
    (hR : 0 < R) (hRa : R < a)
    {n k A : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (hkR : (k : ℝ) ≤ R * n) (haA : a * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ max (k - 1) p.jetDegree < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        firstOrderRateListConstant (a - R) p.jetDegree * n := by
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := hkR.trans
      ((mul_le_mul_of_nonneg_right hRa.le (Nat.cast_nonneg n)).trans haA)
    exact_mod_cast h
  have hf := closePolynomialSet_finite domain received hkA
  refine ⟨hf, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact finite_firstOrderRate_list_bound p hR hRa hn hk hkR haA hAn domain received
    hchar hf.toFinset (fun _ hP ↦ hf.mem_toFinset.mp hP)

open Classical in
/-- Above the analytic threshold, choose one finite rate certificate before all code data. -/
theorem exists_firstOrderRate_list_bound {R a : ℝ}
    (hR : 0 < R) (hRa : R < a) (haone : a < 1)
    (hthreshold : firstOrderRateThreshold R < a) :
    ∃ p : FirstOrderFiniteRateParameters R a,
      ∀ (F : Type u) [Field F] (n k A : ℕ),
      2 ≤ n → 0 < k → (k : ℝ) ≤ R * n → a * n ≤ A → A ≤ n →
      ∀ (domain : Fin n ↪ F) (received : Fin n → F),
      (ringChar F = 0 ∨ max (k - 1) p.jetDegree < ringChar F) →
      (closePolynomialSet domain received k A).Finite ∧
        ((closePolynomialSet domain received k A).ncard : ℝ) ≤
          firstOrderRateListConstant (a - R) p.jetDegree * n := by
  obtain ⟨p⟩ := exists_firstOrderFiniteRateParameters hR hRa haone hthreshold
  exact ⟨p, fun _ _ _ _ _ hn hk hkR haA hAn domain received hchar ↦
    firstOrderRate_close_list_bound p hR hRa hn hk hkR haA hAn domain received hchar⟩

end ReedSolomon

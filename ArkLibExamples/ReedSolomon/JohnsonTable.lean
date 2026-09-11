/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.WeightedCertificate

/-!
# The three finite weighted Johnson rows

These declarations turn the checked integer certificates into their mathematical consequences:
complete Reed--Solomon lists over arbitrary fields, exact full-agreement recovery outside a
uniform exceptional set, and finite-field affine-line probabilities.  The displayed dimension is
`D + 1`; hence the three rates are exactly `1/16`, `1/4`, and `1/2` at block length `65536`.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

noncomputable section

open Classical in
/-- The `k/n = 1/16`, gap `0.01` row: complete list size `38` and at most
`2498629121` exceptional line challenges. -/
theorem weightedJohnsonTable_rate_one_sixteenth
    {F : Type*} [Field F] (domain : Fin 65536 ↪ F) :
    (∀ received : Fin 65536 → F,
      (closePolynomialSet domain received 4096 17038).Finite ∧
        (closePolynomialSet domain received 4096 17038).ncard ≤ 38) ∧
    ∀ f g : Fin 65536 → F, ∃ exceptional : Finset F,
      exceptional.card ≤ 2498629121 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 4096 →
        ∀ indices : Finset (Fin 65536), 17038 ≤ indices.card →
          (∀ i ∈ indices, P.eval (domain i) = f i + z * g i) →
          HasExactCorrelatedPair domain f g (RingHom.id F) 4096 z P := by
  rcases johnsonWeightedCertificate_rate_one_sixteenth with
    ⟨hcert, _hcutoff, hBD, _hU, _hN, _hW, _hR, _hT, _hslope, _hmoment,
      _hsource, _hrows, hlist, hfloor⟩
  constructor
  · intro received
    have h := closePolynomialSet_finite_and_ncard_le_johnsonPairwise
      (D := 4095) (A := 17038) domain received (by norm_num) (by norm_num)
    simpa [hlist] using h
  · intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_weightedJohnsonMCA domain f g hcert
        (by norm_num) (by norm_num) (by norm_num) hBD
    refine ⟨exceptional, ?_, hgood⟩
    have hcardInt : (exceptional.card : ℤ) ≤
        johnsonWeightedSharpExceptionFloor 65536 4095 17038 57 568 := by
      apply Int.le_floor.mpr
      exact_mod_cast hcard
    rw [hfloor] at hcardInt
    exact_mod_cast hcardInt

open Classical in
/-- Finite-field probability consequence of the `k/n = 1/16` row. -/
theorem weightedJohnsonTable_rate_one_sixteenth_mcaError
    {F : Type} [Field F] [Fintype F] (domain : Fin 65536 ↪ F) :
    mcaError (AffineLineGenerator F) (code domain 4096)
        (1 - (√((4095 : ℝ) / 65536) + 1 / 100)) ≤
      min 1 (ENNReal.ofReal (2498629121 / (Fintype.card F : ℝ))) := by
  have hrow := weightedJohnsonTable_rate_one_sixteenth domain
  have hline : LineExactAgreementBound domain 4096 17038 2498629121 := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ := hrow.2 f g
    refine ⟨exceptional, by exact_mod_cast hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP
      (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) hagree
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    exact ⟨pair.1, pair.2, hp0, hp1,
      by simpa [correlatedPairSpecialization] using heq,
      by simpa [mappedDomain] using hset⟩
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  rw [← johnsonWeightedAgreementCeil_rate_one_sixteenth]
  apply Nat.ceil_mono
  apply le_of_eq
  ring

open Classical in
/-- The `k/n = 1/4`, gap `0.01` row: complete list size `25` and at most
`3383852708` exceptional line challenges. -/
theorem weightedJohnsonTable_rate_one_fourth
    {F : Type*} [Field F] (domain : Fin 65536 ↪ F) :
    (∀ received : Fin 65536 → F,
      (closePolynomialSet domain received 16384 33423).Finite ∧
        (closePolynomialSet domain received 16384 33423).ncard ≤ 25) ∧
    ∀ f g : Fin 65536 → F, ∃ exceptional : Finset F,
      exceptional.card ≤ 3383852708 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 16384 →
        ∀ indices : Finset (Fin 65536), 33423 ≤ indices.card →
          (∀ i ∈ indices, P.eval (domain i) = f i + z * g i) →
          HasExactCorrelatedPair domain f g (RingHom.id F) 16384 z P := by
  rcases johnsonWeightedCertificate_rate_one_fourth with
    ⟨hcert, _hcutoff, hBD, _hU, _hN, _hW, _hR, _hT, _hslope, _hmoment,
      _hsource, _hrows, hlist, hfloor⟩
  constructor
  · intro received
    have h := closePolynomialSet_finite_and_ncard_le_johnsonPairwise
      (D := 16383) (A := 33423) domain received (by norm_num) (by norm_num)
    simpa [hlist] using h
  · intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_weightedJohnsonMCA domain f g hcert
        (by norm_num) (by norm_num) (by norm_num) hBD
    refine ⟨exceptional, ?_, hgood⟩
    have hcardInt : (exceptional.card : ℤ) ≤
        johnsonWeightedSharpExceptionFloor 65536 16383 33423 36 504 := by
      apply Int.le_floor.mpr
      exact_mod_cast hcard
    rw [hfloor] at hcardInt
    exact_mod_cast hcardInt

open Classical in
/-- Finite-field probability consequence of the `k/n = 1/4` row. -/
theorem weightedJohnsonTable_rate_one_fourth_mcaError
    {F : Type} [Field F] [Fintype F] (domain : Fin 65536 ↪ F) :
    mcaError (AffineLineGenerator F) (code domain 16384)
        (1 - (√((16383 : ℝ) / 65536) + 1 / 100)) ≤
      min 1 (ENNReal.ofReal (3383852708 / (Fintype.card F : ℝ))) := by
  have hrow := weightedJohnsonTable_rate_one_fourth domain
  have hline : LineExactAgreementBound domain 16384 33423 3383852708 := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ := hrow.2 f g
    refine ⟨exceptional, by exact_mod_cast hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP
      (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) hagree
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    exact ⟨pair.1, pair.2, hp0, hp1,
      by simpa [correlatedPairSpecialization] using heq,
      by simpa [mappedDomain] using hset⟩
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  rw [← johnsonWeightedAgreementCeil_rate_one_fourth]
  apply Nat.ceil_mono
  apply le_of_eq
  ring

open Classical in
/-- The `k/n = 1/2`, gap `0.01` row: complete list size `15` and at most
`1448631664` exceptional line challenges. -/
theorem weightedJohnsonTable_rate_one_half
    {F : Type*} [Field F] (domain : Fin 65536 ↪ F) :
    (∀ received : Fin 65536 → F,
      (closePolynomialSet domain received 32768 46996).Finite ∧
        (closePolynomialSet domain received 32768 46996).ncard ≤ 15) ∧
    ∀ f g : Fin 65536 → F, ∃ exceptional : Finset F,
      exceptional.card ≤ 1448631664 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 32768 →
        ∀ indices : Finset (Fin 65536), 46996 ≤ indices.card →
          (∀ i ∈ indices, P.eval (domain i) = f i + z * g i) →
          HasExactCorrelatedPair domain f g (RingHom.id F) 32768 z P := by
  rcases johnsonWeightedCertificate_rate_one_half with
    ⟨hcert, _hcutoff, hBD, _hU, _hN, _hW, _hR, _hT, _hslope, _hmoment,
      _hsource, _hrows, hlist, hfloor⟩
  constructor
  · intro received
    have h := closePolynomialSet_finite_and_ncard_le_johnsonPairwise
      (D := 32767) (A := 46996) domain received (by norm_num) (by norm_num)
    simpa [hlist] using h
  · intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_weightedJohnsonMCA domain f g hcert
        (by norm_num) (by norm_num) (by norm_num) hBD
    refine ⟨exceptional, ?_, hgood⟩
    have hcardInt : (exceptional.card : ℤ) ≤
        johnsonWeightedSharpExceptionFloor 65536 32767 46996 21 234 := by
      apply Int.le_floor.mpr
      exact_mod_cast hcard
    rw [hfloor] at hcardInt
    exact_mod_cast hcardInt

open Classical in
/-- Finite-field probability consequence of the `k/n = 1/2` row. -/
theorem weightedJohnsonTable_rate_one_half_mcaError
    {F : Type} [Field F] [Fintype F] (domain : Fin 65536 ↪ F) :
    mcaError (AffineLineGenerator F) (code domain 32768)
        (1 - (√((32767 : ℝ) / 65536) + 1 / 100)) ≤
      min 1 (ENNReal.ofReal (1448631664 / (Fintype.card F : ℝ))) := by
  have hrow := weightedJohnsonTable_rate_one_half domain
  have hline : LineExactAgreementBound domain 32768 46996 1448631664 := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ := hrow.2 f g
    refine ⟨exceptional, by exact_mod_cast hcard, ?_⟩
    intro z hz P hP hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP
      (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) hagree
      (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    exact ⟨pair.1, pair.2, hp0, hp1,
      by simpa [correlatedPairSpecialization] using heq,
      by simpa [mappedDomain] using hset⟩
  apply mcaError_affineLine_le_min_one_of_exactAgreement domain _ hline
  rw [← johnsonWeightedAgreementCeil_rate_one_half]
  apply Nat.ceil_mono
  apply le_of_eq
  ring

end

end ReedSolomon

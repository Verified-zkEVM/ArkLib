/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TaylorCharZeroSolutions
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate
/-!
# List bounds from a finite differential certificate

An order-`d` equation with total jet degree at most `ν` explains a complete agreement
list. Taylor reconstruction and incidence counting bound every finite subset; the
agreement condition then identifies the finite whole list. The resulting coefficient
is exactly `ν² * (2ν/δ)^d`, without tying the jet budget to multiplicity.

The numerical rate constructions consume this theorem after constructing their
equation and verifying the ambient dimension and characteristic guards.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative

open Classical in
/-- The complete list bound from a nonzero differential equation explaining every accepted
polynomial. Characteristic equal to the block length is included. -/
theorem close_list_bound_of_differential_equation {F : Type*} [Field F]
    {n k A K d ν : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (equation : DifferentialPolynomial F d)
    (hequation : equation ≠ 0) (hdegree : jetTotalDegree equation ≤ ν)
    (hsound : ∀ polynomial, IsAgreementSolution domain received k A polynomial →
      differentialSpecialization equation polynomial = 0)
    (hn : 0 < n) (hk : 0 < k) (hν : 0 < ν) (hνn : ν < n)
    (hdK : d < K) (hkK : k ≤ K) (hKn : K ≤ n) (hkA : k ≤ A) (hAn : A ≤ n)
    (hδ : 0 < δ) (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  classical
  have hfinite := closePolynomialSet_finite domain received hkA
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  let candidates := hfinite.toFinset
  have haccept : ∀ polynomial ∈ candidates,
      IsAgreementSolution domain received k A polynomial := by
    intro polynomial hpolynomial
    exact hfinite.mem_toFinset.mp hpolynomial
  have hsolutions : ∀ polynomial ∈ candidates,
      differentialSpecialization equation polynomial = 0 :=
    fun polynomial hpolynomial ↦ hsound polynomial (haccept polynomial hpolynomial)
  have hbin : ∀ order, order ≤ d → ∀ index, order < index → index < K →
      (index.choose order : F) ≠ 0 := by
    intro order _ index horder hindex
    exact binomial_pivots_of_characteristic
      (hchar.imp_right (fun h ↦ hKn.trans h)) order index horder hindex
  have hcount : (candidates.card : ℚ) ≤ (ν : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ d) := by
    rcases hchar with hzero | hpositive
    · have : CharP F 0 := hzero ▸ inferInstanceAs (CharP F (ringChar F))
      have : CharZero F := CharP.charP_to_charZero F
      exact finite_agreement_solutions_card_le_charZero equation K k ν hdK hkK
        hequation hdegree domain received hk hkA hAn hbin candidates hsolutions haccept
    · have hcontract : IsBelowCharacteristic (k - 1) equation := by
        refine ⟨by omega, ?_⟩
        intro index
        exact (jetDegree_le_total equation index).trans_lt
          (hdegree.trans_lt (hνn.trans_le hpositive))
      exact finite_agreement_solutions_card_le equation K k ν hdK hkK
        hequation hcontract hdegree domain received hk hkA hAn hbin candidates
        hsolutions haccept
  have hreal : (candidates.card : ℝ) ≤ (ν : ℝ) ^ 2 *
      ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) /
        ((A - k + 1 : ℕ) : ℝ)) ^ d) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hcount
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_div] using hcast
  have hratio := geometric_ratio_le hn hν hδ hKn hkA hgap
  calc
    (candidates.card : ℝ) ≤ (ν : ℝ) ^ 2 *
        ((((n * (1 + 2 * K * (ν - 1)) : ℕ) : ℝ) /
          ((A - k + 1 : ℕ) : ℝ)) ^ d) := hreal
    _ ≤ (ν : ℝ) ^ 2 * ((2 * ν / δ) * n) ^ d := by gcongr
    _ = (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by rw [mul_pow]; ring

universe u

open Classical in
/-- Constant received curves specialize to a certificate for the complete list. -/
theorem close_list_bound_of_curve_certificate {F : Type u} [Field F]
    {n k A K d ν height : ℕ} {δ : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (certificate : SymbolicReceivedCurve.Certificate.{u, u} F A k 0 ν d height domain
      (fun index ↦ Polynomial.C (received index)))
    (hn : 0 < n) (hk : 0 < k) (hν : 0 < ν) (hνn : ν < n)
    (hdK : d < K) (hkK : k ≤ K) (hKn : K ≤ n) (hkA : k ≤ A) (hAn : A ≤ n)
    (hδ : 0 < δ) (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (ν : ℝ) ^ 2 * (2 * ν / δ) ^ d * n ^ d := by
  obtain ⟨hnonzero, hdegree, hsound⟩ := certificate.specialization_sound (RingHom.id F) 0
  apply close_list_bound_of_differential_equation domain received _ hnonzero hdegree _
    hn hk hν hνn hdK hkK hKn hkA hAn hδ hgap hchar
  intro polynomial haccept
  apply hsound (polynomialAgreementSet domain received polynomial) polynomial
    haccept.1 haccept.2
  intro index hindex
  simpa using (Finset.mem_filter.mp hindex).2

end ReedSolomon

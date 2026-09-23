/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.HiddenDerivativeBound
import ArkLib.Data.Polynomial.Differential.WitnessCount
import ArkLibTest.Data.CodingTheory.HiddenDerivative.Interpolation.Certificates

/-!
# Acceptance cases for exact-interpolant list bounds

* For the order-zero interpolant `Y₀ - r` over `ZMod 5`, the agreement list on two points embeds
  into its bounded solutions, and the pointwise list bound applies.
* The characteristic form used by the interpolation API supplies the jet-cast and binomial
  hypotheses of the total-jet-degree root count.
* A zero interpolation budget forces every exact interpolant to be zero, and the binomial
  coefficient at the characteristic vanishes.
-/

open MvPolynomial PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative ListDecoding

namespace HiddenDerivativeBoundTest

private theorem hzero_lt_one : (0 : ℕ) < 1 := by decide

/-- `Y₀ - r` lies in the exact interpolation space with `D = 1`, `A = 2`, and `m = 1`. -/
private theorem Y_zero_sub_mem_exact (r : ZMod 5) :
    (X (some 0) - C r : DifferentialPolynomial (ZMod 5) 0) ∈
      exactInterpolationSpace (ZMod 5) 1 2 0 1 0 0 hzero_lt_one := by
  refine Submodule.sub_mem _ ?_ ?_
  · rw [MvPolynomial.X, monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight,
      Finsupp.weight_single, jetFirstWeight, jetHigherWeight, differentialWeight]
  · rw [← monomial_zero', monomial_mem_exactInterpolationSpace]
    left
    simp [ExactInterpolationEligibleExponent, firstJetExponent, fullHigherJetWeight]

/-- Each `Y₀ - r` satisfies the multiplicity-one constraints at `(a, r)`. -/
private theorem Y_zero_sub_satisfies_local (a r : ZMod 5) :
    SatisfiesLocalConstraints (d := 0) 1 a r (X (some 0) - C r) :=
  CertificatesTest.satisfiesLocalConstraints_one_Y_zero_sub a r

/-- The characteristic form of the root-count hypotheses for an exact interpolant. -/
private theorem listBound_of_below_characteristic
    {F index : Type*} [Field F] [Finite F] [DecidableEq F] [Fintype index]
    {messageDim K A d m M W : ℕ} (hK : 0 < K) (hmessageDim : messageDim ≤ K)
    (hdK : d < K - 1)
    (domain : index ↪ F) (received : index → F) {Q : DifferentialPolynomial F d}
    (hQ : Q ≠ 0) (hQspace : Q ∈ exactInterpolationSpace F (K - 1) A d m M W hdK)
    (hconstraints : ∀ i, SatisfiesLocalConstraints m (domain i) (received i) Q)
    (hDchar : K - 1 < ringChar F) (hjetChar : ∀ j, jetDegree Q j < ringChar F)
    (hfield : m * A ≤ Nat.card F ^ 2) :
    (agreeingPolynomials domain messageDim A received).encard ≤
      (2 * (d + 1) * Nat.card F ^ (3 * d + 2) : ℕ∞) := by
  apply agreeingPolynomials_encard_le_two_mul_pow_of_exactInterpolant hK hmessageDim hdK
    domain received hQ hQspace hconstraints
  · intro j
    exact jetDegreeCastsNeZero_of_ringChar (Or.inr (hjetChar j))
  · intro k s hk hks
    exact PolynomialDifferential.natCast_choose_ne_zero_of_ringChar
      (Or.inr hDchar) k hk hks
  · exact hfield

/-- The agreeing-polynomial embedding preserves the polynomial over `ZMod 5`. -/
example (r : ZMod 5) (p : agreeingPolynomials CertificatesTest.zmodDomain 2 2 (fun _ ↦ r)) :
    ((agreeingPolynomialsToBoundedSolution (by decide) (by decide)
      CertificatesTest.zmodDomain (fun _ ↦ r) (Y_zero_sub_mem_exact r)
      (fun i ↦ Y_zero_sub_satisfies_local (CertificatesTest.zmodDomain i) r) p).polynomial) =
      (p.1 : Polynomial (ZMod 5)) := by
  simp

/-- The selected representative has an existential witness with the prescribed polynomial. -/
example (r : ZMod 5) (p : agreeingPolynomials CertificatesTest.zmodDomain 2 2 (fun _ ↦ r)) :
    ∃ solution : BoundedSolution (X (some 0) - C r : DifferentialPolynomial (ZMod 5) 0) 1,
      solution.polynomial = (p.1 : Polynomial (ZMod 5)) :=
  exists_boundedSolution_polynomial_eq (by decide) (by decide) CertificatesTest.zmodDomain
    (fun _ ↦ r) (Y_zero_sub_mem_exact r)
    (fun i ↦ Y_zero_sub_satisfies_local (CertificatesTest.zmodDomain i) r) p

/-- The agreement-list cardinality compares with a natural cardinal over the finite field. -/
example (r : ZMod 5) :
    (agreeingPolynomials CertificatesTest.zmodDomain 2 2 (fun _ ↦ r)).encard ≤
      (Nat.card (BoundedSolution (X (some 0) - C r : DifferentialPolynomial (ZMod 5) 0) 1) :
        ℕ∞) :=
  agreeingPolynomials_encard_le_boundedSolution_natCard (by decide) (by decide)
    CertificatesTest.zmodDomain (fun _ ↦ r) (Y_zero_sub_mem_exact r)
    (fun i ↦ Y_zero_sub_satisfies_local (CertificatesTest.zmodDomain i) r)

/-- The exact-interpolant list bound on `ZMod 5` uses its characteristic guard. -/
example (r : ZMod 5) :
    (agreeingPolynomials CertificatesTest.zmodDomain 2 2 (fun _ ↦ r)).encard ≤
      (2 * (0 + 1) * Nat.card (ZMod 5) ^ (3 * 0 + 2) : ℕ∞) := by
  apply listBound_of_below_characteristic (F := ZMod 5) (index := Fin 2)
    (messageDim := 2) (K := 2) (A := 2) (d := 0) (m := 1) (M := 0) (W := 0)
    (by decide) (by decide) (by decide) CertificatesTest.zmodDomain
    (fun _ ↦ r) (CertificatesTest.Y_zero_sub_ne_zero r) (Y_zero_sub_mem_exact r)
    (fun i ↦ Y_zero_sub_satisfies_local (CertificatesTest.zmodDomain i) r)
  · rw [ZMod.ringChar_zmod_n]
    decide
  · intro j
    rw [ZMod.ringChar_zmod_n]
    exact (CertificatesTest.jetDegree_Y_zero_sub_le r j).trans_lt (by decide)
  · norm_num

/-- With zero interpolation budget, exact-space membership forces the interpolant to vanish. -/
example (Q : DifferentialPolynomial (ZMod 2) 0)
    (hQ : Q ∈ exactInterpolationSpace (ZMod 2) 1 0 0 1 0 0 hzero_lt_one) : Q = 0 := by
  exact eq_zero_of_mem_exactInterpolationSpace_of_mul_eq_zero (by simp) hzero_lt_one hQ

/-- At characteristic `2`, the binomial coefficient `(2 choose 1)` vanishes. -/
example : ¬ ∀ k s, 0 < k → k + s ≤ 2 → ((k + s).choose s : ZMod 2) ≠ 0 := by
  intro h
  have hzero := h 1 1 (by decide) (by decide)
  change ((Nat.choose 2 1 : ℕ) : ZMod 2) ≠ 0 at hzero
  have hchoose : Nat.choose 2 1 = 2 := by decide
  rw [hchoose] at hzero
  have hcast : ((2 : ℕ) : ZMod 2) = 0 := by
    rw [CharP.cast_eq_zero_iff (ZMod 2) 2]
  exact hzero hcast

end HiddenDerivativeBoundTest

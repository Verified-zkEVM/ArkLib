/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FirstOrder.FirstOrderHybridList
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.AutomaticBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CertificateList
public import ArkLib.ToMathlib.Set.Finite
/-!
# Complete first-order lists above the rate curve

The first-order threshold is
`a₁(ρ) = (3ρ + 2√(ρ(5 - ρ)(2 - ρ))) / (8 - ρ)`. For `a > a₁(ρ)`, the automatic
recipe uses `a₀ = min(a,(1+a₁(ρ))/2)`, `β = 3(1-a₀)/(2(2-ρ))`, positive surplus `S`, and
`m = ceil(4/S)`. The finite surplus supplies a nonzero first-order interpolation equation.
Separant descent counts regular solution families while retaining the `Y₁`-degree cap; the
residual ordinary equation supplies the tail count.

The main finite theorem retains the optimized real and natural bounds. The paper-facing
projection displays
`Λ = 2DθT + μ - M`, where `D = k - 1`, `θ = (n - D) / (A - D)`, and
`T = ∑_{r=1}^M r(2(μ-M)+r)`. The same bound applies to every finite subset of close
polynomials, which proves that the complete list is finite even over an infinite field.
-/

@[expose] public section

open Polynomial

namespace ReedSolomon

open HiddenDerivative
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.SymbolicWeightedSupportInterpolation

noncomputable section

set_option autoImplicit false

open Classical in
private theorem mem_closePolynomialSet_iff_isAgreementSolution
    {F : Type*} [Field F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (P : F[X]) :
    P ∈ closePolynomialSet domain received k A ↔
      IsAgreementSolution domain received k A P := by
  unfold closePolynomialSet IsAgreementSolution
  constructor
  · intro hP
    refine ⟨hP.1, ?_⟩
    convert hP.2 using 1
    congr 1
  · intro hP
    refine ⟨hP.1, ?_⟩
    convert hP.2 using 1
    congr 1

open Classical in
/-- The complete close-polynomial set is finite and obeys the optimized and closed `Λ` bounds.

The rate and agreement hypotheses make the automatic interpolation surplus positive. The
characteristic guard covers Taylor recovery through degree `D` and differentiation through the
`Y₁`-degree cap. Finiteness follows from a uniform natural bound on every finite subset, rather
than from a finite-field assumption. -/
theorem automaticFirstOrder_closePolynomialSet_finite_and_card_le
    {rho a : ℝ} {n D A k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    /-

    The dimension and integer agreement threshold enforce the fixed physical rate
    and the requested agreement fraction.
    -/
    (hn : 0 < n) (hD : D = k - 1) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n) (hA : a * n ≤ A) (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type*} [Field F] (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ max D (automaticDerivativeCap rho a) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        hybridListOptimizedRaw (hybridTheta n D A) D
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      (closePolynomialSet domain received k A).ncard ≤
        hybridListOptimizedCeil (hybridTheta n D A) D
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        hybridLambdaClosed (hybridTheta n D A) D
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) := by
  let T := closePolynomialSet domain received k A
  let B := hybridListOptimizedCeil (hybridTheta n D A) D
    (automaticJetDegree rho a) (automaticDerivativeCap rho a)
  have hfinite : T.Finite := by
    refine Set.finite_of_forall_finset_card_le (R := ℕ) (ℓ := B) ?_
    intro S hST
    have hbound := finite_automaticFirstOrder_hybrid_agreement_solutions_card_le
      hrho hrhoOne ha haOne hn hD hk hkRate hA hAn domain received hchar S
      (fun P hP ↦ (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
        (hST hP))
    exact hbound.2.1
  have hwhole := finite_automaticFirstOrder_hybrid_agreement_solutions_card_le
    hrho hrhoOne ha haOne hn hD hk hkRate hA hAn domain received hchar hfinite.toFinset
    (fun P hP ↦ (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
      (hfinite.mem_toFinset.mp hP))
  have hncard : T.ncard = hfinite.toFinset.card := Set.ncard_eq_toFinset_card T hfinite
  refine ⟨hfinite, ?_, ?_, ?_⟩
  · simpa only [T, hncard] using hwhole.1
  · simpa only [T, B, hncard] using hwhole.2.1
  · simpa only [T, hncard] using hwhole.2.2

open Classical in
/-- **The complete first-order list has size at most `Λ = 2DθT + μ-M`.**

The list consists of all polynomials of degree strictly below `k` that agree with the
received word at at least `A` of the distinct evaluation points. It includes zero when
zero meets the agreement threshold. Finiteness is explicit because the field may be infinite.

With `η₁ = a - a₁(ρ)`, the companion rate bound proves `Λ = O_ρ(n/η₁³)`.
This declaration gives the finite expression; it does not assert a decoder runtime. In
characteristic zero the characteristic guard is automatic; in positive characteristic it
requires the characteristic to exceed both `D` and `M`.
-/
theorem automatic_first_order_list_bound
    /-

    Choose the physical rate and agreement fraction before the code data.
    -/
    (ρ a : ℝ)
    (hρ : 0 < ρ)
    (hρone : ρ < 1)
    (ha : automaticFirstOrderThreshold ρ < a)
    (haone : a < 1)
    /-

    Dimension k means degree strictly below k; A counts agreeing positions.
    -/
    (n k A : ℕ)
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hrate : (k : ℝ) ≤ ρ * n)
    (hagree : a * n ≤ A)
    (hAn : A ≤ n)
    /-

    Distinct evaluation points over an arbitrary field.
    -/
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    -- Taylor recovery through degree D divides by 1,...,D; separant descent
    -- differentiates at most M times in Y₁. These require p > D and p > M
    -- in positive characteristic. The ordinary tail is characteristic-free,
    -- so no p > μ assumption is needed.
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap ρ a) < ringChar F)
    (received : Fin n → F) :
    /-

    Candidate degrees are at most D. Agreement strictly exceeds D.
    -/
    let D := k - 1
    /-

    θ = (n-D)/(A-D) is the incidence factor for fixed-word solution families.
    The hypotheses give 1 ≤ θ ≤ 1/(a-ρ).
    -/
    let θ := hybridTheta n D A
    /-

    M = floor(βm) bounds the Y₁ exponent; μ = ceil(m a₀/ρ) bounds
    total degree in (Y₀,Y₁). The recipe proves its normalized M equals the
    printed floor and satisfies M ≤ μ.
    -/
    let M := automaticDerivativeCap ρ a
    let μ := automaticJetDegree ρ a
    /-

    T = sum_{r=1}^M r(2(μ-M)+r)
      = (μ-M)M(M+1) + M(M+1)(2M+1)/6.
    This bounds the accumulated algebraic degree at the regular stages.
    -/
    let T := hybridT μ M
    /-

    At actual Y₁-degree e ≤ M, the raw count is θ B₁(e) + μ-e.
    The whole expression is monotone in e. Evaluating its envelope at M,
    then using B₁(M) ≤ 2DT, gives the printed bound below.
    Thus μ-M is the tail term of the envelope, not necessarily the actual tail degree.
    -/
    let Λ : ℝ := 2 * D * θ * T + (μ - M : ℕ)
    /-

    Finiteness and the cardinality bound concern the complete list, even over infinite fields.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ Λ := by
  dsimp only
  obtain ⟨hfinite, _hraw, _hceil, hclosed⟩ :=
    automaticFirstOrder_closePolynomialSet_finite_and_card_le
      hρ hρone ha haone hn rfl hk hrate hagree hAn domain received hchar
  exact ⟨hfinite, hclosed⟩

open Classical in
/-- Paper-facing positive-slack form of `automatic_first_order_list_bound`.

Here `a = a₁(ρ) + η₁` and `η₁ > 0`, so agreement lies strictly above the first-order rate
curve. The companion rate theorem bounds the displayed `Λ` by `O_ρ(n / η₁³)`. -/
theorem automatic_first_order_list_bound_of_slack
    (ρ η₁ : ℝ)
    (hρ : 0 < ρ)
    (hρone : ρ < 1)
    (hη₁ : 0 < η₁)
    (haone : automaticFirstOrderThreshold ρ + η₁ < 1)
    /-

    Dimension k means degree < k; A is the integer agreement threshold.
    -/
    (n k A : ℕ)
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hrate : (k : ℝ) ≤ ρ * n)
    (hagree : (automaticFirstOrderThreshold ρ + η₁) * n ≤ A)
    (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    (hchar : ringChar F = 0 ∨
      max (k - 1)
        (automaticDerivativeCap ρ (automaticFirstOrderThreshold ρ + η₁)) < ringChar F)
    (received : Fin n → F) :
    /-

    Positive slack fixes a strictly above a₁(ρ); the recipe below is evaluated at this a.
    -/
    let a := automaticFirstOrderThreshold ρ + η₁
    let D := k - 1
    let θ := hybridTheta n D A
    let M := automaticDerivativeCap ρ a
    let μ := automaticJetDegree ρ a
    let T := hybridT μ M
    let Λ : ℝ := 2 * D * θ * T + (μ - M : ℕ)
    /-

    Finiteness and the cardinality bound concern the complete list, even over infinite fields.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ Λ := by
  dsimp only
  exact automatic_first_order_list_bound ρ (automaticFirstOrderThreshold ρ + η₁)
    hρ hρone (lt_add_of_pos_right _ hη₁) haone n k A hn hk hrate hagree hAn
    domain hchar received

open Classical in
/-- Physical-parameter form with the exact integer threshold `A = ceil (a*n)`. -/
theorem automaticFirstOrder_closePolynomialSet_at_ceil_finite_and_card_le
    {rho a : ℝ} {n k : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1)
    (ha : automaticFirstOrderThreshold rho < a) (haOne : a < 1)
    /-

    The dimension and integer agreement threshold enforce the fixed physical rate
    and the requested agreement fraction.
    -/
    (hn : 0 < n) (hk : 2 ≤ k) (hkRate : (k : ℝ) ≤ rho * n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    {F : Type*} [Field F] (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (automaticDerivativeCap rho a) < ringChar F) :
    (closePolynomialSet domain received k (Nat.ceil (a * n))).Finite ∧
      ((closePolynomialSet domain received k (Nat.ceil (a * n))).ncard : ℝ) ≤
        hybridListOptimizedRaw (hybridTheta n (k - 1) (Nat.ceil (a * n))) (k - 1)
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      (closePolynomialSet domain received k (Nat.ceil (a * n))).ncard ≤
        hybridListOptimizedCeil (hybridTheta n (k - 1) (Nat.ceil (a * n))) (k - 1)
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) ∧
      ((closePolynomialSet domain received k (Nat.ceil (a * n))).ncard : ℝ) ≤
        hybridLambdaClosed (hybridTheta n (k - 1) (Nat.ceil (a * n))) (k - 1)
          (automaticJetDegree rho a) (automaticDerivativeCap rho a) := by
  have hA : a * (n : ℝ) ≤ (Nat.ceil (a * n) : ℕ) := Nat.le_ceil _
  have hAn : Nat.ceil (a * n) ≤ n := by
    apply Nat.ceil_le.mpr
    calc
      a * (n : ℝ) ≤ 1 * n := mul_le_mul_of_nonneg_right haOne.le (Nat.cast_nonneg n)
      _ = n := one_mul _
  exact automaticFirstOrder_closePolynomialSet_finite_and_card_le
    hrho hrhoOne ha haOne hn rfl hk hkRate hA hAn domain received hchar

open Classical in
/-- The squarefree product/resultant argument improves the automatic complete-list dependence
from cubic to quadratic in the positive slack.  The `M = 0` endpoint is discharged by the
ordinary branch of the retained hybrid theorem; no positive-derivative hypothesis is exposed. -/
theorem automatic_first_order_squarefree_list_bound_of_slack
    (rho eta : ℝ)
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : automaticFirstOrderThreshold rho + eta < 1)
    (n k A : ℕ) (hn : 0 < n) (hk : 2 ≤ k)
    (hkRate : (k : ℝ) ≤ rho * n)
    (hA : (automaticFirstOrderThreshold rho + eta) * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ max (k - 1)
      (automaticDerivativeCap rho (automaticFirstOrderThreshold rho + eta)) < ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        FirstOrder.Squarefree.automaticSquarefreeListBoundConstant rho * n / eta ^ 2 := by
  let a := automaticFirstOrderThreshold rho + eta
  let D := k - 1
  let M := automaticDerivativeCap rho a
  let B := automaticJetDegree rho a
  have ha : automaticFirstOrderThreshold rho < a := by dsimp only [a]; linarith
  have hOld := automaticFirstOrder_closePolynomialSet_finite_and_card_le
    hrho hrhoOne ha haOne hn (show D = k - 1 from rfl) hk hkRate hA hAn
      domain received hchar
  refine ⟨hOld.1, ?_⟩
  have hkA : k ≤ A := by
    have hrhok := (rho_lt_automaticFirstOrderThreshold hrho hrhoOne).trans ha
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact_mod_cast (hkRate.trans (mul_le_mul_of_nonneg_right hrhok.le hnR.le) |>.trans hA)
  have hkn : k ≤ n := hkA.trans hAn
  have hD : 1 ≤ D := by dsimp only [D]; omega
  have hDn : D ≤ n := by dsimp only [D]; omega
  have hDA : D < A := by dsimp only [D]; omega
  have hDrate : (D : ℝ) ≤ rho * n := by
    exact (show (D : ℝ) ≤ k by exact_mod_cast (show D ≤ k by dsimp [D]; omega)).trans hkRate
  by_cases hMzero : M = 0
  · have hcard : ((closePolynomialSet domain received k A).ncard : ℝ) ≤ B := by
      have hclosed := hOld.2.2.2
      simpa only [D, M, B, hMzero, hybridLambdaClosed, hybridT, Nat.cast_zero,
        mul_zero, zero_mul, zero_div, zero_add, add_zero, Nat.sub_zero] using hclosed
    let C := automaticHybridEnvelopeConstant rho
    let q := 1 / eta
    have hC : 1 ≤ C := one_le_automaticHybridEnvelopeConstant rho
    have hetaOne : eta ≤ 1 := by
      have hgap := automatic_eta_lt_rateGap hrho hrhoOne heta haOne
      have hthresholdPos := (rho_lt_automaticFirstOrderThreshold hrho hrhoOne).trans' hrho
      unfold automaticRateGap at hgap
      linarith
    have hq : 1 ≤ q := (one_le_div heta).2 hetaOne
    have hB : (B : ℝ) ≤ C * q := by
      calc
        (B : ℝ) ≤ automaticJetBoundConstant rho / eta :=
          automaticJetDegree_le_inv_eta hrho hrhoOne heta haOne
        _ = automaticJetBoundConstant rho * q := by dsimp only [q]; ring
        _ ≤ C * q := by
          gcongr
          exact automaticJetBoundConstant_le_envelope rho
    have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    have hq0 : 0 ≤ q := zero_le_one.trans hq
    have hx : 1 ≤ C * q := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hq)]
    have hCN : 1 ≤ C * (n : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hN)]
    have hsquare : C * q ≤ (C * q) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hC0 hq0) (sub_nonneg.mpr hx)]
    have hlarge : (C * q) ^ 2 ≤ C ^ 3 * n * q ^ 2 := by
      have hnonneg : 0 ≤ (C * q) ^ 2 := sq_nonneg _
      have := mul_nonneg hnonneg (sub_nonneg.mpr hCN)
      nlinarith
    calc
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ B := hcard
      _ ≤ C * q := hB
      _ ≤ C ^ 3 * n * q ^ 2 := hsquare.trans hlarge
      _ ≤ FirstOrder.Squarefree.automaticSquarefreeListBoundConstant rho * n /
          eta ^ 2 := by
        dsimp only [C, q]
        unfold FirstOrder.Squarefree.automaticSquarefreeListBoundConstant
        field_simp [ne_of_gt heta]
        have hnonneg : 0 ≤ automaticHybridEnvelopeConstant rho ^ 3 * (n : ℝ) := by
          positivity
        nlinarith
  · have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hMzero
    have hMB : M ≤ B := by
      dsimp only [M, B]
      unfold automaticDerivativeCap
      exact min_le_right _ _
    obtain ⟨cert⟩ := exists_automaticFirstOrder_symbolicCertificate
      hrho hrhoOne ha haOne hn (show D = k - 1 from rfl) hk hkRate hA
        domain received (fun _ ↦ 0)
    let list := hOld.1.toFinset
    have hsolutions : ∀ P ∈ list, IsAgreementSolution domain received k A P := by
      intro P hP
      exact (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
        (hOld.1.mem_toFinset.mp hP)
    have hcard := FirstOrder.Squarefree.firstOrder_finite_agreement_solutions_card_le_squarefree
      domain received
        (firstOrderColumns (D := D) (A := A) (m := automaticMultiplicity rho a)
          (M := M) (μ := B)) cert hk hkn hkA hAn hM hMB hchar list hsolutions
    have hbound := FirstOrder.Squarefree.automaticSquarefreeListExpression_le
      hrho hrhoOne heta haOne (show 1 ≤ n by omega) hD hDn hDA hDrate hA hM
    have hncard := Set.ncard_eq_toFinset_card _ hOld.1
    rw [hncard]
    exact hcard.trans (by simpa only [D, M, B, a, hybridTheta, mul_div_assoc,
      (show k - 1 + 1 = k by omega),
      (show 2 * (k - 1) - 1 = 2 * k - 3 by omega),
      (show n - k + 1 = n - (k - 1) by omega),
      (show A - k + 1 = A - (k - 1) by omega)] using hbound)

end

end ReedSolomon

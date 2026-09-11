/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveTransfer

/-!
# Ordinary-tail savings in first-order curve transfer

The joint-degree saving pays the content and resultant exclusions before comparing the
regular-stage sums. All comparisons precede the finite retention optimization.
-/

@[expose] public section

namespace ReedSolomon

open HiddenDerivative

noncomputable section

/-- The ordinary joint-degree saving pays the extra preliminary exclusions. -/
theorem ordinaryPsi_add_exclusions_le_fullDifferentiation {D b : ℕ}
    (hD : 1 ≤ D) (hb : 1 ≤ b) :
    ordinaryPsi D b + 2 * (b - 1) ≤ b + (2 * D - 1) * b ^ 2 := by
  have htau : 1 ≤ 2 * D - 1 := by omega
  by_cases hbOne : b = 1
  · subst b
    simp [ordinaryPsi]
  have hbTwo : 2 ≤ b := by omega
  unfold ordinaryPsi
  by_cases hsmall : b ≤ 2 * D + 1
  · have hz : b - 2 * D - 1 = 0 := by omega
    rw [hz]
    have hprod := Nat.mul_le_mul_left ((b - 1) ^ 2) htau
    have hsub : b - 1 + 1 = b := by omega
    have htwice : 2 * b - 1 + 1 = 2 * b := by omega
    nlinarith [sq_nonneg ((b : ℤ) - 2)]
  · have hlarge : 2 * D + 2 ≤ b := by omega
    have hsub : b - 1 + 1 = b := by omega
    have htwice : 2 * b - 1 + 1 = 2 * b := by omega
    have htail : b - 2 * D - 1 + (2 * D + 1) = b := by omega
    have hprod := Nat.mul_le_mul_left ((b - 1) ^ 2) htau
    have hbFour : 4 ≤ b := by omega
    have hquad : 3 * (b - 1) ≤ (b - 1) ^ 2 := by nlinarith
    have htauEq : 2 * D - 1 + 1 = 2 * D := by omega
    have hsquare : b ^ 2 = (b - 1) ^ 2 + 2 * (b - 1) + 1 := by nlinarith
    have htwice' : 2 * b - 1 = 2 * (b - 1) + 1 := by omega
    rw [hsquare, htwice']
    nlinarith

/-- Full differentiation of an ordinary tail, before the regular-stage contribution. -/
def hybridCurveFullTail (n D ell b H A L : ℕ) : ℝ :=
  let fiber := b * (b + 1) / 2
  H + hybridLambdaOne n A L *
      (ell * fiber + H * (b + (2 * D - 1) * b ^ 2) : ℕ) +
    (ell * (n - L) * fiber : ℕ)

/-- The free-threshold ordinary transfer is pointwise no worse than differentiating its
ordinary tail completely. This includes the separate zero-degree height branch. -/
theorem hybridCurveTail_le_fullTail {n D ell b H A L : ℕ}
    (hD : 1 ≤ D) (hLA : L ≤ A) (hAn : A ≤ n) :
    hybridCurveTail n D ell b H A L ≤ hybridCurveFullTail n D ell b H A L := by
  by_cases hb : b = 0
  · subst b
    simp [hybridCurveTail, hybridCurveFullTail]
  have hbpos : 1 ≤ b := by omega
  let fiber := b * (b + 1) / 2
  have hbf : b ≤ fiber := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    nlinarith
  have hsave := ordinaryPsi_add_exclusions_le_fullDifferentiation hD hbpos
  have hjoint : ell * b + H * ordinaryPsi D b + 2 * (b - 1) * H ≤
      ell * fiber + H * (b + (2 * D - 1) * b ^ 2) := by
    have h₁ := Nat.mul_le_mul_left H hsave
    have h₂ := Nat.mul_le_mul_left ell hbf
    nlinarith
  have haccidental : (ell * (n - L) * b : ℕ) ≤ ell * (n - L) * fiber :=
    Nat.mul_le_mul_left _ hbf
  have hlambda : 1 ≤ hybridLambdaOne n A L := by
    unfold hybridLambdaOne
    apply (one_le_div (by exact_mod_cast (show 0 < A - L + 1 by omega))).2
    exact_mod_cast (show A - L + 1 ≤ n - L + 1 by omega)
  have hpre : (2 * b - 1) * H = H + 2 * (b - 1) * H := by
    have hsub : b - 1 + 1 = b := by omega
    have htwice : 2 * b - 1 + 1 = 2 * b := by omega
    nlinarith
  have hjointR : ((ell * b + H * ordinaryPsi D b + 2 * (b - 1) * H : ℕ) : ℝ) ≤
      (ell * fiber + H * (b + (2 * D - 1) * b ^ 2) : ℕ) := by
    exact_mod_cast hjoint
  have hmult := mul_le_mul_of_nonneg_left hjointR (zero_le_one.trans hlambda)
  have hpaid : ((2 * (b - 1) * H : ℕ) : ℝ) ≤
      hybridLambdaOne n A L * (2 * (b - 1) * H : ℕ) := by
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hlambda
  have haccR : ((ell * (n - L) * b : ℕ) : ℝ) ≤
      (ell * (n - L) * fiber : ℕ) := by exact_mod_cast haccidental
  simp only [hybridCurveTail, if_neg hb, ordinaryUnifiedPowerFactorAt,
    ordinaryUnifiedPowerFactorRawAt, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, hybridCurveFullTail]
  change (((2 * b - 1) * H : ℕ) : ℝ) + hybridLambdaOne n A L *
      (ell * b + H * ordinaryPsi D b : ℕ) + (ell * ((n - L) * b) : ℕ) ≤ _
  rw [hpre]
  push_cast at hmult hpaid haccR ⊢
  dsimp only [fiber] at hmult haccR
  nlinarith

end

end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.Uniform
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrderCurve
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.UniformLineMCA
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.SharpCountingBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
/-!
# Uniform first-order mutual correlated agreement at gap 6/25

The squarefree fixed certificate with MCA support `(12, 4, 23)` and height `276` gives one
exceptional set, chosen before the challenge and candidate polynomial, of size at most
`1325775 n^2`; outside the set the complete agreement set is the common agreement set of two
degree-`< k` constituents.

All interpolation and graded-rank inputs are constructed in this module.  The hypotheses contain
only the code parameters, the gap inequality, and the field-characteristic condition.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped BigOperators

universe u

set_option maxHeartbeats 4000000 in
-- Expanding the closed eighteen-term sum needs more than the default heartbeat budget.
private theorem uniformFirstOrder_jointZero_two_mul (n : ℕ) :
    firstOrderCurveJointZero n 22 4 1 851 (2 * n) = 551448 * n + 15489 := by
  norm_num [firstOrderCurveJointZero, Finset.sum_range_succ]
  ring

private theorem uniformFirstOrder_fiberZero_eq :
    firstOrderCurveFiberZero 22 4 = 171 := by decide

private theorem uniformFirstOrder_jointZero_mono {k n τ : ℕ} (hτ : τ ≤ 2 * n) :
    firstOrderCurveJointZero k 22 4 1 851 τ ≤
      firstOrderCurveJointZero n 22 4 1 851 (2 * n) := by
  unfold firstOrderCurveJointZero
  apply Finset.sum_le_sum
  intro t ht
  gcongr

/-- Forgetting the derivative restriction is enough for this uniform corollary. -/
private theorem uniformFirstOrder_jointStage_le {k n j r τ : ℕ}
    (hrj : r ≤ j) (hτ : τ ≤ 2 * n) :
    firstOrderCurveJointStageOne k 1 851 j r τ ≤
      851 * (1 + 2 * n * (j - 1)) ^ 2 +
        2 * (1 + 2 * n * 851) * (j * (1 + 2 * n * (j - 1))) := by
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap k j r τ
  have harea : 2 * b * c - c ^ 2 ≤ b ^ 2 := by
    apply Nat.sub_le_iff_le_add.mpr
    nlinarith [sq_nonneg ((b : ℤ) - c)]
  have hB := firstOrderCurveFiberStageOne_le_full (K := k) (τ := τ) hrj
  change 851 * (2 * b * c - c ^ 2) +
    2 * (1 + τ * 851) * firstOrderCurveFiberStageOne k j r τ ≤ _
  calc
    _ ≤ 851 * b ^ 2 + 2 * (1 + τ * 851) * (j * b) := by gcongr
    _ ≤ _ := by dsimp [b, firstOrderTaylorTotalCap]; gcongr

set_option maxHeartbeats 4000000 in
-- The four full-triangle upper bounds expand to a closed quadratic polynomial.
private theorem uniformFirstOrder_jointOne_le_two_mul {k n τ : ℕ} (hτ : τ ≤ 2 * n) :
    firstOrderCurveJointOne k 22 4 1 851 τ ≤
      16114536 * n ^ 2 + 551056 * n + 3568 := by
  have hsum : firstOrderCurveJointOne k 22 4 1 851 τ ≤
      ∑ t ∈ Finset.range 22, if 18 ≤ t then
        851 * (1 + 2 * n * t) ^ 2 +
          2 * (1 + 2 * n * 851) * ((t + 1) * (1 + 2 * n * t)) else 0 := by
    unfold firstOrderCurveJointOne
    apply Finset.sum_le_sum
    intro t ht
    norm_num only [Nat.min_eq_left (by decide : 4 ≤ 22), Nat.reduceSub]
    split
    · simpa using uniformFirstOrder_jointStage_le
        (k := k) (j := t + 1) (r := t + 1 - 18) (Nat.sub_le _ _) hτ
    · exact le_rfl
  convert hsum using 1
  norm_num [Finset.sum_range_succ]
  ring

set_option maxHeartbeats 4000000 in
-- The four full-triangle fiber upper bounds expand to a closed linear polynomial.
private theorem uniformFirstOrder_fiberOne_le_two_mul {k n τ : ℕ} (hτ : τ ≤ 2 * n) :
    firstOrderCurveFiberOne k 22 4 τ ≤ 3208 * n + 82 := by
  have hsum : firstOrderCurveFiberOne k 22 4 τ ≤
      ∑ t ∈ Finset.range 22, if 18 ≤ t then
        (t + 1) * (1 + 2 * n * t) else 0 := by
    unfold firstOrderCurveFiberOne
    apply Finset.sum_le_sum
    intro t ht
    norm_num only [Nat.min_eq_left (by decide : 4 ≤ 22), Nat.reduceSub]
    split
    · exact (firstOrderCurveFiberStageOne_le_full (Nat.sub_le _ _)).trans (by
        unfold firstOrderTaylorTotalCap
        simp only [Nat.add_sub_cancel]
        gcongr)
    · exact le_rfl
  convert hsum using 1
  norm_num [Finset.sum_range_succ]
  ring

private theorem uniformFirstOrder_directRatio_le
    (n k A : ℕ) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A) :
    firstOrderCurveDirectRatio n k A ≤ 25 / 6 := by
  have hkA : k ≤ A := by exact_mod_cast (show (k : ℝ) ≤ A by linarith)
  have hden : (0 : ℚ) < (A - k + 1 : ℕ) := by positivity
  unfold firstOrderCurveDirectRatio
  apply (div_le_iff₀ hden).2
  have hnk : n - k + 1 ≤ n := by omega
  have hgapQ : (6 : ℚ) * n ≤ 25 * (A - k + 1) := by
    exact_mod_cast (show (6 : ℝ) * n ≤ 25 * (A - k + 1) by nlinarith)
  have hnkQ : ((n - k + 1 : ℕ) : ℚ) ≤ n := by exact_mod_cast hnk
  have hdenCast : ((A - k + 1 : ℕ) : ℚ) = (A : ℚ) - k + 1 := by
    push_cast [Nat.cast_sub hkA]
    rfl
  rw [hdenCast]
  calc
    ((n - k + 1 : ℕ) : ℚ) ≤ n := hnkQ
    _ ≤ (25 / 6 : ℚ) * ((A : ℚ) - k + 1) := by nlinarith

set_option maxHeartbeats 10000000 in
-- The final cap-sensitive rational estimate contains four large normalized products.
private theorem uniformFirstOrder_curveBound_le (n k A : ℕ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A) :
    let L := correlatedMidpoint (6 / 25 : ℝ) n k
    firstOrderCurveBound n k k L A 22 4 1 851
        (τ := 2 * k - 3) (η := firstOrderCurveDirectRatio n k A) ≤
      (1714463276 / 3 : ℚ) * n ^ 2 := by
  dsimp only
  let L := correlatedMidpoint (6 / 25 : ℝ) n k
  have hnpos : 0 < n := by omega
  have hkpos : 0 < k := by omega
  have hmid := correlatedMidpoint_bounds (6 / 25 : ℝ) n k A (by norm_num) hgap hAn
  have hratiosR := correlatedMidpoint_ratios_le_two_div
    (6 / 25 : ℝ) n k A (by norm_num) hnpos hkpos hgap hAn
  have hratioOne : firstOrderCurveJointRatio n L A ≤ (25 / 3 : ℚ) := by
    unfold firstOrderCurveJointRatio
    have h := hratiosR.1
    norm_num at h
    refine (Rat.cast_le (K := ℝ)).mp ?_
    norm_num
    simpa [L, Nat.cast_add] using h
  have hratioTwo : firstOrderCurveFiberRatio n k L ≤ (25 / 3 : ℚ) := by
    unfold firstOrderCurveFiberRatio
    have h := hratiosR.2
    norm_num at h
    refine (Rat.cast_le (K := ℝ)).mp ?_
    norm_num
    simpa [L, Nat.cast_add] using h
  have hratioDirect := uniformFirstOrder_directRatio_le n k A hkpos hAn hgap
  have hkN : k ≤ n := hmid.1.trans (hmid.2.1.trans hAn)
  have hτ : 2 * k - 3 ≤ 2 * n := by omega
  have hJzero :
      (firstOrderCurveJointZero k 22 4 1 851 (2 * k - 3) : ℚ) ≤
        (1118385 / 4 : ℚ) * n ^ 2 := by
    calc
      (firstOrderCurveJointZero k 22 4 1 851 (2 * k - 3) : ℚ) ≤
          firstOrderCurveJointZero n 22 4 1 851 (2 * n) := by
            exact_mod_cast uniformFirstOrder_jointZero_mono hτ
      _ = 551448 * n + 15489 := by
        rw [uniformFirstOrder_jointZero_two_mul]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ (1118385 / 4 : ℚ) * n ^ 2 := by
        have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg ((n : ℚ) - 2)]
  have hJone :
      (firstOrderCurveJointOne k 22 4 1 851 (2 * k - 3) : ℚ) ≤
        (16390956 : ℚ) * n ^ 2 := by
    calc
      (firstOrderCurveJointOne k 22 4 1 851 (2 * k - 3) : ℚ) ≤
          16114536 * n ^ 2 + 551056 * n + 3568 := by
            exact_mod_cast uniformFirstOrder_jointOne_le_two_mul (k := k) hτ
      _ ≤ (16390956 : ℚ) * n ^ 2 := by
        have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg ((n : ℚ) - 2)]
  have hBzero : (firstOrderCurveFiberZero 22 4 : ℚ) = 171 := by
    norm_num [uniformFirstOrder_fiberZero_eq]
  have hBone :
      (firstOrderCurveFiberOne k 22 4 (2 * k - 3) : ℚ) ≤ 3249 * n := by
    calc
      (firstOrderCurveFiberOne k 22 4 (2 * k - 3) : ℚ) ≤
          3208 * n + 82 := by
            exact_mod_cast uniformFirstOrder_fiberOne_le_two_mul (k := k) hτ
      _ ≤ 3249 * n := by
        have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
        nlinarith
  have hnL : n - L ≤ n := Nat.sub_le _ _
  unfold firstOrderCurveBound
  dsimp only
  simp only [Nat.one_mul]
  change (851 : ℚ) +
      ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ) * _ +
      ((n - L + 1 : ℕ) : ℚ) / (A - L + 1 : ℕ) *
          firstOrderCurveDirectRatio n k A * _ +
      ((n - L : ℕ) : ℚ) * ((firstOrderCurveFiberZero 22 4 : ℚ) +
        ((n - k + 1 : ℕ) : ℚ) / (L - k + 1 : ℕ) * _) ≤ _
  unfold firstOrderCurveJointRatio at hratioOne
  unfold firstOrderCurveFiberRatio at hratioTwo
  rw [hBzero]
  have hnLq : ((n - L : ℕ) : ℚ) ≤ n := by exact_mod_cast hnL
  have hz0 : (0 : ℚ) ≤ firstOrderCurveJointZero k 22 4 1 851 (2 * k - 3) := by
    exact_mod_cast Nat.zero_le (firstOrderCurveJointZero k 22 4 1 851 (2 * k - 3))
  have hz1 : (0 : ℚ) ≤ firstOrderCurveJointOne k 22 4 1 851 (2 * k - 3) := by
    exact_mod_cast Nat.zero_le (firstOrderCurveJointOne k 22 4 1 851 (2 * k - 3))
  have hb1 : (0 : ℚ) ≤ firstOrderCurveFiberOne k 22 4 (2 * k - 3) := by
    exact_mod_cast Nat.zero_le (firstOrderCurveFiberOne k 22 4 (2 * k - 3))
  have hrd : (0 : ℚ) ≤ firstOrderCurveDirectRatio n k A := by
    unfold firstOrderCurveDirectRatio
    positivity
  have htermZero :
      firstOrderCurveJointRatio n L A *
          firstOrderCurveJointZero k 22 4 1 851 (2 * k - 3) ≤
        (25 / 3 : ℚ) * ((1118385 / 4 : ℚ) * n ^ 2) :=
    mul_le_mul hratioOne hJzero hz0 (by positivity)
  have hratioProduct :
      firstOrderCurveJointRatio n L A * firstOrderCurveDirectRatio n k A ≤
        (25 / 3 : ℚ) * (25 / 6 : ℚ) :=
    mul_le_mul hratioOne hratioDirect hrd (by positivity)
  have htermOne :
      firstOrderCurveJointRatio n L A * firstOrderCurveDirectRatio n k A *
          firstOrderCurveJointOne k 22 4 1 851 (2 * k - 3) ≤
        (25 / 3 : ℚ) * (25 / 6 : ℚ) * ((16390956 : ℚ) * n ^ 2) :=
    mul_le_mul hratioProduct hJone hz1 (by positivity)
  have hfiberInner :
      (171 : ℚ) + firstOrderCurveFiberRatio n k L *
          firstOrderCurveFiberOne k 22 4 (2 * k - 3) ≤
        171 + (25 / 3 : ℚ) * (3249 * n) := by
    exact add_le_add le_rfl (mul_le_mul hratioTwo hBone hb1 (by positivity))
  have hfiberNonneg : (0 : ℚ) ≤
      171 + firstOrderCurveFiberRatio n k L *
        firstOrderCurveFiberOne k 22 4 (2 * k - 3) := by
    apply add_nonneg (by norm_num)
    exact mul_nonneg (by unfold firstOrderCurveFiberRatio; positivity) hb1
  have htermFiber :
      ((n - L : ℕ) : ℚ) * ((171 : ℚ) + firstOrderCurveFiberRatio n k L *
          firstOrderCurveFiberOne k 22 4 (2 * k - 3)) ≤
        n * (171 + (25 / 3 : ℚ) * (3249 * n)) :=
    mul_le_mul hnLq hfiberInner hfiberNonneg (by positivity)
  calc
    (851 : ℚ) + firstOrderCurveJointRatio n L A *
          firstOrderCurveJointZero k 22 4 1 851 (2 * k - 3) +
        firstOrderCurveJointRatio n L A * firstOrderCurveDirectRatio n k A *
          firstOrderCurveJointOne k 22 4 1 851 (2 * k - 3) +
        (n - L : ℕ) * (171 + firstOrderCurveFiberRatio n k L *
          firstOrderCurveFiberOne k 22 4 (2 * k - 3))
      ≤ 851 + (25 / 3 : ℚ) * ((1118385 / 4 : ℚ) * n ^ 2) +
          (25 / 3 : ℚ) * (25 / 6 : ℚ) * ((16390956 : ℚ) * n ^ 2) +
          n * (171 + (25 / 3 : ℚ) * (3249 * n)) := by
            exact add_le_add (add_le_add (add_le_add le_rfl htermZero) htermOne) htermFiber
    _ = (6857849525 / 12 : ℚ) * n ^ 2 + 171 * n + 851 := by ring
    _ ≤ (6857849525 / 12 : ℚ) * n ^ 2 +
          (171 / 2 : ℚ) * n ^ 2 + (851 / 4 : ℚ) * n ^ 2 := by
      have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
      have hlinear : (171 : ℚ) * n ≤ (171 / 2 : ℚ) * n ^ 2 := by nlinarith
      have hheight : (851 : ℚ) ≤ (851 / 4 : ℚ) * n ^ 2 := by nlinarith
      linarith
    _ = (1714463276 / 3 : ℚ) * n ^ 2 := by ring

set_option maxHeartbeats 4000000 in
-- The recursive list weight has twenty-two closed stages to normalize.
/-- For `k >= 2`, the height-851 shifted curve certificate gives one exceptional set for the
whole received line and all close candidates, with equality of complete agreement sets. -/
private theorem exists_uniformFirstOrder_lineMCA_of_two_le
    {F : Type u} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (k - 1) 22 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 571487759 * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let D := k - 1
  let L := correlatedMidpoint (6 / 25 : ℝ) n k
  let values : Fin 2 → Fin n → F := ![f, g]
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  have hgapNat : 25 * k + 6 * n ≤ 25 * A := by
    exact_mod_cast (show (25 : ℝ) * k + 6 * n ≤ 25 * A by nlinarith)
  obtain ⟨hD, hbudget, hkD, hheight⟩ :=
    uniformFirstOrder_parameters n k A hn hk hAn hgapNat
  have hkpos : 0 < k := by omega
  have hmid := correlatedMidpoint_bounds (6 / 25 : ℝ) n k A (by norm_num) hgap hAn
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := D) (A := A) (m := 12) (M := 4) (mu := 22) (k := k) (h := 851)
      (n := n) (K := k) (L := L) (ell := 1)
      domain values iota (by omega) hbudget hkD hheight (by omega) (le_refl k) hkpos
        hmid.1 hmid.2.1 hAn (by norm_num) hchar
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardR : (exceptional.card : ℝ) ≤
        (firstOrderCurveBound n k k L A 22 4 1 851
          (τ := 2 * k - 3) (η := firstOrderCurveDirectRatio n k A) : ℚ) := by
      exact_mod_cast hcard
    exact hcardR.trans <| (show
      ((firstOrderCurveBound n k k L A 22 4 1 851
        (τ := 2 * k - 3) (η := firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) ≤
          571487759 * (n : ℝ) ^ 2 by
        have hb := uniformFirstOrder_curveBound_le n k A hn hk hAn hgap
        have hbR :
            ((firstOrderCurveBound n k k L A 22 4 1 851
              (τ := 2 * k - 3) (η := firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) ≤
              ((1714463276 / 3 : ℚ) : ℝ) * n ^ 2 := by exact_mod_cast hb
        apply hbR.trans
        gcongr
        norm_num)
  · intro z hz P hdegree hagree
    have hword : powerBatchedWord values z = fun i ↦ f i + z * g i := by
      funext i
      simp [values, powerBatchedWord, Fin.sum_univ_two]
    have hpower := hgood z hz P hdegree (by rwa [hword])
    simpa [values] using
      (exactCorrelatedPair_of_powerAgreement_one domain values (RingHom.id F) z P hpower)

/-- Constant message polynomials admit an elementary exact-agreement argument.  A challenge is
exceptional only when two received coordinate pairs collide on the affine line. -/
private theorem exists_uniformFirstOrder_lineMCA_one
    {F : Type u} [Field F] [DecidableEq F]
    (n A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hA : 0 < A) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 1325775 * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) 1 z P := by
  classical
  let collision : Fin n × Fin n → F := fun ij ↦
    if g ij.1 = g ij.2 then 0 else -(f ij.1 - f ij.2) / (g ij.1 - g ij.2)
  let exceptional := (Finset.univ : Finset (Fin n × Fin n)).image collision
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : exceptional.card ≤ n * n := by
      calc
        exceptional.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
          Finset.card_image_le
        _ = n * n := by simp
    have hcardR : (exceptional.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (by simpa [pow_two] using hcard)
    exact hcardR.trans (by
      have hs : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith)
  · intro z hz P hdegree hagree
    let agreement := polynomialAgreementSet domain (fun i ↦ f i + z * g i) P
    have hagreementPos : 0 < agreement.card := hA.trans_le hagree
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hagreementPos
    have hiEq : P.eval (domain i) = f i + z * g i := by
      exact (Finset.mem_filter.mp hi).2
    have hconstant : P = Polynomial.C (P.eval (domain i)) := by
      have hpdeg : P.degree ≤ 0 := Order.lt_succ_iff.mp hdegree
      rw [Polynomial.eq_C_of_degree_le_zero hpdeg]
      simp
    have hpair : ∀ j, j ∈ agreement → f j = f i ∧ g j = g i := by
      intro j hj
      have hjEq : P.eval (domain j) = f j + z * g j :=
        (Finset.mem_filter.mp hj).2
      have heq : f j + z * g j = f i + z * g i := by
        rw [← hjEq, ← hiEq, hconstant]
        simp only [Polynomial.eval_C]
      by_cases hg : g j = g i
      · refine ⟨?_, hg⟩
        rw [hg] at heq
        simpa using heq
      · exfalso
        apply hz
        apply Finset.mem_image.mpr
        refine ⟨(j, i), Finset.mem_univ _, ?_⟩
        rw [show collision (j, i) = -(f j - f i) / (g j - g i) by simp [collision, hg]]
        apply (div_eq_iff (sub_ne_zero.mpr hg)).2
        linear_combination -heq
    let P₀ : F[X] := Polynomial.C (f i)
    let P₁ : F[X] := Polynomial.C (g i)
    refine ⟨⟨P₀, P₁⟩,
      Polynomial.degree_C_le.trans_lt (by norm_num),
      Polynomial.degree_C_le.trans_lt (by norm_num), ?_, ?_⟩
    · rw [hconstant, hiEq]
      simp [P₀, P₁, correlatedPairSpecialization]
    · ext j
      simp only [polynomialAgreementSet, commonPolynomialAgreementSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        have hjmem : j ∈ agreement := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa [mappedDomain] using hj
        obtain ⟨hfj, hgj⟩ := hpair j hjmem
        simp [P₀, P₁, hfj, hgj]
      · rintro ⟨hfj, hgj⟩
        have hfj' : f i = f j := by simpa only [P₀, Polynomial.eval_C] using hfj
        have hgj' : g i = g j := by simpa only [P₁, Polynomial.eval_C] using hgj
        rw [hconstant, Polynomial.eval_C, hiEq, hfj', hgj']
        simp

/-- At gap `6/25`, one exceptional set of at most `1325775 n^2` challenges works for every
degree-`< k` candidate and preserves equality of the complete agreement set. -/
theorem exists_uniformFirstOrder_lineMCA
    {F : Type u} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ max (k - 1) 4 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 1325775 * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  by_cases hkTwo : 2 ≤ k
  · exact exists_uniformFirstOrder_squarefree_lineMCA_of_two_le n k A domain f g
      hn hkTwo hAn hgap (hchar hkTwo)
  · have hkOne : k = 1 := by omega
    subst k
    have hA : 0 < A := by exact_mod_cast (show (0 : ℝ) < A by linarith)
    exact exists_uniformFirstOrder_lineMCA_one n A domain f g hA

/-- The uniform line theorem packaged for the generic affine-line and affine-space reductions. -/
theorem lineExactAgreementBound_uniformFirstOrder
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ max (k - 1) 4 < ringChar F) :
    LineExactAgreementBound domain k A (1325775 * (n : ℝ) ^ 2) := by
  intro f g
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_uniformFirstOrder_lineMCA n k A domain f g hn hk hAn hgap hchar
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hdegree hagree
  obtain ⟨pair, hp0, hp1, hP, hsets⟩ := hgood z hz P hdegree hagree
  exact ⟨pair.1, pair.2, hp0, hp1, by simpa [correlatedPairSpecialization] using hP,
    by simpa [mappedDomain] using hsets⟩

open Classical in
/-- The corresponding canonical affine-line MCA error is at most the exceptional-set budget
divided by the field size. -/
theorem mcaError_affineLine_uniformFirstOrder_le
    {F : Type} [Field F] [Fintype F]
    (n k A : ℕ) (domain : Fin n ↪ F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ max (k - 1) 4 < ringChar F)
    (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineLineGenerator F) (code domain k) radius ≤
      ENNReal.ofReal
        (1325775 * (n : ℝ) ^ 2 / (Fintype.card F : ℝ)) := by
  exact mcaError_affineLine_le_of_exactAgreement domain _
    (lineExactAgreementBound_uniformFirstOrder n k A domain hn hk hAn hgap hchar)
      radius hthreshold

open Classical in
/-- For every positive affine dimension, the uniform first-order line certificate gives the
same dimension-independent error bound with the standard `|F| - 1` denominator. -/
theorem mcaError_affineSpace_uniformFirstOrder_le
    {F : Type} [Field F] [Fintype F]
    (n k A s : ℕ) (domain : Fin n ↪ F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ max (k - 1) 4 < ringChar F)
    (hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F s) (code domain k) radius ≤
      ENNReal.ofReal
        (1325775 * (n : ℝ) ^ 2 / ((Fintype.card F : ℝ) - 1)) := by
  exact mcaError_affineSpace_le_of_exactAgreement domain _
    (lineExactAgreementBound_uniformFirstOrder n k A domain hn hk hAn hgap hchar)
      hs radius hthreshold

end ReedSolomon

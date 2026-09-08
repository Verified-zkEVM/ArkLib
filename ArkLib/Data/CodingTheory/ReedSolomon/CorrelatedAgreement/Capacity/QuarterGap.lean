/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.FirstOrderCurve
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.QuarterGapParameters
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.SharpCountingBound
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.PowerToLine

/-!
# The explicit quarter-gap line bound

The fixed first-order interpolation certificate with jet cap `119` and challenge height `1449`
gives the quadratic exceptional-set bound in the quarter-gap regime.  The construction is over
the original field and retains equality of the complete agreement sets.
-/

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain
open scoped BigOperators

universe u

/-- The explicit coefficient in the quarter-gap line theorem. -/
def quarterGapMCAConstant (δ : ℝ) : ℝ :=
  1449 + 156274905024 / δ ^ 2 + 6740636 / δ

/-- The cap-sensitive first-order envelope with the tight Taylor exponent and direct
dimension-sensitive order-one factor is no larger than the arbitrary-order sharp scalar with
derivative cap one. -/
theorem firstOrderCurveBound_midpoint_le_sharpScalar
    (δ : ℝ) (n K k A μ M h : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : 0 < n) (hk : 0 < k) (hμ : 0 < μ)
    (hh : 0 < h) (hKn : K ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    (firstOrderCurveBound n K k (correlatedMidpoint δ n k) A μ M 1 h
      (τ := 2 * K - 3) (η := firstOrderCurveDirectRatio n k A) : ℝ) ≤
      polynomialCurveSharpMCAConstant δ μ h 1 * (n : ℝ) ^ 2 := by
  let L := correlatedMidpoint δ n k
  let τ := 2 * K - 3
  let s := firstOrderCurveJointRatio n L A
  let η := firstOrderCurveDirectRatio n k A
  let t := firstOrderCurveFiberRatio n k L
  let c : ℚ := ((n - L : ℕ) : ℚ)
  let c₀ := curveStageZero K 1 h s c (τ := τ)
  let c₁ := curveStageOne K 1 h s t c (τ := τ) (η := η)
  let q : ℕ → ℚ := fun v ↦
    regularSymbolicCurveMCASharpBound 1 n 1 K k L A v h (τ := τ)
  have hL := correlatedMidpoint_bounds δ n k A hδ.le hgap hAn
  have hs : 1 ≤ s := by
    unfold s firstOrderCurveJointRatio
    apply (le_div_iff₀ (by positivity)).2
    simpa only [one_mul] using
      (show ((A - L + 1 : ℕ) : ℚ) ≤ (n - L + 1 : ℕ) by exact_mod_cast (by omega))
  have ht : 1 ≤ t := by
    unfold t firstOrderCurveFiberRatio
    apply (le_div_iff₀ (by positivity)).2
    simpa only [one_mul] using
      (show ((L - k + 1 : ℕ) : ℚ) ≤ (n - k + 1 : ℕ) by exact_mod_cast (by omega))
  have hη : 1 ≤ η := by
    exact firstOrderCurveDirectRatio_one_le (hL.1.trans hL.2.1) hAn
  have hc : 0 ≤ c := by positivity
  have hq (v : ℕ) : q v =
      (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) * s * η +
        c * (v : ℚ) * (sourceCurveCutJetDegree K v (τ := τ) : ℚ) * t := by
    simp only [q, regularSymbolicCurveMCASharpBound,
      AffineHilbert.dimensionSensitiveIncidenceProduct_one, Nat.mul_one, one_mul, pow_one]
    simp only [s, η, t, c, firstOrderCurveJointRatio, firstOrderCurveFiberRatio,
      firstOrderCurveDirectRatio]
  have hzerocharge (v : ℕ) : c₀ v ≤ q v := by
    let b := sourceCurveCutJetDegree K v (τ := τ)
    let a := sourceCurveCutChallengeDegree 1 K h (τ := τ)
    have hb : 1 ≤ b := by simp [b, sourceCurveCutJetDegree]
    have hjointNat : h * b + v * a ≤ sourceCurveInitialMixedDegree 1 1 K v h
        (τ := τ) := by
      have hb2 : b ≤ b ^ 2 := by nlinarith
      have ha : v * a ≤ 2 * v * a * b := by
        calc
          v * a = 1 * (v * a) := by ring
          _ ≤ (2 * b) * (v * a) := Nat.mul_le_mul_right _ (by omega)
          _ = 2 * v * a * b := by ring
      calc
        h * b + v * a ≤ h * b ^ 2 + 2 * v * a * b :=
          Nat.add_le_add (Nat.mul_le_mul_left h hb2) ha
        _ = sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) := by
          simp [sourceCurveInitialMixedDegree, b, a, pow_two]
    have hfiberNat : v ≤ v * b := by
      simpa only [Nat.mul_one v] using Nat.mul_le_mul_left v hb
    rw [hq]
    unfold c₀ curveStageZero
    change s * ((h * b + v * a : ℕ) : ℚ) + c * v ≤ _
    have hjoint : s * ((h * b + v * a : ℕ) : ℚ) ≤
        (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) * s * η := by
      have hs0 : 0 ≤ s := le_trans (by norm_num) hs
      have hbig : 0 ≤ (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) * s :=
        mul_nonneg (by positivity) hs0
      calc
        s * ((h * b + v * a : ℕ) : ℚ) ≤
            s * (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) := by
          apply mul_le_mul_of_nonneg_left _ hs0
          exact_mod_cast hjointNat
        _ = (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) * s := by ring
        _ ≤ (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) * s * η := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hη hbig
        _ = _ := by ring
    have hfiber : c * (v : ℚ) ≤ c * (v : ℚ) * (b : ℚ) * t := by
      calc
        c * (v : ℚ) ≤ c * ((v * b : ℕ) : ℚ) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact_mod_cast hfiberNat
        _ ≤ c * ((v * b : ℕ) : ℚ) * t := by
          have hnonneg : 0 ≤ c * ((v * b : ℕ) : ℚ) := by positivity
          simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hnonneg
        _ = _ := by push_cast; ring
    exact add_le_add hjoint hfiber
  have honecharge (v r : ℕ) (hrv : r ≤ v) : c₁ v r ≤ q v := by
    let b := firstOrderTaylorTotalCap v τ
    let cap := firstOrderTaylorDerivativeCap K v r τ
    let a := sourceCurveCutChallengeDegree 1 K h (τ := τ)
    have hcapb : cap ≤ b := min_le_left _ _
    have harea : 2 * b * cap - cap ^ 2 ≤ b ^ 2 := by
      have h := AffineHilbert.cappedTriangleDegree_le hcapb le_rfl le_rfl hcapb
      simpa only [show 2 * b * b - b ^ 2 = b ^ 2 by
        rw [show 2 * b * b = b ^ 2 + b ^ 2 by ring, Nat.add_sub_cancel_left]] using h
    have hfiberNat := firstOrderCurveFiberStageOne_le_full
      (K := K) (j := v) (r := r) (τ := τ) hrv
    have hjointNat : firstOrderCurveJointStageOne K 1 h v r τ ≤
        sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) := by
      have hleft := Nat.mul_le_mul_left h harea
      have hright := Nat.mul_le_mul_left (2 * a) hfiberNat
      calc
        firstOrderCurveJointStageOne K 1 h v r τ =
            h * (2 * b * cap - cap ^ 2) +
              2 * a * firstOrderCurveFiberStageOne K v r τ := by
          simp [firstOrderCurveJointStageOne, AffineHilbert.mixedDerivativeImageDegree,
            firstOrderCurveFiberStageOne, AffineHilbert.fixedFiberDerivativeImageDegree,
            b, cap, a, sourceCurveCutChallengeDegree]
        _ ≤ h * b ^ 2 + 2 * a * (v * b) := Nat.add_le_add hleft hright
        _ = sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) := by
          simp [sourceCurveInitialMixedDegree, b, a, firstOrderTaylorTotalCap,
            sourceCurveCutJetDegree, sourceCurveCutChallengeDegree, pow_two]
          ring
    rw [hq]
    unfold c₁ curveStageOne
    have hjoint : s * η * (firstOrderCurveJointStageOne K 1 h v r τ : ℚ) ≤
        (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) * s * η := by
      calc
        s * η * (firstOrderCurveJointStageOne K 1 h v r τ : ℚ) ≤
            s * η * (sourceCurveInitialMixedDegree 1 1 K v h (τ := τ) : ℚ) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (by positivity))
          exact_mod_cast hjointNat
        _ = _ := by ring
    have hfiber : c * t * (firstOrderCurveFiberStageOne K v r τ : ℚ) ≤
        c * (v : ℚ) * (sourceCurveCutJetDegree K v (τ := τ) : ℚ) * t := by
      have hf : (firstOrderCurveFiberStageOne K v r τ : ℚ) ≤
          ((v * firstOrderTaylorTotalCap v τ : ℕ) : ℚ) := by
        exact_mod_cast hfiberNat
      rw [show sourceCurveCutJetDegree K v (τ := τ) = firstOrderTaylorTotalCap v τ by rfl]
      calc
        c * t * (firstOrderCurveFiberStageOne K v r τ : ℚ) ≤
            c * t * ((v * firstOrderTaylorTotalCap v τ : ℕ) : ℚ) := by
          exact mul_le_mul_of_nonneg_left hf (mul_nonneg hc (by positivity))
        _ = _ := by push_cast; ring
    exact add_le_add hjoint hfiber
  have hcap : firstOrderStageCap c₀ c₁ μ M ≤ ∑ j ∈ Finset.range μ, q (j + 1) := by
    unfold firstOrderStageCap
    rw [← Finset.sum_range_add_sum_Ico (fun j ↦ q (j + 1))
      (Nat.sub_le μ (min M μ))]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro j _
      exact hzerocharge (j + 1)
    · apply Finset.sum_le_sum
      intro j hj
      exact honecharge (j + 1) (j + 1 - (μ - min M μ)) (by omega)
  have hboundQ : firstOrderCurveBound n K k L A μ M 1 h
      (τ := τ) (η := η) ≤
      (h : ℚ) + ∑ j ∈ Finset.range μ, q (j + 1) := by
    rw [← firstOrderCurveStageCap_add_height_eq_of_factors n K k L A μ M 1 h τ η]
    simp only [Nat.one_mul]
    change (h : ℚ) + firstOrderStageCap c₀ c₁ μ M ≤ _
    exact add_le_add le_rfl hcap
  have hboundR : (firstOrderCurveBound n K k L A μ M 1 h
      (τ := τ) (η := η) : ℝ) ≤
      (h : ℝ) + ∑ j ∈ Finset.range μ,
        (regularSymbolicCurveMCASharpBound 1 n 1 K k L A (j + 1) h
          (τ := τ) : ℝ) := by
    have := hboundQ
    simp only [q] at this
    exact_mod_cast this
  have hmono : ∑ j ∈ Finset.range μ,
        (regularSymbolicCurveMCASharpBound 1 n 1 K k L A (j + 1) h
          (τ := τ) : ℝ) ≤
      ∑ j ∈ Finset.range μ,
        (regularSymbolicCurveMCASharpBound 1 n 1 K k L A (j + 1) h : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact_mod_cast regularSymbolicCurveMCASharpBound_mono_exponent
      1 n 1 K k L A (j + 1) h τ (2 * K) (by dsimp [τ]; omega)
  apply hboundR.trans
  apply (add_le_add (le_refl (h : ℝ)) hmono).trans
  simpa only [L, Nat.one_mul, Nat.cast_one, one_mul, Nat.reduceAdd] using
    (regularSymbolicCurveMCASharp_finiteStage_uniform_le (Finset.range μ)
      (fun _ ↦ 1) (fun j ↦ j + 1) (fun _ ↦ h)
      δ n K k A 1 μ h 1 hδ hδone hn hk hμ hh hKn hgap hAn
      (by simp) (by simp) (by simp) (by simp) (by simp))

/-- The generic sharp coefficient at the fixed first-order parameters is exactly the explicit
quarter-gap coefficient. -/
theorem polynomialCurveSharpMCAConstant_quarterGap (δ : ℝ) (hδ : 0 < δ) :
    polynomialCurveSharpMCAConstant δ 119 1449 1 = quarterGapMCAConstant δ := by
  unfold polynomialCurveSharpMCAConstant quarterGapMCAConstant
  have hδne : δ ≠ 0 := hδ.ne'
  simp only [Nat.cast_ofNat, Nat.reduceAdd, div_pow]
  field_simp [hδne]
  ring

/-- In the quarter-gap regime, a fixed first-order interpolation certificate gives the exact
line-agreement conclusion outside an exceptional set of the advertised quadratic size.  The
algebraic-closure construction descends both the exceptional challenges and the witness
polynomials to the original field. -/
theorem exists_quarterGapLineMCA
    {F : Type u} [Field F] [DecidableEq F]
    (δ : ℝ) (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 512 ≤ n) (hδ : (1 / 4 : ℝ) ≤ δ) (hδhalf : δ < 1 / 2)
    (hk : 0 < k) (hkn : k ≤ n) (hAn : A ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ quarterGapMCAConstant δ * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let D := max k 3 - 1
  let K := max k 2
  let L := correlatedMidpoint δ n k
  let values : Fin 2 → Fin n → F := ![f, g]
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  have hδpos : 0 < δ := lt_of_lt_of_le (by norm_num) hδ
  have hδone : δ ≤ 1 := by linarith
  have hnpos : 0 < n := by omega
  have hmid := correlatedMidpoint_bounds δ n k A hδpos.le hgap hAn
  have hK : 1 < K := by
    dsimp only [K]
    omega
  have hkK : k ≤ K := by
    dsimp only [K]
    omega
  have hKn : K ≤ n := by
    dsimp only [K]
    omega
  have hchar' : ringChar F = 0 ∨ max (K - 1) 119 < ringChar F := by
    apply hchar.imp_right
    intro hnchar
    apply (show max (K - 1) 119 < n by
      apply max_lt
      · dsimp only [K]
        omega
      · omega).trans_le hnchar
  obtain ⟨hD, hbudget, hkD, hheight⟩ :=
    quarterGap_firstOrderCurve_parameters δ n k A hn hk hkn hAn hδ hδhalf hgap
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_tight
      (D := D) (A := A) (m := 64) (M := 16) (mu := 119) (k := k) (h := 1449)
      (n := n) (K := K) (L := L) (ell := 1)
      domain values iota (by omega) hbudget hkD hheight hK hkK hk hmid.1 hmid.2.1 hAn
        (by norm_num) hchar'
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardR : (exceptional.card : ℝ) ≤
        (firstOrderCurveBound n K k L A 119 16 1 1449
          (τ := 2 * K - 3) (η := firstOrderCurveDirectRatio n k A) : ℝ) := by
      exact_mod_cast hcard
    apply hcardR.trans
    have hscalar := firstOrderCurveBound_midpoint_le_sharpScalar
      δ n K k A 119 16 1449 hδpos hδone hnpos hk (by norm_num) (by norm_num)
        hKn hgap hAn
    rw [polynomialCurveSharpMCAConstant_quarterGap δ hδpos] at hscalar
    simpa only [L] using hscalar
  · intro z hz P hdegree hagree
    have hword : powerBatchedWord values z = fun i ↦ f i + z * g i := by
      funext i
      simp [values, powerBatchedWord, Fin.sum_univ_two]
    have hpower := hgood z hz P hdegree (by rwa [hword])
    simpa [values] using
      (exactCorrelatedPair_of_powerAgreement_one domain values (RingHom.id F) z P hpower)

end ReedSolomon

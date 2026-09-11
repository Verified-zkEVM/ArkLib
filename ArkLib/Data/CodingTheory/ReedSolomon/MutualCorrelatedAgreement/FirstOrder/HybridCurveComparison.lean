/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveDominance
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageMonotonicity
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.StageSum

/-!
# Dominance of the first-order hybrid curve bound

The hybrid curve transfer reconstructs at the actual message dimension and differentiates only
through the actual regular stages. This file proves, pointwise in the actual derivative degree
and retention threshold, that its charge is no larger than the manuscript's former
full-differentiation envelope. The latter is identified with the retained
`firstOrderCurveBound` evaluator, so existing exact numerical certificates transfer directly.

The proof first pays the ordinary content and resultant exclusions from the triangular tail
saving. It then promotes missing ordinary stages to order one and increases the reconstruction
dimension. Only after the pointwise comparison does it take the maximum over actual degrees and
the minimum over retention thresholds.
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative.SymbolicSeparantChain

private theorem firstOrderStageCap_le_succ_derivativeCap
    {c₀ : ℕ → ℚ} {c₁ : ℕ → ℕ → ℚ} {μ e : ℕ}
    (heμ : e + 1 ≤ μ)
    (hpromote : ∀ j, c₀ j ≤ c₁ j 1)
    (hderiv : ∀ {j r q}, r ≤ q → q ≤ j → c₁ j r ≤ c₁ j q) :
    firstOrderStageCap c₀ c₁ μ e ≤ firstOrderStageCap c₀ c₁ μ (e + 1) := by
  let b := μ - (e + 1)
  have hsplit : μ - e = b + 1 := by omega
  have hbμ : b + 1 ≤ μ := by omega
  have hregular :
      (∑ t ∈ Finset.Ico (b + 1) μ, c₁ (t + 1) (t + 1 - (b + 1))) ≤
        ∑ t ∈ Finset.Ico (b + 1) μ, c₁ (t + 1) (t + 1 - b) := by
    apply Finset.sum_le_sum
    intro t ht
    have htb : b + 1 ≤ t := (Finset.mem_Ico.mp ht).1
    apply hderiv (by omega)
    omega
  rw [firstOrderStageCap, firstOrderStageCap, min_eq_left (by omega : e ≤ μ),
    min_eq_left heμ]
  rw [hsplit, Finset.sum_range_succ]
  change
    (∑ x ∈ Finset.range b, c₀ (x + 1)) + c₀ (b + 1) +
        ∑ x ∈ Finset.Ico (b + 1) μ, c₁ (x + 1) (x + 1 - (b + 1)) ≤
      (∑ x ∈ Finset.range b, c₀ (x + 1)) +
        ∑ x ∈ Finset.Ico b μ, c₁ (x + 1) (x + 1 - b)
  have hhead : c₀ (b + 1) ≤ c₁ (b + 1) 1 := hpromote (b + 1)
  have hjoin := Finset.sum_Ico_consecutive
    (fun t ↦ c₁ (t + 1) (t + 1 - b)) (show b ≤ b + 1 by omega) hbμ
  have hsingle :
      (∑ t ∈ Finset.Ico b (b + 1), c₁ (t + 1) (t + 1 - b)) = c₁ (b + 1) 1 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [hsingle] at hjoin
  calc
    (∑ x ∈ Finset.range b, c₀ (x + 1)) + c₀ (b + 1) +
        ∑ x ∈ Finset.Ico (b + 1) μ, c₁ (x + 1) (x + 1 - (b + 1)) ≤
      (∑ x ∈ Finset.range b, c₀ (x + 1)) + c₁ (b + 1) 1 +
        ∑ x ∈ Finset.Ico (b + 1) μ, c₁ (x + 1) (x + 1 - b) := by
          gcongr
    _ = (∑ x ∈ Finset.range b, c₀ (x + 1)) +
        ∑ x ∈ Finset.Ico b μ, c₁ (x + 1) (x + 1 - b) := by
          rw [← hjoin]
          ring

/-- Promoting ordinary stages to order one makes the extremal stage cap monotone in the
permitted derivative degree. -/
theorem firstOrderStageCap_mono_derivativeCap
    {c₀ : ℕ → ℚ} {c₁ : ℕ → ℕ → ℚ} {μ e M : ℕ}
    (heM : e ≤ M) (hMμ : M ≤ μ)
    (hpromote : ∀ j, c₀ j ≤ c₁ j 1)
    (hderiv : ∀ {j r q}, r ≤ q → q ≤ j → c₁ j r ≤ c₁ j q) :
    firstOrderStageCap c₀ c₁ μ e ≤ firstOrderStageCap c₀ c₁ μ M := by
  induction M with
  | zero =>
      have : e = 0 := by omega
      subst e
      exact le_rfl
  | succ M ih =>
      by_cases heq : e = M + 1
      · subst e
        exact le_rfl
      · have heM' : e ≤ M := by omega
        exact (ih heM' (by omega)).trans
          (firstOrderStageCap_le_succ_derivativeCap (by omega) hpromote hderiv)

end ReedSolomon.HiddenDerivative.SymbolicSeparantChain

namespace ReedSolomon.HiddenDerivative

open SymbolicSeparantChain

/-- The full-stage curve envelope increases when both the permitted derivative degree and the
ambient reconstruction dimension increase. The message dimension and incidence factors stay
fixed. -/
theorem firstOrderCurveBound_mono_ambient
    {n k K L A μ e M ell H : ℕ}
    (hk : 2 ≤ k) (hkK : k ≤ K) (heM : e ≤ M) (hMμ : M ≤ μ)
    (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    firstOrderCurveBound n k k L A μ e ell H (hybridTau (k - 1))
        (firstOrderCurveDirectRatio n k A) ≤
      firstOrderCurveBound n K k L A μ M ell H (hybridTau (K - 1))
        (firstOrderCurveDirectRatio n k A) := by
  let s := firstOrderCurveJointRatio n L A
  let t := firstOrderCurveFiberRatio n k L
  let η := firstOrderCurveDirectRatio n k A
  let c : ℚ := ((ell * (n - L) : ℕ) : ℚ)
  let τ := hybridTau (k - 1)
  let τ' := hybridTau (K - 1)
  let c₀ : ℕ → ℚ := fun j ↦ curveStageZero k ell H s c j τ
  let c₀' : ℕ → ℚ := fun j ↦ curveStageZero K ell H s c j τ'
  let c₁ : ℕ → ℕ → ℚ := fun j r ↦ curveStageOne k ell H s t c j r τ η
  let c₁' : ℕ → ℕ → ℚ := fun j r ↦ curveStageOne K ell H s t c j r τ' η
  have hs : 1 ≤ s := firstOrderCurveJointRatio_one_le hLA hAn
  have ht : 1 ≤ t := firstOrderCurveFiberRatio_one_le hkL (hLA.trans hAn)
  have hη : 1 ≤ η := firstOrderCurveDirectRatio_one_le (hkL.trans hLA) hAn
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hη0 : 0 ≤ η := le_trans (by norm_num) hη
  have hc0 : 0 ≤ c := by positivity
  have hτ : τ ≤ τ' := by
    dsimp only [τ, τ', hybridTau]
    omega
  have hzero : ∀ j, c₀ j ≤ c₀' j := by
    intro j
    unfold c₀ c₀' curveStageZero
    have hnat :
        H * (1 + τ * (j - 1)) + j * (ell + τ * H) ≤
          H * (1 + τ' * (j - 1)) + j * (ell + τ' * H) := by gcongr
    have hrat :
        ((H * (1 + τ * (j - 1)) + j * (ell + τ * H) : ℕ) : ℚ) ≤
          (H * (1 + τ' * (j - 1)) + j * (ell + τ' * H) : ℕ) := by
      exact_mod_cast hnat
    simpa only [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hrat hs0) (c * (j : ℚ))
  have hone : ∀ {j r}, r ≤ j → c₁ j r ≤ c₁' j r := by
    intro j r hrj
    have hjoint := firstOrderCurveJointStageOne_mono_reconstruction
      (K := k) (K' := K) (ell := ell) (h := H) (j := j) (r := r)
      (τ := τ) (τ' := τ') hrj hkK hτ
    have hfiber := firstOrderCurveFiberStageOne_mono_reconstruction
      (K := k) (K' := K) (j := j) (r := r) (τ := τ) (τ' := τ') hrj hkK hτ
    unfold c₁ c₁' curveStageOne
    exact add_le_add
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hjoint) (mul_nonneg hs0 hη0))
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hfiber) (mul_nonneg hc0 ht0))
  have heμ : e ≤ μ := heM.trans hMμ
  have hsameCap : firstOrderStageCap c₀ c₁ μ e ≤ firstOrderStageCap c₀' c₁' μ e := by
    unfold firstOrderStageCap
    rw [min_eq_left heμ]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro j _
      exact hzero (j + 1)
    · apply Finset.sum_le_sum
      intro j hj
      apply hone
      omega
  have hupperCap : firstOrderStageCap c₀' c₁' μ e ≤
      firstOrderStageCap c₀' c₁' μ M := by
    apply firstOrderStageCap_mono_derivativeCap heM hMμ
    · intro j
      exact curveStageZero_le_one_of_factors K ell H (by omega) hs hη ht hc0 j τ'
    · intro j r q hrq hqj
      exact curveStageOne_mono_derivative_of_factors K ell H hs0 hη0 ht0 hc0 τ' hrq hqj
  rw [← firstOrderCurveStageCap_add_height_eq_of_factors
      n k k L A μ e ell H (hybridTau (k - 1)) (firstOrderCurveDirectRatio n k A),
    ← firstOrderCurveStageCap_add_height_eq_of_factors
      n K k L A μ M ell H (hybridTau (K - 1)) (firstOrderCurveDirectRatio n k A)]
  change (H : ℚ) + firstOrderStageCap c₀ c₁ μ e ≤
    (H : ℚ) + firstOrderStageCap c₀' c₁' μ M
  exact add_le_add_right (hsameCap.trans hupperCap) _

private theorem sum_range_succ_id (b : ℕ) :
    ∑ t ∈ Finset.range b, (t + 1) = b * (b + 1) / 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_range_id]
  simp only [Finset.sum_const_nat, Finset.card_range]
  by_cases hb : b = 0
  · simp [hb]
  apply Nat.eq_of_mul_eq_mul_right (m := 2) (by omega)
  rw [Nat.add_mul, Nat.div_mul_cancel, Nat.div_mul_cancel]
  · calc
      b * (b - 1) + b * 1 * 2 = b * ((b - 1) + 2) := by ring
      _ = b * (b + 1) := by congr 1; omega
  · exact even_iff_two_dvd.mp (Nat.even_mul_succ_self b)
  · apply even_iff_two_dvd.mp
    have hev := Nat.even_mul_succ_self (b - 1)
    have hsub : b - 1 + 1 = b := by omega
    rw [hsub, Nat.mul_comm] at hev
    exact hev

private theorem sum_upper_schedule_eq_descending
    {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R) {μ e : ℕ} (heμ : e ≤ μ) :
    (∑ t ∈ Finset.range μ,
      if μ - e ≤ t then f (t + 1) (t + 1 - (μ - e)) else 0) =
      ∑ i ∈ Finset.range e, f (μ - i) (e - i) := by
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range μ).filter (μ - e ≤ ·) = Finset.Ico (μ - e) μ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter, Finset.sum_Ico_eq_sum_range]
  have hlength : μ - (μ - e) = e := by omega
  rw [hlength, ← Finset.sum_range_reflect (fun i ↦ f (μ - i) (e - i)) e]
  apply Finset.sum_congr rfl
  intro i hi
  have hie : i < e := Finset.mem_range.mp hi
  have heSplit : e = (e - 1 - i) + (i + 1) := by omega
  have hμSplit : μ = (μ - e) + e := by omega
  have hfirst : μ - e + i + 1 = μ - (e - 1 - i) := by omega
  have hsecond : μ - (e - 1 - i) - (μ - e) = i + 1 := by omega
  have hthird : e - (e - 1 - i) = i + 1 := by omega
  rw [hfirst]
  rw [hsecond, hthird]

/-- The upper-block stage schedule is the descending actual-stage joint sum used by the hybrid
curve transfer. -/
theorem firstOrderCurveJointOne_eq_hybridCurveJ1
    {D ell H μ e : ℕ} (heμ : e ≤ μ) :
    firstOrderCurveJointOne (D + 1) μ e ell H (hybridTau D) =
      ReedSolomon.hybridCurveJ1 D ell H μ e := by
  unfold firstOrderCurveJointOne ReedSolomon.hybridCurveJ1
  rw [min_eq_left heμ]
  exact sum_upper_schedule_eq_descending
    (R := ℕ) (fun j r ↦ firstOrderCurveJointStageOne (D + 1) ell H j r (hybridTau D)) heμ

/-- The upper-block fiber schedule is the descending actual-stage fiber sum. -/
theorem firstOrderCurveFiberOne_eq_hybridB1
    {D μ e : ℕ} (heμ : e ≤ μ) :
    firstOrderCurveFiberOne (D + 1) μ e (hybridTau D) = hybridB1 D μ e := by
  unfold firstOrderCurveFiberOne hybridB1
  rw [min_eq_left heμ]
  exact sum_upper_schedule_eq_descending
    (R := ℕ) (fun j r ↦ firstOrderCurveFiberStageOne (D + 1) j r (hybridTau D)) heμ

/-- The order-zero block has the triangular fixed-fiber degree from the manuscript. -/
theorem firstOrderCurveFiberZero_eq_triangular {μ e : ℕ} (heμ : e ≤ μ) :
    firstOrderCurveFiberZero μ e = (μ - e) * (μ - e + 1) / 2 := by
  unfold firstOrderCurveFiberZero
  rw [min_eq_left heμ]
  exact sum_range_succ_id (μ - e)

/-- The order-zero block has the old full-differentiation joint degree
`ell * b(b+1)/2 + H * (b + τb²)`. -/
theorem firstOrderCurveJointZero_eq_full {K μ e ell H τ : ℕ} (heμ : e ≤ μ) :
    firstOrderCurveJointZero K μ e ell H τ =
      ell * ((μ - e) * (μ - e + 1) / 2) +
        H * ((μ - e) + τ * (μ - e) ^ 2) := by
  unfold firstOrderCurveJointZero
  rw [min_eq_left heμ]
  let b := μ - e
  change Finset.sum (Finset.range b) (fun x ↦
      H * (1 + τ * x) + (x + 1) * (ell + τ * H)) =
    ell * (b * (b + 1) / 2) + H * (b + τ * b ^ 2)
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.sum_range_succ, ih]
      have htri : (b + 1) * (b + 1 + 1) / 2 = b * (b + 1) / 2 + (b + 1) := by
        rw [← sum_range_succ_id (b + 1), Finset.sum_range_succ, sum_range_succ_id]
      rw [htri]
      ring

end ReedSolomon.HiddenDerivative

namespace ReedSolomon

open HiddenDerivative

/-- At a fixed actual derivative degree, fully differentiating the ordinary tail and adding the
regular stages is exactly the retained full-stage evaluator at the actual message dimension. -/
theorem hybridCurveFullAtDegree_eq_firstOrderCurveBound
    {n k ell A H μ e L : ℕ}
    (hk : 1 ≤ k) (heμ : e ≤ μ) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    hybridCurveFullTail n (k - 1) ell (μ - e) H A L +
        hybridCurveRegular n (k - 1) ell A H μ e L =
      ((firstOrderCurveBound n k k L A μ e ell H (hybridTau (k - 1))
        (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) := by
  have hkpred : k - 1 + 1 = k := by omega
  have hnD : n - (k - 1) = n - k + 1 := by omega
  have hAD : A - (k - 1) = A - k + 1 := by omega
  have hLD : L - (k - 1) = L - k + 1 := by omega
  have hJ := firstOrderCurveJointOne_eq_hybridCurveJ1
    (D := k - 1) (ell := ell) (H := H) heμ
  have hF := firstOrderCurveFiberOne_eq_hybridB1 (D := k - 1) heμ
  rw [hkpred] at hJ hF
  unfold firstOrderCurveBound
  dsimp only
  rw [hJ, hF,
    firstOrderCurveFiberZero_eq_triangular heμ,
    firstOrderCurveJointZero_eq_full (ell := ell) (H := H)
      (τ := hybridTau (k - 1)) heμ]
  unfold hybridCurveFullTail hybridCurveRegular
  simp only [firstOrderCurveDirectRatio,
    hybridLambdaOne, hybridLambdaTwo, hybridTheta,
    hybridTau, hnD, hAD, hLD]
  push_cast
  ring

end ReedSolomon

namespace ReedSolomon

open HiddenDerivative

/-- The manuscript's former full-differentiation envelope, expressed through the retained
`firstOrderCurveBound` evaluator at ambient reconstruction dimension `K`. -/
def hybridCurveFullDifferentiationEnvelope
    (n k K ell A H μ M L : ℕ) : ℝ :=
  ((firstOrderCurveBound n K k L A μ M ell H (2 * K - 3)
    (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ)

/-- For every actual derivative degree and every retained threshold, the optimized-tail hybrid
charge is no larger than the old full-differentiation envelope. -/
theorem hybridCurveAtDegree_le_fullDifferentiationEnvelope
    {n k K ell A H μ M e L : ℕ}
    (hk : 2 ≤ k) (hkK : k ≤ K) (_hKn : K ≤ n)
    (heM : e ≤ M) (hMμ : M ≤ μ)
    (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    hybridCurveAtDegree n (k - 1) ell A H μ e ≤
      hybridCurveFullDifferentiationEnvelope n k K ell A H μ M L := by
  have hDL : k - 1 < L := by omega
  have htail := hybridCurveTail_le_fullTail
    (n := n) (D := k - 1) (ell := ell) (b := μ - e) (H := H) (A := A) (L := L)
    (by omega) hLA hAn
  have hpair := hybridCurveAtDegree_le_pair
    (n := n) (D := k - 1) (ell := ell) (A := A) (H := H) (B := μ)
    (e := e) (L := L) (L₀ := L) hDL hLA hDL hLA
  have hlower := firstOrderCurveBound_mono_ambient
    (n := n) (k := k) (K := K) (L := L) (A := A) (μ := μ) (e := e) (M := M)
    (ell := ell) (H := H) hk hkK heM hMμ hkL hLA hAn
  have hlowerR :
      ((firstOrderCurveBound n k k L A μ e ell H (hybridTau (k - 1))
        (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) ≤
      ((firstOrderCurveBound n K k L A μ M ell H (hybridTau (K - 1))
        (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) := by
    exact_mod_cast hlower
  have hτK : hybridTau (K - 1) = 2 * K - 3 := by
    unfold hybridTau
    omega
  calc
    hybridCurveAtDegree n (k - 1) ell A H μ e ≤
        hybridCurveTail n (k - 1) ell (μ - e) H A L +
          hybridCurveRegular n (k - 1) ell A H μ e L := hpair
    _ ≤ hybridCurveFullTail n (k - 1) ell (μ - e) H A L +
          hybridCurveRegular n (k - 1) ell A H μ e L := by
        simpa only [add_comm] using
          add_le_add_right htail (hybridCurveRegular n (k - 1) ell A H μ e L)
    _ = ((firstOrderCurveBound n k k L A μ e ell H (hybridTau (k - 1))
          (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) :=
        hybridCurveFullAtDegree_eq_firstOrderCurveBound
          (by omega) (heM.trans hMμ) hkL hLA hAn
    _ ≤ ((firstOrderCurveBound n K k L A μ M ell H (hybridTau (K - 1))
          (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) := hlowerR
    _ = hybridCurveFullDifferentiationEnvelope n k K ell A H μ M L := by
      rw [hτK]
      rfl

/-- Maximizing over all permitted actual derivative degrees preserves the pointwise comparison
with every admissible full-differentiation threshold. -/
theorem hybridCurveOptimized_le_fullDifferentiationEnvelope
    {n k K ell A H μ M L : ℕ}
    (hk : 2 ≤ k) (hkK : k ≤ K) (hKn : K ≤ n)
    (hMμ : M ≤ μ) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    hybridCurveOptimized n (k - 1) ell A H μ M ≤
      hybridCurveFullDifferentiationEnvelope n k K ell A H μ M L := by
  classical
  unfold hybridCurveOptimized
  apply Finset.max'_le
  intro x hx
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  exact hybridCurveAtDegree_le_fullDifferentiationEnvelope hk hkK hKn
    (by have := Finset.mem_range.mp he; omega) hMμ hkL hLA hAn

/-- Direct compatibility form for consumers of the retained `firstOrderCurveBound` evaluator. -/
theorem hybridCurveOptimized_le_firstOrderCurveBound
    {n k K ell A H μ M L : ℕ}
    (hk : 2 ≤ k) (hkK : k ≤ K) (hKn : K ≤ n)
    (hMμ : M ≤ μ) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) :
    hybridCurveOptimized n (k - 1) ell A H μ M ≤
      ((firstOrderCurveBound n K k L A μ M ell H (2 * K - 3)
        (firstOrderCurveDirectRatio n k A) : ℚ) : ℝ) := by
  simpa only [hybridCurveFullDifferentiationEnvelope] using
    hybridCurveOptimized_le_fullDifferentiationEnvelope
      hk hkK hKn hMμ hkL hLA hAn

/-- The paper's max-then-min consequence: optimize the hybrid bound at each actual degree,
then compare with the best retained threshold in the old full-differentiation envelope. -/
theorem hybridCurveOptimized_le_min_fullDifferentiationEnvelope
    {n k K ell A H μ M : ℕ}
    (hk : 2 ≤ k) (hkK : k ≤ K) (hKn : K ≤ n)
    (hMμ : M ≤ μ) (hkA : k ≤ A) (hAn : A ≤ n) :
    hybridCurveOptimized n (k - 1) ell A H μ M ≤
      curveRetentionMinimum (k - 1) A
        (hybridCurveFullDifferentiationEnvelope n k K ell A H μ M) := by
  obtain ⟨L, hDL, hLA, hL⟩ := exists_curveRetentionMinimum
    (D := k - 1) (A := A)
    (hybridCurveFullDifferentiationEnvelope n k K ell A H μ M) (by omega)
  rw [← hL]
  exact hybridCurveOptimized_le_fullDifferentiationEnvelope
    hk hkK hKn hMμ (by omega) hLA hAn

end ReedSolomon

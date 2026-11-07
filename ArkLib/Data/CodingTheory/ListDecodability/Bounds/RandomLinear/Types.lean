/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.ProductLaw
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Row orbits and the bad matrix

Row-permutation orbits have multinomial size. Their size is bounded below by the entropy of the
row distribution. The bad distribution is rounded to row counts that sum to `n`. This gives the
bad matrix `M₀`. [GLMRSW22], Section 2, sketches this rounding in a remark.

## Main statements

* `CodingTheory.RandomLinearInternal.rowOrbit_ncard_mul`: `|rowOrbit N| · ∏_b c_b! = n!`.
* `CodingTheory.RandomLinearInternal.factorial_mul_lower`: the entropy lower bound for multinomials.
* `CodingTheory.RandomLinearInternal.exists_badMatrix`: the columns of `M₀` are independent and lie
  in one Hamming ball of radius `⌊δ n⌋`. Every full-rank image `A M₀` has a large row orbit.

## References

The key [GLMRSW22] is resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal


variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Orbit–stabilizer for row permutations: `|orbit N| · ∏_b c_b! = n!`. -/
theorem rowOrbit_ncard_mul {β : Type} [Fintype β] [DecidableEq β] (N : ι → β) :
    (rowOrbit N).ncard * ∏ b, (Fintype.card {j // N j = b}).factorial =
      (Fintype.card ι).factorial := by
  classical
  set φ : Equiv.Perm ι → (ι → β) := fun σ => N ∘ σ with hφ
  have h1 : (rowOrbit N).ncard = (Finset.univ.image φ).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [rowOrbit, φ]
  have h2 : ∀ x ∈ Finset.univ.image φ, (Finset.univ.filter (fun σ => φ σ = x)).card =
      ∏ b, (Fintype.card {j // N j = b}).factorial := by
    intro x hx
    obtain ⟨σ₀, -, rfl⟩ := Finset.mem_image.1 hx
    rw [← DomMulAct.stabilizer_card N, Fintype.card_subtype]
    refine Finset.card_bij (fun σ _ => σ * σ₀⁻¹) ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ] at hσ ⊢
      funext i
      have := congrFun hσ (σ₀⁻¹ i)
      simpa using this
    · intro a _ b _ h
      simpa using h
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨g * σ₀, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ]
      funext i
      have := congrFun hg (σ₀ i)
      simpa using this
  have h3 := Finset.card_eq_sum_card_image φ Finset.univ
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at h3
  rw [h1, ← Fintype.card_perm, ← Finset.card_univ, h3]

private theorem factorial_le_exp_mul_pow_div (c n : ℕ) (hc : c ≤ n) :
    (c.factorial : ℝ) ≤ Real.exp 1 * (n + 1) * (((c : ℝ) ^ c) / Real.exp 1 ^ c) := by
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, pow_zero, div_one, mul_one]
    nlinarith
  · have hs : Stirling.stirlingSeq c ≤ Stirling.stirlingSeq 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      exact Stirling.stirlingSeq'_antitone (Nat.zero_le k)
    rw [Stirling.stirlingSeq_one] at hs
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc0
    have hcn : (c : ℝ) ≤ n := by exact_mod_cast hc
    have hsq : √(2 * (c : ℝ)) = √2 * √c := by
      rw [Real.sqrt_mul (by norm_num)]
    have hpos : 0 < √(2 * (c : ℝ)) * ((c : ℝ) / Real.exp 1) ^ c := by positivity
    have h1 : (c.factorial : ℝ) = Stirling.stirlingSeq c * (√(2 * (c : ℝ)) *
        ((c : ℝ) / Real.exp 1) ^ c) := by
      unfold Stirling.stirlingSeq
      field_simp
    have h2 : (c.factorial : ℝ) ≤ Real.exp 1 / √2 * (√(2 * (c : ℝ)) *
        ((c : ℝ) / Real.exp 1) ^ c) := by
      rw [h1]; exact mul_le_mul_of_nonneg_right hs hpos.le
    have h3 : Real.exp 1 / √2 * (√(2 * (c : ℝ)) * ((c : ℝ) / Real.exp 1) ^ c) =
        Real.exp 1 * √c * (((c : ℝ) / Real.exp 1) ^ c) := by
      rw [hsq]
      have : (0 : ℝ) < √2 := by positivity
      field_simp
    have h4 : √(c : ℝ) ≤ n + 1 := by
      have : √(c : ℝ) ≤ c := by
        calc √(c : ℝ) ≤ √((c : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = c := Real.sqrt_sq (by linarith)
      linarith
    rw [div_pow] at h2 h3
    calc (c.factorial : ℝ) ≤ _ := h2.trans_eq h3
      _ ≤ Real.exp 1 * (n + 1) * ((c : ℝ) ^ c / Real.exp 1 ^ c) := by
        have : 0 ≤ (c : ℝ) ^ c / Real.exp 1 ^ c := by positivity
        have := mul_le_mul_of_nonneg_right h4 this
        nlinarith [Real.exp_pos 1]

/-- Entropy lower bound for multinomial coefficients. -/
theorem factorial_mul_lower (q : ℕ) (hq : 1 < q) {β : Type} [Fintype β] (c : β → ℕ) (n : ℕ)
    (hc : ∑ b, c b = n) :
    (q : ℝ) ^ ((n : ℝ) * ((∑ b, Real.negMulLog ((c b : ℝ) / n)) / Real.log q)) ≤
      (Real.exp 1 * (n + 1)) ^ Fintype.card β *
        ((n.factorial : ℝ) / ∏ b, ((c b).factorial : ℝ)) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hcn : ∀ b, c b ≤ n := fun b => hc ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ b)
  have hcR : ∑ b, (c b : ℝ) = n := by exact_mod_cast hc
  have hPc : 0 < ∏ b, ((c b : ℝ) ^ c b) := Finset.prod_pos fun b _ => by
    rcases Nat.eq_zero_or_pos (c b) with h | h
    · simp [h]
    · have : (0 : ℝ) < c b := by exact_mod_cast h
      positivity
  have hPf : 0 < ∏ b, ((c b).factorial : ℝ) := Finset.prod_pos fun b _ => by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ b, c b = 0 := fun b => Nat.le_zero.1 (hcn b)
    simp only [Nat.cast_zero, zero_mul, Real.rpow_zero, h0, Nat.factorial_zero, Nat.cast_one,
      Finset.prod_const_one, div_one, mul_one, zero_add]
    exact one_le_pow₀ (by linarith)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnS : (n : ℝ) * ∑ b, Real.negMulLog ((c b : ℝ) / n) =
      n * Real.log n - ∑ b, (c b : ℝ) * Real.log (c b) := by
    rw [Finset.mul_sum]
    have : ∀ b, (n : ℝ) * Real.negMulLog ((c b : ℝ) / n) =
        (c b : ℝ) * Real.log n - (c b : ℝ) * Real.log (c b) := by
      intro b
      unfold Real.negMulLog
      rcases Nat.eq_zero_or_pos (c b) with h | h
      · simp [h]
      · have : (0 : ℝ) < c b := by exact_mod_cast h
        rw [Real.log_div this.ne' hnR.ne']
        field_simp
        ring
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, ← Finset.sum_mul, hcR]
  have hL : (q : ℝ) ^ ((n : ℝ) * ((∑ b, Real.negMulLog ((c b : ℝ) / n)) / Real.log q)) =
      (n : ℝ) ^ n / ∏ b, ((c b : ℝ) ^ c b) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    have : Real.log q * ((n : ℝ) * ((∑ b, Real.negMulLog ((c b : ℝ) / n)) / Real.log q)) =
        n * Real.log n - ∑ b, (c b : ℝ) * Real.log (c b) := by
      rw [← hnS]; field_simp
    rw [this, Real.exp_sub, Real.exp_sum]
    congr 1
    · rw [Real.exp_nat_mul, Real.exp_log hnR]
    · refine Finset.prod_congr rfl fun b _ => ?_
      rcases Nat.eq_zero_or_pos (c b) with h | h
      · simp [h]
      · have : (0 : ℝ) < c b := by exact_mod_cast h
        rw [Real.exp_nat_mul, Real.exp_log this]
  have hprod : ∏ b, ((c b).factorial : ℝ) ≤
      (Real.exp 1 * (n + 1)) ^ Fintype.card β * (∏ b, ((c b : ℝ) ^ c b)) / Real.exp 1 ^ n := by
    calc ∏ b, ((c b).factorial : ℝ)
        ≤ ∏ b, (Real.exp 1 * (n + 1) * (((c b : ℝ) ^ c b) / Real.exp 1 ^ c b)) :=
          Finset.prod_le_prod₀ (fun b _ => Nat.cast_nonneg _)
            (fun b _ => factorial_le_exp_mul_pow_div (c b) n (hcn b))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hc]
        ring
  have hnf : (n : ℝ) ^ n / Real.exp 1 ^ n ≤ n.factorial := by
    have h1 := Stirling.le_factorial_stirling n
    have h2 : (1 : ℝ) ≤ √(2 * Real.pi * n) := by
      rw [Real.one_le_sqrt]
      have := Real.two_le_pi
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    rw [← div_pow]
    calc ((n : ℝ) / Real.exp 1) ^ n ≤ √(2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n :=
          le_mul_of_one_le_left (by positivity) h2
      _ ≤ _ := h1
  rw [hL, div_le_iff₀ hPc]
  have hA : 0 < (Real.exp 1 * (n + 1)) ^ Fintype.card β := by positivity
  have he' : 0 < Real.exp 1 ^ n := by positivity
  have a := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ n)
  have b : ((Real.exp 1 * (n + 1)) ^ Fintype.card β * (∏ b, ((c b : ℝ) ^ c b)) / Real.exp 1 ^ n) *
      (n : ℝ) ^ n = (Real.exp 1 * (n + 1)) ^ Fintype.card β * (∏ b, ((c b : ℝ) ^ c b)) *
        ((n : ℝ) ^ n / Real.exp 1 ^ n) := by ring
  have d := mul_le_mul_of_nonneg_left hnf (mul_pos hA hPc).le
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hPf]
  nlinarith [a, b, d]

/-- Rounding a probability weight to counts summing to `n`. -/
theorem exists_rounding {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (hμ : IsProb μ)
    (ω₀ : Ω) (n : ℕ) (hn : 0 < n) :
    ∃ N : Ω → ℕ, ∑ ω, N ω = n ∧ (∀ ω ≠ ω₀, N ω = ⌊n * μ ω⌋₊) ∧
      ∀ ω, |(N ω : ℝ) / n - μ ω| ≤ Fintype.card Ω / n := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set T := Finset.univ.erase ω₀ with hT
  set S := ∑ ω ∈ T, ⌊(n : ℝ) * μ ω⌋₊ with hS
  have hfl : ∀ ω, ((⌊(n : ℝ) * μ ω⌋₊ : ℕ) : ℝ) ≤ n * μ ω := fun ω =>
    Nat.floor_le (mul_nonneg hn'.le (hμ.1 ω))
  have hlt : ∀ ω, (n : ℝ) * μ ω < ((⌊(n : ℝ) * μ ω⌋₊ : ℕ) : ℝ) + 1 := fun ω =>
    Nat.lt_floor_add_one _
  have hsumT : ∑ ω ∈ T, μ ω = 1 - μ ω₀ := by
    rw [← hμ.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ ω₀)]; ring
  have hSR : (S : ℝ) ≤ n * ∑ ω ∈ T, μ ω := by
    rw [hS, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => hfl ω
  have hSn : S ≤ n := by
    have : (S : ℝ) ≤ n := by
      rw [hsumT] at hSR
      nlinarith [hμ.1 ω₀]
    exact_mod_cast this
  have hdiff : (n : ℝ) * ∑ ω ∈ T, μ ω - S ≤ T.card := by
    rw [hS, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ ω ∈ T, (1 : ℝ) := Finset.sum_le_sum fun ω _ => by linarith [hlt ω]
      _ = T.card := by simp
  have hTc : (T.card : ℝ) ≤ Fintype.card Ω := by
    exact_mod_cast Finset.card_le_univ T
  have hone : (1 : ℝ) ≤ Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨ω₀⟩
  refine ⟨fun ω => if ω = ω₀ then n - S else ⌊(n : ℝ) * μ ω⌋₊, ?_, ?_, ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ω₀)]
    simp only [↓reduceIte]
    have : ∑ x ∈ T, (if x = ω₀ then n - S else ⌊(n : ℝ) * μ x⌋₊) = S := by
      rw [hS]
      exact Finset.sum_congr rfl fun x hx => by
        simp [Finset.ne_of_mem_erase hx]
    rw [this]; omega
  · intro ω hω; simp [hω]
  · intro ω
    by_cases h : ω = ω₀
    · subst h
      simp only [ite_true]
      rw [Nat.cast_sub hSn, abs_le]
      have h1 : ((n : ℝ) - S) / n - μ ω = (n * ∑ ω ∈ T, μ ω - S) / n := by
        rw [hsumT]; field_simp; ring
      rw [h1]
      constructor
      · have : 0 ≤ (n : ℝ) * ∑ ω ∈ T, μ ω - S := by linarith
        have := div_nonneg this hn'.le
        have : (0 : ℝ) ≤ Fintype.card Ω / n := by positivity
        linarith
      · exact div_le_div_of_nonneg_right (hdiff.trans hTc) hn'.le
    · simp only [h, ite_false]
      rw [abs_le]
      have h1 : ((⌊(n : ℝ) * μ ω⌋₊ : ℕ) : ℝ) / n - μ ω ≤ 0 := by
        rw [sub_nonpos, div_le_iff₀ hn']; linarith [hfl ω]
      have h2 : -(1 / (n : ℝ)) ≤ ((⌊(n : ℝ) * μ ω⌋₊ : ℕ) : ℝ) / n - μ ω := by
        have : -1 ≤ ((⌊(n : ℝ) * μ ω⌋₊ : ℕ) : ℝ) - n * μ ω := by linarith [hlt ω]
        have := div_le_div_of_nonneg_right this hn'.le
        calc -(1 / (n : ℝ)) = -1 / n := by ring
          _ ≤ _ := by
            refine this.trans (le_of_eq ?_)
            field_simp
      have h3 : 1 / (n : ℝ) ≤ Fintype.card Ω / n :=
        div_le_div_of_nonneg_right hone hn'.le
      have : (0 : ℝ) ≤ Fintype.card Ω / n := by positivity
      constructor <;> linarith

omit [DecidableEq ι] in
/-- Any count vector summing to `|ι|` is the fibre-count vector of some `g : ι → Ω`. -/
theorem exists_fun_fiber_card {Ω : Type} [Fintype Ω] [DecidableEq Ω] (N : Ω → ℕ)
    (h : ∑ ω, N ω = Fintype.card ι) :
    ∃ g : ι → Ω, ∀ ω, Fintype.card {j // g j = ω} = N ω := by
  have hc : Fintype.card ι = Fintype.card (Σ ω, Fin (N ω)) := by
    simp [Fintype.card_sigma, h]
  let e : ι ≃ Σ ω, Fin (N ω) := Fintype.equivOfCardEq hc
  refine ⟨fun j => (e j).1, fun ω => ?_⟩
  have e2 : {j // (e j).1 = ω} ≃ {s : Σ ω, Fin (N ω) // s.1 = ω} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  rw [Fintype.card_congr (e2.trans (Equiv.sigmaSubtype ω))]
  simp

/-- Uniform continuity of entropy of push-forwards, with a modulus independent of the spaces. -/
theorem entQ_pushforward_close (η : ℝ) (hη : 0 < η) :
    ∃ θ > 0, ∀ {Ω β : Type} [Fintype Ω] [Fintype β] [DecidableEq β] (μ ν : Ω → ℝ),
      IsProb μ → IsProb ν → ∀ f : Ω → β, (∀ ω, |μ ω - ν ω| ≤ θ / Fintype.card Ω) →
        |∑ b, Real.negMulLog (law μ f b) - ∑ b, Real.negMulLog (law ν f b)| ≤
          Fintype.card β * η := by
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous
    Real.continuous_negMulLog.continuousOn
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  refine ⟨d / 2, by positivity, fun {Ω β} _ _ _ μ ν hμ hν f hclose => ?_⟩
  classical
  have hΩ : 0 < Fintype.card Ω := by
    rw [Fintype.card_pos_iff]
    by_contra h
    rw [not_nonempty_iff] at h
    have := hμ.2
    simp at this
  have hΩR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hΩ
  have hmem : ∀ (ρ : Ω → ℝ), IsProb ρ → ∀ b, law ρ f b ∈ Set.Icc (0 : ℝ) 1 := by
    intro ρ hρ b
    refine ⟨Finset.sum_nonneg fun ω _ => hρ.1 ω, ?_⟩
    rw [← hρ.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun ω _ _ => hρ.1 ω
  have hlaw : ∀ b, |law μ f b - law ν f b| ≤ d / 2 := by
    intro b
    unfold law
    rw [← Finset.sum_sub_distrib]
    calc |∑ ω ∈ Finset.univ.filter (fun ω => f ω = b), (μ ω - ν ω)|
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω => f ω = b), |μ ω - ν ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => f ω = b), (d / 2) / Fintype.card Ω :=
          Finset.sum_le_sum fun ω _ => hclose ω
      _ ≤ ∑ ω : Ω, (d / 2) / Fintype.card Ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => by positivity
      _ = d / 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
  rw [← Finset.sum_sub_distrib]
  calc |∑ b, (Real.negMulLog (law μ f b) - Real.negMulLog (law ν f b))|
      ≤ ∑ b, |Real.negMulLog (law μ f b) - Real.negMulLog (law ν f b)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : β, η := Finset.sum_le_sum fun b _ => by
        have := hdist _ (hmem μ hμ b) _ (hmem ν hν b)
          (by rw [Real.dist_eq]; linarith [hlaw b])
        rw [Real.dist_eq] at this
        exact this.le
    _ = Fintype.card β * η := by simp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private theorem one_sub_inv_mem_Ioo {q : ℕ} (hq : 2 ≤ q) :
    0 < 1 - 1 / (q : ℝ) ∧ 1 - 1 / (q : ℝ) < 1 := by
  have : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h : 0 < 1 / (q : ℝ) := by positivity
  have h2 : 1 / (q : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
  constructor <;> linarith

private theorem isProb_badLaw_factor {q : ℕ} (hq : 2 ≤ q) (hF : Fintype.card F = q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 - 1 / q) (L : ℕ) (o : Option (Fin L)) :
    IsProb (ber q (o.elim (1 - 1 / (q : ℝ)) (fun _ => p)) : F → ℝ) := by
  have := one_sub_inv_mem_Ioo hq
  cases o with
  | none => exact isProb_ber hq hF this.1.le this.2.le
  | some i => exact isProb_ber (t := p) hq hF hp0 (by linarith)

/-- The bad distribution is a probability weight. -/
theorem isProb_badLaw {q : ℕ} (hq : 2 ≤ q) (hF : Fintype.card F = q) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1 - 1 / q) (L : ℕ) : IsProb (badLaw q p L F) :=
  isProb_prodLaw _ (isProb_badLaw_factor hq hF hp0 hp1 L)

/-- Each `u`-coordinate of the bad distribution is nonzero with probability `p`. -/
theorem sum_badLaw_coord_ne_zero {q : ℕ} (hq : 2 ≤ q) (hF : Fintype.card F = q) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 - 1 / q) {L : ℕ} (i : Fin L) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Option (Fin L) → F => ω (some i) ≠ 0),
      badLaw q p L F ω = p := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have key := law_coord _ (isProb_badLaw_factor hq hF hp0 hp1 L) (some i)
  have h1 : ∑ ω ∈ Finset.univ.filter (fun ω : Option (Fin L) → F => ω (some i) ≠ 0),
      badLaw q p L F ω = ∑ a ∈ Finset.univ.filter (fun a : F => a ≠ 0),
        law (badLaw q p L F) (fun ω => ω (some i)) a := by
    unfold law
    exact (Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
      (fun ω : Option (Fin L) → F => ω (some i) ≠ 0)) (t := Finset.univ.filter (fun a : F => a ≠ 0))
      (g := fun ω => ω (some i)) (f := badLaw q p L F) (fun ω hω => by simpa using hω)).symm.trans
        (Finset.sum_congr rfl fun a ha => by
          congr 1; ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨by simpa [h] using (Finset.mem_filter.1 ha).2, h⟩)
  rw [h1]
  have h2 : ∀ a ∈ Finset.univ.filter (fun a : F => a ≠ 0),
      law (badLaw q p L F) (fun ω => ω (some i)) a = p / ((q : ℝ) - 1) := by
    intro a ha
    have := key a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    unfold badLaw
    simpa [ber, ha] using this
  rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.filter_ne' , Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, hF, nsmul_eq_mul, Nat.cast_sub (by omega)]
  push_cast
  field_simp

private theorem exists_le_badLaw (q : ℕ) (hq : 2 ≤ q) {δ : ℝ} (h0 : 0 < δ)
    (h1 : δ < 1 - 1 / q) (L : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (G : Type) [Field G] [DecidableEq G] (ω : Option (Fin L) → G), c₀ ≤ badLaw q δ L G ω := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hinv := one_sub_inv_mem_Ioo hq
  have hlow : ∀ t : ℝ, 0 < t → t < 1 → 0 < min (1 - t) (t / ((q : ℝ) - 1)) := fun t ht0 ht1 =>
    lt_min (by linarith) (by positivity)
  have hber : ∀ (G : Type) [Field G] [DecidableEq G] (t : ℝ) (a : G),
      min (1 - t) (t / ((q : ℝ) - 1)) ≤ ber q t a := by
    intro G _ _ t a
    unfold ber
    split_ifs
    exacts [min_le_left _ _, min_le_right _ _]
  have hm : 0 < min (min (1 - δ) (δ / ((q : ℝ) - 1)))
      (min (1 - (1 - 1 / (q : ℝ))) ((1 - 1 / (q : ℝ)) / ((q : ℝ) - 1))) :=
    lt_min (hlow δ h0 (by linarith)) (hlow _ hinv.1 hinv.2)
  refine ⟨_, pow_pos hm (L + 1), fun G _ _ ω => ?_⟩
  unfold badLaw prodLaw
  calc _ = ∏ _o : Option (Fin L), min (min (1 - δ) (δ / ((q : ℝ) - 1)))
        (min (1 - (1 - 1 / (q : ℝ))) ((1 - 1 / (q : ℝ)) / ((q : ℝ) - 1))) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hm.le) fun o _ => by
      cases o with
      | none => exact (min_le_right _ _).trans (hber G _ _)
      | some i => exact (min_le_left _ _).trans (hber G δ _)

omit [DecidableEq ι] in
private theorem card_filter_mem_eq_sum_card {Ω : Type} [DecidableEq Ω] (g : ι → Ω)
    (S : Finset Ω) :
    (Finset.univ.filter fun j => g j ∈ S).card = ∑ ω ∈ S, Fintype.card {j // g j = ω} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ.filter fun j => g j ∈ S) (t := S)
    (fun j hj => by simpa using hj)]
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [Fintype.card_subtype]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hω, h⟩⟩

omit [DecidableEq ι] in
private theorem rpow_entQ_le_rowOrbit_ncard (q : ℕ) (hq : 1 < q) {Ω β : Type} [Fintype Ω]
    [DecidableEq Ω] [Fintype β] [DecidableEq β] (N : Ω → ℕ) (g : ι → Ω)
    (hg : ∀ ω, Fintype.card {j // g j = ω} = N ω) (φ : Ω → β) :
    (q : ℝ) ^ ((Fintype.card ι : ℝ) *
        entQ q (fun ω => (N ω : ℝ) / Fintype.card ι) φ) ≤
      (Real.exp 1 * (Fintype.card ι + 1)) ^ Fintype.card β *
        (rowOrbit (φ ∘ g)).ncard := by
  classical
  set n := Fintype.card ι with hn_def
  set c : β → ℕ := fun b => Fintype.card {j // φ (g j) = b} with hc_def
  have hc : ∑ b, c b = n := by
    simp only [c]
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv (φ ∘ g))
  have hcb : ∀ b, c b = ∑ ω ∈ Finset.univ.filter (fun ω => φ ω = b), N ω := by
    intro b
    have := card_filter_mem_eq_sum_card g (Finset.univ.filter fun ω => φ ω = b)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    simp only [c]
    rw [Fintype.card_subtype, this]
    exact Finset.sum_congr rfl fun ω _ => hg ω
  have hlaw : ∀ b, law (fun ω => (N ω : ℝ) / n) φ b = (c b : ℝ) / n := by
    intro b
    unfold law
    rw [← Finset.sum_div, hcb b]
    push_cast
    rfl
  have hent : entQ q (fun ω => (N ω : ℝ) / n) φ = (∑ b, Real.negMulLog ((c b : ℝ) / n)) /
      Real.log q := by
    unfold entQ
    simp only [hlaw]
  rw [hent]
  refine (factorial_mul_lower q hq c n hc).trans (le_of_eq ?_)
  congr 1
  have h1 := rowOrbit_ncard_mul (φ ∘ g)
  have h2 : (n.factorial : ℝ) = (rowOrbit (φ ∘ g)).ncard * ∏ b, ((c b).factorial : ℝ) := by
    rw [hn_def, ← h1]
    push_cast
    rfl
  have hpos : 0 < ∏ b, ((c b).factorial : ℝ) := Finset.prod_pos fun b _ => by positivity
  rw [h2, mul_div_assoc, div_self hpos.ne', mul_one]

/-- The bad matrix `M₀`: its `L` columns are linearly independent and lie in one Hamming ball of
radius `⌊δ n⌋`. Every full-rank image `A M₀` has a large row orbit. -/
theorem exists_badMatrix (q : ℕ) (hq : 2 ≤ q) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 - 1 / q)
    (L : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ n₁ : ℕ, ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F], Fintype.card F = q →
      n₁ ≤ Fintype.card ι → ∃ M₀ : ι → Fin L → F,
        (∃ z : ι → F, ∀ i, hammingDist (cols M₀ i) z ≤ ⌊δ * Fintype.card ι⌋₊) ∧
        LinearIndependent F (cols M₀) ∧
        ∀ s : ℕ, 1 ≤ s → ∀ A : Matrix (Fin s) (Fin L) F, LinearIndependent F A →
          (q : ℝ) ^ ((Fintype.card ι : ℝ) *
              (entQ q (badLaw q δ L F) (fun ω => A.mulVec (badRow ω)) - η)) ≤
            (Real.exp 1 * (Fintype.card ι + 1)) ^ (q ^ L) *
              (rowOrbit (fun j => A.mulVec (M₀ j))).ncard := by
  classical
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hqL : (0 : ℝ) < (q : ℝ) ^ L := by positivity
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_le_badLaw q hq hδ0 hδ1 L
  obtain ⟨θ, hθ, hclose⟩ := entQ_pushforward_close (η * Real.log q / (q : ℝ) ^ L) (by positivity)
  refine ⟨max 1 (max ⌈1 / c₀⌉₊ ⌈((q : ℝ) ^ (L + 1)) ^ 2 / θ⌉₊), ?_⟩
  intro ι _ _ _ F _ _ _ hF hn
  have hn1 : 1 ≤ Fintype.card ι := le_trans (le_max_left _ _) hn
  have hn2 : 1 / c₀ ≤ Fintype.card ι := by
    have h : ⌈1 / c₀⌉₊ ≤ Fintype.card ι :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h)
  have hn3 : ((q : ℝ) ^ (L + 1)) ^ 2 / θ ≤ Fintype.card ι := by
    have h : ⌈((q : ℝ) ^ (L + 1)) ^ 2 / θ⌉₊ ≤ Fintype.card ι :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h)
  set n := Fintype.card ι with hn_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hμ : IsProb (badLaw q δ L F) := isProb_badLaw hq hF hδ0.le hδ1.le L
  have hcardΩ : (Fintype.card (Option (Fin L) → F) : ℝ) = (q : ℝ) ^ (L + 1) := by
    rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, hF]
    push_cast; rfl
  obtain ⟨N, hNsum, hNeq, hNerr⟩ := exists_rounding (badLaw q δ L F) hμ 0 n hn1
  obtain ⟨g, hg⟩ := exists_fun_fiber_card (ι := ι) N hNsum
  have hNle : ∀ ω, ω ≠ 0 → (N ω : ℝ) ≤ n * badLaw q δ L F ω := fun ω hω => by
    rw [hNeq ω hω]; exact Nat.floor_le (mul_nonneg hnR.le (hμ.1 ω))
  refine ⟨fun j => badRow (g j), ⟨fun j => g j none, fun i => ?_⟩, ?_, ?_⟩
  · set S := Finset.univ.filter (fun ω : Option (Fin L) → F => ω (some i) ≠ 0) with hS
    have h1 : hammingDist (cols (fun j => badRow (g j)) i) (fun j => g j none) =
        (Finset.univ.filter fun j => g j ∈ S).card := by
      unfold hammingDist
      congr 1
      ext j
      simp [cols, badRow, hS]
    rw [h1, card_filter_mem_eq_sum_card]
    apply Nat.le_floor
    push_cast
    calc ∑ ω ∈ S, ((Fintype.card {j // g j = ω} : ℕ) : ℝ)
        ≤ ∑ ω ∈ S, (n : ℝ) * badLaw q δ L F ω := Finset.sum_le_sum fun ω hω => by
          rw [hg ω]
          exact hNle ω (fun h => by simp [hS, h] at hω)
      _ = δ * n := by
          rw [← Finset.mul_sum, sum_badLaw_coord_ne_zero hq hF hδ0.le hδ1.le i]; ring
  · have hω : ∀ i : Fin L, ∃ j, g j = Pi.single (some i) (1 : F) := by
      intro i
      have hne : (Pi.single (some i) (1 : F) : Option (Fin L) → F) ≠ 0 := fun h => by
        have := congrFun h (some i)
        simp at this
      have : 1 ≤ N (Pi.single (some i) (1 : F)) := by
        rw [hNeq _ hne]
        apply Nat.le_floor
        push_cast
        have := mul_le_mul_of_nonneg_left (hc₀le F (Pi.single (some i) (1 : F))) hnR.le
        have h2 : 1 ≤ (n : ℝ) * c₀ := by
          rw [div_le_iff₀ hc₀] at hn2; linarith
        linarith
      have h3 := hg (Pi.single (some i) (1 : F))
      have : 0 < Fintype.card {j // g j = Pi.single (some i) (1 : F)} := by omega
      obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.1 this
      exact ⟨j, hj⟩
    choose j hj using hω
    rw [linearIndependent_iff']
    intro s a hs i hi
    have := congrFun hs (j i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, hj, badRow] at this
    simpa [Pi.single_apply, hi] using this
  · intro s hs A hA
    have hsL : s ≤ L := by
      have := hA.fintype_card_le_finrank
      simpa using this
    have hlow := rpow_entQ_le_rowOrbit_ncard (ι := ι) q (by omega) N g hg
      (fun ω => A.mulVec (badRow ω))
    have hν : IsProb (fun ω => (N ω : ℝ) / n) := by
      refine ⟨fun ω => by positivity, ?_⟩
      have : ∑ ω, (N ω : ℝ) = n := by exact_mod_cast hNsum
      rw [← Finset.sum_div, this, div_self hnR.ne']
    have hKpos : (0 : ℝ) < (q : ℝ) ^ (L + 1) := by positivity
    have hcl : ∀ ω, |badLaw q δ L F ω - (N ω : ℝ) / n| ≤
        θ / Fintype.card (Option (Fin L) → F) := by
      intro ω
      rw [abs_sub_comm]
      refine (hNerr ω).trans ?_
      rw [hcardΩ, div_le_div_iff₀ hnR hKpos]
      have : ((q : ℝ) ^ (L + 1)) ^ 2 ≤ n * θ := by rwa [div_le_iff₀ hθ] at hn3
      linarith [this]
    have hcl4 := hclose (badLaw q δ L F) (fun ω => (N ω : ℝ) / n) hμ hν
      (fun ω => A.mulVec (badRow ω)) hcl
    have hcardβ : (Fintype.card (Fin s → F) : ℝ) = (q : ℝ) ^ s := by
      rw [Fintype.card_fun, Fintype.card_fin, hF]; push_cast; rfl
    have hsq : (q : ℝ) ^ s ≤ (q : ℝ) ^ L := pow_le_pow_right₀ (by linarith) hsL
    rw [hcardβ] at hcl4
    have hr : (q : ℝ) ^ s / (q : ℝ) ^ L ≤ 1 := (div_le_one hqL).2 hsq
    have hkey : (q : ℝ) ^ s * (η * Real.log q / (q : ℝ) ^ L) ≤ η * Real.log q := by
      have e : (q : ℝ) ^ s * (η * Real.log q / (q : ℝ) ^ L) =
          ((q : ℝ) ^ s / (q : ℝ) ^ L) * (η * Real.log q) := by ring
      rw [e]
      calc _ ≤ 1 * (η * Real.log q) := mul_le_mul_of_nonneg_right hr (by positivity)
        _ = _ := one_mul _
    have hent : entQ q (badLaw q δ L F) (fun ω => A.mulVec (badRow ω)) - η ≤
        entQ q (fun ω => (N ω : ℝ) / n) (fun ω => A.mulVec (badRow ω)) := by
      have h := (abs_le.1 hcl4).2
      have h2 : (∑ b, Real.negMulLog (law (badLaw q δ L F) (fun ω => A.mulVec (badRow ω)) b)) /
          Real.log q - (∑ b, Real.negMulLog (law (fun ω => (N ω : ℝ) / n)
            (fun ω => A.mulVec (badRow ω)) b)) / Real.log q ≤ η := by
        rw [← sub_div, div_le_iff₀ hlogq]
        linarith [hkey]
      unfold entQ
      linarith
    have hnn : (0 : ℝ) ≤ n := hnR.le
    have h1 : (q : ℝ) ^ ((n : ℝ) * (entQ q (badLaw q δ L F) (fun ω => A.mulVec (badRow ω)) - η))
        ≤ (q : ℝ) ^ ((n : ℝ) * entQ q (fun ω => (N ω : ℝ) / n)
          (fun ω => A.mulVec (badRow ω))) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (mul_le_mul_of_nonneg_left hent hnn)
    have he : (1 : ℝ) ≤ Real.exp 1 * (n + 1) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) (by linarith)
    have h2 : (Real.exp 1 * ((Fintype.card ι : ℝ) + 1)) ^ Fintype.card (Fin s → F) ≤
        (Real.exp 1 * (n + 1)) ^ q ^ L := by
      have : Fintype.card (Fin s → F) ≤ q ^ L := by
        rw [Fintype.card_fun, Fintype.card_fin, hF]; exact Nat.pow_le_pow_right (by omega) hsL
      exact pow_le_pow_right₀ he this
    calc _ ≤ _ := h1
      _ ≤ _ := hlow
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)

end CodingTheory.RandomLinearInternal

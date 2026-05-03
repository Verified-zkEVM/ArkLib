/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.Data.Classes.Serde
import ArkLib.Data.Probability.Instances
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import ToMathlib.Probability.ProbabilityMassFunction.TotalVariation

/-!
# DSFS Preliminaries

This file contains paper-facing preliminaries for the duplex-sponge Fiat-Shamir formalization.
Currently it provides CO25 Lemma 3.2 about uniform preimage sampling.
-/

open ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace DuplexSpongeFS.Preliminaries

section Lemma32

variable {A B : Type*} [DecidableEq A] [Fintype B]

/-- The fiber of `ψ` over `a`. -/
abbrev Preimage (ψ : B → A) (a : A) := { b : B // ψ b = a }

/-- Surjectivity provides a canonical nonempty witness for each fiber. -/
noncomputable def preimageNonempty (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    Nonempty (Preimage ψ a) := by
  rcases hψ a with ⟨b, rfl⟩
  exact ⟨⟨b, rfl⟩⟩

/-- Sample a uniformly random preimage of `a` under `ψ`. -/
noncomputable def sampleUniformPreimage (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) : PMF B :=
  by
    classical
    letI := preimageNonempty ψ hψ a
    exact (PMF.uniformOfFintype (Preimage ψ a)).map Subtype.val

/-- Pointwise description of `sampleUniformPreimage`
Probability of sampling `b` from the fiber of `a` = `1/|fiber_{a}|` or `0` -/
theorem sampleUniformPreimage_apply (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) (b : B) :
    sampleUniformPreimage ψ hψ a b =
      if ψ b = a then (Fintype.card (Preimage ψ a) : ENNReal)⁻¹ else 0 := by
  classical
  letI := preimageNonempty ψ hψ a
  rw [sampleUniformPreimage, PMF.map_apply]
  by_cases h : ψ b = a
  · rw [tsum_eq_single ⟨b, h⟩]
    · simp [PMF.uniformOfFintype_apply, h]
    · intro y hy
      have hy' : b ≠ y.1 := by
        intro hEq
        apply hy
        apply Subtype.ext
        simpa using hEq.symm
      simp [hy']
  · rw [if_neg h]
    rw [ENNReal.tsum_eq_zero]
    intro y
    have hy' : b ≠ y.1 := by
      intro hEq
      exact h (by simpa [hEq] using y.2)
    simp [hy']

variable [Nonempty B]

/-- Paper notation `𝒰(X)` for the uniform distribution on a finite inhabited type `X`. -/
noncomputable abbrev 𝒰 (X : Type*) [Fintype X] [Nonempty X] : PMF X := $ᵖ X

/-- Distribution-level action of a deterministic map. This is the `ψ` in
`ψ⁻¹ ∘ ψ ∘ 𝒰(B)`. -/
noncomputable abbrev pushforward (ψ : B → A) : PMF B → PMF A := PMF.map ψ

/-- Distribution-level action of the uniform preimage sampler. This is the `ψ⁻¹` in
`ψ⁻¹ ∘ ψ ∘ 𝒰(B)`. -/
noncomputable abbrev uniformPreimageSampler
    (ψ : B → A) (hψ : Function.Surjective ψ) : PMF A → PMF B :=
  fun D => D.bind (sampleUniformPreimage ψ hψ)

-- monadic computation

-- ψ⁻¹ ∘ ψ ∘ U(B)

/-- CO25 Lemma 3.2 as an equality of PMFs. -/
theorem bind_sampleUniformPreimage_eq_uniform (ψ : B → A) (hψ : Function.Surjective ψ) :
    (do
      let b' ← $ᵖ B
      sampleUniformPreimage ψ hψ (ψ b')) = $ᵖ B := by
  classical
  change PMF.bind ($ᵖ B : PMF B) (fun b' => sampleUniformPreimage ψ hψ (ψ b')) = $ᵖ B
  apply PMF.ext
  intro b
  let c : ENNReal := (Fintype.card (Preimage ψ (ψ b)) : ENNReal)⁻¹
  have hcard_nat : Fintype.card (Preimage ψ (ψ b)) ≠ 0 := by
    letI := preimageNonempty ψ hψ (ψ b)
    exact Fintype.card_ne_zero
  have hcard :
      (Fintype.card (Preimage ψ (ψ b)) : ENNReal) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hfiber :
      (Finset.filter (fun b' : B => ψ b' = ψ b) Finset.univ).card =
        Fintype.card (Preimage ψ (ψ b)) := by
    simpa [Preimage] using
      (Fintype.card_subtype (fun b' : B => ψ b' = ψ b)).symm
  let s : Finset B := Finset.filter (fun b' : B => ψ b' = ψ b) Finset.univ
  have hs_def : s = Finset.filter (fun b' : B => ψ b' = ψ b) Finset.univ := rfl
  have hs_card : s.card = Fintype.card (Preimage ψ (ψ b)) := by
    rw [hs_def]
    exact hfiber
  change (PMF.bind ($ᵖ B : PMF B) (fun b' => sampleUniformPreimage ψ hψ (ψ b'))) b =
    ($ᵖ B : PMF B) b
  rw [PMF.bind_apply]
  rw [tsum_eq_sum
    (α := ENNReal)
    (β := B)
    (f := fun x => (($ᵖ B : PMF B) x) * sampleUniformPreimage ψ hψ (ψ x) b)
    (s := s)
    (hf := fun x hx => by
      have hx' : ψ x ≠ ψ b := by
        rw [hs_def] at hx
        simpa [Finset.mem_filter] using hx
      have hx'' : ψ b ≠ ψ x := by
        intro hEq
        exact hx' hEq.symm
      change (($ᵖ B : PMF B) x) * sampleUniformPreimage ψ hψ (ψ x) b = 0
      simp [PMF.uniformOfFintype_apply, sampleUniformPreimage_apply, hx''])]
  calc
    s.sum (fun x => (($ᵖ B : PMF B) x) * sampleUniformPreimage ψ hψ (ψ x) b)
        =
      s.sum (fun _ => (Fintype.card B : ENNReal)⁻¹ * c) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hx' : ψ x = ψ b := by
            rw [hs_def] at hx
            simpa using (Finset.mem_filter.mp hx).2
          rw [PMF.uniformOfFintype_apply, sampleUniformPreimage_apply, if_pos hx'.symm]
          simp [c, hx']
  _ = s.card * ((Fintype.card B : ENNReal)⁻¹ * c) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  _ = (Fintype.card (Preimage ψ (ψ b)) : ENNReal) * ((Fintype.card B : ENNReal)⁻¹ * c) := by
          rw [hs_card]
  _ = ((Fintype.card (Preimage ψ (ψ b)) : ENNReal) * (Fintype.card B : ENNReal)⁻¹) * c := by
          rw [← mul_assoc]
  _ = ((Fintype.card (Preimage ψ (ψ b)) : ENNReal) * (Fintype.card B : ENNReal)⁻¹) *
        ((Fintype.card (Preimage ψ (ψ b)) : ENNReal)⁻¹) := by
          rfl
  _ = ((Fintype.card (Preimage ψ (ψ b)) : ENNReal) *
        ((Fintype.card (Preimage ψ (ψ b)) : ENNReal)⁻¹)) *
        (Fintype.card B : ENNReal)⁻¹ := by
          ac_rfl
  _ = (Fintype.card B : ENNReal)⁻¹ := by
          simpa [mul_assoc] using
            congrArg (fun t : ENNReal => t * (Fintype.card B : ENNReal)⁻¹)
              (ENNReal.mul_inv_cancel hcard
                (ENNReal.natCast_ne_top (Fintype.card (Preimage ψ (ψ b)))))
  _ = ($ᵖ B : PMF B) b := by
          rw [PMF.uniformOfFintype_apply]

/-- CO25 Lemma 3.2: resampling a uniformly random element via a uniformly random preimage preserves
the uniform distribution.
ψ⁻¹ ∘ ψ ∘ U(B) = U(B), where ψ⁻¹ is uniform sampling of fiber of a value in `A`
-/
theorem lemma_3_2 (ψ : B → A) (hψ : Function.Surjective ψ) :
    Dist.dist ($ᵖ B)
      (do
        let b ← $ᵖ B
        sampleUniformPreimage ψ hψ (ψ b)) = 0 := by
  rw [bind_sampleUniformPreimage_eq_uniform (ψ := ψ) hψ]
  simp [dist]

/-- CO25 Lemma 3.2 as the paper's composition equation:
`ψ⁻¹ ∘ ψ ∘ 𝒰(B) = 𝒰(B)`. -/
theorem lemma_3_2_paperEquation (ψ : B → A) (hψ : Function.Surjective ψ) :
    ((uniformPreimageSampler ψ hψ) ∘ pushforward ψ) (𝒰 B) = 𝒰 B := by
  simpa [uniformPreimageSampler, pushforward, 𝒰, Functor.map] using
    (bind_sampleUniformPreimage_eq_uniform (ψ := ψ) hψ)

/-- CO25 Lemma 3.2 in the paper's `Δ(...)=0` form:
`Δ(𝒰(B), ψ⁻¹ ∘ ψ ∘ 𝒰(B)) = 0`.

The helper definitions `𝒰`, `pushforward`, and `uniformPreimageSampler` make the Lean statement
track the paper notation directly. -/
theorem lemma_3_2_paperNotation (ψ : B → A) (hψ : Function.Surjective ψ) :
    Dist.dist (𝒰 B) (((uniformPreimageSampler ψ hψ) ∘ pushforward ψ) (𝒰 B)) = 0 := by
  rw [lemma_3_2_paperEquation (ψ := ψ) hψ]
  simp [dist, 𝒰]

end Lemma32

section Claim1210

variable {α : Type*}

-- TV distance conditioning bound via indicator decomposition (CY24 Claim 1.2.10)
/-- CY24 Claim 1.2.10: conditioning on equi-probable events bounds TV distance.

Let `p q : PMF α` be distributions and `s₁ s₂ : Set α` events with equal probability
under `p` and `q` respectively (`Pr_p[s₁] = Pr_q[s₂]`). Then
`Δ(p, q) ≤ Δ(p | s₁, q | s₂) + Pr_p[s₁ᶜ]`,
where `p | s₁` is `p.filter s₁` (PMF `p` conditioned on `s₁`, see `PMF.filter`),
and `Pr_p[s₁ᶜ] = 1 - Pr_p[s₁] = 1 - ∑' a ∈ s₁, p a`. -/
theorem claim_1_2_10
    (p q : PMF α) (s₁ s₂ : Set α)
    (hs₁ : ∃ a ∈ s₁, a ∈ p.support)
    (hs₂ : ∃ a ∈ s₂, a ∈ q.support)
    (hProb : ∑' a, s₁.indicator p a = ∑' a, s₂.indicator q a) :
    p.tvDist q ≤ (p.filter s₁ hs₁).tvDist (q.filter s₂ hs₂) +
      (1 - (∑' a, s₁.indicator p a).toReal) := by
  set c := ∑' a, s₁.indicator p a with hc_def
  -- Basic properties of c (= Pr_p[s₁] = Pr_q[s₂])
  have hc_le : c ≤ 1 :=
    (ENNReal.tsum_le_tsum fun a => Set.indicator_le_self s₁ p a).trans p.tsum_coe.le
  have hc_ne_top : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc_le
  have hc_ne_zero : c ≠ 0 := by
    obtain ⟨a, ha₁, ha_p⟩ := hs₁
    have : 0 < s₁.indicator p a := by
      rw [Set.indicator_of_mem ha₁]
      exact ha_p.bot_lt
    exact (this.trans_le (ENNReal.le_tsum a)).ne'
  have hc_inv_ne_top : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc_ne_zero
  -- Each filter value equals the indicator value * c⁻¹
  -- Pointwise: absDiff of filter values = absDiff of indicators * c⁻¹
  have habs_filter : ∀ x,
      ENNReal.absDiff ((p.filter s₁ hs₁) x) ((q.filter s₂ hs₂) x) =
      ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x) * c⁻¹ := by
    intro x
    rw [PMF.filter_apply, PMF.filter_apply, ← hProb, ← hc_def]
    simp only [ENNReal.absDiff]
    rw [← ENNReal.sub_mul (fun _ _ => hc_inv_ne_top),
        ← ENNReal.sub_mul (fun _ _ => hc_inv_ne_top),
        ← add_mul]
  -- Sum: ∑' x, absDiff (filter1 x) (filter2 x) = (∑' x, absDiff (ind1 x) (ind2 x)) * c⁻¹
  have hsum_abs_filter :
      ∑' x, ENNReal.absDiff ((p.filter s₁ hs₁) x) ((q.filter s₂ hs₂) x) =
      (∑' x, ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x)) * c⁻¹ := by
    simp_rw [habs_filter, ← ENNReal.tsum_mul_right]
  -- Pointwise: absDiff (p x) (q x) ≤ absDiff (ind1 x) (ind2 x) + compl1 x + compl2 x
  have hpointwise : ∀ x, ENNReal.absDiff (p x) (q x) ≤
      ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x) +
      (s₁ᶜ).indicator p x + (s₂ᶜ).indicator q x := by
    intro x
    have hpx : s₁.indicator p x ≠ ⊤ :=
      ne_top_of_le_ne_top (PMF.apply_ne_top p x) (Set.indicator_le_self s₁ p x)
    have hqx : (s₂ᶜ).indicator q x ≠ ⊤ :=
      ne_top_of_le_ne_top (PMF.apply_ne_top q x) (Set.indicator_le_self _ q x)
    rw [← Set.indicator_self_add_compl_apply s₁ p x,
        ← Set.indicator_self_add_compl_apply s₂ q x]
    -- two-step triangle: absDiff(a+b)(c+d) ≤ absDiff a c + absDiff b d
    calc ENNReal.absDiff (s₁.indicator p x + (s₁ᶜ).indicator p x)
            (s₂.indicator q x + (s₂ᶜ).indicator q x)
        ≤ ENNReal.absDiff (s₁.indicator p x + (s₁ᶜ).indicator p x)
              (s₁.indicator p x + (s₂ᶜ).indicator q x) +
          ENNReal.absDiff (s₁.indicator p x + (s₂ᶜ).indicator q x)
              (s₂.indicator q x + (s₂ᶜ).indicator q x) :=
              ENNReal.absDiff_triangle _ _ _
      _ = ENNReal.absDiff ((s₁ᶜ).indicator p x) ((s₂ᶜ).indicator q x) +
            ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x) := by
            simp only [ENNReal.absDiff,
              ENNReal.add_sub_add_eq_sub_left hpx,
              ENNReal.add_sub_add_eq_sub_right hqx]
      _ ≤ (s₁ᶜ).indicator p x + (s₂ᶜ).indicator q x +
            ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x) := by
            gcongr; exact ENNReal.absDiff_le_add _ _
      _ = _ := by ring
  -- Complement tsums equal 1 - c
  have hcompl₁ : ∑' a, (s₁ᶜ).indicator p a = 1 - c := by
    have h : c + ∑' a, (s₁ᶜ).indicator p a = 1 := by
      calc c + ∑' a, (s₁ᶜ).indicator p a
          = ∑' a, s₁.indicator p a + ∑' a, (s₁ᶜ).indicator p a := rfl
        _ = ∑' a, (s₁.indicator p a + (s₁ᶜ).indicator p a) := (ENNReal.tsum_add).symm
        _ = ∑' a, p a := by
            congr 1; ext a; exact Set.indicator_self_add_compl_apply s₁ p a
        _ = 1 := p.tsum_coe
    have key : c + ∑' a, (s₁ᶜ).indicator p a - c = ∑' a, (s₁ᶜ).indicator p a :=
      ENNReal.add_sub_cancel_left hc_ne_top
    rw [h] at key; exact key.symm
  have hcompl₂ : ∑' a, (s₂ᶜ).indicator q a = 1 - c := by
    have h : c + ∑' a, (s₂ᶜ).indicator q a = 1 := by
      calc c + ∑' a, (s₂ᶜ).indicator q a
          = ∑' a, s₂.indicator q a + ∑' a, (s₂ᶜ).indicator q a := by rw [hProb]
        _ = ∑' a, (s₂.indicator q a + (s₂ᶜ).indicator q a) := (ENNReal.tsum_add).symm
        _ = ∑' a, q a := by
            congr 1; ext a; exact Set.indicator_self_add_compl_apply s₂ q a
        _ = 1 := q.tsum_coe
    have key : c + ∑' a, (s₂ᶜ).indicator q a - c = ∑' a, (s₂ᶜ).indicator q a :=
      ENNReal.add_sub_cancel_left hc_ne_top
    rw [h] at key; exact key.symm
  -- Sum bound: ∑' absDiff (p) (q) ≤ ∑' absDiff (ind1) (ind2) + (1-c) + (1-c)
  have hsum_ineq : ∑' x, ENNReal.absDiff (p x) (q x) ≤
      (∑' x, ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x)) + (1 - c) + (1 - c) := by
    calc ∑' x, ENNReal.absDiff (p x) (q x)
        ≤ ∑' x, (ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x) +
              (s₁ᶜ).indicator p x + (s₂ᶜ).indicator q x) :=
            ENNReal.tsum_le_tsum hpointwise
      _ = (∑' x, ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x)) +
          (∑' x, (s₁ᶜ).indicator p x) + ∑' x, (s₂ᶜ).indicator q x := by
            rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
      _ = _ := by rw [hcompl₁, hcompl₂]
  -- Main ENNReal inequality: etvDist p q ≤ c * etvDist(filter1, filter2) + (1 - c)
  have hmain_ennreal : p.etvDist q ≤ c * (p.filter s₁ hs₁).etvDist (q.filter s₂ hs₂) + (1 - c) := by
    rw [PMF.etvDist, PMF.etvDist, hsum_abs_filter]
    -- c * (sum_ind * c⁻¹ / 2) = sum_ind / 2
    have hc_mul : c * ((∑' x, ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x)) * c⁻¹ / 2) =
        (∑' x, ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x)) / 2 := by
      rw [← mul_div_assoc, ← mul_assoc, mul_comm c, mul_assoc,
          ENNReal.mul_inv_cancel hc_ne_zero hc_ne_top, mul_one]
    rw [hc_mul]
    calc (∑' x, ENNReal.absDiff (p x) (q x)) / 2
        ≤ ((∑' x, ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x)) + (1 - c) + (1 - c)) / 2 :=
            ENNReal.div_le_div_right hsum_ineq 2
      _ = (∑' x, ENNReal.absDiff (s₁.indicator p x) (s₂.indicator q x)) / 2 + (1 - c) := by
            rw [ENNReal.add_div, ENNReal.add_div, add_assoc, ENNReal.add_halves]
  -- Convert to ℝ:
  -- tvDist ≤ c.toReal * tvDist(filter) + (1 - c.toReal) ≤ tvDist(filter) + (1 - c.toReal)
  have hc_toReal_le : c.toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hc_le
  have h1mc_eq : (1 - c).toReal = 1 - c.toReal :=
    ENNReal.toReal_sub_of_le hc_le ENNReal.one_ne_top
  have hmain_real :
      p.tvDist q ≤ c.toReal * (p.filter s₁ hs₁).tvDist (q.filter s₂ hs₂) + (1 - c.toReal) := by
    rw [PMF.tvDist, PMF.tvDist]
    have hRHS_ne_top : c * (p.filter s₁ hs₁).etvDist (q.filter s₂ hs₂) + (1 - c) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hc_ne_top (PMF.etvDist_ne_top _ _),
        ENNReal.sub_ne_top ENNReal.one_ne_top⟩
    have := ENNReal.toReal_mono hRHS_ne_top hmain_ennreal
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hc_ne_top (PMF.etvDist_ne_top _ _))
          (ENNReal.sub_ne_top ENNReal.one_ne_top),
        ENNReal.toReal_mul, h1mc_eq] at this
    exact this
  linarith [PMF.tvDist_nonneg (p.filter s₁ hs₁) (q.filter s₂ hs₂),
    mul_le_of_le_one_left (PMF.tvDist_nonneg (p.filter s₁ hs₁) (q.filter s₂ hs₂)) hc_toReal_le]

end Claim1210

end DuplexSpongeFS.Preliminaries

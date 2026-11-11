/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import CompPoly.Data.Classes.Serialize
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.UniformOn
public import ToMathlib.MeasureTheory.Measure.TotalVariation

/-!
# DSFS Preliminaries

This file contains preliminaries for the duplex-sponge Fiat-Shamir formalization, stated for
probability measures:
- CO25 Lemma 3.2 (uniform preimage sampling preserves the uniform distribution), for the
  uniform-on-the-fiber measure `sampleUniformPreimage`;
- CY24 Claim 1.2.10 (conditioning bound on total-variation distance), `claim_1_2_10`.

Statistical distance is VCVio's `MeasureTheory.Measure.tvDist`, the largest probability
discrepancy over measurable events. Under the discrete σ-algebra it is `½ ∑ₓ |μ{x} − ν{x}|`
(`MeasureTheory.Measure.tvDist_eq_half_sum_abs` on a finite type).

No declaration in Section 5 uses these results yet. Section 5 samples `ψᵢ⁻¹` preimages with the
`OracleComp` sampler `ProverTransform.uniformDeserializePreimage`, which draws an index into the
list of the fiber `deserializePreimageFinset` with one `unifSpec` query. A proof of Claim 5.22
that uses Lemma 3.2 needs a bridge lemma: under a handler that answers `unifSpec` queries
uniformly, the output measure of `uniformDeserializePreimage α` is
`sampleUniformPreimage Deserialize.deserialize α`. That lemma is not formalized yet.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace DuplexSpongeFS.Preliminaries

section Lemma32

variable {A B : Type*}

/-- The fiber of `ψ` over `a`. -/
abbrev Preimage (ψ : B → A) (a : A) := { b : B // ψ b = a }

/-- Surjectivity provides a canonical nonempty witness for each fiber. -/
theorem preimageNonempty (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    Nonempty (Preimage ψ a) := by
  rcases hψ a with ⟨b, rfl⟩
  exact ⟨⟨b, rfl⟩⟩

variable [MeasurableSpace B]

/-- Sample a uniformly random preimage of `a` under `ψ`: the uniform measure on the fiber. -/
noncomputable def sampleUniformPreimage (ψ : B → A) (a : A) : Measure B :=
  uniformOn {b | ψ b = a}

/-- On a surjective map, the uniform preimage sampler is a probability measure at every point. -/
theorem isProbabilityMeasure_sampleUniformPreimage [Finite B] [MeasurableSingletonClass B]
    (ψ : B → A) (hψ : Function.Surjective ψ) (a : A) :
    IsProbabilityMeasure (sampleUniformPreimage ψ a) := by
  obtain ⟨b, rfl⟩ := hψ a
  exact isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨b, rfl⟩

/-- Pointwise description of `sampleUniformPreimage`.
Probability of sampling `b` from the fiber of `a` = `1/|fiber_{a}|` or `0` -/
theorem sampleUniformPreimage_apply_singleton [DecidableEq A] [Fintype B]
    [MeasurableSingletonClass B] (ψ : B → A) (a : A) (b : B) :
    sampleUniformPreimage ψ a {b} =
      if ψ b = a then (Fintype.card (Preimage ψ a) : ℝ≥0∞)⁻¹ else 0 := by
  rw [sampleUniformPreimage, uniformOn, cond_apply' (measurableSet_singleton b),
    Measure.count_apply (Set.toFinite _).measurableSet,
    Set.encard_eq_coe_toFinset_card, Set.toFinset_card]
  by_cases h : ψ b = a
  · rw [Set.inter_singleton_of_mem (s := {b | ψ b = a}) h, Measure.count_singleton, mul_one]
    simp only [h, ite_true]
    rfl
  · rw [(Set.inter_singleton_eq_empty (s := {b | ψ b = a})).mpr h, measure_empty, mul_zero]
    simp [h]

variable [Finite B] [MeasurableSingletonClass B]

/-- CO25 Lemma 3.2 as an equality of measures: drawing `b'` uniformly and then a uniform
preimage of `ψ b'` is a uniform draw. -/
theorem bind_sampleUniformPreimage_eq_uniform (ψ : B → A) :
    (uniformOn Set.univ : Measure B).bind (fun b' => sampleUniformPreimage ψ (ψ b')) =
      uniformOn Set.univ := by
  classical
  let := Fintype.ofFinite B
  refine Measure.ext_of_singleton fun b => ?_
  rw [Measure.bind_apply (measurableSet_singleton b) Measurable.of_discrete.aemeasurable,
    lintegral_fintype]
  simp only [sampleUniformPreimage_apply_singleton, uniformOn_univ, Measure.count_singleton]
  let c : ℝ≥0∞ := (Fintype.card (Preimage ψ (ψ b)) : ℝ≥0∞)⁻¹
  have hcard : (Fintype.card (Preimage ψ (ψ b)) : ℝ≥0∞) ≠ 0 := by
    have : Nonempty (Preimage ψ (ψ b)) := ⟨⟨b, rfl⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  let s : Finset B := Finset.filter (fun b' : B => ψ b' = ψ b) Finset.univ
  have hs_card : s.card = Fintype.card (Preimage ψ (ψ b)) :=
    (Fintype.card_subtype (fun b' : B => ψ b' = ψ b)).symm
  calc ∑ x, (if ψ b = ψ x then (Fintype.card (Preimage ψ (ψ x)) : ℝ≥0∞)⁻¹ else 0) *
        (1 / (Fintype.card B : ℝ≥0∞))
      = ∑ x ∈ s, c * (1 / (Fintype.card B : ℝ≥0∞)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : ψ x = ψ b
        · simp only [hx, ite_true]; rfl
        · simp [hx, Ne.symm hx]
    _ = (Fintype.card (Preimage ψ (ψ b)) : ℝ≥0∞) * c * (1 / (Fintype.card B : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hs_card, mul_assoc]
    _ = 1 / (Fintype.card B : ℝ≥0∞) := by
        rw [ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _), one_mul]

/-- CO25 Lemma 3.2: resampling a uniformly random element via a uniformly random preimage preserves
the uniform distribution.
ψ⁻¹ ∘ ψ ∘ U(B) = U(B), where ψ⁻¹ is uniform sampling of fiber of a value in `A`
-/
theorem lemma_3_2 (ψ : B → A) :
    (uniformOn Set.univ : Measure B).tvDist
      ((uniformOn Set.univ : Measure B).bind fun b => sampleUniformPreimage ψ (ψ b)) = 0 := by
  rw [bind_sampleUniformPreimage_eq_uniform ψ, Measure.tvDist_self]

variable [MeasurableSpace A] [DiscreteMeasurableSpace A]

/-- Paper notation `𝒰(X)` for the uniform distribution on a finite type `X`. -/
noncomputable abbrev 𝒰 (X : Type*) [MeasurableSpace X] : Measure X := uniformOn Set.univ

/-- Distribution-level action of a deterministic map. This is the `ψ` in
`ψ⁻¹ ∘ ψ ∘ 𝒰(B)`. -/
noncomputable abbrev pushforward (ψ : B → A) : Measure B → Measure A := Measure.map ψ

/-- Distribution-level action of the uniform preimage sampler. This is the `ψ⁻¹` in
`ψ⁻¹ ∘ ψ ∘ 𝒰(B)`. -/
noncomputable abbrev uniformPreimageSampler (ψ : B → A) : Measure A → Measure B :=
  fun D => D.bind (sampleUniformPreimage ψ)

/-- CO25 Lemma 3.2 as the paper's composition equation:
`ψ⁻¹ ∘ ψ ∘ 𝒰(B) = 𝒰(B)`. -/
theorem lemma_3_2_paperEquation (ψ : B → A) :
    ((uniformPreimageSampler ψ) ∘ pushforward ψ) (𝒰 B) = 𝒰 B := by
  rw [Function.comp_apply, uniformPreimageSampler, pushforward,
    Measure.bind_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  exact bind_sampleUniformPreimage_eq_uniform ψ

/-- CO25 Lemma 3.2 in the paper's `Δ(...)=0` form:
`Δ(𝒰(B), ψ⁻¹ ∘ ψ ∘ 𝒰(B)) = 0`.

The helper definitions `𝒰`, `pushforward`, and `uniformPreimageSampler` make the Lean statement
track the paper notation directly. -/
theorem lemma_3_2_paperNotation (ψ : B → A) :
    (𝒰 B).tvDist (((uniformPreimageSampler ψ) ∘ pushforward ψ) (𝒰 B)) = 0 := by
  rw [lemma_3_2_paperEquation ψ, Measure.tvDist_self]

end Lemma32

section Claim1210

variable {α : Type*} [MeasurableSpace α]

/-- If two pairs of values differ by their first components up to `d` and their second
components are at most `k`, the sums differ by at most `d + k`. -/
private lemma absDiff_add_le_of_le {a b a' b' k : ℝ≥0∞} (ha' : a' ≤ k) (hb' : b' ≤ k) :
    ENNReal.absDiff (a + a') (b + b') ≤ ENNReal.absDiff a b + k := by
  obtain ⟨hab, hba⟩ := ENNReal.absDiff_le_iff.mp (le_refl (ENNReal.absDiff a b))
  refine ENNReal.absDiff_le_iff.mpr ⟨?_, ?_⟩
  · calc a + a' ≤ (b + ENNReal.absDiff a b) + (b' + k) :=
          add_le_add hab (ha'.trans le_add_self)
      _ = b + b' + (ENNReal.absDiff a b + k) := by ring
  · calc b + b' ≤ (a + ENNReal.absDiff a b) + (a' + k) :=
          add_le_add hba (hb'.trans le_add_self)
      _ = a + a' + (ENNReal.absDiff a b + k) := by ring

/-- CY24 Claim 1.2.10: conditioning on equi-probable events bounds TV distance.

Let `μ ν` be probability measures and `s₁ s₂` measurable events with equal probability
under `μ` and `ν` respectively (`Pr_μ[s₁] = Pr_ν[s₂]`), and `Pr_μ[s₁] ≠ 0`. Then
`Δ(μ, ν) ≤ Δ(μ | s₁, ν | s₂) + Pr_μ[s₁ᶜ]`,
where `μ | s₁` is the conditional measure `μ[|s₁]` (see `ProbabilityTheory.cond`),
and `Pr_μ[s₁ᶜ] = 1 - Pr_μ[s₁]`. -/
theorem claim_1_2_10
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {s₁ s₂ : Set α}
    (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) (hμs₁ : μ s₁ ≠ 0)
    (hProb : μ s₁ = ν s₂) :
    μ.tvDist ν ≤ (μ[|s₁]).tvDist (ν[|s₂]) + (1 - (μ s₁).toReal) := by
  set c := μ s₁ with hc_def
  have hc_ne_top : c ≠ ⊤ := measure_ne_top μ s₁
  have hνs₂ : ν s₂ ≠ 0 := hProb ▸ hμs₁
  have : IsProbabilityMeasure μ[|s₁] := cond_isProbabilityMeasure hμs₁
  have : IsProbabilityMeasure ν[|s₂] := cond_isProbabilityMeasure hνs₂
  -- Each measurable event splits into its part inside the conditioning event, which is `c` times
  -- its conditional probability, and its part outside, which has mass at most `1 - c`.
  have hmain : μ.etvDist ν ≤ (μ[|s₁]).etvDist (ν[|s₂]) + (1 - c) := by
    refine iSup_le fun T => ?_
    obtain ⟨T, hT⟩ := T
    have hμT : μ T = c * μ[T|s₁] + μ (T \ s₁) := by
      rw [← measure_inter_add_sdiff T hs₁, Set.inter_comm, ← cond_mul_eq_inter hs₁, mul_comm]
    have hνT : ν T = c * ν[T|s₂] + ν (T \ s₂) := by
      rw [← measure_inter_add_sdiff T hs₂, Set.inter_comm, ← cond_mul_eq_inter hs₂, mul_comm,
        hProb]
    have hμout : μ (T \ s₁) ≤ 1 - c := by
      rw [← prob_compl_eq_one_sub hs₁]
      exact measure_mono (Set.sdiff_subset_compl _ _)
    have hνout : ν (T \ s₂) ≤ 1 - c := by
      rw [hProb, ← prob_compl_eq_one_sub hs₂]
      exact measure_mono (Set.sdiff_subset_compl _ _)
    have hc_le : c ≤ 1 := prob_le_one
    calc ENNReal.absDiff (μ T) (ν T)
        ≤ ENNReal.absDiff (c * μ[T|s₁]) (c * ν[T|s₂]) + (1 - c) := by
          rw [hμT, hνT]
          exact absDiff_add_le_of_le hμout hνout
      _ ≤ ENNReal.absDiff (μ[T|s₁]) (ν[T|s₂]) * c + (1 - c) := by
          gcongr
          rw [mul_comm c, mul_comm c]
          exact ENNReal.absDiff_mul_right_le _ _ _
      _ ≤ ENNReal.absDiff (μ[T|s₁]) (ν[T|s₂]) + (1 - c) := by
          gcongr
          exact mul_le_of_le_one_right' hc_le
      _ ≤ (μ[|s₁]).etvDist (ν[|s₂]) + (1 - c) := by
          gcongr
          exact Measure.absDiff_apply_le_etvDist _ _ hT
  have hcond_ne_top : (μ[|s₁]).etvDist (ν[|s₂]) ≠ ⊤ :=
    Measure.etvDist_ne_top _ _ prob_le_one prob_le_one
  have hc_le : c ≤ 1 := prob_le_one
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hcond_ne_top, ENNReal.sub_ne_top ENNReal.one_ne_top⟩) hmain
  rw [ENNReal.toReal_add hcond_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top),
    ENNReal.toReal_sub_of_le hc_le ENNReal.one_ne_top, ENNReal.toReal_one] at h
  exact h

end Claim1210

end DuplexSpongeFS.Preliminaries

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.Data.Classes.Serde
import ArkLib.Data.Probability.Instances

/-!
# DSFS Preliminaries

This file contains paper-facing preliminaries for the duplex-sponge Fiat-Shamir formalization.
Currently it provides CO25 Lemma 3.2 about uniform preimage sampling.
-/

open ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace DuplexSpongeFS

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

end DuplexSpongeFS

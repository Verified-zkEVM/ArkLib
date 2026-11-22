/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import Mathlib.Algebra.Field.ZMod

/-! # The proximity gap for affine lines at the `ε < 1` boundary

Words of length one over `ZMod 2`, the zero code `{0}` and `δ = 0`. At `ε = 1/2` the zero code has
`(0, 1/2)`-correlated agreement for affine lines, and
`δ_ε_proximityGap_of_δ_ε_correlatedAgreementAffineLines` gives the `(0, 1/2)`-proximity gap. At
`ε = 1` correlated agreement holds vacuously, but the constant line `{0}` is `0`-close to the code
with probability `1`, which is also at most `1`, so the `(0, 1)`-proximity gap fails: the
hypothesis `ε < 1` cannot be dropped.
-/

open Code ProximityGap NNReal ProbabilityTheory

namespace ProximityGapBasicTest

private noncomputable instance : SampleableType (ZMod 2) := SampleableType.ofFintype _

/-- The zero code of length one over `ZMod 2`. -/
private def zeroCode : Finset (Fin 1 → ZMod 2) := {0}

/-- The affine lines `{u₀ + z • u₁ | z ∈ ZMod 2}`. -/
private def lines : Set (Finset (Fin 1 → ZMod 2)) :=
  Set.range fun u : WordStack (ZMod 2) (Fin 2) (Fin 1) =>
    Finset.univ.image fun z : ZMod 2 => u 0 + z • u 1

private theorem close_zeroCode_iff (w : Fin 1 → ZMod 2) :
    δᵣ(w, (zeroCode : Set (Fin 1 → ZMod 2))) ≤ ((0 : ℝ≥0) : ENNReal) ↔ w = 0 := by
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  simp [zeroCode, relHammingDist]

-- Below the boundary: correlated agreement, hence the proximity gap, at `ε = 1/2`.
private theorem correlatedAgreement_half :
    δ_ε_correlatedAgreementAffineLines (F := ZMod 2)
      (zeroCode : Set (Fin 1 → ZMod 2)) 0 (1 / 2) := by
  intro u hu
  have hall : ∀ z : ZMod 2, u 0 + z • u 1 = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨z₀, hz₀⟩ := hne
    have hle : Pr{let z ← $ᵗ ZMod 2}[δᵣ(u 0 + z • u 1, (zeroCode : Set (Fin 1 → ZMod 2))) ≤
        ((0 : ℝ≥0) : ENNReal)] ≤ Pr{let z ← $ᵗ ZMod 2}[z = z₀ + 1] := by
      refine prEvent_mono _ _ _ fun z hz => ?_
      rw [close_zeroCode_iff] at hz
      have hne : ∀ a b : ZMod 2, a ≠ b → a = b + 1 := by decide
      exact hne z z₀ fun h => hz₀ (h ▸ hz)
    rw [SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card] at hle
    have := hu.trans_le hle
    norm_num at this
  have h0 : u 0 = 0 := by simpa using hall 0
  have h1 : u 1 = 0 := by simpa [h0] using hall 1
  have hu' : ∀ i, u i = 0 := Fin.forall_fin_two.2 ⟨h0, h1⟩
  exact ⟨Finset.univ, by simp, 0, fun i =>
    ⟨by simp [zeroCode], fun j _ => by simp [hu', Fin.fin_one_eq_zero j]⟩⟩

example : δ_ε_proximityGap zeroCode lines 0 (1 / 2) :=
  δ_ε_proximityGap_of_δ_ε_correlatedAgreementAffineLines zeroCode (by norm_num)
    correlatedAgreement_half

-- At the boundary `ε = 1`: correlated agreement holds vacuously ...
example : δ_ε_correlatedAgreementAffineLines (F := ZMod 2)
    (zeroCode : Set (Fin 1 → ZMod 2)) 0 1 := fun _ h => by
  have := h.trans_le (prEvent_le_one _)
  simp at this

-- ... but the constant line `{0}` takes both alternatives of the proximity gap.
example : ¬ δ_ε_proximityGap zeroCode lines 0 1 := by
  intro h
  let S : Finset (Fin 1 → ZMod 2) := Finset.univ.image fun z : ZMod 2 => 0 + z • 0
  have hS : S ∈ lines := ⟨0, rfl⟩
  have : Nonempty S := ⟨⟨0, by simp [S]⟩⟩
  rcases h S hS with ⟨-, hle⟩ | ⟨-, hone⟩
  · exact hle ((prEvent_le_one _).trans (by simp))
  · -- `δ_ε_proximityGap` samples `S` with the finite-set sampler `instSampleableTypeFinsetCoe`.
    refine hone ((@SampleableType.prEvent_uniformSample_eq_one_iff _
      (instSampleableTypeFinsetCoe S) _).2 fun x => ?_)
    have hx : x.val = 0 := by
      obtain ⟨z, -, hz⟩ := Finset.mem_image.mp x.property
      rw [← hz]
      simp
    rw [hx]
    exact (close_zeroCode_iff 0).2 rfl

end ProximityGapBasicTest

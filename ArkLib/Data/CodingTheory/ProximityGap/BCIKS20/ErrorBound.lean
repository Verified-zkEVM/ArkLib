/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ReedSolomon

namespace ProximityGap

open NNReal Finset Function Code
open scoped BigOperators LinearCode

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ (0, (1-ρ)/2]` and Johnson bound, i.e. `δ ∈ ((1-ρ)/2 , 1 - √ρ)`. Otherwise,
  we set `ε = 0`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI ρ : ℝ≥0 := ρ (ReedSolomon.code domain deg)
  if δ ∈ Set.Icc 0 ((1 - ρ) / 2) then
    Fintype.card ι / Fintype.card F
  else if δ ∈ Set.Ioo ((1 - ρ) / 2) (1 - ρ.sqrt) then
    letI m := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
    ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
  else
    0

omit [DecidableEq ι] in
theorem errorBound_eq_n_div_q_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    errorBound δ deg domain = Fintype.card ι / Fintype.card F := by
  classical
  let C : LinearCode ι F := ReedSolomon.code domain deg
  let n : ℕ := Fintype.card ι
  let kdim : ℕ := Module.finrank F C
  let d : ℕ := Code.dist (C : Set (ι → F))
  have hk : kdim ≤ n := by
    have hk' : Module.finrank F C ≤ Module.finrank F (ι → F) :=
      Submodule.finrank_le (R := F) (M := (ι → F)) C
    simpa [n, kdim, Module.finrank_pi] using hk'
  have hSB : kdim ≤ n - d + 1 := by
    simpa [n, d, kdim] using (LinearCode.singleton_bound_linear (LC := C))
  have hdle : d ≤ n := by
    exact Code.dist_le_card (C := (C : Set (ι → F)))
  have hdistNat : d - 1 ≤ n - kdim := by
    omega
  -- Compare the unique-decoding radius with the rate-based threshold.
  have hrel :
      relativeUniqueDecodingRadius (ι := ι) (F := F) (C := C) ≤
        ((1 - (↑(LinearCode.rate C) : ℝ≥0)) / 2) := by
    have hUDR :
        relativeUniqueDecodingRadius (ι := ι) (F := F) (C := C) =
          (((d : ℝ≥0) - 1) / 2) / (n : ℝ≥0) := by
      simp [Code.relativeUniqueDecodingRadius, d, n]
    have hrate : (↑(LinearCode.rate C) : ℝ≥0) = (kdim : ℝ≥0) / (n : ℝ≥0) := by
      simp [LinearCode.rate, LinearCode.dim, LinearCode.length, kdim, n]
    -- Cast the distance-gap inequality into `ℝ≥0`.
    have hdistNN : ((d : ℝ≥0) - 1) ≤ (n - kdim : ℝ≥0) := by
      exact_mod_cast hdistNat
    -- The blocklength is positive because the index type is nonempty.
    have hn0 : (n : ℝ≥0) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      exact Fintype.card_ne_zero (α := ι)
    -- Rewrite the rate term using the codimension expression.
    have hR :
        ((1 : ℝ≥0) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2 =
          ((n - kdim : ℝ≥0) / 2) / (n : ℝ≥0) := by
      calc
        ((1 : ℝ≥0) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2
            = (((n : ℝ≥0) / (n : ℝ≥0)) - (kdim : ℝ≥0) / (n : ℝ≥0)) / 2 := by
                rw [← div_self hn0]
        _ = (((n : ℝ≥0) - (kdim : ℝ≥0)) / (n : ℝ≥0)) / 2 := by
              rw [← NNReal.sub_div (a := (n : ℝ≥0)) (b := (kdim : ℝ≥0)) (c := (n : ℝ≥0))]
        _ = ((n - kdim : ℝ≥0) / (n : ℝ≥0)) / 2 := by
              simp
        _ = ((n - kdim : ℝ≥0) / 2) / (n : ℝ≥0) := by
              simp [div_div, mul_comm]
    -- Substitute the distance and rate identities into the target bound.
    rw [hUDR, hrate, hR]
    gcongr
  -- The assumed radius bound puts `δ` in the unique-decoding branch.
  have hmem : δ ∈ Set.Icc 0 ((1 - (↑(LinearCode.rate C) : ℝ≥0)) / 2) := by
    refine ⟨by simp, le_trans hδ hrel⟩
  -- Evaluate `errorBound` on that branch.
  simp [errorBound, C, hmem]

end CoreResults

end ProximityGap

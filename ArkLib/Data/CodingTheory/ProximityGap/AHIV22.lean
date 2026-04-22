/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation

/-!
## Main Definitions
- Statements of proximity results for Reed Solomon codes (`Lemma 4.3`, `Lemma 4.4` and `Lemma 4.5`
   from `[AHIV22]`

## References

* [Ames, S., Hazay, C., Ishai, Y., and Venkitasubramaniam, M., *Ligero: Lightweight sublinear
    arguments without a trusted setup*][AHIV22]
      * NB we use version 20221118:030830
-/

noncomputable section

open Code ProbabilityTheory

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]
         {κ : Type*} [Fintype κ]
         {ι : Type*} [Fintype ι]

local instance : Fintype F := Fintype.ofFinite F

/-- **Lemma 4.3, [AHIV22]**. Let `L` be an `[n, k, d]`-linear code over `𝔽`, `U⋆` be a WordStack in
`(𝔽ᵐ)ⁿ`. Let `e` be a positive integer such that `e < d/3` and `|𝔽| ≥ e`.
Suppose `d(U⋆, L^⋈m) > e`. Then, there exists `v⋆ ∈ L⋆` such that `d(v⋆, L) > e`, where `L⋆` is the
row-span of `U⋆`. -/
lemma distInterleavedCodeToCodeLB
    {L : LinearCode ι F} {U_star : WordStack (A := F) κ ι}
  {e : ℕ} -- Might change e to ℕ+ if really needed
  (hF : Fintype.card F ≥ e)
  (he : (e : ℚ≥0) < ‖(L : Set (ι → F))‖₀ / 3) -- `e < d/3`
  (hU : e < Δ₀(⋈|U_star, L^⋈κ)) : -- `d(U⋆, L^⋈ m) > e`, here we interleave U
    -- before using `Δ₀` for correct symbol specification
  ∃ v ∈ Matrix.rowSpan U_star , e < Δ₀(v, L) := by
  sorry

namespace ProximityToRS

open ReedSolomon NNReal

/-- The set of points on an affine line, which are within distance `e` from a Reed-Solomon code.
-/
def closePtsOnAffineLine {ι : Type*} [Fintype ι]
                         (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : Set (ι → F) :=
  {x : ι → F | x ∈ Affine.affineLineAtOrigin (F := F) (origin := u) (direction := v)
    ∧ Δ₀(x, ReedSolomon.code α deg) ≤ e}

/-- The number of points on an affine line between, which are within distance `e` from a
Reed-Solomon code.
-/
def numberOfClosePts (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : ℕ :=
  Fintype.card (closePtsOnAffineLine u v deg α e)

omit [DecidableEq F] in
/-- **Lemma 4.4, [AHIV22] (Combinatorial proximity gap for affine lines)**
Let `L = RS_{𝔽, n, k, η}` be a Reed-Solomon code with minimal distance
`d = n - k + 1`. Let `e` be a positive integer such that `e < d / 3`. Then for every two words
`u, v ∈ 𝔽^n`, defining an affine line `ℓ_{u, v} = {u + α v : α ∈ 𝔽}`.
**Either (i.e. mutually exclusive/XOR)**
- (1) for every `x ∈ ℓ_{u, v}` we have `d(x, L) ≤ e`,
- or (2) for at most `d` points `x ∈ ℓ_{u, v}` we have `d(x, L) ≤ e`.
This is a concrete statement via cardinality of proximity gap for affine lines.
-/
lemma e_leq_dist_over_3 [DecidableEq F] {deg : ℕ} {α : ι ↪ F} {e : ℕ} {u v : ι → F}
    (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3) :
  Xor'
    (∀ x ∈ Affine.affineLineAtOrigin (F := F) u v, Δ₀(x, ReedSolomon.code α deg) ≤ e)
    ((numberOfClosePts u v deg α e) ≤ ‖(RScodeSet α deg)‖₀) := by sorry

/-- **`Lemma 4.5` from `[AHIV22]`.** Let `L = RS_{𝔽, n, k, η}` be a Reed-Solomon code with minimal
distance `d = n - k + 1` and `e` a positive integer such that `e < d / 3`. Suppose `d(U⋆, L^m) > e`.
Then, for a random `w⋆` in the row-span of `U⋆`, we have: `Pr[d(w⋆, L) ≤ e] ≤ d / |𝔽|` -/
lemma probOfBadPts {deg : ℕ} {α : ι ↪ F} {e : ℕ} {U_star : WordStack (A := F) κ ι}
  (he : (e : ℚ≥0) < ‖(RScodeSet α deg)‖₀ / 3)
  (hU : e < Δ₀(⋈|U_star, (ReedSolomon.code α deg)^⋈κ)) :
  (PMF.uniformOfFintype (Matrix.rowSpan U_star)).toOuterMeasure
    {w_star | Δ₀(w_star, RScodeSet α deg) ≤ e} ≤ ‖(RScodeSet α deg)‖₀ /(Fintype.card F) := by
  sorry

end ProximityToRS
end

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter (Least Authority)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation

namespace Generator

open NNReal ProbabilityTheory

variable  {F : Type*} [Semiring F] [Fintype F] [DecidableEq F]
          {ι : Type*} [Fintype ι] [Nonempty ι]
          {parℓ : Type*} [Fintype parℓ]

/-- For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ`
    and linear code `C` the predicate `proximityCondition(r)` is true, if the linear
    combination f := ∑ⱼ rⱼ * fⱼ is within relative Hamming distance `δ` to the linear
    code `C`.  -/
noncomputable def proximityCondition
   (f : parℓ → ι → F) (δ : ℝ≥0) (GenFun : F → parℓ → F) (C : LinearCode ι F): F → Prop
   | r => δᵣ( (fun x => ∑ j : parℓ, (GenFun r j) * f j x) , C ) ≤ (δ : ℝ)


/-- A proximity generator for a linear code `C`, Definition 4.7 -/
structure ProximityGenerator
  (ι : Type) [Fintype ι] [Nonempty ι]
  (F : Type) [Semiring F] [Fintype F] [DecidableEq F] where
  -- Underlying linear code
  C         : LinearCode ι F
  -- Number of functions
  parℓ      : Type
  hℓ        : Fintype parℓ
  -- Generator function maps sampled randomness `r : 𝔽 ` to `parℓ`-tuples of field elements
  Fun       : F → parℓ → F
  -- Distance threshold parameter
  B         : (LinearCode ι F) → Type → ℝ
  -- Error function bounding the probability of distance within `δ`
  err       : (LinearCode ι F) → Type → ℝ → ENNReal
  /- Proximity:
      For all `parℓ`-tuples of functions `fᵢ : ι → 𝔽`
        and distance parameter `δ ∈ (0, 1-BStar(C,parℓ))` :
      If the probability that `proximityCondition(r)` is true for uniformly random
      sampled  `r ← 𝔽 `, exceeds `err(C,parℓ,δ)`, then there exists a  subset `S ⊆ ι ` of size
      `|S| ≥ (1-δ)⬝|ι|`) on which each `fᵢ` agrees with some codeword in `C`. -/
  proximity:
    ∀ (f : parℓ → ι → F)
      (δ : ℝ≥0)
      (_hδ : δ < 1 - (B C parℓ)) ,
      Pr_{ let r ← $ᵖ F }[ (proximityCondition f δ Fun C r) ] > (err C parℓ δ) →
        ∃ S : Finset ι,
          S.card ≥ (1 - δ) * (Fintype.card ι) ∧
        ∀ i : parℓ, ∃ u ∈ C, ∀ x ∈ S, f i x = u x

end Generator

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation

/-!
# Proximity Generators

This file formalizes the notion of proximity generators,
introduced in the [Section 4 of the WHIR paper][todo: ArkLib bibliography].

## Implementation notes

Todo?

## References

* G Arnon, A Chies, G Fenzi, and E Yogev,
  [*WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification*][todo: ArkLib bibliography]
Freely available at https://eprint.iacr.org/2024/1586

## Tags
Todo: should we aim to add tags?
-/

namespace Generator

open NNReal ProbabilityTheory

variable {F : Type*} [Semiring F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι] [Nonempty ι]
         {parℓ : Type*} [Fintype parℓ]

/-- For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ`
    and linear code `C` the predicate `proximityCondition(r)` is true, if the linear
    combination f := ∑ⱼ rⱼ * fⱼ is within relative Hamming distance `δ` to the linear
    code `C`.
-/
noncomputable def proximityCondition
   (f : parℓ → ι → F) (δ : ℝ) (r : parℓ → F) (C : LinearCode ι F) : Prop :=
  δᵣ( (fun x => ∑ j : parℓ, (r j) * f j x) , C ) ≤ (δ : ℝ)


/-- A proximity generator for a linear code `C`, Definition 4.7 -/
structure ProximityGenerator
  (ι : Type) [Fintype ι] [Nonempty ι]
  (F : Type) [Semiring F] [Fintype F] [DecidableEq F] where
  -- Underlying linear code
  C : LinearCode ι F
  -- Number of functions
  parℓ : Type
  hℓ : Fintype parℓ
  -- Generator function maps sampled randomness `r : 𝔽` to `parℓ`-tuples of field elements
  Gen : Finset (parℓ → F)
  Gen_nonempty : Nonempty Gen
  -- Rate
  rate : ℝ
  -- Distance threshold parameter
  B : (LinearCode ι F) → Type → ℝ
  -- Error function bounding the probability of distance within `δ`
  err : (LinearCode ι F) → Type → ℝ → ENNReal
  /- Proximity:
      For all `parℓ`-tuples of functions `fᵢ : ι → 𝔽`
        and distance parameter `δ ∈ (0, 1-B(C,parℓ))` :
      If the probability that `proximityCondition(r)` is true for uniformly random
      sampled  `r ← 𝔽 `, exceeds `err(C,parℓ,δ)`, then there exists a  subset `S ⊆ ι ` of size
      `|S| ≥ (1-δ)⬝|ι|`) on which each `fᵢ` agrees with some codeword in `C`. -/
  proximity:
    ∀ (f : parℓ → ι → F)
      (δ : ℝ≥0) -- temp added back ℝ≥0 to satisfy the type checker and allow the file to build,
      (_hδ : 0 < δ ∧ δ < 1 - (B C parℓ)) ,
      Pr_{ let r ← $ᵖ Gen }[ (proximityCondition f δ r C) ] > (err C parℓ δ) →
        ∃ S : Finset ι,
          S.card ≥ (1 - δ) * (Fintype.card ι) ∧
        ∀ i : parℓ, ∃ u ∈ C, ∀ x ∈ S, f i x = u x

end Generator

-- moved from ProximityGap.lean for convenience, will do a clean up pass later as required.
namespace RSGenerator

open Generator NNReal ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/- Theorem 4.8 [BCIKS20] Proximity Gap Theorem
  Smooth Reed Solomon codes C:= RSC[F,ι,m] have proximity generators for any given `parℓ`
   with generator function Gen(parℓ) : 𝔽 → parℓ → 𝔽 ; α → (1,α, α², …, α^{parℓ - 1}),
   B(C,parℓ) := √ρ
   err(C,parℓ,δ) :=  (parℓ-1)2ᵐ / ρ * |F| for δ in (0, (1-ρ)/2]
                     (parℓ-1)*2²ᵐ / (|F|(2 min{1-√ρ-δ, √ρ/20})⁷)
                      for δ in ((1-ρ)/ 2, 1 - B(C,parℓ)) -/
noncomputable def genRSC
  [Nonempty F] (parℓ : Type) [hℓ : Fintype parℓ] (φ : ι ↪ F) [Smooth φ]
  (m : ℕ) (exp : parℓ ↪ ℕ) : ProximityGenerator ι F :=
    let r := LinearCode.rate (smoothCode φ m);
    { C := smoothCode φ m,
      parℓ := parℓ,
      hℓ := hℓ,
      rate := r,
      Gen := Finset.image (fun r => (fun j => r ^ (exp j))) (Finset.univ : Finset F),
      Gen_nonempty := by
        constructor
        constructor
        · simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exists (Classical.ofNonempty)
      B := fun _ _ => (Real.sqrt r),
      err := fun _ _ δ =>
        ENNReal.ofReal (
          if 0 < δ ∧ δ ≤ (1 - r) / 2 then
            ((Fintype.card parℓ - 1) * 2^m) / (r * Fintype.card F)
          else
            let min_val := min (1 - (Real.sqrt r) - δ)
                               ((Real.sqrt r) / 20)
            ((Fintype.card parℓ - 1) * (2^(2 * m))) / ((Fintype.card F) * (2 * min_val)^7)
          ),
      proximity := by sorry
    }

end RSGenerator

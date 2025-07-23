/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das, Miguel Quaresma (Least Authority)
-/

import ArkLib.ProofSystem.Whir.ProximityGen
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Proximity Gap

This file formalizes the proximity gap theorem, introduced in the [Section 4 of the WHIR paper][todo: ArkLib bibliography].

## Implementation notes

Todo?

## References

* [G Arnon, A Chies, G Fenzi, and E Yogev, *WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification*][todo: ArkLib bibliography]
Freely available at https://eprint.iacr.org/2024/1586

## Tags
Todo: should we aim to add tags?
-/

namespace RSGenerator

open Generator NNReal ReedSolomon

variable   {F : Type} [Field F] [Fintype F] [DecidableEq F]
           {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def rate (φ : ι ↪ F) (m : ℕ) [Smooth φ] : ℝ :=
  LinearCode.rate (smoothCode φ m)


/- Theorem 4.8 [BCIKS20] Proximity Gap Theorem
  Smooth Reed Solomon codes C:= RSC[F,ι,m] have proximity generators for any given `parℓ`
   with generator function Gen(parℓ) : 𝔽 → parℓ → 𝔽 ; α → (1,α, α², …, α^{parℓ - 1}),
   B(C,parℓ) := √ρ
   err(C,parℓ,δ) :=  (parℓ-1)2ᵐ / ρ * |F| for δ in (0, (1-ρ)/2]
                     (parℓ-1)*2²ᵐ / (|F|(2 min{1-√ρ-δ, √ρ/20})⁷)
                      for δ in ((1-ρ)/ 2, 1 - B(C,parℓ)) -/
noncomputable def proximityGapTheorem
  (parℓ : Type) [hℓ : Fintype parℓ] (φ : ι ↪ F) [Smooth φ]
  (m : ℕ) {exp : parℓ ↪ ℕ} : ProximityGenerator ι F :=
    { C      := smoothCode φ m,
      parℓ   := parℓ,
      hℓ     := hℓ,
      Fun    := fun r j => r ^ (exp j),
      B      := fun _ _ => (Real.sqrt (rate φ m)),
      err    := fun _ _ δ =>
        ENNReal.ofReal (
          if 0 < δ ∧ δ ≤ (1 - (rate φ m)) / 2 then
          ((Fintype.card parℓ - 1) * 2^m) / ((rate φ m)  * Fintype.card F)
          else
            let min_val := min (1 - (Real.sqrt (rate φ m)) - δ)
                               ((Real.sqrt (rate φ m)) / 20)
            ((Fintype.card parℓ - 1) * (2^(2 * m))) / ((Fintype.card F) * (2 * min_val)^7)
          ),
      proximity := by sorry
    }

end RSGenerator

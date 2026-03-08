/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks, Petar Maksimović
-/

import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ProofSystem.Whir.ProximityGen


/-!
# Mutual Correlated Agreement for Proximity Generators

This file formalizes the notion of mutual correlated agreement for proximity generators,
introduced in Section 4 of [ACFY24].

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

## Implementation notes

The reference paper is phrased in terms of a minimum distance,
which should be understood as being the minimum relative hamming distance, which is used here.

## Tags
Todo: should we aim to add tags?
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
          {ι parℓ : Type} [Fintype ι] [Nonempty ι] [Fintype parℓ] [Nonempty parℓ]

/-- For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽`
    and linear code `C` the predicate `proximityCondition(r)` is true, if `∃ S ⊆ ι`, s.t.
    the following three conditions hold
      (i) `|S| ≥ (1-δ)*|ι|`
      (ii) `∃ u ∈ C, u(S) = ∑ j : parℓ, rⱼ * fⱼ(S)`
      (iii) `∃ i : parℓ, ∀ u' ∈ C, u'(S) ≠ fᵢ(S)` -/
def proximityCondition (f : parℓ → ι → F) (δ : ℝ≥0) (r : parℓ → F)
    (C : LinearCode ι F) : Prop :=
  ∃ S : Finset ι,
    (S.card : ℝ≥0) ≥ (1-δ) * Fintype.card ι ∧
    ∃ u ∈ C, ∀ s ∈ S, u s = ∑ j : parℓ, r j * f j s ∧
    ∃ i : parℓ, ∀ u' ∈ C, ∃ s ∈ S, u' s ≠ f i s

/-- Definition 4.9
  Let `C` be a linear code, then Gen is a proximity generator with mutual correlated agreement,
  if for `parℓ` functions `fᵢ : ι → F` and distance `δ < 1 - BStar(C,parℓ)`,
  `Pr_{ r ← F } [ proximityCondition(r) ] ≤ errStar(δ)`.

  Note that there is a typo in the paper:
  it should `δ < 1 - BStar(C,parℓ)` in place of `δ < 1 - B(C,parℓ)`
-/
noncomputable def hasMutualCorrAgreement
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (BStar : ℝ) (errStar : ℝ → ENNReal) :=
    haveI := Gen.Gen_nonempty
    ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0) (_hδ : 0 < δ ∧ δ < 1 - BStar),
    Pr_{let r ←$ᵖ Gen.Gen}[ proximityCondition f δ r Gen.C ] ≤ errStar δ

/-- Lemma 4.10
  Let `C` be a linear code with minimum distance `δ_C`, `Gen` be a proximity generator for C
  with parameters `B` and `err`, then Gen has mutual correlated agreement with proximity bounds
  `BStar = min {1 - δ_C/2, B}` and `errStar = err`.
-/
lemma mca_linearCode
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ] [Nonempty Gen.parℓ]
  (C : LinearCode ι F) (hC : C = Gen.C) :
    hasMutualCorrAgreement
     -- Gen
      Gen
    -- BStar (using δᵣ produced )
      (min (1 - (δᵣ (C : Set (ι → F))) / 2) (Gen.B Gen.C Gen.parℓ))
    -- errStar
      (fun δ => Gen.err C Gen.parℓ δ) := by sorry

/-- Corollary 4.11
  Let `C` be a (smooth) ReedSolomon Code with rate `ρ`, then the function
  `Gen(parℓ,α)={1,α,..,α^(parℓ-1)}` is a proximity generator for Gen with
  mutual correlated agreement with proximity bounds
    `BStar = (1+ρ) / 2`
    `errStar = (parℓ-1)*2^m / ρ*|F|`.

  function `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}`
-/

lemma mca_rsc
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ) :
  let Gen := RSGenerator.genRSC parℓ_type φ m exp
  let : Fintype Gen.parℓ := Gen.hℓ
  hasMutualCorrAgreement
    -- Generator
    Gen
    -- BStar
    ((1 + Gen.rate) / 2)
    -- errStar
    (fun δ => ENNReal.ofReal
        ((Fintype.card parℓ_type - 1) * (2^m / (Gen.rate * (Fintype.card F)))))
  := by sorry


/-- Conjecture 4.12 (Johnson Bound)
  The function `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}` is a proximity generator with
  mutual correlated agreement for every (smooth) ReedSolomon code `C` with rate `ρ = 2^m / |ι|`.
  1. Up to Johnson bound: BStar = √ρ and
                         errStar = (parℓ-1) * 2^2m / |F| * (2 * min {1 - √ρ - δ, √ρ/20}) ^ 7.
-/
theorem mca_johnson_bound_CONJECTURE
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ) :
  let Gen := RSGenerator.genRSC parℓ_type φ m exp
  let : Fintype Gen.parℓ := Gen.hℓ
  hasMutualCorrAgreement Gen
    -- Conjectured BStar = √ρ
    (Real.sqrt Gen.rate)
    -- Conjectured errStar
    (fun δ =>
      let min_val := min (1 - Real.sqrt Gen.rate - (δ : ℝ)) (Real.sqrt Gen.rate / 20)
      ENNReal.ofReal (
        ((Fintype.card parℓ_type - 1) * 2^(2*m)) /
        ((Fintype.card F) * (2 * min_val)^7)
      )
    )
  := by sorry

/-- Conjecture 4.12 (Capacity Bound)
  The function `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}` is a proximity generator with
  mutual correlated agreement for every (smooth) ReedSolomon code `C` with rate `ρ = 2^m / |ι|`.
  2. Up to capacity: BStar = ρ and ∃ c₁,c₂ ∈ ℕ s.t. ∀ η > 0 and 0 < δ < 1 - ρ - η
      errStar = (parℓ-1)^c₂ * d^c₂ / η^c₁ * ρ^(c₁+c₂) * |F|, where d = 2^m is the degree.

  N.b: there is a typo in the paper, c₃ is not needed and carried over from STIR paper definition
-/
theorem mca_capacity_bound_CONJECTURE
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ) :
  let Gen := RSGenerator.genRSC parℓ_type φ m exp
  let : Fintype Gen.parℓ := Gen.hℓ
  haveI := Gen.Gen_nonempty
  ∃ (c₁ c₂ : ℕ),
    ∀ (f : Gen.parℓ → ι → F) (η : ℝ) (_hη : 0 < η) (δ : ℝ≥0)
      (_hδ : 0 < δ ∧ δ < 1 - Gen.rate - η),
      Pr_{let r ←$ᵖ Gen.Gen}[ proximityCondition f δ r Gen.C ] ≤
        ENNReal.ofReal (
          (((Fintype.card parℓ_type - 1) : ℝ)^c₂ * ((2^m) : ℝ)^c₂) /
          (η^c₁ * Gen.rate^(c₁+c₂) * (Fintype.card F))
        )
  := by sorry

section

open ListDecodable

/-- For `parℓ` functions `{f₀,..,f_{parℓ - 1}}`,
  `IC` be the `parℓ`-interleaved code from a linear code C,
  with `Gen` as a proximity generator with mutual correlated agreement,
  `proximityListDecodingCondition(r)` is true if,
  `List(C, ∑ⱼ rⱼ * fⱼ, δ) ≠ `
  `{ ∑ⱼ rⱼ * uⱼ, where {u₀,..u_{parℓ-1}} ∈ Λᵢ({f₀,..,f_{parℓ-1}}, IC, δ) }` -/
def proximityListDecodingCondition (C : LinearCode ι F)
  [Fintype ι] [Nonempty ι]
  (r : parℓ → F) [Fintype parℓ]
  (δ : ℝ≥0) (fs : Matrix parℓ ι F) : Prop := -- fs is a WordStack
      let f_r := fun x => ∑ j, r j * fs j x
      let listHamming := closeCodewordsRel C f_r δ
      let listIC := { fun x => ∑ j, r j * (us.val j x) | us ∈ Λᵢ(fs, (C : Set (ι → F)), δ)}
      listHamming ≠ listIC


/-- Lemma 4.13: Mutual correlated agreement preserves list decoding
  Let C be a linear code with minimum distance δ_c and `Gen` be a proximity generator
  with mutual correlated agreement for `C`.
  Then for every `{f₀,..,f_{parℓ - 1}}` and `δ ∈ (0, min δ_c (1 - BStar))`,
  `Pr_{ r ← F} [ proximityListDecodingCondition(r) ] ≤ errStar(δ)`. -/
lemma mca_list_decoding
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (δ BStar : ℝ≥0) (errStar : ℝ → ENNReal)
  (fs us : Matrix Gen.parℓ ι F)
  (hGen : hasMutualCorrAgreement Gen BStar errStar)
  (C : Set (ι → F)) (hC : C = Gen.C) :
    haveI := Gen.Gen_nonempty
    ∀ {fs : Matrix Gen.parℓ ι F}
    (hδPos : δ > 0) (hδLt : δ < min ((δᵣ C) : ℝ≥0) (1 - BStar)),
      Pr_{let r ←$ᵖ Gen.Gen}[ proximityListDecodingCondition Gen.C r δ fs ]
        ≤ errStar δ
  := by sorry

end

end MutualCorrAgreement

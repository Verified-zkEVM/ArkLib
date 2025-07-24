/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks,  Petar Maksimović
-/

import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ProofSystem.Whir.ProximityGen


/-!
# Mutual Correlated Agreement for Proximity Generators

This file formalizes the notion of mutual correlated agreement for proximity generators,
introduced in the [Section 4 of the WHIR paper][todo: ArkLib bibliography].

## Implementation notes

The reference paper is phrased in terms of a minimum distance,
which should be understood as being the minimum relative hamming distance, which is used here.

## References

* [G Arnon, A Chies, G Fenzi, and E Yogev, *WHIR: Reed–Solomon Proximity Testing with Super-Fast Verification*][todo: ArkLib bibliography]
Freely available at https://eprint.iacr.org/2024/1586

## Tags
Todo: should we aim to add tags?
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon

variable  {F : Type} [Field F] [Fintype F] [DecidableEq F]
          {ι parℓ : Type} [Fintype ι] [Nonempty ι] [Fintype parℓ] [Nonempty parℓ]

/-- For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽`
    and linear code `C` the predicate `proximityCondition(r)` is true, if `∃ S ⊆ ι`, s.t.
    the following three conditions hold
      (i) `|S| ≥ (1-δ)*|ι|`
      (ii) `∃ u ∈ C, u(S) = ∑ j : parℓ, rⱼ * fⱼ(S)`
      (iii) `∃ i : parℓ, ∀ u' ∈ C, u'(S) ≠ fᵢ(S)` -/
def proximityCondition (f : parℓ → ι → F) (δ : ℝ≥0) (GenFun : F → parℓ → F)
  (C : LinearCode ι F): F → Prop
    | r =>
      ∃ S : Finset ι,
      (S.card : ℝ≥0) ≥ (1-δ) * Fintype.card ι ∧
      ∃ u ∈ C, ∀ s ∈ S, u s = ∑ j : parℓ, GenFun r j * f j s ∧
      ∃ i : parℓ, ∀ u' ∈ C, ∃ s ∈ S, u' s ≠ f i s

/-- Definition 4.9
  Let `C` be a linear code, then Gen is a proximity generator with mutual correlated agreement,
  if for `parℓ` functions `fᵢ : ι → F` and distance `δ < 1 - BStar(C,parℓ)`,
  `Pr_{ r ← F } [ proximityCondition(r) ] ≤ errStar(δ)`.

  Note that there is a typo in the paper:
  it should `δ < 1 - BStar(C,parℓ)` in place of `δ < 1 - B(C,parℓ)`
-/

noncomputable def MutualCorrAgreement
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (BStar : ℝ) (errStar : ℝ → ENNReal) :=
    ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0) (_hδ : δ < 1 - BStar),
    Pr_{let r ←$ᵖ F}[ (proximityCondition f δ Gen.Fun Gen.C) r ] ≤ errStar δ

/-- Lemma 4.10
  Let `C` be a linear code with minimum distance `δ_C`, `Gen` be a proximity generator for C
  with parameters `B` and `err`, then Gen has mutual correlated agreement with proximity bounds
  `BStar = min {1 - δ_C/2, B}` and `errStar = err`.
-/
lemma mca_linearCode
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ] [Nonempty Gen.parℓ]
  (C : LinearCode ι F) (hC : C = Gen.C) :
    MutualCorrAgreement
     -- Gen
      Gen
    -- BStar
      (min (1 - Code.minRelHammingDistCode (C : Set (ι → F)) / 2) (Gen.B Gen.C Gen.parℓ))
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
  [DecidableEq ι]
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ) :
  let Gen := RSGenerator.genRSC parℓ_type φ m (exp := exp)
  let : Fintype Gen.parℓ := Gen.hℓ
  let rate := LinearCode.rate (smoothCode φ m)
  MutualCorrAgreement
    -- Generator
    Gen
    -- BStar
    ((1 + rate) / 2)
    -- errStar
    (fun δ => ENNReal.ofReal
        ((Fintype.card parℓ_type - 1) * (2^m / (rate * (Fintype.card F)))))
  := by sorry


/-- Conjecture 4.12 (Johnson Bound)
  The function `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}` is a proximity generator with
  mutual correlated agreement for every (smooth) ReedSolomon code `C` with rate `ρ = 2^m / |ι|`.
  1. Up to Johnson bound: BStar = √ρ and
                         errStar = (parℓ-1) * 2^2m / |F| * (2 * min {1 - √ρ - δ, √ρ/20}) ^ 7.
-/
theorem mca_johnson_bound_CONJECTURE
  [DecidableEq ι]
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ) :
  let Gen := RSGenerator.genRSC parℓ_type φ m (exp := exp)
  let : Fintype Gen.parℓ := Gen.hℓ
  let rate := LinearCode.rate Gen.C
  MutualCorrAgreement Gen
    -- Conjectured BStar = √ρ
    (Real.sqrt rate)
    -- Conjectured errStar
    (fun δ =>
      let min_val := min (1 - Real.sqrt rate - (δ : ℝ)) (Real.sqrt rate / 20)
      ENNReal.ofReal (
        ((Fintype.card parℓ_type - 1) * 2^(2*m)) /
        ((Fintype.card F) * (2 * min_val)^7)
      )
    )
  := by sorry

/-- Conjecture 4.12 (Capacity Bound)
  The function `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}` is a proximity generator with
  mutual correlated agreement for every (smooth) ReedSolomon code `C` with rate `ρ = 2^m / |ι|`.
  2. Up to capacity: BStar = ρ and ∃ c₁,c₂,c₃ ∈ ℕ s.t. ∀ η > 0 and 0 < δ < 1 - ρ - η
      errStar = (parℓ-1)^c₂ * d^c₂ / η^c₁ * ρ^(c₁+c₂) * |F|, where d = 2^m is the degree. -/
theorem mca_capacity_bound_CONJECTURE
  [DecidableEq ι]
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ]
  (parℓ_type : Type) [Fintype parℓ_type] (exp : parℓ_type ↪ ℕ) :
  let Gen := RSGenerator.genRSC parℓ_type φ m (exp := exp)
  let : Fintype Gen.parℓ := Gen.hℓ
  let rate := LinearCode.rate Gen.C
  ∃ (c₁ c₂ c₃ : ℕ),
    ∀ (f : Gen.parℓ → ι → F) (η : ℝ) (_hη : 0 < η) (δ : ℝ≥0)
      (_hδ : δ < 1 - rate - η),
      Pr_{let r ←$ᵖ F}[ (proximityCondition f δ Gen.Fun Gen.C) r ] ≤
        ENNReal.ofReal (
          (((Fintype.card parℓ_type - 1) : ℝ)^c₂ * ((2^m) : ℝ)^c₂) /
          (η^c₁ * rate^(c₁+c₂) * (Fintype.card F))
        )
  := by sorry

section

open InterleavedCode ListDecodable

/-- For `parℓ` functions `{f₀,..,f_{parℓ - 1}}`,
  `IC` be the `parℓ`-interleaved code from a linear code C,
  with `Gen` as a proximity generator with mutual correlated agreement,
  `proximityListDecodingCondition(r)` is true if,
  List(C, ∑ⱼ rⱼ * fⱼ, δ) ≠ { ∑ⱼ rⱼ * uⱼ, where {u₁,..u_parℓ} ∈ Λᵢ({f₁,..,f_parℓ}, IC, δ) } -/
def proximityListDecodingCondition
  [Fintype ι] [Nonempty ι]
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (δ : ℝ) (fs : Matrix Gen.parℓ ι F)
  (IC : InterleavedCode Gen.parℓ ι F) : F → Prop :=
    fun r =>
      let f_r := fun x => ∑ j, Gen.Fun r j * fs j x
      let listHamming := relHammingBall Gen.C f_r δ
      let listIC := { fun x => ∑ j, Gen.Fun r j * us j x | us ∈ Λᵢ(fs, IC.MF, δ)}
      listHamming ≠ listIC


/-- Lemma 4.13: Mutual correlated agreement preserves list decoding
  Let C be a linear code with minimum distance δ_c and `Gen` be a proximity generator
  with mutual correlated agreement for `C`.
  Then for every `{f₀,..,f_{parℓ - 1}}` and `δ ∈ (0, min δ_c (1 - BStar))`,
  `Pr_{ r ← F} [ proximityListDecodingCondition(r) ] ≤ errStar(δ)`. -/
lemma mca_list_decoding
  [Fintype ι] [Nonempty ι]
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (δ BStar : ℝ) (errStar : ℝ → ENNReal)
  (fs us : Matrix Gen.parℓ ι F)
  (IC : InterleavedCode Gen.parℓ ι F)
  (haveIC : IC = codeOfLinearCode Gen.parℓ Gen.C)
  (hGen : MutualCorrAgreement Gen BStar errStar)
  (C : Set (ι → F)) (hC : C = Gen.C) :
    ∀ {fs : Matrix Gen.parℓ ι F}
    (hδPos : δ > 0) (hδLt : δ < min (δᵣ C : ℝ) (1 - BStar)),
      Pr_{let r ←$ᵖ F}[ proximityListDecodingCondition Gen δ fs IC r]
        ≤ errStar δ
  := by sorry

end

end MutualCorrAgreement

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Whir.ProximityGen

namespace CorrelatedAgreement

open NNReal Generator ProbabilityTheory ReedSolomon

variable  {F : Type} [Field F] [Fintype F] [DecidableEq F]
          {ι parℓ : Type} [Fintype ι] [Nonempty ι] [Fintype parℓ]

/-- For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽`
    and linear code `C` the predicate `proximityCondition(r)` is true, if `∃ S ⊆ ι`, s.t.
    the following three conditions hold
      (i) `|S| > (1-δ)*|ι|` and
      (ii) `∃ u ∈ C, u(S) = ∑ j : parℓ, rⱼ * fⱼ(S)`
      (iii) `∃ i : parℓ, ∀ u' ∈ C, u'(S) ≠ fᵢ(S)` -/
def proximityCondition (f : parℓ → ι → F) (δ : ℝ≥0) (GenFun : F → parℓ → F)
  (C : LinearCode ι F): F → Prop
    | r =>
      ∃ S : Finset ι,
      (S.card : ℝ≥0) > (1-δ) * Fintype.card ι ∧
      ∃ u ∈ C, ∀ s ∈ S, u s = ∑ j : parℓ, GenFun r j * f j s ∧
      ∃ i : parℓ, ∀ u' ∈ C, ∀ s ∈ S, u' s ≠ f i s

/-- Definition 4.9
  Let `C` be a linear code, then Gen is a proximity generator with mutual correlated agreement,
  if for `parℓ` functions `fᵢ : ι → F` and distance `δ < 1 - B(C,parℓ)`,
  `Pr_{ r ← F } [ proximityCondition(r) ] ≤ errStar(δ)`. -/
noncomputable def genMutualCorrAgreement
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (BStar : ℝ) (errStar : ℝ → ENNReal) :=
    ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0) (_hδ : δ < 1 - (Gen.B Gen.C Gen.parℓ)),
    Pr_{let r ←$ᵖ F}[ (proximityCondition f δ Gen.Fun Gen.C) r ] ≤ errStar δ

/--Lemma 4.10
  Let `C` be a linear code with minimum distance `δ_C`, `Gen` be a proximity generator for C
  with parameters `B` and `err`, then Gen has mutual correlated agreement with proximity bounds
  `BStar = min {1 - δ_C/2, B}` and `errStar = err`. -/
lemma genMutualCorrAgreement_le_bound
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (BStar : ℝ) (errStar : ℝ → ENNReal)
  (C : Set (ι → F)) (hC : C = Gen.C)
  (h: genMutualCorrAgreement Gen BStar errStar) :
    BStar < min (1 - (δᵣ C) / 2 : ℝ) (Gen.B Gen.C Gen.parℓ)
    ∧
    errStar = Gen.err Gen.C Gen.parℓ := by sorry

/--Corollary 4.11
  Let `C` be a (smooth) ReedSolomon Code with rate `ρ`, then the function
  `Gen(parℓ,α)={1,α,..,α^(parℓ-1)}` is a proximity generator for Gen with
  mutual correlated agreement with proximity bounds
    `BStar = (1+ρ) / 2`
    `errStar = (parℓ-1)*2^m / ρ*|F|`.

  function `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}`-/
noncomputable def gen_α (α : F) (parℓ : Type) (exp : parℓ → ℕ): F → parℓ → F :=
  fun _ j => α ^ (exp j)

/--the proximity generator for smooth ReedSolomon codes wrt function
  `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}`-/
noncomputable def proximityGenerator_α
  [DecidableEq ι] (Gen : ProximityGenerator ι F) [hℓ : Fintype Gen.parℓ]
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Gen.parℓ → ℕ) :
  ProximityGenerator ι F :=
  {
    C := smoothCode φ m,
    parℓ := Gen.parℓ,
    hℓ := hℓ,
    Fun := gen_α α Gen.parℓ exp,
    B := Gen.B,
    err := Gen.err,
    proximity := by
      intro f δ hδ hprob
      sorry
  }

/--Corollary 4.11
  Let `C` be a smooth ReedSolomon code with rate `ρ`, then `Gen_α` is the proximity generator with
  mutual correlated agreement with bounds
    BStar = (1-ρ) / 2
    errStar = (parℓ-1)*2^m / ρ*|F|. -/
lemma genMutualCorrAgreement_rsc_le_bound
  [DecidableEq ι] (Gen Gen_α: ProximityGenerator ι F)
  [Fintype Gen.parℓ] [Fintype Gen_α.parℓ]
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Gen.parℓ → ℕ)
  (BStar rate : ℝ) (errStar : ℝ → ENNReal)
  -- `Gen_α` is the proximity generator wrt function `Gen(parℓ, α)`
  (hGen : Gen_α = proximityGenerator_α Gen α φ m exp)
  -- the proof that `Gen_α` is the proximity generator with mutual correlated agreement
  -- with proximity bound parameters BStar and errStar
  (h : genMutualCorrAgreement Gen_α BStar errStar)
  (hrate : rate = LinearCode.rate (smoothCode φ m)) :
    BStar = (1 - rate) / 2 ∧
    errStar = fun _ => ENNReal.ofReal
        ((Fintype.card Gen.parℓ - 1) * (2^m / rate * (Fintype.card F)))
  := by sorry


/--Conjecture 4.12
  The function `Gen(parℓ,α)={1,α,..,α ^ parℓ-1}` is a proximity generator with
  mutual correlated agreement for every (smooth) ReedSolomon code `C` with rate `ρ = 2^m / |ι|`.
  Below we state two conjectures for the parameters of the proximity bound.

  1. Upto Johnson bound: BStar = √ρ and
                         errStar = (parℓ-1) * 2^2m / |F| * (2 * min {1 - √ρ - δ, √ρ/20}) ^ 7.-/
theorem genMutualCorrAgreement_le_johnsonBound
  [DecidableEq ι] (Gen Gen_α: ProximityGenerator ι F)
  [Fintype Gen.parℓ] [Fintype Gen_α.parℓ]
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Gen.parℓ → ℕ)
  (BStar rate δ: ℝ) (errStar : ℝ → ENNReal)
  (hGen : Gen_α = proximityGenerator_α Gen α φ m exp)
  (h : genMutualCorrAgreement Gen_α BStar errStar)
  (hrate : rate = LinearCode.rate (smoothCode φ m)) :
    let minval := min (1 - Real.sqrt rate - δ) (Real.sqrt rate / 20)
    BStar = Real.sqrt rate ∧
    ∀ {η : ℝ≥0} (hδPos : δ > 0) (hδLe : δ < 1 - Real.sqrt rate - η),
      errStar = fun δ =>
        ENNReal.ofReal
          ((Fintype.card Gen.parℓ - 1) * 2 ^ (2 * m) / (Fintype.card ι * (2 * minval)^7))
  := by sorry

/--2. Upto capacity: BStar = ρ and ∃ c₁,c₂,c₃ ∈ ℕ s.t. ∀ η > 0 and 0 < δ < 1 - ρ - η
      errStar = (parℓ-1)^c₂ * d^c₂ / η^c₁ * ρ^(c₁+c₂) * |F|, where d = 2^m is the degree.-/
theorem genMutualCorrAgreement_le_capacity
  [DecidableEq ι] (Gen Gen_α: ProximityGenerator ι F)
  [Fintype Gen.parℓ] [Fintype Gen_α.parℓ]
  (α : F) (φ : ι ↪ F) (m : ℕ) [Smooth φ] (exp : Gen.parℓ → ℕ)
  (BStar rate δ: ℝ) (errStar : ℝ → ENNReal)
  (hGen : Gen_α = proximityGenerator_α Gen α φ m exp)
  (h : genMutualCorrAgreement Gen_α BStar errStar)
  (hrate : rate = LinearCode.rate (smoothCode φ m)) :
    BStar = rate ∧
    ∃ (c₁ c₂ c₃ : ℕ), ∀ {η : ℝ≥0} (hδPos : δ > 0) (hδLe : δ < 1 - rate - η),
      errStar = fun δ => ENNReal.ofReal
        ((Fintype.card Gen.parℓ - 1)^c₂ * (2^m)^c₂ / (η^c₁ * rate^(c₁+c₂) * (Fintype.card ι)))
  := by sorry

section

open InterleavedCode ListDecodable

/--For `parℓ` functions `{f₁,..,f_parℓ}`, `IC` be the `parℓ`-interleaved code from a linear code C,
  with `Gen` as a proximity generator with mutual correlated agreement,
  `proximityListDecodingCondition(r)` is true if,
  List(C, ∑ⱼ rⱼ*fⱼ, δ) ≠ { ∑ⱼ rⱼ*uⱼ, where {u₁,..u_parℓ} ∈ Λᵢ({f₁,..,f_parℓ}, IC, δ) } -/
def proximityListDecodingCondition
  [Fintype ι] [Nonempty ι]
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (δ : ℝ) (fs us : Matrix Gen.parℓ ι F)
  (IC : InterleavedCode Gen.parℓ ι F)
  (haveIC : IC = codeOfLinearCode Gen.parℓ Gen.C) : F → Prop :=
    fun r =>
      let f_r := fun x => ∑ j, Gen.Fun r j * fs j x
      let listHamming := relHammingBall Gen.C f_r δ
      let listIC := { fun x => ∑ j, Gen.Fun r j * us j x | us ∈ Λᵢ(fs, IC.MF, δ)}
      listHamming ≠ listIC


/--lemma 4.13: Mutual correlated agreement preserves list decoding
  Let C be a linear code with minimum distance δ_c and `Gen` be a proximity generator
  with mutual correlated agreement for `C`.
  Then for every `{f₁,..,f_parℓ}` and `δ ∈ (0, min δ_c (1 - BStar))`,
  `Pr_{ r ← F} [ proximityListDecodingCondition(r) ] ≤ errStar(δ)`. -/
lemma mutualCorrAgreement_list_decoding
  [Fintype ι] [Nonempty ι]
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (δ BStar : ℝ) (errStar : ℝ → ENNReal)
  (fs us : Matrix Gen.parℓ ι F)
  (IC : InterleavedCode Gen.parℓ ι F)
  (haveIC : IC = codeOfLinearCode Gen.parℓ Gen.C)
  (hGen : genMutualCorrAgreement Gen BStar errStar)
  (C : Set (ι → F)) (hC : C = Gen.C) :
    ∀ {fs : Matrix Gen.parℓ ι F}
    (hδPos : δ > 0) (hδLt : δ < min (δᵣ C : ℝ) (1 - BStar)),
      Pr_{let r ←$ᵖ F}[ proximityListDecodingCondition Gen δ fs us IC haveIC r]
        ≤ errStar δ
  := by sorry

end

end CorrelatedAgreement

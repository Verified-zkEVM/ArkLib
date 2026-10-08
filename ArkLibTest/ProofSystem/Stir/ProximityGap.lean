/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.FieldTheory.Finite.Basic
import ArkLib.ProofSystem.Stir.ProximityGap
import ArkLib.ProofSystem.Stir.Quotienting

/-!
# STIR proximity gap: the coefficients are the powers of `r`

`proximity_gap` (Theorem 4.1 of [ACFY24stir]) combines `f₀, …, f_{m-1}` as `∑ⱼ rʲ * fⱼ`. It used
to take the coefficients as a free function `GenFun`, and `GenFun = 0` made it false (#1284).

For `m = 1` the combination is `f₀` itself and `err⋆` is `0`, so the hypothesis of
`proximity_gap` reads `δᵣ(f₀, C) ≤ δ` (`prob_hypothesis_one_iff`). This gives:
* `proximity_gap_one`: the `m = 1` case of the statement is provable;
* `not_prob_hypothesis_counterexample`: the data that refuted the statement with `GenFun = 0`
  does not satisfy the hypothesis any more.

Two of its hypotheses are needed too, with data for which the other hypotheses hold and the
conclusion fails: `hδLt : δ < 1 - B⋆(ρ)` (`proximity_gap_fails_at_proximity_bound`, at
`δ = 1 - B⋆(ρ)`) and `0 < degree` (`proximity_gap_fails_for_degree_zero`: `err⋆` divides by the
rate, and `x / 0 = 0`).

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open NNReal ProbabilityTheory ReedSolomon STIR

namespace ArkLibTest.StirProximityGap

/-- For `m = 1` the error `err⋆` is zero. -/
lemma proximityError_one {F : Type} [Fintype F] (d : ℕ) (ρ δ : ℝ≥0) :
    proximityError F d ρ δ 1 = 0 := by
  unfold proximityError
  split_ifs <;> simp

/-- For `m = 1` the probability hypothesis of `proximity_gap` says that `f 0` is `δ`-close to the
code: the combination does not depend on `r`. -/
lemma prob_hypothesis_one_iff {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F} {degree : ℕ} {δ : ℝ≥0}
    (f : Fin 1 → ι → F) :
    Pr{let r ← $ᵗ F}[δᵣ((fun x => ∑ j : Fin 1, r ^ (j : ℕ) * f j x), code φ degree) ≤ δ] >
        ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ 1) ↔
      δᵣ(f 0, (code φ degree : Set (ι → F))) ≤ δ := by
  simp only [proximityError_one]
  by_cases h : δᵣ(f 0, (code φ degree : Set (ι → F))) ≤ δ
  · simp [h]
  · simp [h]

/-- The `m = 1` case of `proximity_gap` is provable: the hypothesis says that `f 0` is `δ`-close to
the code, and `S` is the agreement set of `f 0` with a closest codeword. -/
theorem proximity_gap_one {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F} {degree : ℕ} {δ : ℝ≥0}
    (f : Fin 1 → ι → F)
    (hProb :
      Pr{let r ← $ᵗ F}[δᵣ((fun x => ∑ j : Fin 1, r ^ (j : ℕ) * f j x), code φ degree) ≤ δ] >
        ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ 1)) :
    ∃ S : Finset ι,
      S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∀ i : Fin 1, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x := by
  have hd := (prob_hypothesis_one_iff (φ := φ) (degree := degree) (δ := δ) f).1 hProb
  obtain ⟨g, hg, hdist⟩ := Quotienting.exists_polynomial_relDistFromCode_eq φ degree (f 0)
  set v := evalOnPoints φ g with hv
  have hvmem : v ∈ code φ degree := mem_code_iff_exists_polynomial.2 ⟨g, hg, rfl⟩
  rw [hdist] at hd
  have hn0 : (Fintype.card ι : ENNReal) ≠ 0 := by simp
  have hnt : (Fintype.card ι : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hn0 hnt] at hd
  have h1 : (hammingDist (f 0) v : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast hd
  refine ⟨Finset.univ.filter (fun x => f 0 x = v x), ?_, fun i => ⟨v, hvmem, ?_⟩⟩
  · have e : (Finset.univ.filter (fun x => f 0 x = v x)).card + hammingDist (f 0) v =
        Fintype.card ι := by
      simpa [hammingDist, add_comm] using
        Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => f 0 x = v x)
    have e' : ((Finset.univ.filter (fun x => f 0 x = v x)).card : ℝ≥0) + hammingDist (f 0) v =
        Fintype.card ι := by exact_mod_cast e
    rw [ge_iff_le, tsub_mul, one_mul]
    calc (Fintype.card ι : ℝ≥0) - δ * Fintype.card ι
        ≤ (Fintype.card ι : ℝ≥0) - hammingDist (f 0) v := tsub_le_tsub_left h1 _
      _ = _ := by rw [← e']; simp
  · intro x hx
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact (Finset.mem_filter.1 hx).2

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Four distinct evaluation points of `ZMod 5`. -/
private def pts : Fin 4 ↪ ZMod 5 := ⟨fun i => ((i : ℕ) : ZMod 5), by decide⟩

/-- A function with four distinct values. -/
private def counterexample : Fin 1 → Fin 4 → ZMod 5 := fun _ i => ((i : ℕ) : ZMod 5)

/-- A word with four distinct values is at distance at least `3/4` from the degree-`1` code
(the constants) on four points. -/
private lemma counterexample_far :
    ¬ δᵣ(counterexample 0, (code pts 1 : Set (Fin 4 → ZMod 5))) ≤ ((1 / 4 : ℝ≥0) : ENNReal) := by
  intro h
  obtain ⟨g, hg, hdist⟩ := Quotienting.exists_polynomial_relDistFromCode_eq pts 1 (counterexample 0)
  rw [hdist, ENNReal.div_le_iff (by simp) (ENNReal.natCast_ne_top _)] at h
  have hconst : g = Polynomial.C (g.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hg))
  have hfar : ∀ c : ZMod 5, 3 ≤ hammingDist (counterexample 0) (fun _ => c) := by
    unfold counterexample
    decide
  have h3 := hfar (g.coeff 0)
  have hev : evalOnPoints pts g = fun _ => g.coeff 0 := by
    funext x
    conv_lhs => rw [hconst]
    simp [evalOnPoints]
  rw [hev] at h
  have h' : (hammingDist (counterexample 0) (fun _ => g.coeff 0) : ℝ≥0) ≤
      (1 / 4 : ℝ≥0) * (Fintype.card (Fin 4) : ℝ≥0) := by
    exact_mod_cast h
  simp at h'
  omega

/-- The data of the counterexample to the statement with a free generator (`F = ZMod 5`, four
points, degree `1`, `m = 1`, `δ = 1/4`, `f` injective) does not satisfy the hypothesis of
`proximity_gap`: with the powers of `r` as coefficients the combination is `f` itself, which is not
`1/4`-close to a constant. -/
theorem not_prob_hypothesis_counterexample :
    ¬ (Pr{let r ← $ᵗ (ZMod 5)}[
          δᵣ((fun x => ∑ j : Fin 1, r ^ (j : ℕ) * counterexample j x), code pts 1) ≤
            (1 / 4 : ℝ≥0)] >
        ENNReal.ofReal (proximityError (ZMod 5) 1 (LinearCode.rate (code pts 1)) (1 / 4) 1)) :=
  fun h => counterexample_far ((prob_hypothesis_one_iff counterexample).1 h)

private lemma rate_eq : LinearCode.rate (code pts 1) = 1 / 4 := by
  rw [rateOfLinearCode_eq_min_div]
  norm_num

private lemma bstar_rate : Bstar (LinearCode.rate (code pts 1)) = 1 / 2 := by
  rw [rate_eq]
  unfold Bstar
  rw [NNReal.sqrt_eq_iff_eq_sq]
  push_cast
  norm_num

/-- At `δ = 1 - √ρ` the error `err⋆` is `0`. -/
private lemma err_at_bound :
    proximityError (ZMod 5) 1 (LinearCode.rate (code pts 1)) (1 / 2) 2 = 0 := by
  unfold proximityError
  rw [rate_eq]
  have hs : NNReal.sqrt ((1 / 4 : ℚ≥0) : ℝ≥0) = 1 / 2 := by
    rw [NNReal.sqrt_eq_iff_eq_sq]
    push_cast
    norm_num
  have h1 : ¬ ((1 / 2 : ℝ≥0) ≤ (1 - ((1 / 4 : ℚ≥0) : ℝ≥0)) / 2) := by
    push_cast
    have h34 : (1 - 1 / 4 : ℝ≥0) = 3 / 4 := tsub_eq_of_eq_add (by norm_num)
    rw [h34]
    norm_num
  have h2 : ¬ ((1 / 2 : ℝ≥0) < 1 - NNReal.sqrt ((1 / 4 : ℚ≥0) : ℝ≥0)) := by
    rw [hs]
    have h12 : (1 - 1 / 2 : ℝ≥0) = 1 / 2 := tsub_eq_of_eq_add (by norm_num)
    rw [h12]
    exact lt_irrefl _
  simp only [h1, h2, ite_false]


/-- Two functions on the four points. -/
private def f₂ : Fin 2 → Fin 4 → ZMod 5 := ![![0, 1, 0, 1], ![0, 0, 1, 1]]

/-- The words of the degree-`1` code are constant. -/
private lemma const_of_mem {u : Fin 4 → ZMod 5} (hu : u ∈ code pts 1) (x y : Fin 4) :
    u x = u y := by
  obtain ⟨p, hp, hpu⟩ := mem_code_iff_eval_of_ne_zero.mp hu
  rw [← hpu x, ← hpu y, Polynomial.eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hp)]
  simp

/-- `f₂ 0` is `1/2`-close to the code: it agrees with `0` on two of the four points. -/
private lemma f₂_zero_close :
    δᵣ(f₂ 0, (code pts 1 : Set (Fin 4 → ZMod 5))) ≤ ((1 / 2 : ℝ≥0) : ENNReal) := by
  refine (Code.relDistFromCode_le_relDist_to_mem (f₂ 0) (0 : Fin 4 → ZMod 5)
    (Submodule.zero_mem _)).trans ?_
  have h2 : hammingDist (f₂ 0) (0 : Fin 4 → ZMod 5) = 2 := by
    unfold f₂
    decide
  have h3 : δᵣ(f₂ 0, (0 : Fin 4 → ZMod 5)) = (1 / 2 : ℚ≥0) := by
    unfold Code.relHammingDist
    rw [h2]
    norm_num
  rw [h3, ← ENNReal.coe_nnratCast]
  exact ENNReal.coe_le_coe.2 (by norm_num)

/-- `hδLt` is needed. At `δ = 1 - √ρ`, the endpoint that `hδLt` excludes, the other hypotheses hold
(`F = ZMod 5`, four points, degree `1`, `m = 2`, `δ = 1/2`, and `err⋆ = 0` there), but no set `S` of
size `2` has both functions constant on it. -/
theorem proximity_gap_fails_at_proximity_bound :
    (1 / 2 : ℝ≥0) = 1 - Bstar (LinearCode.rate (code pts 1)) ∧
    0 < (1 / 2 : ℝ≥0) ∧
    Pr{let r ← $ᵗ (ZMod 5)}[
        δᵣ((fun x => ∑ j : Fin 2, r ^ (j : ℕ) * f₂ j x), code pts 1) ≤ (1 / 2 : ℝ≥0)] >
      ENNReal.ofReal (proximityError (ZMod 5) 1 (LinearCode.rate (code pts 1)) (1 / 2) 2) ∧
    ¬ ∃ S : Finset (Fin 4), S.card ≥ (1 - (1 / 2 : ℝ≥0)) * (Fintype.card (Fin 4)) ∧
        ∀ i : Fin 2, ∃ u : Fin 4 → ZMod 5, u ∈ code pts 1 ∧ ∀ x ∈ S, f₂ i x = u x := by
  have h12 : (1 - 1 / 2 : ℝ≥0) = 1 / 2 := tsub_eq_of_eq_add (by norm_num)
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · rw [bstar_rate, h12]
  · rw [err_at_bound, NNReal.coe_zero, ENNReal.ofReal_zero]
    refine (SampleableType.prEvent_uniformSample_pos_iff _).2 ⟨0, ?_⟩
    have hf : (fun x => ∑ j : Fin 2, (0 : ZMod 5) ^ (j : ℕ) * f₂ j x) = f₂ 0 := by
      funext x
      simp [Fin.sum_univ_two]
    rw [hf]
    exact f₂_zero_close
  · rintro ⟨S, hS, h⟩
    have h2 : 2 ≤ S.card := by
      rw [ge_iff_le, h12] at hS
      have : (2 : ℝ≥0) ≤ S.card := by
        convert hS using 1
        simp
        norm_num
      exact_mod_cast this
    have key : ∀ S : Finset (Fin 4), 2 ≤ S.card →
        ∃ x ∈ S, ∃ y ∈ S, f₂ 0 x ≠ f₂ 0 y ∨ f₂ 1 x ≠ f₂ 1 y := by
      unfold f₂
      decide
    obtain ⟨x, hx, y, hy, hne⟩ := key S h2
    obtain ⟨u0, hu0, h0⟩ := h 0
    obtain ⟨u1, hu1, h1⟩ := h 1
    rcases hne with hne | hne
    · exact hne ((h0 x hx).trans ((const_of_mem hu0 x y).trans (h0 y hy).symm))
    · exact hne ((h1 x hx).trans ((const_of_mem hu1 x y).trans (h1 y hy).symm))

/-- Two functions on the four points. -/
private def g₂ : Fin 2 → Fin 4 → ZMod 5 := ![![1, 0, 0, 0], ![0, 1, 1, 0]]

/-- The code of degree `0` has rate `0`. -/
private lemma rate_zero : LinearCode.rate (code pts 0) = 0 := by
  rw [rateOfLinearCode_eq_min_div]
  norm_num

/-- With degree `0`, the code is `{0}`. -/
private lemma eq_zero_of_mem {u : Fin 4 → ZMod 5} (hu : u ∈ code pts 0) : u = 0 := by
  obtain ⟨p, hp, rfl⟩ := mem_code_iff_exists_polynomial.1 hu
  have : p = 0 := by
    rw [← Polynomial.degree_eq_bot]
    simpa using hp
  subst this
  ext x
  simp [evalOnPoints]

/-- `g₂ 0` is `1/4`-close to the code `{0}`: it has a single nonzero entry. -/
private lemma g₂_zero_close :
    δᵣ(g₂ 0, (code pts 0 : Set (Fin 4 → ZMod 5))) ≤ ((1 / 4 : ℝ≥0) : ENNReal) := by
  refine (Code.relDistFromCode_le_relDist_to_mem (g₂ 0) (0 : Fin 4 → ZMod 5)
    (Submodule.zero_mem _)).trans ?_
  have h1 : hammingDist (g₂ 0) (0 : Fin 4 → ZMod 5) = 1 := by
    unfold g₂
    decide
  have h3 : δᵣ(g₂ 0, (0 : Fin 4 → ZMod 5)) = (1 / 4 : ℚ≥0) := by
    unfold Code.relHammingDist
    rw [h1]
    norm_num
  rw [h3, ← ENNReal.coe_nnratCast]
  exact ENNReal.coe_le_coe.2 (by norm_num)

/-- `0 < degree` is needed. With `degree = 0` the code is `{0}`, its rate is `0`, and `err⋆`, which
divides by the rate, is `0` (`x / 0 = 0`). Then the other hypotheses hold for explicit data
(`F = ZMod 5`, four points, `m = 2`, `δ = 1/4`, `f₀ = (1, 0, 0, 0)`, `f₁ = (0, 1, 1, 0)`: `f₀` is
`1/4`-close to `0`), but no three points are common zeros of `f₀` and `f₁`. -/
theorem proximity_gap_fails_for_degree_zero :
    0 < (1 / 4 : ℝ≥0) ∧
    (1 / 4 : ℝ≥0) < 1 - Bstar (LinearCode.rate (code pts 0)) ∧
    Pr{let r ← $ᵗ (ZMod 5)}[
        δᵣ((fun x => ∑ j : Fin 2, r ^ (j : ℕ) * g₂ j x), code pts 0) ≤ (1 / 4 : ℝ≥0)] >
      ENNReal.ofReal (proximityError (ZMod 5) 0 (LinearCode.rate (code pts 0)) (1 / 4) 2) ∧
    ¬ ∃ S : Finset (Fin 4), S.card ≥ (1 - (1 / 4 : ℝ≥0)) * (Fintype.card (Fin 4)) ∧
        ∀ i : Fin 2, ∃ u : Fin 4 → ZMod 5, u ∈ code pts 0 ∧ ∀ x ∈ S, g₂ i x = u x := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [rate_zero]
    simp [Bstar]
    norm_num
  · have herr : proximityError (ZMod 5) 0 (LinearCode.rate (code pts 0)) (1 / 4) 2 = 0 := by
      rw [rate_zero]
      unfold proximityError
      simp
    rw [herr, NNReal.coe_zero, ENNReal.ofReal_zero]
    refine (SampleableType.prEvent_uniformSample_pos_iff _).2 ⟨0, ?_⟩
    have hf : (fun x => ∑ j : Fin 2, (0 : ZMod 5) ^ (j : ℕ) * g₂ j x) = g₂ 0 := by
      funext x
      simp [Fin.sum_univ_two]
    rw [hf]
    exact g₂_zero_close
  · rintro ⟨S, hS, h⟩
    have h3 : 3 ≤ S.card := by
      have h34 : (1 - 1 / 4 : ℝ≥0) = 3 / 4 := tsub_eq_of_eq_add (by norm_num)
      rw [ge_iff_le, h34] at hS
      have : (3 : ℝ≥0) ≤ S.card := by
        convert hS using 1
        simp
      exact_mod_cast this
    have key : ∀ S : Finset (Fin 4), 3 ≤ S.card → ∃ x ∈ S, g₂ 0 x ≠ 0 ∨ g₂ 1 x ≠ 0 := by
      unfold g₂
      decide
    obtain ⟨x, hx, hne⟩ := key S h3
    obtain ⟨u0, hu0, h0⟩ := h 0
    obtain ⟨u1, hu1, h1⟩ := h 1
    rcases hne with hne | hne
    · exact hne ((h0 x hx).trans (by rw [eq_zero_of_mem hu0]; rfl))
    · exact hne ((h1 x hx).trans (by rw [eq_zero_of_mem hu1]; rfl))

end ArkLibTest.StirProximityGap

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.FoldingComputable
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for folding many words with equal-degree combiners -/

open Polynomial ReedSolomon
open scoped Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The whole field `F₅` as the evaluation domain. -/
private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

-- The first round produces `2 + X` and `4 + 3X`. A different second challenge adds them.
private def folded : CompPoly.CPolynomial (ZMod 5) :=
  ReedSolomon.Computable.foldPolynomials 2 ![(0, 0, 1), (0, 1, 0)]
    ![CompPoly.CPolynomial.C 1, CompPoly.CPolynomial.C 2,
      CompPoly.CPolynomial.C 3, CompPoly.CPolynomial.C 4]

/-- info: true -/
#guard_msgs in
#eval folded.coeff 0 == 1 && folded.coeff 1 == 4 && folded.coeff 2 == 0

-- One round combines the first two received rows.
example {F ι : Type*} [Field F] (domain : ι ↪ F) (c : Fin 1 → F × F × F)
    (f : Fin (2 ^ 1) → ι → F) :
    foldWords domain 1 c f = equalDegreeWord domain (f 0) (f 1) (c 0).1 (c 0).2.1 (c 0).2.2 :=
  rfl

-- With one round, a bad folding is an exceptional pair for the single round.
example {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] (domain : ι ↪ F) (d A : ℕ)
    (c : Fin 1 → F × F × F) (f : Fin (2 ^ 1) → ι → F) :
    HasBadFoldingRound domain d A 1 c f ↔
      ∃ P, IsInterleavedEqualDegreeExceptional domain (evenRows f) (oddRows f) (d + 1) A 1
        (c 0).1 (c 0).2.1 (c 0).2.2 P := by
  simp [HasBadFoldingRound]

-- With one round, the polynomial fold is the equal-degree combination of `P 0` and `P 1`.
example {F : Type*} [Field F] (c : Fin 1 → F × F × F) (P : Fin (2 ^ 1) → F[X]) :
    foldPolynomials 1 c P =
      P 1 + affineMultiplier (c 0).2.1 (c 0).2.2 * (P 0 + C (c 0).1 * P 1) :=
  rfl

-- Two rounds with `θ = 0`, `α = 1`, `β = 0` add the four rows.
example (W : Fin (2 ^ 2) → (ZMod 5)[X]) :
    foldPolynomials 2 ![(0, 1, 0), (0, 1, 0)] W = W 0 + W 1 + W 2 + W 3 := by
  simp [foldPolynomials, foldRoundPolynomials, evenRows, oddRows, affineMultiplier]
  ring_nf

-- Two rounds on the words `f k = k`, with `(θ, α, β) = (1, 2, 0)` and then `(0, 1, 0)`.
-- The first round gives `f₁ + 2 (f₀ + f₁) = 3` and `f₃ + 2 (f₂ + f₃) = 3 + 2 · 5 = 3` in `𝔽₅`.
-- The second round gives `3 + 1 · (3 + 0 · 3) = 1`.
-- Swapping even and odd rows, pairing `(k, k + 2)`, or reversing the rounds gives 4, 2 or 2.
example : foldWords fullDomain 2 ![(1, 2, 0), (0, 1, 0)] (fun k _ ↦ (k : ZMod 5)) = 1 := by
  funext x
  simp only [Nat.reducePow]
  revert x
  decide

-- The zero words are never bad for one round at threshold `2` on `𝔽₅` from degree `0`.
-- A candidate of degree at most one with two zeros vanishes, so zero witnesses lose nothing.
private theorem zero_not_hasBadFoldingRound (c : Fin 1 → ZMod 5 × ZMod 5 × ZMod 5) :
    ¬ HasBadFoldingRound fullDomain 0 2 1 c 0 := by
  simp only [HasBadFoldingRound, or_false]
  rintro ⟨P, hP, hA, hexc⟩
  have hzero (k : Fin (2 ^ 0)) : P k = 0 := by
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hA
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (P k) S (fun x hx ↦ ?_) ?_
    · have := (mem_interleavedEqualDegreeAgreementSet ..).mp (hS hx) k
      simpa [equalDegreeWord, evenRows, oddRows, fullDomain] using this
    · rw [hcard]
      exact (natDegree_le_iff_degree_le.mpr (hP k)).trans_lt (by norm_num)
  have := hexc 0 0 (fun _ ↦ by simp) (fun _ ↦ by simp)
    (fun k ↦ by simp [hzero k])
  simp [interleavedEqualDegreeAgreementLoss, evenRows, oddRows] at this

-- The deterministic guarantee applies: the zero candidate has the zero witnesses.
example (c : Fin 1 → ZMod 5 × ZMod 5 × ZMod 5) :
    ∃ W : Fin (2 ^ 1) → (ZMod 5)[X], (∀ k, (W k).degree ≤ (0 : ℕ)) ∧
      foldPolynomials 1 c W = 0 ∧
      #{i ∈ Finset.univ | ∃ k, (W k).eval (fullDomain i) ≠ (0 : Fin (2 ^ 1) → ZMod 5 → ZMod 5) k i}
        ≤ 1 :=
  exists_foldPolynomials_eq_of_not_hasBadFoldingRound fullDomain
    (zero_not_hasBadFoldingRound c) (by simp) (fun i _ ↦ by
      simp [foldWords, foldRoundWords, equalDegreeWord, evenRows, oddRows])
    (by simp [ZMod.card])

-- A caller may supply its own decidable equality on the field.
example {F ι : Type*} [Field F] [Fintype F] [inst : DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (r d A : ℕ) :
    @badFoldingRoundError F _ inst ι _ _ domain r d A ≤ 1 :=
  badFoldingRoundError_le_one domain r d A

-- One round with error `ε` gives the folding bound `ε`.
example {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (d A : ℕ) :
    foldingMcaError domain 1 d A ≤ interleavedEqualDegreeMcaError domain 1 (d + 1) A 1 := by
  simpa using foldingMcaError_le_mul domain (r := 1) (d := d) (A := A)
    (ε := interleavedEqualDegreeMcaError domain 1 (d + 1) A 1) fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      exact le_rfl

private noncomputable instance : Fintype (GaloisField 2 64) := Fintype.ofFinite _

private theorem field_card : Fintype.card (GaloisField 2 64) = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 64 (by norm_num)]

/-- A 100-point domain in the field with `2^64` elements. -/
private noncomputable def largeDomain : Fin 100 ↪ GaloisField 2 64 :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by rw [Fintype.card_fin, field_card]; norm_num))

private theorem card_fin_hundred : ((Fintype.card (Fin 100) : ℕ) : ℝ) = 100 := by simp

open Classical in
-- Round one of the client below: two pairs folded to degree `16`.
-- At `η = 1/2` the threshold is `⌈(2/5 + 1/2) 100⌉ = 90` and `ℓ₀ = ⌊7300/6321⌋ = 1`.
-- The threshold `92` only lowers the error.
private theorem round_one_error_le :
    interleavedEqualDegreeMcaError largeDomain 2 16 92 1 ≤ ENNReal.ofReal (10 / 2 ^ 64) := by
  refine (interleavedEqualDegreeMcaError_anti_threshold largeDomain 2 (by norm_num :
    90 ≤ 92)).trans ?_
  have hsqrt : √((16 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) = 2 / 5 := by
    rw [card_fin_hundred, Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]
    norm_num
  have h := interleavedEqualDegreeMcaError_le largeDomain 2 (d := 16) (η := 1 / 2)
    (by norm_num) (by simp) (by norm_num) (by rw [hsqrt]; norm_num)
    (by rw [card_fin_hundred]; norm_num)
  have hA : ⌈(2 / 5 + 1 / 2) * ((Fintype.card (Fin 100) : ℕ) : ℝ)⌉₊ = 90 := by
    rw [card_fin_hundred]
    norm_num
  rw [hsqrt, hA, card_fin_hundred, field_card] at h
  have hℓ : ⌊(100 : ℝ) * (((90 : ℕ) : ℝ) - 1 - ((16 : ℕ) : ℝ)) /
      ((((90 : ℕ) : ℝ) - 1) ^ 2 - 100 * ((16 : ℕ) : ℝ))⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [hℓ] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  norm_num

open Classical in
-- Round two of the client below: one pair folded to degree `17`.
-- With `√0.17 ∈ (0.41, 0.42]` and `η = 1/2`, the threshold is `92` and `ℓ₀ = ⌊7400/6581⌋ = 1`.
private theorem round_two_error_le :
    interleavedEqualDegreeMcaError largeDomain 1 17 92 1 ≤ ENNReal.ofReal (10 / 2 ^ 64) := by
  set s := √((17 : ℕ) / ((Fintype.card (Fin 100) : ℕ) : ℝ)) with hs
  have hs' : s = √(17 / 100) := by rw [hs, card_fin_hundred]; norm_num
  have hlo : 41 / 100 < s := by
    rw [hs', Real.lt_sqrt (by norm_num)]
    norm_num
  have hhi : s ≤ 42 / 100 := by
    rw [hs', Real.sqrt_le_left (by norm_num)]
    norm_num
  have h := interleavedEqualDegreeMcaError_le largeDomain 1 (d := 17) (η := 1 / 2)
    (by norm_num) (by simp) (by norm_num) (by rw [← hs]; linarith)
    (by rw [card_fin_hundred]; norm_num)
  have hA : ⌈(s + 1 / 2) * ((Fintype.card (Fin 100) : ℕ) : ℝ)⌉₊ = 92 := by
    rw [card_fin_hundred, Nat.ceil_eq_iff (by norm_num)]
    constructor <;> push_cast <;> linarith
  rw [hA, card_fin_hundred, field_card] at h
  have hℓ : ⌊(100 : ℝ) * (((92 : ℕ) : ℝ) - 1 - ((17 : ℕ) : ℝ)) /
      ((((92 : ℕ) : ℝ) - 1) ^ 2 - 100 * ((17 : ℕ) : ℝ))⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  rw [hℓ] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  norm_num

open Classical in
-- Four words over the field with `2⁶⁴` elements, folded in two rounds from degree `15`.
-- Round one has two pairs at degree `16`, round two one pair at degree `17`.
-- Both use the threshold `92`, so the failure probability is at most `2 ε = 20 / 2⁶⁴`.
example : foldingMcaError largeDomain 2 15 92 ≤ 2 * ENNReal.ofReal (10 / 2 ^ 64) := by
  refine foldingMcaError_le_mul largeDomain fun j hj ↦ ?_
  interval_cases j
  · exact round_one_error_le
  · exact round_two_error_le

-- A sequential union bound on pairs of challenges in `Fin 2`.
example : #{c : Fin 2 → Fin 2 | c 0 = 0 ∨ Fin.tail c 0 = 0} ≤ 1 * 2 + 2 :=
  (Fin.card_filter_or_tail_le (fun a : Fin 2 ↦ a = 0) (fun _ c ↦ c 0 = 0)).trans (by decide)

/-- info: 'ReedSolomon.exists_foldPolynomials_eq_of_not_hasBadFoldingRound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_foldPolynomials_eq_of_not_hasBadFoldingRound

/-- info: 'ReedSolomon.badFoldingRoundError_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.badFoldingRoundError_le_mul

/-- info: 'ReedSolomon.foldingMcaError_le_mul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldingMcaError_le_mul

/-- info: 'ReedSolomon.foldingMcaError_le_badFoldingRoundError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldingMcaError_le_badFoldingRoundError

/-- info: 'ReedSolomon.IsFoldingExceptional.hasBadFoldingRound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.IsFoldingExceptional.hasBadFoldingRound

/-- info: 'ReedSolomon.le_foldingMcaError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_foldingMcaError

/-- info: 'ReedSolomon.foldingMcaError_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldingMcaError_le_one

/-- info: 'ReedSolomon.le_badFoldingRoundError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.le_badFoldingRoundError

/-- info: 'ReedSolomon.badFoldingRoundError_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.badFoldingRoundError_le_one

/-- info: 'ReedSolomon.evenRows_interleaveRows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.evenRows_interleaveRows

/-- info: 'ReedSolomon.oddRows_interleaveRows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.oddRows_interleaveRows

/-- info: 'ReedSolomon.exists_eq_evenRows_or_eq_oddRows' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_eq_evenRows_or_eq_oddRows

/-- info: 'Fin.card_filter_or_tail_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fin.card_filter_or_tail_le

/-- info: 'ReedSolomon.foldRows_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldRows_zero

/-- info: 'ReedSolomon.foldRows_succ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.foldRows_succ

/-- info: 'ReedSolomon.Computable.toPoly_foldRoundPolynomials' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.Computable.toPoly_foldRoundPolynomials

/-- info: 'ReedSolomon.Computable.toPoly_foldPolynomials' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.Computable.toPoly_foldPolynomials

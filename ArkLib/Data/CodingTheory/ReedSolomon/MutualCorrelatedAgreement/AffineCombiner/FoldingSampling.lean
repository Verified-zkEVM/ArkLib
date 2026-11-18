/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Folding

/-!
# Uniform probabilities for folding with equal-degree combiners

The counting errors of one folding round and of `r` rounds are suprema of native uniform
probabilities.
One round samples its shared challenge `(θ, α, β)` uniformly from `F × F × F`.
The `r` rounds sample a uniform tuple in `Fin r → F × F × F`, so the rounds are independent.
The counting definitions and their bounds have no sampler assumptions.
These characterizations use `SampleableType F` to connect them to probability bounds.

The errors follow Theorem 5.2 of [CWYZ26] and the one-round guarantee in its proof.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedSolomon.prob_isInterleavedEqualDegreeExceptional_eq`: the uniform probability as a
  counting fraction.
* `ReedSolomon.interleavedEqualDegreeMcaError_eq_iSup_prob`: the error as a supremum of native
  probabilities.
* `ReedSolomon.prob_isInterleavedEqualDegreeExceptional_le`: the error bounds the probability
  for each pair of row tuples.
* `ReedSolomon.prob_isFoldingExceptional_eq`: the probability of a bad round as a counting
  fraction.
* `ReedSolomon.foldingMcaError_eq_iSup_prob`: the folding error as a supremum of native
  probabilities.
* `ReedSolomon.prob_isFoldingExceptional_le`: the folding error bounds the probability for each
  family of received words.
* `ReedSolomon.prob_isFoldingExceptional_le_mul`: some round is bad with probability at most
  `r ε`.
* `ReedSolomon.prob_exists_not_exists_foldPolynomials_eq_le_mul`: Theorem 5.2, some close
  candidate lacks folding witnesses with probability at most `r ε`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial
open scoped ProbabilityTheory Finset

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι] [Fintype F] [SampleableType F]
  {t : ℕ}

open Classical in
/-- The uniform exceptional-event probability equals the fraction of exceptional challenges. -/
theorem prob_isInterleavedEqualDegreeExceptional_eq (domain : ι ↪ F) (f g : Fin t → ι → F)
    (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F × F)}[∃ P,
      IsInterleavedEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P] =
      ENNReal.ofReal
        ((#{c : F × F × F | ∃ P,
          IsInterleavedEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P} : ℝ) /
            (Fintype.card F : ℝ) ^ 3) := by
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp [pow_succ, mul_assoc]

/-- The interleaved equal-degree error is the worst-case native probability of
exceptionality. -/
theorem interleavedEqualDegreeMcaError_eq_iSup_prob (domain : ι ↪ F) (t d A s : ℕ) :
    interleavedEqualDegreeMcaError domain t d A s =
      ⨆ w : (Fin t → ι → F) × (Fin t → ι → F),
        Pr{let c ← $ᵗ (F × F × F)}[∃ P,
          IsInterleavedEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P] := by
  simp only [interleavedEqualDegreeMcaError, prob_isInterleavedEqualDegreeExceptional_eq]

/-- The interleaved equal-degree error bounds the exceptional-event probability for each pair
of row tuples. -/
theorem prob_isInterleavedEqualDegreeExceptional_le (domain : ι ↪ F) (f g : Fin t → ι → F)
    (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F × F)}[∃ P,
      IsInterleavedEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P] ≤
        interleavedEqualDegreeMcaError domain t d A s := by
  rw [prob_isInterleavedEqualDegreeExceptional_eq]
  exact le_interleavedEqualDegreeMcaError domain d A s f g

open Classical in
/-- The probability that some folding round is bad equals the fraction of bad challenge tuples. -/
theorem prob_isFoldingExceptional_eq (domain : ι ↪ F) (r d A : ℕ) (f : Fin (2 ^ r) → ι → F) :
    Pr{let c ← $ᵗ (Fin r → F × F × F)}[IsFoldingExceptional domain d A r c f] =
      ENNReal.ofReal ((#{c : Fin r → F × F × F | IsFoldingExceptional domain d A r c f} : ℝ) /
        (Fintype.card F : ℝ) ^ (3 * r)) := by
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp [pow_mul, pow_succ, mul_assoc]

/-- The folding error is the worst-case native probability that some round is bad. -/
theorem foldingMcaError_eq_iSup_prob (domain : ι ↪ F) (r d A : ℕ) :
    foldingMcaError domain r d A =
      ⨆ f : Fin (2 ^ r) → ι → F,
        Pr{let c ← $ᵗ (Fin r → F × F × F)}[IsFoldingExceptional domain d A r c f] := by
  simp only [foldingMcaError, prob_isFoldingExceptional_eq]

/-- The folding error bounds the probability that some round is bad, for each family of
received words. -/
theorem prob_isFoldingExceptional_le (domain : ι ↪ F) (r d A : ℕ) (f : Fin (2 ^ r) → ι → F) :
    Pr{let c ← $ᵗ (Fin r → F × F × F)}[IsFoldingExceptional domain d A r c f] ≤
      foldingMcaError domain r d A := by
  rw [prob_isFoldingExceptional_eq]
  exact le_foldingMcaError domain r d A f

/-- Some folding round is bad with probability at most `r ε`.

There are `2^r` received words `f` folded in `r` rounds with independent uniform challenges.
The base degree is `d`, the agreement threshold is `A`, and the shared loss is one per round.
Round `j + 1`, for `j < r`, folds `2^(r - 1 - j)` pairs into words of degree `d + j + 1`.
Assume its interleaved equal-degree error is at most `ε`. -/
theorem prob_isFoldingExceptional_le_mul (domain : ι ↪ F) {r d A : ℕ} {ε : ENNReal}
    (hε : ∀ j < r, interleavedEqualDegreeMcaError domain (2 ^ (r - 1 - j)) (d + j + 1) A 1 ≤ ε)
    (f : Fin (2 ^ r) → ι → F) :
    Pr{let c ← $ᵗ (Fin r → F × F × F)}[IsFoldingExceptional domain d A r c f] ≤ r * ε :=
  (prob_isFoldingExceptional_le domain r d A f).trans (foldingMcaError_le_mul domain hε)

/-- Except with probability at most `r ε`, every close candidate of the folded word has
witnesses that fold to it.

There are `2^r` received words `f` folded in `r` rounds with independent uniform challenges.
The base degree is `d`, the agreement threshold is `A`, and the shared loss is one per round.
Round `j + 1`, for `j < r`, folds `2^(r - 1 - j)` pairs into words of degree `d + j + 1`.
Assume its interleaved equal-degree error is at most `ε`.
The failure event is a candidate `P` of degree at most `d + r` and a set `S` of at least
`A + r` points where `P` agrees with the folded word.
No polynomials `W` of degree at most `d` fold to `P` while failing `f` on at most `r` points
of `S`. -/
theorem prob_exists_not_exists_foldPolynomials_eq_le_mul (domain : ι ↪ F) {r d A : ℕ}
    {ε : ENNReal}
    (hε : ∀ j < r, interleavedEqualDegreeMcaError domain (2 ^ (r - 1 - j)) (d + j + 1) A 1 ≤ ε)
    (f : Fin (2 ^ r) → ι → F) :
    Pr{let c ← $ᵗ (Fin r → F × F × F)}[∃ P : F[X], P.degree ≤ ↑(d + r) ∧ ∃ S : Finset ι,
      (∀ i ∈ S, P.eval (domain i) = foldWords domain r c f i) ∧ A + r ≤ #S ∧
      ¬ ∃ W : Fin (2 ^ r) → F[X], (∀ k, (W k).degree ≤ d) ∧ foldPolynomials r c W = P ∧
        #{i ∈ S | ∃ k, (W k).eval (domain i) ≠ f k i} ≤ r] ≤ r * ε := by
  classical
  refine le_trans ?_ (prob_isFoldingExceptional_le_mul domain hε f)
  rw [SampleableType.prEvent_uniformSample_eq_ofReal,
    SampleableType.prEvent_uniformSample_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
  refine Nat.cast_le.mpr (Finset.card_le_card fun c hc ↦ ?_)
  rw [Finset.mem_filter] at hc ⊢
  obtain ⟨P, hP, S, hS, hA, hno⟩ := hc.2
  exact ⟨Finset.mem_univ c, by_contra fun hbad ↦
    hno (exists_foldPolynomials_eq_of_not_isFoldingExceptional domain hbad hP hS hA)⟩

end ReedSolomon

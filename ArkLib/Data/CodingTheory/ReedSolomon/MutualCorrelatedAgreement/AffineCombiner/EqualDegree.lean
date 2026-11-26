/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import ArkLib.ToMathlib.Finset.TripleCount

/-!
# Equal-degree combiners

The combiner maps received words `f, g` to `g + (α + β x)(f + θ g)`.
It uses three independent uniform challenges.
Both witnesses have degree below `d`, while the output has degree at most `d`.
For one point of agreement loss, its error is at most the affine error plus `ℓ₀/q`.
Here `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`, `n` is the domain size, and `q` the field size.
The bound assumes `nd < (A - 1)²`.

For fixed `θ`, the affine combiner on `(g, f + θ g)` supplies witnesses `U, V`.
The pair `(V - θ U, U)` explains the same agreements with the same loss.
It can fail the strict degree bounds only if `U` has degree exactly `d`.
Such a pair fixes `θ` by its leading coefficients.
The Johnson bound limits the number of these bad challenges.
This is the first inequality of (5.4) in Theorem 5.1 of [CWYZ26].
This module proves the one-row lemmas of that argument.
`EqualDegreeTheorem` states the inequality as `equalDegreeMcaError_le_affineMcaError_add`.
It derives the inequality from the `t`-row bound in `FoldingRound` at `t = 1`, and it also
proves the second inequality.
The linear-claims assertion in `LinearClaims` reuses the one-row lemmas.
It counts exceptional triples with the shared bound in `ToMathlib/Finset/TripleCount`.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

The error is a mathematical supremum with classical decidability for polynomial witnesses.
Its counting definition requires no sampler.
The sampling module identifies it with native uniform probabilities.

`ReedSolomon.equalDegreeMcaErrorRat` in `AffineCombiner.Computable` computes this error as an exact
nonnegative rational by finite searches.

## Main definitions

* `ReedSolomon.equalDegreeWord`: the combined received word.
* `ReedSolomon.IsEqualDegreeExceptional`: an exceptional candidate for three challenges.
* `ReedSolomon.badEqualDegreeChallenges`: challenges whose witness reaches degree `d`.
* `ReedSolomon.equalDegreeMcaError`: the supremum of exceptional-event probabilities.

## Main statements

* `ReedSolomon.equalDegreeMcaError_le_one`: the error is at most one.
* `ReedSolomon.IsEqualDegreeExceptional.isAffineExceptional_or_exists_degree_eq`: an exceptional
  candidate is affine exceptional for `(g, f + θ g)`, or `θ` is bad.
* `ReedSolomon.card_badEqualDegreeChallenges_add_card_mul_le`: the integer count of bad `θ`
  values together with a list of lower-degree pairs.
* `ReedSolomon.card_badEqualDegreeChallenges_mul_le`: the integer count of bad `θ` values.
* `ReedSolomon.card_filter_isAffineExceptional_le_mul_affineMcaError`: the affine pair count.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- The equal-degree combined word `g + (α + β x) (f + θ g)`. -/
def equalDegreeWord (domain : ι ↪ F) (f g : ι → F) (θ α β : F) : ι → F :=
  fun i ↦ g i + (α + β * domain i) * (f i + θ * g i)

/-- The challenge `(θ, α, β)` makes `P` exceptional for the equal-degree combiner.

`P` has degree at most `d` and agrees with `g + (α + β x)(f + θ g)` on at least `A` points.
No pair `F₀, G₀` of degrees below `d` satisfies
`P = G₀ + (α + βX)(F₀ + θG₀)` while losing at most `s` of these points. -/
def IsEqualDegreeExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree < d → G₀.degree < d →
      P = G₀ + affineMultiplier α β * (F₀ + C θ * G₀) →
      s < #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P |
        F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i}

open Classical in
/-- The supremum over received word pairs of the probability that some candidate is exceptional
for independent uniform challenges `(θ, α, β)`.

The output degree bound is `d`, both witness degrees are below `d`, the agreement threshold
is `A`, and the allowed agreement loss is `s`.
`ReedSolomon.equalDegreeMcaError_eq_iSup_prob` gives the native sampling characterization. -/
noncomputable def equalDegreeMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ENNReal :=
  ⨆ w : (ι → F) × (ι → F),
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P,
        IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 3)

omit [DecidableEq F] [Fintype ι] in
/-- The equal-degree word is the affine word of the pair `(g, f + θ g)`. -/
theorem equalDegreeWord_eq_combinedWord (domain : ι ↪ F) (f g : ι → F) (θ α β : F) :
    equalDegreeWord domain f g θ α β =
      combinedWord domain g (fun i ↦ f i + θ * g i) (affineMultiplier α β) := by
  funext i
  simp [equalDegreeWord]

open Classical in
/-- One received word pair bounds the equal-degree error from below. -/
theorem le_equalDegreeMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) (f g : ι → F) :
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P,
        IsEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 3) ≤ equalDegreeMcaError domain d A s := by
  unfold equalDegreeMcaError
  exact le_iSup_of_le (f, g) le_rfl

/-- The equal-degree error is at most one. -/
theorem equalDegreeMcaError_le_one [Fintype F] (domain : ι ↪ F) (d A s : ℕ) :
    equalDegreeMcaError domain d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  calc (#{c : F × F × F | ∃ P,
        IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} : ℝ)
      ≤ (Finset.univ : Finset (F × F × F)).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ 3 := by simp [pow_succ, mul_assoc]

/-- An exceptional candidate is affine exceptional for `(g, f + θ g)`, or `θ` is bad.

Bad means that some pair `F₀, G₀` with `deg G₀ = d` satisfies `[X^d] F₀ + θ [X^d] G₀ = 0`.
That pair agrees with `(f, g)` on at least `A - s` points. -/
theorem IsEqualDegreeExceptional.isAffineExceptional_or_exists_degree_eq
    {domain : ι ↪ F} {f g : ι → F}
    {d A s : ℕ} {θ α β : F} {P : F[X]} (h : IsEqualDegreeExceptional domain f g d A s θ α β P) :
    IsAffineExceptional domain g (fun i ↦ f i + θ * g i) d A s α β P ∨
      ∃ F₀ G₀ : F[X], F₀.degree ≤ d ∧ G₀.degree = d ∧ F₀.coeff d + θ * G₀.coeff d = 0 ∧
        A - s ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀) := by
  obtain ⟨hP, hA, hexc⟩ := h
  rw [equalDegreeWord_eq_combinedWord] at hA hexc
  by_cases haff : IsAffineExceptional domain g (fun i ↦ f i + θ * g i) d A s α β P
  · exact Or.inl haff
  right
  obtain ⟨U, V, hU, hV, hPeq, hloss⟩ : ∃ U V : F[X], U.degree ≤ d ∧ V.degree < d ∧
      IsLossWitness domain g (fun i ↦ f i + θ * g i) s (affineMultiplier α β) P U V := by
    by_contra hno
    push Not at hno
    exact haff ⟨hP, hA, fun U V hU hV hw ↦ hno U V hU hV hw⟩
  have hloss_eq : {i ∈ polynomialAgreementSet domain
      (combinedWord domain g (fun i ↦ f i + θ * g i) (affineMultiplier α β)) P |
        (V - C θ * U).eval (domain i) ≠ f i ∨ U.eval (domain i) ≠ g i} =
      agreementLoss domain g (fun i ↦ f i + θ * g i) (affineMultiplier α β) P U V := by
    unfold agreementLoss
    refine Finset.filter_congr fun i _ ↦ ?_
    by_cases hu : U.eval (domain i) = g i
    · simp only [eval_sub, eval_mul, eval_C, hu, ne_eq, not_true_eq_false, or_false, false_or]
      constructor <;> intro h₁ h₂ <;> apply h₁ <;> linear_combination h₂
    · simp [hu]
  have hCU : (C θ * U).degree ≤ U.degree := by
    rw [← smul_eq_C_mul]
    exact degree_smul_le θ U
  have hFdeg : (V - C θ * U).degree ≤ d :=
    (degree_sub_le _ _).trans (max_le hV.le (hCU.trans hU))
  have hUd : U.degree = d := by
    refine le_antisymm hU (not_lt.mp fun hlt ↦ ?_)
    have hF : (V - C θ * U).degree < d :=
      (degree_sub_le _ _).trans_lt (max_lt hV (hCU.trans_lt hlt))
    have := hexc (V - C θ * U) U hF hlt (by rw [hPeq]; ring)
    rw [hloss_eq] at this
    omega
  refine ⟨V - C θ * U, U, hFdeg, hUd, ?_, ?_⟩
  · simp [coeff_C_mul, coeff_eq_zero_of_degree_lt hV]
  · classical
    refine (Nat.sub_le_sub_left hloss A).trans ((Nat.sub_le_sub_right hA _).trans
      ((Finset.le_card_sdiff _ _).trans (Finset.card_le_card fun i hi ↦ ?_)))
    obtain ⟨hiP, hiL⟩ := Finset.mem_sdiff.mp hi
    simp only [agreementLoss, Finset.mem_filter, hiP, true_and, not_or, not_not] at hiL
    rw [mem_commonPolynomialAgreementSet]
    simp only [eval_sub, eval_mul, eval_C, hiL.1, hiL.2]
    exact ⟨by ring, trivial⟩

open Classical in
/-- Challenges `θ` admitting a pair `F₀, G₀` with `deg F₀ ≤ d`, `deg G₀ = d`,
`[X^d] F₀ + θ [X^d] G₀ = 0`, and at least `L` common agreements with `(f, g)`. -/
noncomputable def badEqualDegreeChallenges [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    (d L : ℕ) : Finset F :=
  {θ : F | ∃ F₀ G₀ : F[X], F₀.degree ≤ d ∧ G₀.degree = d ∧
    F₀.coeff d + θ * G₀.coeff d = 0 ∧
    L ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀)}

/-- The bad challenges and a list of pairs together satisfy the Johnson count:
`(#B + #T) · (L² - nd) ≤ n · (L - d)`, where `B = badEqualDegreeChallenges domain f g d L`.
Both subtractions are in `ℕ`.

Here `T` is any finite set of pairs with first degree at most `d`, second degree below `d`,
and at least `L` common agreements with `(f, g)`.

A bad `θ` comes with a pair `F₀, G₀` of degree at most `d`, with `deg G₀ = d`.
The pair agrees with `(f, g)` on at least `L` points, and `[X^d] F₀ + θ [X^d] G₀ = 0`.
The pair fixes `θ`, so distinct bad values give distinct pairs.
These pairs are not in `T`, since their second degree is exactly `d`. -/
theorem card_badEqualDegreeChallenges_add_card_mul_le [Fintype F] (domain : ι ↪ F)
    (f g : ι → F) (d L : ℕ) (T : Finset (F[X] × F[X]))
    (hT : ∀ p ∈ T, p.1.degree ≤ d ∧ p.2.degree < d ∧
      L ≤ #(commonPolynomialAgreementSet domain f g p.1 p.2)) :
    (#(badEqualDegreeChallenges domain f g d L) + #T) *
      (L * L - Fintype.card ι * d) ≤ Fintype.card ι * (L - d) := by
  classical
  set B := badEqualDegreeChallenges domain f g d L
  have hB : ∀ θ ∈ B, ∃ F₀ G₀ : F[X], F₀.degree ≤ d ∧ G₀.degree = d ∧
      F₀.coeff d + θ * G₀.coeff d = 0 ∧
      L ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀) := fun θ hθ ↦ by
    simpa [B, badEqualDegreeChallenges] using hθ
  choose! F₀ G₀ hF hG hc hL using hB
  -- The leading coefficient of `G₀` is nonzero, so the pair fixes `θ`.
  have hinj : Set.InjOn (fun θ ↦ (F₀ θ, G₀ θ)) B := by
    intro θ hθ θ' hθ' heq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
    have hlead : (G₀ θ).coeff d ≠ 0 := by
      rw [← (natDegree_eq_of_degree_eq_some (hG θ hθ))]
      exact leadingCoeff_ne_zero.mpr fun h0 ↦ by simpa [h0] using hG θ hθ
    have := (hc θ hθ).trans (hc θ' hθ').symm
    rw [h₁, h₂] at this
    exact mul_right_cancel₀ (h₂ ▸ hlead) (add_left_cancel this)
  have hdisj : Disjoint (B.image fun θ ↦ (F₀ θ, G₀ θ)) T := by
    refine Finset.disjoint_left.mpr fun p hp hpT ↦ ?_
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hp
    exact (hT _ hpT).2.1.ne (hG θ hθ)
  rw [← Finset.card_image_of_injOn hinj, ← Finset.card_union_of_disjoint hdisj]
  refine card_mul_sq_sub_card_mul_le_of_commonPolynomialAgreementSet domain f g _
    (fun p hp ↦ ?_) (fun p hp ↦ ?_)
  · rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp h
      exact ⟨hF θ hθ, (hG θ hθ).le⟩
    · exact ⟨(hT p h).1, (hT p h).2.1.le⟩
  · rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp h
      exact hL θ hθ
    · exact (hT p h).2.2

/-- The bad-challenge count satisfies `#B · (L² - nd) ≤ n · (L - d)`,
where `B = badEqualDegreeChallenges domain f g d L` and both subtractions are in `ℕ`.
This is `card_badEqualDegreeChallenges_add_card_mul_le` with no listed pairs. -/
theorem card_badEqualDegreeChallenges_mul_le [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    (d L : ℕ) :
    #(badEqualDegreeChallenges domain f g d L) *
      (L * L - Fintype.card ι * d) ≤ Fintype.card ι * (L - d) := by
  simpa using card_badEqualDegreeChallenges_add_card_mul_le domain f g d L ∅ (by simp)

open Classical in
/-- For one word pair, the affine error bounds the exceptional challenge pairs.

At most `q² ε` pairs `(α, β)` make some candidate affine exceptional for `(f, g)`.
Here `q` is the field size and `ε` is the affine error with the same parameters. -/
theorem card_filter_isAffineExceptional_le_mul_affineMcaError [Fintype F] (domain : ι ↪ F)
    (d A s : ℕ) (f g : ι → F) :
    (#{x : F × F | ∃ P, IsAffineExceptional domain f g d A s x.1 x.2 P} : ℝ) ≤
      (Fintype.card F : ℝ) ^ 2 * (affineMcaError domain d A s).toReal := by
  have hE : affineMcaError domain d A s ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (affineMcaError_le_one domain d A s)
  have := (ENNReal.ofReal_le_iff_le_toReal hE).mp (le_affineMcaError domain d A s f g)
  rw [div_le_iff₀ (by positivity)] at this
  simpa [mul_comm] using this

end ReedSolomon

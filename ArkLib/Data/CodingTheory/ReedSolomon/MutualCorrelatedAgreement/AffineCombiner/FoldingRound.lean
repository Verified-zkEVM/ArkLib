/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegree
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Interleaved

/-!
# Interleaved equal-degree combiners

Rows `f r, g r` are combined into `g r + (α + β x)(f r + θ g r)` with one shared challenge.
A candidate tuple agrees at a point when every row agrees there.
A point is lost when some row of the witness tuples fails its received word there.
This is one round of the row folding in the sibling folding module.

Fix `θ` and apply the interleaved affine combiner to the rows `(g r, f r + θ g r)`.
It supplies witness tuples `U, V`.
The tuples `(V - θ U, U)` explain the same shared agreements with the same loss.
They fail the strict degree bounds only if some row of `U` has degree exactly `d`.
Such a pair of tuples fixes `θ` by the leading coefficients of that row.
Distinct pairs of tuples share at most `d` common agreements, since some row differs.
So the Johnson bound limits the bad challenges by `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`.
Here `n` is the domain size and `q` the field size.

This is the first inequality of (5.4) for `t` rows.
The proof of Theorem 5.2 of [CWYZ26] uses it in every folding round.
For `t = 1`, `interleavedEqualDegreeMcaError_one` identifies the error with
`equalDegreeMcaError`. The one-row reduction is proved in `EqualDegree`.
Both reductions count exceptional triples with the shared bound in `ToMathlib/Finset/TripleCount`.
The paper packs the rows into an extension of degree `t`.
The direct tuple count gives the paper’s bound with no factor of `t`.
The explicit bound `(4/η + ℓ₀)/q + 2¹⁴ n² / (ρ³ η¹⁰ q²)` follows from the bound (5.7).
The linear-claims assertion (5.5) for `t` rows is not formalized here.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

The error has type `ENNReal` and a counting definition that requires no sampler.
The sibling sampling module identifies it with a supremum of native probabilities.
The definitions use classical decidability for predicates over polynomial witnesses.

## Main definitions

* `ReedSolomon.interleavedEqualDegreeAgreementSet`: the shared agreement set of a tuple.
* `ReedSolomon.interleavedEqualDegreeAgreementLoss`: the shared points lost by witness tuples.
* `ReedSolomon.IsInterleavedEqualDegreeExceptional`: exceptional tuples.
* `ReedSolomon.badInterleavedEqualDegreeChallenges`: challenges `θ` fixed by a pair of tuples
  of degree `d`.
* `ReedSolomon.interleavedEqualDegreeMcaError`: the uniform error probability.

## Main statements

* `ReedSolomon.le_interleavedEqualDegreeMcaError` and
  `ReedSolomon.interleavedEqualDegreeMcaError_le_one`: basic bounds on the error.
* `ReedSolomon.interleavedEqualDegreeAgreementSet_eq_interleavedAgreementSet`: the shared
  agreement set is the interleaved affine one for the rows `(g r, f r + θ g r)`.
* `ReedSolomon.isInterleavedEqualDegreeExceptional_one_iff` and
  `ReedSolomon.interleavedEqualDegreeMcaError_one`: one row is the equal-degree combiner.
* `ReedSolomon.IsInterleavedEqualDegreeExceptional.isInterleavedAffineExceptional_or_exists`:
  an exceptional tuple is interleaved affine exceptional, or `θ` is bad.
* `ReedSolomon.card_badInterleavedEqualDegreeChallenges_mul_le`: the Johnson count of bad `θ`.
* `ReedSolomon.interleavedEqualDegreeMcaError_le_interleavedAffineMcaError_add`: the first
  inequality of (5.4) for `t` rows.
* `ReedSolomon.interleavedEqualDegreeMcaError_le`: the explicit bound.
* `ReedSolomon.IsInterleavedEqualDegreeExceptional.anti_threshold` and
  `ReedSolomon.interleavedEqualDegreeMcaError_anti_threshold`: raising the threshold.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] {t : ℕ}

/-- The points where every row `P r` agrees with `g r + (α + β x)(f r + θ g r)`. -/
def interleavedEqualDegreeAgreementSet (domain : ι ↪ F) (f g : Fin t → ι → F) (θ α β : F)
    (P : Fin t → F[X]) : Finset ι :=
  interleavedPolynomialAgreementSet domain (fun i r ↦ equalDegreeWord domain (f r) (g r) θ α β i) P

/-- A position agrees exactly when every combined row agrees there. -/
@[simp]
theorem mem_interleavedEqualDegreeAgreementSet (domain : ι ↪ F) (f g : Fin t → ι → F)
    (θ α β : F) (P : Fin t → F[X]) (i : ι) :
    i ∈ interleavedEqualDegreeAgreementSet domain f g θ α β P ↔
      ∀ r, (P r).eval (domain i) = equalDegreeWord domain (f r) (g r) θ α β i := by
  simp [interleavedEqualDegreeAgreementSet]

/-- The shared agreement points of `P` where some row of `F₀` or `G₀` fails its received word. -/
def interleavedEqualDegreeAgreementLoss (domain : ι ↪ F) (f g : Fin t → ι → F) (θ α β : F)
    (P F₀ G₀ : Fin t → F[X]) : Finset ι :=
  (interleavedEqualDegreeAgreementSet domain f g θ α β P).filter fun i ↦
    ∃ r, (F₀ r).eval (domain i) ≠ f r i ∨ (G₀ r).eval (domain i) ≠ g r i

/-- An agreeing position is lost if either witness differs from its received word in any row. -/
@[simp]
theorem mem_interleavedEqualDegreeAgreementLoss (domain : ι ↪ F) (f g : Fin t → ι → F)
    (θ α β : F) (P F₀ G₀ : Fin t → F[X]) (i : ι) :
    i ∈ interleavedEqualDegreeAgreementLoss domain f g θ α β P F₀ G₀ ↔
      i ∈ interleavedEqualDegreeAgreementSet domain f g θ α β P ∧
        ∃ r, (F₀ r).eval (domain i) ≠ f r i ∨ (G₀ r).eval (domain i) ≠ g r i := by
  simp [interleavedEqualDegreeAgreementLoss]

/-- The tuple `P` is exceptional for the shared challenge `(θ, α, β)`.

Every row has degree at most `d`, and at least `A` points are shared agreements.
Consider witness tuples with `deg F₀ r < d` and `deg G₀ r < d`.
They satisfy `P r = G₀ r + (α + β X)(F₀ r + θ G₀ r)` in every row.
No such tuples lose at most `s` shared agreements. -/
def IsInterleavedEqualDegreeExceptional (domain : ι ↪ F) (f g : Fin t → ι → F) (d A s : ℕ)
    (θ α β : F) (P : Fin t → F[X]) : Prop :=
  (∀ r, (P r).degree ≤ d) ∧ A ≤ #(interleavedEqualDegreeAgreementSet domain f g θ α β P) ∧
    ∀ F₀ G₀ : Fin t → F[X], (∀ r, (F₀ r).degree < d) → (∀ r, (G₀ r).degree < d) →
      (∀ r, P r = G₀ r + affineMultiplier α β * (F₀ r + C θ * G₀ r)) →
      s < #(interleavedEqualDegreeAgreementLoss domain f g θ α β P F₀ G₀)

open Classical in
/-- The worst-case probability that a uniform shared challenge has an exceptional tuple.

The supremum ranges over row tuples `(f, g)` and the challenge `(θ, α, β)` is uniform in `F³`.
There are `t` rows, the output degree bound is `d`, and both witness degrees are below `d`.
The agreement threshold is `A` and the allowed shared loss is `s`. -/
noncomputable def interleavedEqualDegreeMcaError [Fintype F] (domain : ι ↪ F) (t d A s : ℕ) :
    ENNReal :=
  ⨆ w : (Fin t → ι → F) × (Fin t → ι → F),
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P,
        IsInterleavedEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 3)

section Error

variable [Fintype F] (domain : ι ↪ F)

open Classical in
/-- One pair of row tuples bounds the interleaved equal-degree error from below. -/
theorem le_interleavedEqualDegreeMcaError (d A s : ℕ) (f g : Fin t → ι → F) :
    ENNReal.ofReal
      ((#{c : F × F × F | ∃ P,
        IsInterleavedEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 3) ≤ interleavedEqualDegreeMcaError domain t d A s := by
  unfold interleavedEqualDegreeMcaError
  exact le_iSup_of_le (f, g) le_rfl

/-- The interleaved equal-degree error is at most one. -/
theorem interleavedEqualDegreeMcaError_le_one (t d A s : ℕ) :
    interleavedEqualDegreeMcaError domain t d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  calc (#{c : F × F × F | ∃ P,
        IsInterleavedEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} : ℝ)
      ≤ (Finset.univ : Finset (F × F × F)).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ 3 := by simp [pow_succ, mul_assoc]

omit [Fintype F] in
/-- Raising the agreement threshold keeps fewer exceptional tuples. -/
theorem IsInterleavedEqualDegreeExceptional.anti_threshold {f g : Fin t → ι → F}
    {d A A' s : ℕ} {θ α β : F} {P : Fin t → F[X]} (hA : A' ≤ A)
    (h : IsInterleavedEqualDegreeExceptional domain f g d A s θ α β P) :
    IsInterleavedEqualDegreeExceptional domain f g d A' s θ α β P :=
  ⟨h.1, hA.trans h.2.1, h.2.2⟩

/-- Raising the agreement threshold does not increase the interleaved equal-degree error. -/
theorem interleavedEqualDegreeMcaError_anti_threshold (t : ℕ) {d A A' s : ℕ} (hA : A' ≤ A) :
    interleavedEqualDegreeMcaError domain t d A s ≤
      interleavedEqualDegreeMcaError domain t d A' s := by
  classical
  refine iSup_le fun w ↦ le_iSup_of_le w (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Nat.cast_le.mpr (Finset.card_le_card fun c hc ↦ ?_)
  rw [Finset.mem_filter] at hc ⊢
  obtain ⟨P, hP⟩ := hc.2
  exact ⟨hc.1, P, hP.anti_threshold domain hA⟩

end Error

/-- The shared agreement set is the interleaved affine one for the rows `(g r, f r + θ g r)`. -/
theorem interleavedEqualDegreeAgreementSet_eq_interleavedAgreementSet
    (domain : ι ↪ F) (f g : Fin t → ι → F) (θ α β : F) (P : Fin t → F[X]) :
    interleavedEqualDegreeAgreementSet domain f g θ α β P =
      interleavedAgreementSet domain g (fun r i ↦ f r i + θ * g r i) α β P := by
  ext i
  simp [equalDegreeWord]

section One

/-- With one row, a tuple is exceptional exactly when its row is equal-degree exceptional.
The received word pair is the single row. -/
theorem isInterleavedEqualDegreeExceptional_one_iff (domain : ι ↪ F) (f g : Fin 1 → ι → F)
    (d A s : ℕ) (θ α β : F) (P : Fin 1 → F[X]) :
    IsInterleavedEqualDegreeExceptional domain f g d A s θ α β P ↔
      IsEqualDegreeExceptional domain (f 0) (g 0) d A s θ α β (P 0) := by
  have hset : interleavedEqualDegreeAgreementSet domain f g θ α β P =
      polynomialAgreementSet domain (equalDegreeWord domain (f 0) (g 0) θ α β) (P 0) := by
    ext i
    simp [Fin.forall_fin_one]
  have hloss (F₀ G₀ : Fin 1 → F[X]) :
      interleavedEqualDegreeAgreementLoss domain f g θ α β P F₀ G₀ =
        {i ∈ polynomialAgreementSet domain (equalDegreeWord domain (f 0) (g 0) θ α β) (P 0) |
          (F₀ 0).eval (domain i) ≠ f 0 i ∨ (G₀ 0).eval (domain i) ≠ g 0 i} := by
    ext i
    simp [hset, Fin.exists_fin_one]
  simp only [IsInterleavedEqualDegreeExceptional, IsEqualDegreeExceptional, hset, hloss,
    Fin.forall_fin_one]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun h F₀ G₀ hF hG hw ↦ ?_,
    fun h F₀ G₀ hF hG hw ↦ h (F₀ 0) (G₀ 0) hF hG hw⟩
  exact h (fun _ ↦ F₀) (fun _ ↦ G₀) hF hG hw

/-- With one row, the interleaved equal-degree error is the equal-degree error. -/
theorem interleavedEqualDegreeMcaError_one [Fintype F] (domain : ι ↪ F) (d A s : ℕ) :
    interleavedEqualDegreeMcaError domain 1 d A s = equalDegreeMcaError domain d A s := by
  classical
  unfold interleavedEqualDegreeMcaError equalDegreeMcaError
  refine (Equiv.prodCongr (Equiv.funUnique (Fin 1) (ι → F))
    (Equiv.funUnique (Fin 1) (ι → F))).iSup_congr fun w ↦ ?_
  congr 3
  refine (congrArg Finset.card (Finset.filter_congr fun c _ ↦ ?_)).symm
  have h := isInterleavedEqualDegreeExceptional_one_iff domain w.1 w.2 d A s c.1 c.2.1 c.2.2
  exact ⟨fun ⟨P, hP⟩ ↦ ⟨P 0, (h P).mp hP⟩, fun ⟨P, hP⟩ ↦ ⟨fun _ ↦ P, (h _).mpr hP⟩⟩

end One

section Reduction

open Classical in
/-- Challenges `θ` fixed by a pair of tuples `F₀, G₀` of degree at most `d`.

Some row of `G₀` has degree exactly `d`.
Every row satisfies `[X^d] F₀ r + θ [X^d] G₀ r = 0`.
The pair agrees with `(f, g)` in every row on at least `L` common points. -/
noncomputable def badInterleavedEqualDegreeChallenges [Fintype F] (domain : ι ↪ F)
    (f g : Fin t → ι → F) (d L : ℕ) : Finset F :=
  {θ : F | ∃ F₀ G₀ : Fin t → F[X], (∀ r, (F₀ r).degree ≤ d) ∧ (∀ r, (G₀ r).degree ≤ d) ∧
    (∃ r, (G₀ r).degree = d) ∧ (∀ r, (F₀ r).coeff d + θ * (G₀ r).coeff d = 0) ∧
    L ≤ #(interleavedCommonAgreementSet domain f g F₀ G₀)}

/-- A challenge `θ` is bad when some pair of tuples `F₀, G₀` of degree at most `d` fixes it.

Some row of `G₀` has degree exactly `d`, and every row satisfies `[X^d] F₀ r + θ [X^d] G₀ r = 0`.
The pair agrees with `(f, g)` in every row on at least `L` common points. -/
@[simp]
theorem mem_badInterleavedEqualDegreeChallenges [Fintype F] (domain : ι ↪ F)
    (f g : Fin t → ι → F) (d L : ℕ) (θ : F) :
    θ ∈ badInterleavedEqualDegreeChallenges domain f g d L ↔
      ∃ F₀ G₀ : Fin t → F[X], (∀ r, (F₀ r).degree ≤ d) ∧ (∀ r, (G₀ r).degree ≤ d) ∧
        (∃ r, (G₀ r).degree = d) ∧ (∀ r, (F₀ r).coeff d + θ * (G₀ r).coeff d = 0) ∧
        L ≤ #(interleavedCommonAgreementSet domain f g F₀ G₀) := by
  simp [badInterleavedEqualDegreeChallenges]

/-- An exceptional tuple is affine exceptional, or a pair of tuples of degree `d` fixes `θ`.

The affine alternative is for the rows `(g r, f r + θ g r)`.
The pair `F₀, G₀` has rows of degree at most `d`, and some row of `G₀` has degree `d`.
Every row satisfies `[X^d] F₀ r + θ [X^d] G₀ r = 0`.
It agrees with `(f, g)` in every row on at least `A - s` points, with the subtraction in `ℕ`. -/
theorem IsInterleavedEqualDegreeExceptional.isInterleavedAffineExceptional_or_exists
    {domain : ι ↪ F} {f g : Fin t → ι → F} {d A s : ℕ} {θ α β : F} {P : Fin t → F[X]}
    (h : IsInterleavedEqualDegreeExceptional domain f g d A s θ α β P) :
    IsInterleavedAffineExceptional domain g (fun r i ↦ f r i + θ * g r i) d A s α β P ∨
      ∃ F₀ G₀ : Fin t → F[X], (∀ r, (F₀ r).degree ≤ d) ∧ (∀ r, (G₀ r).degree ≤ d) ∧
        (∃ r, (G₀ r).degree = d) ∧ (∀ r, (F₀ r).coeff d + θ * (G₀ r).coeff d = 0) ∧
        A - s ≤ #(interleavedCommonAgreementSet domain f g F₀ G₀) := by
  classical
  obtain ⟨hP, hA, hexc⟩ := h
  rw [interleavedEqualDegreeAgreementSet_eq_interleavedAgreementSet] at hA
  by_cases haff : IsInterleavedAffineExceptional domain g (fun r i ↦ f r i + θ * g r i)
    d A s α β P
  · exact Or.inl haff
  right
  obtain ⟨U, V, hU, hV, hw⟩ : ∃ U V : Fin t → F[X], (∀ r, (U r).degree ≤ d) ∧
      (∀ r, (V r).degree < d) ∧
      IsInterleavedLossWitness domain g (fun r i ↦ f r i + θ * g r i) s α β P U V := by
    by_contra hno
    push Not at hno
    exact haff ⟨hP, hA, fun U V hU hV hw ↦ hno U V hU hV hw⟩
  have hloss_eq : interleavedEqualDegreeAgreementLoss domain f g θ α β P
      (fun r ↦ V r - C θ * U r) U =
      interleavedAgreementLoss domain g (fun r i ↦ f r i + θ * g r i) α β P U V := by
    ext i
    simp only [mem_interleavedEqualDegreeAgreementLoss, mem_interleavedAgreementLoss,
      interleavedEqualDegreeAgreementSet_eq_interleavedAgreementSet]
    refine and_congr_right fun _ ↦ exists_congr fun r ↦ ?_
    by_cases hu : (U r).eval (domain i) = g r i
    · simp only [eval_sub, eval_mul, eval_C, hu, ne_eq, not_true_eq_false, or_false, false_or]
      constructor <;> intro h₁ h₂ <;> apply h₁ <;> linear_combination h₂
    · simp [hu]
  have hCU (r : Fin t) : (C θ * U r).degree ≤ (U r).degree := by
    rw [← smul_eq_C_mul]
    exact degree_smul_le θ (U r)
  have hFdeg (r : Fin t) : (V r - C θ * U r).degree ≤ d :=
    (degree_sub_le _ _).trans (max_le (hV r).le ((hCU r).trans (hU r)))
  have hUd : ∃ r, (U r).degree = d := by
    by_contra hno
    push Not at hno
    have hlt (r : Fin t) : (U r).degree < d := lt_of_le_of_ne (hU r) (hno r)
    have := hexc (fun r ↦ V r - C θ * U r) U
      (fun r ↦ (degree_sub_le _ _).trans_lt (max_lt (hV r) ((hCU r).trans_lt (hlt r)))) hlt
      (fun r ↦ by rw [hw.1 r]; ring)
    rw [hloss_eq] at this
    exact absurd hw.2 (not_le.mpr this)
  refine ⟨fun r ↦ V r - C θ * U r, U, hFdeg, hU, hUd, fun r ↦ ?_, ?_⟩
  · simp [coeff_C_mul, coeff_eq_zero_of_degree_lt (hV r)]
  · refine (Nat.sub_le_sub_left hw.2 A).trans ((Nat.sub_le_sub_right hA _).trans
      ((Finset.le_card_sdiff _ _).trans (Finset.card_le_card fun i hi ↦ ?_)))
    obtain ⟨hiP, hiL⟩ := Finset.mem_sdiff.mp hi
    rw [mem_interleavedAgreementLoss] at hiL
    simp only [hiP, true_and, not_exists, not_or, not_not] at hiL
    rw [mem_interleavedCommonAgreementSet]
    intro r
    simp only [eval_sub, eval_mul, eval_C, (hiL r).1, (hiL r).2]
    exact ⟨by ring, trivial⟩

/-- The bad-challenge count satisfies `#B · (L² - nd) ≤ n · (L - d)`, with subtractions in `ℕ`.

Here `n` is the domain size.
The set `B` holds the challenges `θ` with a pair of tuples `F₀, G₀` of degree at most `d`.
Some row of `G₀` has degree exactly `d`.
Every row satisfies `[X^d] F₀ r + θ [X^d] G₀ r = 0`.
The pair agrees with `(f, g)` in every row on at least `L` common points.
The pair fixes `θ`, so distinct bad values give distinct pairs. -/
theorem card_badInterleavedEqualDegreeChallenges_mul_le [Fintype F] (domain : ι ↪ F)
    (f g : Fin t → ι → F) (d L : ℕ) :
    #(badInterleavedEqualDegreeChallenges domain f g d L) *
      (L * L - Fintype.card ι * d) ≤ Fintype.card ι * (L - d) := by
  classical
  set T := badInterleavedEqualDegreeChallenges domain f g d L
  have hT (θ : F) (hθ : θ ∈ T) := (mem_badInterleavedEqualDegreeChallenges domain f g d L θ).mp hθ
  choose! F₀ G₀ hF hG hGd hc hL using hT
  refine Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le T
    (fun θ ↦ interleavedCommonAgreementSet domain f g (F₀ θ) (G₀ θ)) L d hL ?_
  intro θ hθ θ' hθ' hne
  refine card_inter_interleavedCommonAgreementSet_le domain f g (hF θ hθ) (hG θ hθ)
    (hF θ' hθ') (hG θ' hθ') fun heq ↦ hne ?_
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
  obtain ⟨r, hr⟩ := hGd θ hθ
  have hlead : (G₀ θ r).coeff d ≠ 0 := by
    rw [← natDegree_eq_of_degree_eq_some hr]
    exact leadingCoeff_ne_zero.mpr fun h0 ↦ by simp [h0] at hr
  have := (hc θ hθ r).trans (hc θ' hθ' r).symm
  rw [h₁, h₂] at this
  exact mul_right_cancel₀ (h₂ ▸ hlead) (add_left_cancel this)

end Reduction

section Bound

/-- The interleaved equal-degree error at shared loss one is at most the affine one plus `ℓ₀/q`.

Assume `nd < (A - 1)²`.
The number `t` of rows is arbitrary, `n` is the domain size, and `q` is the field size.
Here `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋` is the rounded-down Johnson bound. -/
theorem interleavedEqualDegreeMcaError_le_interleavedAffineMcaError_add [Fintype F]
    (domain : ι ↪ F) (t : ℕ) {d A : ℕ} (hJ : Fintype.card ι * d < (A - 1) ^ 2) :
    interleavedEqualDegreeMcaError domain t d A 1 ≤ interleavedAffineMcaError domain t d A 1 +
      ENNReal.ofReal
        (((⌊(Fintype.card ι : ℝ) * ((A : ℝ) - 1 - d) /
          (((A : ℝ) - 1) ^ 2 - Fintype.card ι * d)⌋₊ : ℕ) : ℝ) / Fintype.card F) := by
  classical
  refine iSup_le fun w ↦ ?_
  obtain ⟨f, g⟩ := w
  set q : ℝ := (Fintype.card F : ℝ)
  set n : ℕ := Fintype.card ι
  set ℓ₀ := ⌊(n : ℝ) * ((A : ℝ) - 1 - d) / (((A : ℝ) - 1) ^ 2 - n * d)⌋₊
  set E := (interleavedAffineMcaError domain t d A 1).toReal
  have hE : interleavedAffineMcaError domain t d A 1 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (interleavedAffineMcaError_le_one domain t d A 1)
  have hq : 0 < q := by positivity
  -- Exceptional triples are interleaved affine exceptional, or their `θ` is bad.
  set B := badInterleavedEqualDegreeChallenges domain f g d (A - 1)
  have hp (c : F × F × F)
      (hc : ∃ P, IsInterleavedEqualDegreeExceptional domain f g d A 1 c.1 c.2.1 c.2.2 P) :
      (∃ P, IsInterleavedAffineExceptional domain g (fun r i ↦ f r i + c.1 * g r i) d A 1
        c.2.1 c.2.2 P) ∨ c.1 ∈ B := by
    obtain ⟨P, hP⟩ := hc
    rcases hP.isInterleavedAffineExceptional_or_exists with h | h
    · exact Or.inl ⟨P, h⟩
    · exact Or.inr ((mem_badInterleavedEqualDegreeChallenges ..).mpr h)
  -- For each `θ`, the interleaved affine error bounds the exceptional pairs `(α, β)`.
  have ha (θ : F) : (#{x : F × F | ∃ P, IsInterleavedAffineExceptional domain g
      (fun r i ↦ f r i + θ * g r i) d A 1 x.1 x.2 P} : ℝ) ≤ q ^ 2 * E := by
    have hcount := (ENNReal.ofReal_le_iff_le_toReal hE).mp
      (le_interleavedAffineMcaError domain d A 1 g (fun r i ↦ f r i + θ * g r i))
    rw [div_le_iff₀ (by positivity)] at hcount
    simpa [mul_comm] using hcount
  -- The Johnson bound on the bad values of `θ`.
  have hA1 : 1 ≤ A := by
    rcases A with _ | A
    · simp at hJ
    · omega
  have hBfloor : (#B : ℝ) ≤ (ℓ₀ : ℝ) := by
    have h := le_floor_johnson_of_mul_le hJ
      (card_badInterleavedEqualDegreeChallenges_mul_le domain f g d (A - 1))
    simp only [Nat.cast_sub hA1, Nat.cast_one] at h
    exact Nat.cast_le.mpr h
  have hcount : (#{c : F × F × F | ∃ P,
        IsInterleavedEqualDegreeExceptional domain f g d A 1 c.1 c.2.1 c.2.2 P} : ℝ) / q ^ 3 ≤
        E + (ℓ₀ : ℝ) / q := by
    have key := Finset.card_filter_triples_le_of_imp_or B hp ha
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ q ^ 3 * E + #B * q ^ 2 := key
      _ ≤ q ^ 3 * E + (ℓ₀ : ℝ) * q ^ 2 := by gcongr
      _ = (E + (ℓ₀ : ℝ) / q) * q ^ 3 := by field_simp
  calc _ ≤ ENNReal.ofReal (E + (ℓ₀ : ℝ) / q) := ENNReal.ofReal_le_ofReal hcount
    _ = _ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hE]

/-- The interleaved equal-degree error is at most `(4/η + ℓ₀)/q + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.

The shared loss is one.

The number `t` of rows is arbitrary.
Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
The threshold is `A = ⌈(√ρ + η) n⌉` and `ℓ₀ = ⌊n(A - 1 - d)/((A - 1)² - nd)⌋`. -/
theorem interleavedEqualDegreeMcaError_le [Fintype F] (domain : ι ↪ F) (t : ℕ) {d : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    interleavedEqualDegreeMcaError domain t d
        ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 ≤
      ENNReal.ofReal ((4 / η +
        ((⌊(Fintype.card ι : ℝ) *
          ((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1 - d) /
          (((⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ : ℝ) - 1) ^ 2 -
            Fintype.card ι * d)⌋₊ : ℕ) : ℝ)) / Fintype.card F +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 /
          (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10 * (Fintype.card F : ℝ) ^ 2)) := by
  have hJ := affineThreshold_johnson hd hdn hη hn
  unfold affineThreshold at hJ
  refine (interleavedEqualDegreeMcaError_le_interleavedAffineMcaError_add domain t hJ).trans ?_
  refine (add_le_add_left (interleavedAffineMcaError_le domain t hd hdn hη hη1 hn) _).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp
  ring

end Bound

end ReedSolomon

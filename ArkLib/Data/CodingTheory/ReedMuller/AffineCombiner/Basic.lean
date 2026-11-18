/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

module

public import ArkLib.Data.CodingTheory.ReedMuller.Grid
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Basic.ENNReal.Real

/-!
# Affine combiners for Reed–Muller codes

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, and let `n = q₀ᵏ` be the size of the grid `K₀ᵏ`.
Received words are functions on the grid, and degrees of polynomials in `F[X₁, …, Xₖ]` are total.
A coefficient vector `α ∈ F^{k+1}` defines the affine multiplier `L_α = α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`.
It combines received words `f, g` into `z ↦ f z + L_α(z) g z`.

A witness pair decomposes a candidate `P` as `P = F₀ + L_α G₀`.
Its agreement loss counts grid points where `P` agrees with the combined word but either witness
fails to agree with its received word.
A candidate of total degree at most `d` with at least `A` agreements is exceptional if no witness
pair of total degrees `≤ d` and `< d` has loss at most `s`.
The error is the supremum, over received word pairs, of the fraction of coefficient vectors for
which some candidate is exceptional.

The definitions follow Section 7 of [CWYZ26], where the error is written `εRM(k, q₀, ρ, A, s, q)`.
The degree bound `d` stands for `ρ q₀`.
The paper uses `1 ≤ A ≤ n`.
The Lean definitions also cover boundary values.
If `A > n`, no candidate is exceptional.
If `d = 0`, no witness pair exists, since no total degree is below zero.
Every candidate of total degree zero with at least `A` agreements is then exceptional.
For `k = 1` and `K₀ = F`, they match the affine combiner definitions on the domain `F`.
Only the case `d = 0` differs, where the univariate second witness may still be zero.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Computability

The error has type `ENNReal` and a counting definition that requires no sampler.
`ReedSolomon.reedMullerMcaError_eq_iSup_prob` in `ReedMuller.AffineCombiner.Probability`
identifies it with a supremum of native uniform probabilities.
The counting definitions use classical decidability for predicates over polynomial witnesses.
The multiplier, combined word, agreement set and loss use noncomputable multivariate polynomial
evaluation.

## Main definitions

* `ReedSolomon.reedMullerMultiplier`: the polynomial `α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`.
* `ReedSolomon.reedMullerCombinedWord`: the combined word `f + L g` on the grid.
* `ReedSolomon.reedMullerAgreementSet` and `ReedSolomon.reedMullerAgreementLoss`:
  agreement points and lost points.
* `ReedSolomon.IsReedMullerLossWitness` and `ReedSolomon.IsReedMullerExceptional`:
  witness pairs and exceptional candidates.
* `ReedSolomon.reedMullerMcaError`: the uniform error probability.

## Main statements

* `ReedSolomon.eval_reedMullerMultiplier`, `ReedSolomon.coeff_zero_reedMullerMultiplier`,
  `ReedSolomon.coeff_single_reedMullerMultiplier`: values and coefficients of the multiplier.
* `ReedSolomon.reedMullerMultiplier_injective`, `ReedSolomon.reedMullerMultiplier_zero`,
  `ReedSolomon.reedMullerMultiplier_sub`, `ReedSolomon.reedMullerMultiplier_smul`:
  the multiplier is an injective linear function of `α`.
* `ReedSolomon.totalDegree_reedMullerMultiplier_le` and
  `ReedSolomon.succ_eq_zero_of_totalDegree_reedMullerMultiplier_eq_zero`: its total degree.
* `ReedSolomon.le_reedMullerMcaError`: one word pair bounds the error from below.
* `ReedSolomon.reedMullerMcaError_le_of_forall_exists`: uniform counts bound the error.
* `ReedSolomon.reedMullerMcaError_le_one`: the error is at most one.
* `ReedSolomon.IsReedMullerExceptional.anti_loss` and
  `ReedSolomon.IsReedMullerExceptional.anti_threshold`: monotonicity in `s` and `A`.
* `ReedSolomon.not_isReedMullerExceptional_of_eval`: a second word of total degree below `d`
  excludes exceptionality.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial Finset ReedMuller

variable {K₀ : Type*} [Field K₀] {F : Type*} [Field F] [Algebra K₀ F] {k : ℕ}

/-- The affine multiplier `α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`. -/
noncomputable def reedMullerMultiplier (α : Fin (k + 1) → F) : MvPolynomial (Fin k) F :=
  C (α 0) + ∑ i, C (α i.succ) * X i

/-- The multiplier evaluates to `α₀ + α₁ x₁ + ⋯ + αₖ xₖ` at `x`. -/
@[simp]
theorem eval_reedMullerMultiplier (α : Fin (k + 1) → F) (x : Fin k → F) :
    eval x (reedMullerMultiplier α) = α 0 + ∑ i, α i.succ * x i := by
  simp [reedMullerMultiplier]

/-- The constant coefficient of the multiplier is `α₀`. -/
@[simp]
theorem coeff_zero_reedMullerMultiplier (α : Fin (k + 1) → F) :
    (reedMullerMultiplier α).coeff 0 = α 0 := by
  simp [reedMullerMultiplier, coeff_C, coeff_X]

/-- The coefficient of `Xᵢ` in the multiplier is `αᵢ₊₁`. -/
@[simp]
theorem coeff_single_reedMullerMultiplier (α : Fin (k + 1) → F) (i : Fin k) :
    (reedMullerMultiplier α).coeff (Finsupp.single i 1) = α i.succ := by
  have h0 : (0 : Fin k →₀ ℕ) ≠ Finsupp.single i 1 :=
    (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  simp [h0, reedMullerMultiplier, coeff_C, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]

/-- Distinct coefficient vectors give distinct multipliers. -/
theorem reedMullerMultiplier_injective :
    Function.Injective (reedMullerMultiplier : (Fin (k + 1) → F) → MvPolynomial (Fin k) F) := by
  intro α α' h
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simpa using congrArg (fun p ↦ p.coeff 0) h
  · simpa using congrArg (fun p ↦ p.coeff (Finsupp.single i 1)) h

/-- The multiplier has total degree at most one. -/
theorem totalDegree_reedMullerMultiplier_le (α : Fin (k + 1) → F) :
    (reedMullerMultiplier α).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  exact (totalDegree_mul _ _).trans (by simp)

/-- The multiplier of a difference of coefficient vectors is the difference of multipliers. -/
theorem reedMullerMultiplier_sub (α α' : Fin (k + 1) → F) :
    reedMullerMultiplier (α - α') = reedMullerMultiplier α - reedMullerMultiplier α' := by
  simp only [reedMullerMultiplier, Pi.sub_apply, map_sub, sub_mul, sum_sub_distrib]
  ring

/-- The zero coefficient vector gives the zero multiplier. -/
@[simp]
theorem reedMullerMultiplier_zero :
    reedMullerMultiplier (0 : Fin (k + 1) → F) = 0 := by
  simp [reedMullerMultiplier]

/-- Scaling the coefficient vector scales the multiplier. -/
theorem reedMullerMultiplier_smul (c : F) (α : Fin (k + 1) → F) :
    reedMullerMultiplier (c • α) = C c * reedMullerMultiplier α := by
  simp only [reedMullerMultiplier, Pi.smul_apply, smul_eq_mul, map_mul, mul_add, mul_sum]
  ring_nf

/-- A multiplier of total degree zero has no linear part. -/
theorem succ_eq_zero_of_totalDegree_reedMullerMultiplier_eq_zero {α : Fin (k + 1) → F}
    (h : (reedMullerMultiplier α).totalDegree = 0) (i : Fin k) : α i.succ = 0 := by
  rw [← coeff_single_reedMullerMultiplier α i, totalDegree_eq_zero_iff_eq_C.mp h, coeff_C]
  simp [eq_comm (a := (0 : Fin k →₀ ℕ))]

/-- The word `z ↦ f z + L(z) g z` on the grid `K₀ᵏ`. -/
noncomputable def reedMullerCombinedWord (f g : (Fin k → K₀) → F) (L : MvPolynomial (Fin k) F) :
    (Fin k → K₀) → F :=
  fun z ↦ f z + eval (gridPoint F z) L * g z

/-- The combined word at a grid point. -/
@[simp]
theorem reedMullerCombinedWord_apply (f g : (Fin k → K₀) → F) (L : MvPolynomial (Fin k) F)
    (z : Fin k → K₀) :
    reedMullerCombinedWord f g L z = f z + eval (gridPoint F z) L * g z :=
  rfl

variable [DecidableEq F] [Fintype K₀]

/-- The grid points where `P` agrees with a word `w`. -/
noncomputable def reedMullerAgreementSet (w : (Fin k → K₀) → F) (P : MvPolynomial (Fin k) F) :
    Finset (Fin k → K₀) :=
  {z | eval (gridPoint F z) P = w z}

/-- Membership in the agreement set is the evaluation equality. -/
@[simp]
theorem mem_reedMullerAgreementSet (w : (Fin k → K₀) → F) (P : MvPolynomial (Fin k) F)
    (z : Fin k → K₀) :
    z ∈ reedMullerAgreementSet w P ↔ eval (gridPoint F z) P = w z := by
  simp [reedMullerAgreementSet]

/-- The agreement points of `P` with `f + L g` where `F₀ ≠ f` or `G₀ ≠ g`. -/
noncomputable def reedMullerAgreementLoss (f g : (Fin k → K₀) → F)
    (L P F₀ G₀ : MvPolynomial (Fin k) F) : Finset (Fin k → K₀) :=
  (reedMullerAgreementSet (reedMullerCombinedWord f g L) P).filter fun z ↦
    eval (gridPoint F z) F₀ ≠ f z ∨ eval (gridPoint F z) G₀ ≠ g z

/-- A lost point is an agreement point where a witness disagrees with its received word. -/
@[simp]
theorem mem_reedMullerAgreementLoss (f g : (Fin k → K₀) → F)
    (L P F₀ G₀ : MvPolynomial (Fin k) F) (z : Fin k → K₀) :
    z ∈ reedMullerAgreementLoss f g L P F₀ G₀ ↔
      eval (gridPoint F z) P = reedMullerCombinedWord f g L z ∧
        (eval (gridPoint F z) F₀ ≠ f z ∨ eval (gridPoint F z) G₀ ≠ g z) := by
  simp [reedMullerAgreementLoss]

/-- `P = F₀ + L G₀`, with at most `s` points of agreement loss. -/
def IsReedMullerLossWitness (f g : (Fin k → K₀) → F) (s : ℕ)
    (L P F₀ G₀ : MvPolynomial (Fin k) F) : Prop :=
  P = F₀ + L * G₀ ∧ #(reedMullerAgreementLoss f g L P F₀ G₀) ≤ s

/-- `P` is exceptional for the coefficient vector `α` at threshold `A` and loss `s`.

It has total degree at most `d` and agrees with `f + L_α g` on at least `A` grid points,
where `L_α = α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`.
No witness pair with total degrees `≤ d` and `< d` has agreement loss at most `s`. -/
def IsReedMullerExceptional (f g : (Fin k → K₀) → F) (d A s : ℕ) (α : Fin (k + 1) → F)
    (P : MvPolynomial (Fin k) F) : Prop :=
  P.totalDegree ≤ d ∧
    A ≤ #(reedMullerAgreementSet (reedMullerCombinedWord f g (reedMullerMultiplier α)) P) ∧
    ∀ F₀ G₀ : MvPolynomial (Fin k) F, F₀.totalDegree ≤ d → G₀.totalDegree < d →
      ¬ IsReedMullerLossWitness f g s (reedMullerMultiplier α) P F₀ G₀

variable (K₀ F) in
open Classical in
/-- The supremum over received word pairs `(f, g)` on the grid `K₀ᵏ` of the probability that
some candidate is exceptional for a uniform coefficient vector `α ∈ F^{k+1}`.

Here `K₀ ⊆ F` are finite fields through `algebraMap`, and candidates are polynomials over `F` in
`k` variables.

The output total degree bound is `d`, the agreement threshold is `A`, and the allowed loss
is `s`.
Witness total degrees are at most `d` and below `d`.
`ReedSolomon.reedMullerMcaError_eq_iSup_prob` gives the native sampling characterization. -/
noncomputable def reedMullerMcaError [Fintype F] (k d A s : ℕ) : ENNReal :=
  ⨆ w : ((Fin k → K₀) → F) × ((Fin k → K₀) → F),
    ENNReal.ofReal
      ((#{α : Fin (k + 1) → F | ∃ P, IsReedMullerExceptional w.1 w.2 d A s α P} : ℝ) /
        (Fintype.card F : ℝ) ^ (k + 1))

section Error

variable [Fintype F]

open Classical in
/-- One pair of received words bounds the Reed–Muller error from below. -/
theorem le_reedMullerMcaError (d A s : ℕ) (f g : (Fin k → K₀) → F) :
    ENNReal.ofReal
      ((#{α : Fin (k + 1) → F | ∃ P, IsReedMullerExceptional f g d A s α P} : ℝ) /
        (Fintype.card F : ℝ) ^ (k + 1)) ≤ reedMullerMcaError K₀ F k d A s := by
  unfold reedMullerMcaError
  exact le_iSup_of_le (f, g) le_rfl

/-- Suppose every word pair has a set of at most `B` coefficient vectors containing every
exceptional one.
Then the error is at most `B / q^{k+1}`, where `q = |F|`. -/
theorem reedMullerMcaError_le_of_forall_exists {d A s : ℕ} {B : ℝ}
    (h : ∀ f g : (Fin k → K₀) → F, ∃ E : Finset (Fin (k + 1) → F), (E.card : ℝ) ≤ B ∧
      ∀ α ∉ E, ∀ P, ¬ IsReedMullerExceptional f g d A s α P) :
    reedMullerMcaError K₀ F k d A s ≤
      ENNReal.ofReal (B / (Fintype.card F : ℝ) ^ (k + 1)) := by
  classical
  refine iSup_le fun w ↦ ENNReal.ofReal_le_ofReal ?_
  obtain ⟨E, hE, hgood⟩ := h w.1 w.2
  gcongr
  calc (#{α : Fin (k + 1) → F | ∃ P, IsReedMullerExceptional w.1 w.2 d A s α P} : ℝ)
      ≤ E.card := by
        gcongr
        intro α hα
        by_contra hαE
        obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hα).2
        exact hgood α hαE P hP
    _ ≤ B := hE

/-- The Reed–Muller error is at most one. -/
theorem reedMullerMcaError_le_one (k d A s : ℕ) : reedMullerMcaError K₀ F k d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (pow_pos (by exact_mod_cast Fintype.card_pos) _)]
  calc (#{α : Fin (k + 1) → F | ∃ P, IsReedMullerExceptional w.1 w.2 d A s α P} : ℝ)
      ≤ (Finset.univ : Finset (Fin (k + 1) → F)).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ (k + 1) := by simp

end Error

/-- An exceptional candidate stays exceptional for a smaller agreement loss. -/
theorem IsReedMullerExceptional.anti_loss {f g : (Fin k → K₀) → F} {d A s s' : ℕ}
    {α : Fin (k + 1) → F} {P : MvPolynomial (Fin k) F}
    (h : IsReedMullerExceptional f g d A s α P) (hs : s' ≤ s) :
    IsReedMullerExceptional f g d A s' α P :=
  ⟨h.1, h.2.1, fun F₀ G₀ hF hG hw ↦ h.2.2 F₀ G₀ hF hG ⟨hw.1, hw.2.trans hs⟩⟩

/-- An exceptional candidate stays exceptional for a smaller agreement threshold. -/
theorem IsReedMullerExceptional.anti_threshold {f g : (Fin k → K₀) → F} {d A A' s : ℕ}
    {α : Fin (k + 1) → F} {P : MvPolynomial (Fin k) F}
    (h : IsReedMullerExceptional f g d A s α P) (hA : A' ≤ A) :
    IsReedMullerExceptional f g d A' s α P :=
  ⟨h.1, hA.trans h.2.1, h.2.2⟩

/-- If `g` evaluates a polynomial `G₀` of total degree below `d` on the grid, no candidate is
exceptional for any first received word `f`.
The threshold `A` and allowed loss `s` are unrestricted.

The witnesses are `P - L_α G₀` and `G₀`, with no agreement loss. -/
theorem not_isReedMullerExceptional_of_eval {d A s : ℕ} (f : (Fin k → K₀) → F)
    (G₀ : MvPolynomial (Fin k) F) (hG : G₀.totalDegree < d) (α : Fin (k + 1) → F)
    (P : MvPolynomial (Fin k) F) :
    ¬ IsReedMullerExceptional f (fun z ↦ eval (gridPoint F z) G₀) d A s α P := by
  rintro ⟨hP, -, h⟩
  refine h (P - reedMullerMultiplier α * G₀) G₀ ?_ hG ⟨by ring, ?_⟩
  · refine (totalDegree_sub _ _).trans (max_le hP ?_)
    refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_reedMullerMultiplier_le α
    omega
  · rw [Finset.card_eq_zero.mpr]
    · exact Nat.zero_le _
    refine Finset.eq_empty_of_forall_notMem fun z hz ↦ ?_
    rw [mem_reedMullerAgreementLoss, reedMullerCombinedWord_apply] at hz
    obtain ⟨hz, hne⟩ := hz
    simp only [map_sub, map_mul] at hne
    rw [hz] at hne
    simp at hne

end ReedSolomon

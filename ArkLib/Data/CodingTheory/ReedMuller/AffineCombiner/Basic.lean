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

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`.
The grid `K₀ᵏ` has `n = q₀ᵏ` points, and received words are functions on it.
Degrees of polynomials in `F[X₁, …, Xₖ]` are total degrees.
A coefficient vector `α ∈ F^{k+1}` defines the multiplier `L_α = α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`.
It combines received words `f, g` into the word `z ↦ f z + L_α(z) g z`.

A witness pair decomposes a candidate `P` as `P = F₀ + L_α G₀`.
Its loss counts agreement points of `P` where a witness disagrees with its received word.
Admissible witnesses have `deg F₀ ≤ d` and `G₀ = 0` or `deg G₀ < d`.
A candidate `P` with `deg P ≤ d` and at least `A` agreements is a candidate for `α`.
It is exceptional if no admissible pair has loss at most `s`.
The error is the worst case, over word pairs, of the fraction of exceptional vectors `α`.

The definitions follow Section 7 of [CWYZ26].
There the error is `εRM(k, q₀, ρ, A, s, q)`, and `d` stands for `ρ q₀`.
The case `G₀ = 0` is the paper's convention `deg 0 = -∞`.
These files do not prove Theorem 7.1 itself.

The paper uses `1 ≤ A ≤ n` and `d ≥ 1`.
The definitions also cover boundary values.
If `A > n`, no candidate is exceptional.
If `d = 0`, the only admissible second witness is `G₀ = 0`.

Informally, `k = 1` with `K₀ = F` recovers the univariate affine combiner on the domain `F`.
This correspondence is not formalized here.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Computability

The error has type `ENNReal` and a counting definition that requires no sampler.
A sibling module gives its native sampling characterization.
The counting definitions use classical decidability for predicates over polynomial witnesses.
The multiplier, combined word, agreement set and loss use noncomputable polynomial evaluation.

## Main definitions

* `ReedMuller.affineMultiplier`: the polynomial `α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`.
* `ReedMuller.combinedWord`: the combined word `f + L g` on the grid.
* `ReedMuller.affineCombinedWord`: the executable fold from the coefficients of the challenge.
* `ReedMuller.agreementSet` and `ReedMuller.agreementLoss`: agreement and lost points.
* `ReedMuller.IsLossWitness` and `ReedMuller.IsAffineExceptional`: witnesses and candidates.
* `ReedMuller.affineMcaError`: the uniform error probability.

## Main statements

* `ReedMuller.eval_affineMultiplier`: the value of the multiplier.
* `ReedMuller.coeff_zero_affineMultiplier` and `ReedMuller.coeff_single_affineMultiplier`:
  its coefficients.
* `ReedMuller.affineMultiplier_injective`, `ReedMuller.affineMultiplier_zero`,
  `ReedMuller.affineMultiplier_sub` and `ReedMuller.affineMultiplier_smul`: linearity in `α`.
* `ReedMuller.totalDegree_affineMultiplier_le` and
  `ReedMuller.succ_eq_zero_of_totalDegree_affineMultiplier_eq_zero`: its total degree.
* `ReedMuller.combinedWord_apply`, `ReedMuller.mem_agreementSet` and
  `ReedMuller.mem_agreementLoss`: unfolding lemmas.
* `ReedMuller.not_isAffineExceptional_of_card_lt` and
  `ReedMuller.affineMcaError_eq_zero_of_card_lt`: the case `A > n`.
* `ReedMuller.le_affineMcaError`: one word pair bounds the error from below.
* `ReedMuller.affineMcaError_le_of_forall_exists`: uniform counts bound the error.
* `ReedMuller.affineMcaError_le_one`: the error is at most one.
* `ReedMuller.IsAffineExceptional.anti_loss` and
  `ReedMuller.IsAffineExceptional.anti_threshold`: monotonicity in `s` and `A`.
* `ReedMuller.not_isAffineExceptional_of_eval`: an admissible second word excludes
  exceptionality.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open MvPolynomial Finset

variable {K₀ : Type*} [Field K₀] {F : Type*} [Field F] [Algebra K₀ F] {k : ℕ}

/-- The affine multiplier `α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`. -/
noncomputable def affineMultiplier (α : Fin (k + 1) → F) : MvPolynomial (Fin k) F :=
  C (α 0) + ∑ i, C (α i.succ) * X i

/-- The multiplier evaluates to `α₀ + α₁ x₁ + ⋯ + αₖ xₖ` at `x`. -/
@[simp]
theorem eval_affineMultiplier (α : Fin (k + 1) → F) (x : Fin k → F) :
    eval x (affineMultiplier α) = α 0 + ∑ i, α i.succ * x i := by
  simp [affineMultiplier]

/-- The constant coefficient of the multiplier is `α₀`. -/
@[simp]
theorem coeff_zero_affineMultiplier (α : Fin (k + 1) → F) :
    (affineMultiplier α).coeff 0 = α 0 := by
  simp [affineMultiplier, coeff_C, coeff_X]

/-- The coefficient of `Xᵢ` in the multiplier is `αᵢ₊₁`. -/
@[simp]
theorem coeff_single_affineMultiplier (α : Fin (k + 1) → F) (i : Fin k) :
    (affineMultiplier α).coeff (Finsupp.single i 1) = α i.succ := by
  have h0 : (0 : Fin k →₀ ℕ) ≠ Finsupp.single i 1 :=
    (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  simp [h0, affineMultiplier, coeff_C, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]

/-- Distinct coefficient vectors give distinct multipliers. -/
theorem affineMultiplier_injective :
    Function.Injective (affineMultiplier : (Fin (k + 1) → F) → MvPolynomial (Fin k) F) := by
  intro α α' h
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simpa using congrArg (fun p ↦ p.coeff 0) h
  · simpa using congrArg (fun p ↦ p.coeff (Finsupp.single i 1)) h

/-- The multiplier has total degree at most one. -/
theorem totalDegree_affineMultiplier_le (α : Fin (k + 1) → F) :
    (affineMultiplier α).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
  exact (totalDegree_mul _ _).trans (by simp)

/-- The multiplier of a difference of coefficient vectors is the difference of multipliers. -/
theorem affineMultiplier_sub (α α' : Fin (k + 1) → F) :
    affineMultiplier (α - α') = affineMultiplier α - affineMultiplier α' := by
  simp only [affineMultiplier, Pi.sub_apply, map_sub, sub_mul, sum_sub_distrib]
  ring

/-- The zero coefficient vector gives the zero multiplier. -/
@[simp]
theorem affineMultiplier_zero :
    affineMultiplier (0 : Fin (k + 1) → F) = 0 := by
  simp [affineMultiplier]

/-- Scaling the coefficient vector scales the multiplier. -/
theorem affineMultiplier_smul (c : F) (α : Fin (k + 1) → F) :
    affineMultiplier (c • α) = C c * affineMultiplier α := by
  simp only [affineMultiplier, Pi.smul_apply, smul_eq_mul, map_mul, mul_add, mul_sum]
  ring_nf

/-- A multiplier of total degree zero has no linear part. -/
theorem succ_eq_zero_of_totalDegree_affineMultiplier_eq_zero {α : Fin (k + 1) → F}
    (h : (affineMultiplier α).totalDegree = 0) (i : Fin k) : α i.succ = 0 := by
  rw [← coeff_single_affineMultiplier α i, totalDegree_eq_zero_iff_eq_C.mp h, coeff_C]
  simp [eq_comm (a := (0 : Fin k →₀ ℕ))]

/-- The word `z ↦ f z + L(z) g z` on the grid `K₀ᵏ`. -/
noncomputable def combinedWord (f g : (Fin k → K₀) → F) (L : MvPolynomial (Fin k) F) :
    (Fin k → K₀) → F :=
  fun z ↦ f z + eval (gridPoint F z) L * g z

/-- The combined word at a grid point. -/
@[simp]
theorem combinedWord_apply (f g : (Fin k → K₀) → F) (L : MvPolynomial (Fin k) F)
    (z : Fin k → K₀) :
    combinedWord f g L z = f z + eval (gridPoint F z) L * g z :=
  rfl

/-- Combine the words directly from the affine coefficients of the challenge. -/
def affineCombinedWord (f g : (Fin k → K₀) → F) (α : Fin (k + 1) → F) :
    (Fin k → K₀) → F :=
  fun z ↦ f z + (α 0 + ∑ i, α i.succ * gridPoint F z i) * g z

/-- Evaluating the affine multiplier gives the coefficient-based word combiner. -/
theorem affineCombinedWord_eq (f g : (Fin k → K₀) → F) (α : Fin (k + 1) → F) :
    affineCombinedWord f g α = combinedWord f g (affineMultiplier α) := by
  funext z
  simp [affineCombinedWord]

variable [DecidableEq F] [Fintype K₀]

/-- The grid points where `P` agrees with a word `w`. -/
noncomputable def agreementSet (w : (Fin k → K₀) → F) (P : MvPolynomial (Fin k) F) :
    Finset (Fin k → K₀) :=
  {z | eval (gridPoint F z) P = w z}

/-- Membership in the agreement set is the evaluation equality. -/
@[simp]
theorem mem_agreementSet (w : (Fin k → K₀) → F) (P : MvPolynomial (Fin k) F)
    (z : Fin k → K₀) :
    z ∈ agreementSet w P ↔ eval (gridPoint F z) P = w z := by
  simp [agreementSet]

/-- The agreement points of `P` with `f + L g` where `F₀ ≠ f` or `G₀ ≠ g`. -/
noncomputable def agreementLoss (f g : (Fin k → K₀) → F)
    (L P F₀ G₀ : MvPolynomial (Fin k) F) : Finset (Fin k → K₀) :=
  (agreementSet (combinedWord f g L) P).filter fun z ↦
    eval (gridPoint F z) F₀ ≠ f z ∨ eval (gridPoint F z) G₀ ≠ g z

/-- A lost point is an agreement point where a witness disagrees with its received word. -/
@[simp]
theorem mem_agreementLoss (f g : (Fin k → K₀) → F)
    (L P F₀ G₀ : MvPolynomial (Fin k) F) (z : Fin k → K₀) :
    z ∈ agreementLoss f g L P F₀ G₀ ↔
      eval (gridPoint F z) P = combinedWord f g L z ∧
        (eval (gridPoint F z) F₀ ≠ f z ∨ eval (gridPoint F z) G₀ ≠ g z) := by
  simp [agreementLoss]

/-- `P = F₀ + L G₀`, with at most `s` points of agreement loss. -/
def IsLossWitness (f g : (Fin k → K₀) → F) (s : ℕ)
    (L P F₀ G₀ : MvPolynomial (Fin k) F) : Prop :=
  P = F₀ + L * G₀ ∧ #(agreementLoss f g L P F₀ G₀) ≤ s

/-- `P` is exceptional for the coefficient vector `α` at threshold `A` and loss `s`.

Write `L_α = α₀ + α₁ X₁ + ⋯ + αₖ Xₖ`.

`P` has total degree at most `d` and agrees with `f + L_α g` on at least `A` grid points.

No pair `F₀, G₀` with `deg F₀ ≤ d` and `G₀ = 0` or `deg G₀ < d` has loss at most `s`.

Degrees are total degrees. -/
def IsAffineExceptional (f g : (Fin k → K₀) → F) (d A s : ℕ) (α : Fin (k + 1) → F)
    (P : MvPolynomial (Fin k) F) : Prop :=
  P.totalDegree ≤ d ∧
    A ≤ #(agreementSet (combinedWord f g (affineMultiplier α)) P) ∧
    ∀ F₀ G₀ : MvPolynomial (Fin k) F, F₀.totalDegree ≤ d → (G₀ = 0 ∨ G₀.totalDegree < d) →
      ¬ IsLossWitness f g s (affineMultiplier α) P F₀ G₀

variable (K₀ F) in
open Classical in
/-- The worst-case probability that some candidate is exceptional for a uniform `α ∈ F^{k+1}`.

The worst case ranges over received word pairs `(f, g)` on the grid `K₀ᵏ`.

Here `K₀ ⊆ F` are finite fields through `algebraMap`.

Candidates are polynomials over `F` in `k` variables.

The degree bound is `d`, the agreement threshold is `A`, and the allowed loss is `s`.

Witnesses are admissible as in the exceptional predicate.

`ReedMuller.affineMcaError_eq_iSup_prob` gives the native sampling characterization. -/
noncomputable def affineMcaError [Fintype F] (k d A s : ℕ) : ENNReal :=
  ⨆ w : ((Fin k → K₀) → F) × ((Fin k → K₀) → F),
    ENNReal.ofReal
      ((#{α : Fin (k + 1) → F | ∃ P, IsAffineExceptional w.1 w.2 d A s α P} : ℝ) /
        (Fintype.card F : ℝ) ^ (k + 1))

/-- If `A > q₀ᵏ`, no candidate is exceptional, since the grid has only `q₀ᵏ` points.

Here `q₀ = |K₀|`. -/
theorem not_isAffineExceptional_of_card_lt {f g : (Fin k → K₀) → F} {d A s : ℕ}
    {α : Fin (k + 1) → F} {P : MvPolynomial (Fin k) F} (hA : Fintype.card K₀ ^ k < A) :
    ¬ IsAffineExceptional f g d A s α P := by
  rintro ⟨-, h, -⟩
  have := card_le_univ (agreementSet (combinedWord f g (affineMultiplier α)) P)
  simp only [Fintype.card_fun, Fintype.card_fin] at this
  omega

section Error

variable [Fintype F]

open Classical in
/-- One pair of received words bounds the Reed–Muller error from below. -/
theorem le_affineMcaError (d A s : ℕ) (f g : (Fin k → K₀) → F) :
    ENNReal.ofReal
      ((#{α : Fin (k + 1) → F | ∃ P, IsAffineExceptional f g d A s α P} : ℝ) /
        (Fintype.card F : ℝ) ^ (k + 1)) ≤ affineMcaError K₀ F k d A s := by
  unfold affineMcaError
  exact le_iSup_of_le (f, g) le_rfl

/-- A uniform count of exceptional coefficient vectors bounds the error.

Suppose every word pair has a set of at most `B` vectors containing all exceptional ones.

Then the error is at most `B / q^{k+1}`, where `q = |F|`. -/
theorem affineMcaError_le_of_forall_exists {d A s : ℕ} {B : ℝ}
    (h : ∀ f g : (Fin k → K₀) → F, ∃ E : Finset (Fin (k + 1) → F), (E.card : ℝ) ≤ B ∧
      ∀ α ∉ E, ∀ P, ¬ IsAffineExceptional f g d A s α P) :
    affineMcaError K₀ F k d A s ≤
      ENNReal.ofReal (B / (Fintype.card F : ℝ) ^ (k + 1)) := by
  classical
  refine iSup_le fun w ↦ ENNReal.ofReal_le_ofReal ?_
  obtain ⟨E, hE, hgood⟩ := h w.1 w.2
  gcongr
  calc (#{α : Fin (k + 1) → F | ∃ P, IsAffineExceptional w.1 w.2 d A s α P} : ℝ)
      ≤ E.card := by
        gcongr
        intro α hα
        by_contra hαE
        obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hα).2
        exact hgood α hαE P hP
    _ ≤ B := hE

/-- If `A > q₀ᵏ`, the error is zero, where `q₀ = |K₀|`. -/
theorem affineMcaError_eq_zero_of_card_lt {d A s : ℕ} (hA : Fintype.card K₀ ^ k < A) :
    affineMcaError K₀ F k d A s = 0 := by
  refine le_antisymm ?_ zero_le
  have h := affineMcaError_le_of_forall_exists (K₀ := K₀) (F := F) (k := k) (d := d) (A := A)
    (s := s) (B := 0) fun _ _ ↦ ⟨∅, by simp, fun _ _ _ ↦ not_isAffineExceptional_of_card_lt hA⟩
  simpa using h

/-- The Reed–Muller error is at most one. -/
theorem affineMcaError_le_one (k d A s : ℕ) : affineMcaError K₀ F k d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (pow_pos (by exact_mod_cast Fintype.card_pos) _)]
  calc (#{α : Fin (k + 1) → F | ∃ P, IsAffineExceptional w.1 w.2 d A s α P} : ℝ)
      ≤ (Finset.univ : Finset (Fin (k + 1) → F)).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ (k + 1) := by simp

end Error

/-- An exceptional candidate stays exceptional for a smaller agreement loss. -/
theorem IsAffineExceptional.anti_loss {f g : (Fin k → K₀) → F} {d A s s' : ℕ}
    {α : Fin (k + 1) → F} {P : MvPolynomial (Fin k) F}
    (h : IsAffineExceptional f g d A s α P) (hs : s' ≤ s) :
    IsAffineExceptional f g d A s' α P :=
  ⟨h.1, h.2.1, fun F₀ G₀ hF hG hw ↦ h.2.2 F₀ G₀ hF hG ⟨hw.1, hw.2.trans hs⟩⟩

/-- An exceptional candidate stays exceptional for a smaller agreement threshold. -/
theorem IsAffineExceptional.anti_threshold {f g : (Fin k → K₀) → F} {d A A' s : ℕ}
    {α : Fin (k + 1) → F} {P : MvPolynomial (Fin k) F}
    (h : IsAffineExceptional f g d A s α P) (hA : A' ≤ A) :
    IsAffineExceptional f g d A' s α P :=
  ⟨h.1, hA.trans h.2.1, h.2.2⟩

/-- Let `g` evaluate a polynomial `G₀` on the grid, with `G₀ = 0` or `deg G₀ < d`.

Then no candidate is exceptional, for any first word `f`, threshold `A` and loss `s`.

The witnesses are `P - L_α G₀` and `G₀`, with no agreement loss. -/
theorem not_isAffineExceptional_of_eval {d A s : ℕ} (f : (Fin k → K₀) → F)
    (G₀ : MvPolynomial (Fin k) F) (hG : G₀ = 0 ∨ G₀.totalDegree < d) (α : Fin (k + 1) → F)
    (P : MvPolynomial (Fin k) F) :
    ¬ IsAffineExceptional f (fun z ↦ eval (gridPoint F z) G₀) d A s α P := by
  rintro ⟨hP, -, h⟩
  refine h (P - affineMultiplier α * G₀) G₀ ?_ hG ⟨by ring, ?_⟩
  · refine (totalDegree_sub _ _).trans (max_le hP ?_)
    rcases hG with rfl | hG
    · simp
    refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_affineMultiplier_le α
    omega
  · rw [Finset.card_eq_zero.mpr]
    · exact Nat.zero_le _
    refine Finset.eq_empty_of_forall_notMem fun z hz ↦ ?_
    rw [mem_agreementLoss, combinedWord_apply] at hz
    obtain ⟨hz, hne⟩ := hz
    simp only [map_sub, map_mul] at hne
    rw [hz] at hne
    simp at hne

end ReedMuller

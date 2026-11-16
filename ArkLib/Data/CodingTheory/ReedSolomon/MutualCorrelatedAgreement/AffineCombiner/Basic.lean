/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement

/-!
# Affine combiners and mutual correlated agreement with agreement loss

Two received words `f g : D → F` are combined by a multiplier polynomial `L` into the word
`x ↦ f x + L(x) g x`. A scalar combiner uses a constant `L = α`. An affine combiner uses
`L = α + β X`, which raises the degree by one, so the second witness has a smaller degree bound.

A candidate `P` agrees with the combined word on a set `S`. Polynomials `F₀ G₀` with
`P = F₀ + L G₀` witness `P` with agreement loss at most `s` if at most `s` points of `S` fail
`F₀ = f` or `G₀ = g`. The challenge is exceptional when some candidate of degree at most `d`
agrees on at least `A` points and has no witness within the degree bounds.

The MCA error is the largest fraction of exceptional challenges over all pairs of received words.
For the affine combiner the witness degrees are `d` for `F₀` and at most `d - 1` for `G₀`, so the
output degree stays `d`. For the scalar combiner both witness degrees are `d`.

## Computability

The exceptional predicates quantify over all polynomials, so they are not decidable in general,
and the two error functions are noncomputable mathematical views. The multiplier
`affineMultiplier α β` is a Mathlib polynomial, whose ring operations are noncomputable. The
combined word of an executable multiplier is the evaluation `x ↦ f x + (α + β x) g x`, given by
`combinedWord_affineMultiplier`.

## Main definitions

* `ReedSolomon.combinedWord`: the word `f + L g` on the domain.
* `ReedSolomon.affineMultiplier`: the multiplier `α + β X`.
* `ReedSolomon.agreementLoss`: the agreement points of `P` lost by the witnesses `F₀ G₀`.
* `ReedSolomon.IsLossWitness`: `P = F₀ + L G₀` with agreement loss at most `s`.
* `ReedSolomon.IsAffineExceptional` and `ReedSolomon.IsScalarExceptional`: exceptional candidates
  for the affine and the scalar combiner.
* `ReedSolomon.affineMCAError` and `ReedSolomon.scalarMCAError`: the worst-case fractions of
  exceptional challenges.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*}

/-- The combined word `x ↦ f x + L(x) g x` on the evaluation domain. -/
def combinedWord (domain : ι ↪ F) (f g : ι → F) (L : F[X]) : ι → F :=
  fun i ↦ f i + L.eval (domain i) * g i

/-- The affine multiplier `α + β X`. -/
noncomputable def affineMultiplier (α β : F) : F[X] :=
  C α + C β * X

@[simp]
theorem eval_affineMultiplier (α β x : F) : (affineMultiplier α β).eval x = α + β * x := by
  simp [affineMultiplier]

theorem degree_affineMultiplier_le (α β : F) : (affineMultiplier α β).degree ≤ 1 := by
  unfold affineMultiplier
  compute_degree

@[simp]
theorem combinedWord_affineMultiplier (domain : ι ↪ F) (f g : ι → F) (α β : F) (i : ι) :
    combinedWord domain f g (affineMultiplier α β) i = f i + (α + β * domain i) * g i := by
  simp [combinedWord]

@[simp]
theorem combinedWord_C (domain : ι ↪ F) (f g : ι → F) (α : F) (i : ι) :
    combinedWord domain f g (C α) i = f i + α * g i := by
  simp [combinedWord]

variable [DecidableEq F] [Fintype ι]

/-- The agreement points of `P` with the combined word `f + L g` where the witnesses `F₀ G₀` do
not both agree with `f g`. -/
def agreementLoss (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : F[X]) : Finset ι :=
  (polynomialAgreementSet domain (combinedWord domain f g L) P).filter fun i ↦
    F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i

/-- `F₀ G₀` witness `P` for the multiplier `L` with agreement loss at most `s`: `P = F₀ + L G₀`,
and at most `s` agreement points of `P` with `f + L g` have `F₀ ≠ f` or `G₀ ≠ g`. -/
def IsLossWitness (domain : ι ↪ F) (f g : ι → F) (s : ℕ) (L P F₀ G₀ : F[X]) : Prop :=
  P = F₀ + L * G₀ ∧ (agreementLoss domain f g L P F₀ G₀).card ≤ s

/-- The challenge `(α, β)` makes `P` exceptional for the affine combiner: `P` has degree at most
`d`, agrees with `f + (α + β x) g` on at least `A` points, and no pair `F₀ G₀` with
`deg F₀ ≤ d` and `deg G₀ ≤ d - 1` witnesses it with agreement loss at most `s`. -/
def IsAffineExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F) (P : F[X]) :
    Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree ≤ d → G₀.degree < d →
      ¬ IsLossWitness domain f g s (affineMultiplier α β) P F₀ G₀

/-- The challenge `α` makes `P` exceptional for the scalar combiner: `P` has degree at most `d`,
agrees with `f + α g` on at least `A` points, and no pair `F₀ G₀` of degree at most `d`
witnesses it with agreement loss at most `s`. -/
def IsScalarExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F) (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g (C α)) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree ≤ d → G₀.degree ≤ d →
      ¬ IsLossWitness domain f g s (C α) P F₀ G₀

open Classical in
/-- The affine-combiner MCA error at output degree `d`, agreement threshold `A` and agreement
loss `s`: the largest fraction, over all pairs of received words, of challenges `(α, β) ∈ F²`
that make some candidate exceptional. -/
noncomputable def affineMCAError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ℝ :=
  ⨆ w : (ι → F) × (ι → F),
    (#{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ) /
      (Fintype.card F : ℝ) ^ 2

open Classical in
/-- The scalar-combiner MCA error at degree `d`, agreement threshold `A` and agreement loss `s`:
the largest fraction, over all pairs of received words, of challenges `α ∈ F` that make some
candidate exceptional. -/
noncomputable def scalarMCAError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ℝ :=
  ⨆ w : (ι → F) × (ι → F),
    (#{α : F | ∃ P, IsScalarExceptional domain w.1 w.2 d A s α P} : ℝ) / (Fintype.card F : ℝ)

section Error

variable [Fintype F] (domain : ι ↪ F)

open Classical in
/-- One pair of received words bounds the affine MCA error from below. -/
theorem le_affineMCAError (d A s : ℕ) (f g : ι → F) :
    (#{c : F × F | ∃ P, IsAffineExceptional domain f g d A s c.1 c.2 P} : ℝ) /
        (Fintype.card F : ℝ) ^ 2 ≤ affineMCAError domain d A s :=
  le_ciSup (f := fun w : (ι → F) × (ι → F) ↦
    (#{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ) /
      (Fintype.card F : ℝ) ^ 2) (Set.finite_range _).bddAbove (f, g)

open Classical in
/-- One pair of received words bounds the scalar MCA error from below. -/
theorem le_scalarMCAError (d A s : ℕ) (f g : ι → F) :
    (#{α : F | ∃ P, IsScalarExceptional domain f g d A s α P} : ℝ) / (Fintype.card F : ℝ) ≤
      scalarMCAError domain d A s :=
  le_ciSup (f := fun w : (ι → F) × (ι → F) ↦
    (#{α : F | ∃ P, IsScalarExceptional domain w.1 w.2 d A s α P} : ℝ) /
      (Fintype.card F : ℝ)) (Set.finite_range _).bddAbove (f, g)

/-- A bound on the exceptional challenges of every pair of received words bounds the affine MCA
error. -/
theorem affineMCAError_le_of_forall_exists {d A s : ℕ} {B : ℝ}
    (h : ∀ f g : ι → F, ∃ E : Finset (F × F), (E.card : ℝ) ≤ B ∧
      ∀ c ∉ E, ∀ P, ¬ IsAffineExceptional domain f g d A s c.1 c.2 P) :
    affineMCAError domain d A s ≤ B / (Fintype.card F : ℝ) ^ 2 := by
  classical
  refine ciSup_le fun w ↦ ?_
  obtain ⟨E, hE, hgood⟩ := h w.1 w.2
  gcongr
  calc (#{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ)
      ≤ E.card := by
        gcongr
        intro c hc
        by_contra hcE
        obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hc).2
        exact hgood c hcE P hP
    _ ≤ B := hE

theorem affineMCAError_nonneg (d A s : ℕ) : 0 ≤ affineMCAError domain d A s :=
  le_trans (by positivity) (le_affineMCAError domain d A s 0 0)

theorem affineMCAError_le_one (d A s : ℕ) : affineMCAError domain d A s ≤ 1 := by
  classical
  refine ciSup_le fun w ↦ ?_
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ 2 := by positivity
  rw [div_le_one hq]
  calc (#{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ)
      ≤ (Finset.univ : Finset (F × F)).card := by exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ 2 := by simp [sq]

end Error

/-- An affine exceptional candidate stays exceptional for a smaller agreement loss. -/
theorem IsAffineExceptional.mono_loss {domain : ι ↪ F} {f g : ι → F} {d A s s' : ℕ} {α β : F}
    {P : F[X]} (h : IsAffineExceptional domain f g d A s α β P) (hs : s' ≤ s) :
    IsAffineExceptional domain f g d A s' α β P :=
  ⟨h.1, h.2.1, fun F₀ G₀ hF hG hw ↦ h.2.2 F₀ G₀ hF hG ⟨hw.1, hw.2.trans hs⟩⟩

/-- An affine exceptional candidate stays exceptional for a smaller agreement threshold. -/
theorem IsAffineExceptional.mono_threshold {domain : ι ↪ F} {f g : ι → F} {d A A' s : ℕ}
    {α β : F} {P : F[X]} (h : IsAffineExceptional domain f g d A s α β P) (hA : A' ≤ A) :
    IsAffineExceptional domain f g d A' s α β P :=
  ⟨h.1, hA.trans h.2.1, h.2.2⟩

/-- **Honest words are never exceptional.** If `f` and `g` are the evaluations of `F₀` and `G₀`
with `deg F₀ ≤ d` and `deg G₀ ≤ d - 1`, then no challenge makes the honest combination
`F₀ + (α + β X) G₀` exceptional, for every threshold and loss. -/
theorem not_isAffineExceptional_of_eval {domain : ι ↪ F} {d A s : ℕ} (F₀ G₀ : F[X])
    (hF : F₀.degree ≤ d) (hG : G₀.degree < d) (α β : F) :
    ¬ IsAffineExceptional domain (fun i ↦ F₀.eval (domain i)) (fun i ↦ G₀.eval (domain i)) d A s
      α β (F₀ + affineMultiplier α β * G₀) := by
  rintro ⟨-, -, h⟩
  refine h F₀ G₀ hF hG ⟨rfl, ?_⟩
  simp [agreementLoss]

end ReedSolomon

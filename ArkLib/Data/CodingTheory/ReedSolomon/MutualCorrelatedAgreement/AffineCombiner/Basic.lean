/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement

/-!
# Affine combiners: mutual correlated agreement with agreement loss

Two received words `f, g` are combined into `f + L g` by a multiplier polynomial `L`.

A scalar combiner uses `L = α`.

An affine combiner uses `L = α + β X`, so the second witness has degree below `d`.

A challenge is exceptional when a close candidate has no witness pair.

The error is the worst fraction of exceptional challenges over all received words.

## Witnesses with agreement loss

A pair `F₀, G₀` witnesses a candidate `P` when `P = F₀ + L G₀`.

Its agreement loss counts the agreement points of `P` where `F₀ ≠ f` or `G₀ ≠ g`.

## Junk values

The paper assumes `1 ≤ d < n` and `1 ≤ A ≤ n`.

For `A > n`, nothing is exceptional.

For `d = 0`, the affine witness `G₀` must be zero.

## Computability

The exceptional predicates quantify over all polynomials, so the two errors are noncomputable.

The affine multiplier is a Mathlib polynomial, whose arithmetic is noncomputable.

Its combined word is the plain evaluation `f x + (α + β x) g x`.

## Main definitions

* `ReedSolomon.combinedWord`: the word `f + L g` on the domain.
* `ReedSolomon.affineMultiplier`: the multiplier `α + β X`.
* `ReedSolomon.agreementLoss`: the agreement points of `P` lost by the witnesses `F₀ G₀`.
* `ReedSolomon.IsLossWitness`: `P = F₀ + L G₀` with agreement loss at most `s`.
* `ReedSolomon.IsAffineExceptional` and `ReedSolomon.IsScalarExceptional`: exceptional candidates
  for the affine and the scalar combiner.
* `ReedSolomon.affineMcaError` and `ReedSolomon.scalarMcaError`: the worst-case fractions of
  exceptional challenges.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*}

/-- The word `x ↦ f x + L(x) g x` on the evaluation domain. -/
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

/-- The agreement points of `P` with `f + L g` where `F₀ ≠ f` or `G₀ ≠ g`. -/
def agreementLoss (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : F[X]) : Finset ι :=
  (polynomialAgreementSet domain (combinedWord domain f g L) P).filter fun i ↦
    F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i

open Classical in
/-- Lost agreements are exactly the candidate's agreement set minus common witness agreement.

The coordinate equality needed by finset difference is local to this characterization. -/
theorem agreementLoss_eq_sdiff (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : F[X]) :
    agreementLoss domain f g L P F₀ G₀ =
      polynomialAgreementSet domain (combinedWord domain f g L) P \
        commonPolynomialAgreementSet domain f g F₀ G₀ := by
  classical
  ext i
  simp only [agreementLoss, mem_filter, mem_sdiff, mem_commonPolynomialAgreementSet]
  tauto

/-- `P = F₀ + L G₀`, with at most `s` points of agreement loss. -/
def IsLossWitness (domain : ι ↪ F) (f g : ι → F) (s : ℕ) (L P F₀ G₀ : F[X]) : Prop :=
  P = F₀ + L * G₀ ∧ (agreementLoss domain f g L P F₀ G₀).card ≤ s

/-- The challenge `(α, β)` makes `P` exceptional for the affine combiner.

`P` has degree at most `d` and agrees with `f + (α + β x) g` on at least `A` points.

No witness pair with `deg F₀ ≤ d` and `deg G₀ < d` has agreement loss at most `s`. -/
def IsAffineExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F) (P : F[X]) :
    Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree ≤ d → G₀.degree < d →
      ¬ IsLossWitness domain f g s (affineMultiplier α β) P F₀ G₀

/-- The challenge `α` makes `P` exceptional for the scalar combiner.

`P` has degree at most `d` and agrees with `f + α g` on at least `A` points.

No witness pair of degree at most `d` has agreement loss at most `s`. -/
def IsScalarExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F) (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g (C α)) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree ≤ d → G₀.degree ≤ d →
      ¬ IsLossWitness domain f g s (C α) P F₀ G₀

open Classical in
/-- The worst-case uniform probability of an affine exceptional challenge.

The counting definition needs no sampler. Its native probability characterization is
`affineMcaError_eq_iSup_prob` in `AffineCombiner.Probability`. -/
noncomputable def affineMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ENNReal :=
  ⨆ w : (ι → F) × (ι → F),
    ENNReal.ofReal
      ((#{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ) /
        (Fintype.card F : ℝ) ^ 2)

open Classical in
/-- The worst-case uniform probability of a scalar exceptional challenge.

The counting definition needs no sampler. At zero loss it is the canonical affine-line
`CoreDefinitions.mcaError`; see `scalarMcaError_zero_eq_mcaError`. -/
noncomputable def scalarMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ENNReal :=
  ⨆ w : (ι → F) × (ι → F),
    ENNReal.ofReal
      ((#{α : F | ∃ P, IsScalarExceptional domain w.1 w.2 d A s α P} : ℝ) /
        (Fintype.card F : ℝ))

section Error

variable [Fintype F] (domain : ι ↪ F)

open Classical in
/-- One pair of received words bounds the affine error from below. -/
theorem le_affineMcaError (d A s : ℕ) (f g : ι → F) :
    ENNReal.ofReal
      ((#{c : F × F | ∃ P, IsAffineExceptional domain f g d A s c.1 c.2 P} : ℝ) /
        (Fintype.card F : ℝ) ^ 2) ≤ affineMcaError domain d A s := by
  unfold affineMcaError
  exact le_iSup_of_le (f, g) le_rfl

open Classical in
/-- One pair of received words bounds the scalar error from below. -/
theorem le_scalarMcaError (d A s : ℕ) (f g : ι → F) :
    ENNReal.ofReal
      ((#{α : F | ∃ P, IsScalarExceptional domain f g d A s α P} : ℝ) /
        (Fintype.card F : ℝ)) ≤ scalarMcaError domain d A s := by
  unfold scalarMcaError
  exact le_iSup_of_le (f, g) le_rfl

/-- A uniform count of affine exceptional challenges bounds the error by `B / q²`. -/
theorem affineMcaError_le_of_forall_exists {d A s : ℕ} {B : ℝ}
    (h : ∀ f g : ι → F, ∃ E : Finset (F × F), (E.card : ℝ) ≤ B ∧
      ∀ c ∉ E, ∀ P, ¬ IsAffineExceptional domain f g d A s c.1 c.2 P) :
    affineMcaError domain d A s ≤ ENNReal.ofReal (B / (Fintype.card F : ℝ) ^ 2) := by
  classical
  refine iSup_le fun w ↦ ENNReal.ofReal_le_ofReal ?_
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

/-- A uniform count of scalar exceptional challenges bounds the error by `B / q`. -/
theorem scalarMcaError_le_of_forall_exists {d A s : ℕ} {B : ℝ}
    (h : ∀ f g : ι → F, ∃ E : Finset F, (E.card : ℝ) ≤ B ∧
      ∀ α ∉ E, ∀ P, ¬ IsScalarExceptional domain f g d A s α P) :
    scalarMcaError domain d A s ≤ ENNReal.ofReal (B / (Fintype.card F : ℝ)) := by
  classical
  refine iSup_le fun w ↦ ENNReal.ofReal_le_ofReal ?_
  obtain ⟨E, hE, hgood⟩ := h w.1 w.2
  gcongr
  calc (#{α : F | ∃ P, IsScalarExceptional domain w.1 w.2 d A s α P} : ℝ)
      ≤ E.card := by
        gcongr
        intro α hα
        by_contra hαE
        obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hα).2
        exact hgood α hαE P hP
    _ ≤ B := hE

/-- The affine error is at most one. -/
theorem affineMcaError_le_one (d A s : ℕ) : affineMcaError domain d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  calc (#{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ)
      ≤ (Finset.univ : Finset (F × F)).card := by exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ 2 := by simp [sq]

/-- The scalar error is at most one. -/
theorem scalarMcaError_le_one (d A s : ℕ) : scalarMcaError domain d A s ≤ 1 := by
  classical
  refine iSup_le fun w ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  exact_mod_cast Finset.card_filter_le (univ : Finset F) _

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

/-- Honest words are never exceptional.

If `g` evaluates a polynomial `G₀` of degree below `d`, no candidate is exceptional.

The witnesses are `P - (α + β X) G₀` and `G₀`, with no agreement loss. -/
theorem not_isAffineExceptional_of_eval {domain : ι ↪ F} {d A s : ℕ} (f : ι → F) (G₀ : F[X])
    (hG : G₀.degree < d) (α β : F) (P : F[X]) :
    ¬ IsAffineExceptional domain f (fun i ↦ G₀.eval (domain i)) d A s
      α β P := by
  rintro ⟨hP, -, h⟩
  refine h (P - affineMultiplier α β * G₀) G₀ ?_ hG ⟨by ring, ?_⟩
  · refine (degree_sub_le _ _).trans (max_le hP ?_)
    by_cases hG0 : G₀ = 0
    · simp [hG0]
    have hn : G₀.natDegree < d := by rwa [degree_eq_natDegree hG0, Nat.cast_lt] at hG
    calc (affineMultiplier α β * G₀).degree
        ≤ (affineMultiplier α β).degree + G₀.degree := degree_mul_le _ _
      _ ≤ 1 + (G₀.natDegree : WithBot ℕ) :=
          add_le_add (degree_affineMultiplier_le α β) degree_le_natDegree
      _ ≤ d := by norm_cast; omega
  · simp only [agreementLoss]
    rw [Finset.card_eq_zero.mpr]
    · exact Nat.zero_le _
    refine Finset.filter_eq_empty_iff.mpr fun i hi ↦ ?_
    rw [mem_polynomialAgreementSet, combinedWord] at hi
    simp [hi]

end ReedSolomon

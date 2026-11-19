/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement

/-!
# Affine combiners with agreement loss

A multiplier polynomial `L` combines received words `f, g` into `x ↦ f x + L(x) g x`.
Scalar combiners use a constant multiplier, while affine combiners use `L = α + β X`.
For an output degree bound `d`, affine witnesses have degrees `≤ d` and `< d` so that
`F₀ + L G₀` has degree at most `d`.

A witness pair decomposes a candidate polynomial `P` as `P = F₀ + L G₀`.
Its agreement loss counts positions where `P` agrees with the combined word but either witness
fails to agree with its received word.
Consider a candidate of degree at most `d` with at least `A` agreements with the combined word.
It is exceptional if no witness pair within the degree bounds has loss at most `s`.
The error is the supremum, over received word pairs, of the fraction of challenges for which
some candidate is exceptional.

The definitions follow Section 1.1 of [CWYZ26].
Definition 3.1 is the affine exceptional predicate at `s = 1`.
The paper uses `1 ≤ d < n` and `1 ≤ A ≤ n`, where `n` is the domain size.
The Lean definitions also cover boundary values: `A > n` gives no exceptional candidates,
and `d = 0` forces the second affine witness to be zero.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the statement correspondence.

## Computability

The errors have type `ENNReal` and counting definitions that require no sampler.
`ReedSolomon.affineMcaError_eq_iSup_prob` and `ReedSolomon.scalarMcaError_eq_iSup_prob` in
`AffineCombiner.Probability` identify them with suprema of native uniform probabilities.
The counting definitions use classical decidability for predicates over polynomial witnesses.
The multiplier uses noncomputable polynomial arithmetic.
Its value at `x` is `α + β * x`.
The combined word has value `f x + (α + β * x) * g x`.

## Main definitions

* `ReedSolomon.combinedWord`: the combined word `f + L g`.
* `ReedSolomon.affineMultiplier`: the polynomial `α + β X`.
* `ReedSolomon.agreementLoss` and `ReedSolomon.IsLossWitness`: lost positions and witness pairs.
* `ReedSolomon.IsAffineExceptional` and `ReedSolomon.IsScalarExceptional`: exceptional candidates.
* `ReedSolomon.affineMcaError` and `ReedSolomon.scalarMcaError`: uniform error probabilities.

## Main statements

* `ReedSolomon.map_affineMultiplier`: a ring map sends `α + β X` to `φ α + φ β X`.
* `ReedSolomon.agreementLoss_eq_sdiff`: loss is agreement minus common witness agreement.
* `ReedSolomon.affineMcaError_le_of_forall_exists` and
  `ReedSolomon.scalarMcaError_le_of_forall_exists`: uniform counts bound the errors.
* `ReedSolomon.affineMcaError_le_one` and `ReedSolomon.scalarMcaError_le_one`:
  each error is at most one.
* `ReedSolomon.not_isAffineExceptional_of_eval`: a second word of degree below `d`
  excludes exceptionality.

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

/-- Distinct pairs `(α, β)` give distinct lines `α + β X`. -/
theorem affineMultiplier_injective :
    Function.Injective fun c : F × F ↦ affineMultiplier c.1 c.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h0 := congrArg (fun p : F[X] ↦ p.coeff 0) h
  have h1 := congrArg (fun p : F[X] ↦ p.coeff 1) h
  simp only [affineMultiplier, coeff_add, coeff_C, coeff_C_mul, coeff_X] at h0 h1
  simp at h0 h1
  simp [h0, h1]

/-- Mapping the coefficients of `α + β X` along a ring map `φ` gives `φ α + φ β X`. -/
@[simp]
theorem map_affineMultiplier {K E : Type*} [Field K] [Field E] (φ : K →+* E) (α β : K) :
    (affineMultiplier α β).map φ = affineMultiplier (φ α) (φ β) := by
  simp [affineMultiplier]

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

/-- Lost agreements are the candidate's agreement set minus common witness agreement. -/
theorem agreementLoss_eq_sdiff [DecidableEq ι] (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : F[X]) :
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

/-- `P` is exceptional for the affine challenge `(α, β)` at threshold `A` and loss `s`.

It has degree at most `d` and agrees with `f + (α + β x) g` on at least `A` points.
No witness pair with `deg F₀ ≤ d` and `deg G₀ < d` has agreement loss at most `s`. -/
def IsAffineExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F) (P : F[X]) :
    Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree ≤ d → G₀.degree < d →
      ¬ IsLossWitness domain f g s (affineMultiplier α β) P F₀ G₀

/-- `P` is exceptional for the scalar challenge `α` at threshold `A` and loss `s`.

It has degree at most `d` and agrees with `f + α g` on at least `A` points.
No witness pair of degree at most `d` has agreement loss at most `s`. -/
def IsScalarExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F) (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g (C α)) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree ≤ d → G₀.degree ≤ d →
      ¬ IsLossWitness domain f g s (C α) P F₀ G₀

open Classical in
/-- The supremum over received word pairs `(f, g)` of the probability that some candidate
is exceptional for a uniform challenge `(α, β)`.

The output degree bound is `d`, the agreement threshold is `A`, and the allowed loss is `s`.
Witness degrees are at most `d` and below `d`.
`ReedSolomon.affineMcaError_eq_iSup_prob` gives the native sampling characterization. -/
noncomputable def affineMcaError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ENNReal :=
  ⨆ w : (ι → F) × (ι → F),
    ENNReal.ofReal
      ((#{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} : ℝ) /
        (Fintype.card F : ℝ) ^ 2)

open Classical in
/-- The supremum over received word pairs `(f, g)` of the probability that some candidate
is exceptional for a uniform scalar challenge `α`.

The output and witness degree bound is `d`, the agreement threshold is `A`, and the allowed
loss is `s`.
`ReedSolomon.scalarMcaError_eq_iSup_prob` gives the native sampling characterization.
`ReedSolomon.scalarMcaError_zero_eq_mcaError` identifies the zero-loss value with
`CoreDefinitions.mcaError` for the affine-line generator and message length `d + 1`. -/
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

/-- If every word pair has a set of at most `B` challenges containing every affine exceptional
challenge, the error is at most `B / |F|²`. -/
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

/-- If every word pair has a set of at most `B` challenges containing every scalar exceptional
challenge, the error is at most `B / |F|`. -/
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
theorem IsAffineExceptional.anti_loss {domain : ι ↪ F} {f g : ι → F} {d A s s' : ℕ} {α β : F}
    {P : F[X]} (h : IsAffineExceptional domain f g d A s α β P) (hs : s' ≤ s) :
    IsAffineExceptional domain f g d A s' α β P :=
  ⟨h.1, h.2.1, fun F₀ G₀ hF hG hw ↦ h.2.2 F₀ G₀ hF hG ⟨hw.1, hw.2.trans hs⟩⟩

/-- An affine exceptional candidate stays exceptional for a smaller agreement threshold. -/
theorem IsAffineExceptional.anti_threshold {domain : ι ↪ F} {f g : ι → F} {d A A' s : ℕ}
    {α β : F} {P : F[X]} (h : IsAffineExceptional domain f g d A s α β P) (hA : A' ≤ A) :
    IsAffineExceptional domain f g d A' s α β P :=
  ⟨h.1, hA.trans h.2.1, h.2.2⟩

/-- A scalar exceptional candidate stays exceptional for a smaller agreement loss. -/
theorem IsScalarExceptional.anti_loss {domain : ι ↪ F} {f g : ι → F} {d A s s' : ℕ} {α : F}
    {P : F[X]} (h : IsScalarExceptional domain f g d A s α P) (hs : s' ≤ s) :
    IsScalarExceptional domain f g d A s' α P :=
  ⟨h.1, h.2.1, fun F₀ G₀ hF hG hw ↦ h.2.2 F₀ G₀ hF hG ⟨hw.1, hw.2.trans hs⟩⟩

/-- A scalar exceptional candidate stays exceptional for a smaller agreement threshold. -/
theorem IsScalarExceptional.anti_threshold {domain : ι ↪ F} {f g : ι → F} {d A A' s : ℕ}
    {α : F} {P : F[X]} (h : IsScalarExceptional domain f g d A s α P) (hA : A' ≤ A) :
    IsScalarExceptional domain f g d A' s α P :=
  ⟨h.1, hA.trans h.2.1, h.2.2⟩

/-- If `g` evaluates a polynomial `G₀` of degree below `d`, no candidate is exceptional
for any first received word `f`.
The threshold `A` and allowed loss `s` are unrestricted.

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

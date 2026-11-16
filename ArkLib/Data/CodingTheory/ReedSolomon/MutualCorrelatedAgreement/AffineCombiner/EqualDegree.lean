/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic
public import ArkLib.Data.Finset.PairwiseIntersection

/-!
# Equal-degree combiner

The equal-degree combiner sends `f, g` to `g + (α + β x)(f + θ g)`, with three challenges.

Both witnesses have degree below `d`, so the combination has degree at most `d`.

Its error is at most the affine error plus `ℓ₀ / q`, where `ℓ₀` is the Johnson list size.

## The reduction

For a fixed `θ`, the affine combiner on `(g, f + θ g)` gives witnesses `U, V`.

The pair `(V - θ U, U)` explains the candidate, unless `U` has degree exactly `d`.

Then `θ` is fixed by the leading coefficients of a pair close to `(f, g)`.

The Johnson bound leaves at most `ℓ₀` such pairs, hence at most `ℓ₀` bad values of `θ`.

## Main statements

* `ReedSolomon.equalDegreeMCAError_le`: with one point of agreement loss, the error is at most
  the affine error plus `n (A - 1 - d) / ((A - 1)² - n d) / q` (Theorem 5.1 of [CWYZ26],
  first part).

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

No witness pair of degrees below `d` loses at most `s` of these points. -/
def IsEqualDegreeExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : F[X]) : Prop :=
  P.degree ≤ d ∧
    A ≤ (polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P).card ∧
    ∀ F₀ G₀ : F[X], F₀.degree < d → G₀.degree < d →
      P = G₀ + affineMultiplier α β * (F₀ + C θ * G₀) →
      s < #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P |
        F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i}

open Classical in
/-- The equal-degree MCA error: the worst fraction of exceptional challenges in `F³`. -/
noncomputable def equalDegreeMCAError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) : ℝ :=
  ⨆ w : (ι → F) × (ι → F),
    (#{c : F × F × F | ∃ P, IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} :
      ℝ) / (Fintype.card F : ℝ) ^ 3

omit [DecidableEq F] [Fintype ι] in
/-- The equal-degree word is the affine word of the pair `(g, f + θ g)`. -/
theorem equalDegreeWord_eq_combinedWord (domain : ι ↪ F) (f g : ι → F) (θ α β : F) :
    equalDegreeWord domain f g θ α β =
      combinedWord domain g (fun i ↦ f i + θ * g i) (affineMultiplier α β) := by
  funext i
  simp [equalDegreeWord]

open Classical in
/-- One pair of received words bounds the equal-degree error from below. -/
theorem le_equalDegreeMCAError [Fintype F] (domain : ι ↪ F) (d A s : ℕ) (f g : ι → F) :
    (#{c : F × F × F | ∃ P, IsEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P} : ℝ) /
        (Fintype.card F : ℝ) ^ 3 ≤ equalDegreeMCAError domain d A s :=
  le_ciSup (f := fun w : (ι → F) × (ι → F) ↦
    (#{c : F × F × F | ∃ P, IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} :
      ℝ) / (Fintype.card F : ℝ) ^ 3) (Set.finite_range _).bddAbove (f, g)

/-- An exceptional candidate is affine exceptional for `(g, f + θ g)`, or `θ` is bad.

Bad means that some pair `F₀, G₀` with `deg G₀ = d` satisfies `[X^d] F₀ + θ [X^d] G₀ = 0`.

That pair agrees with `(f, g)` on at least `A - s` points. -/
theorem IsEqualDegreeExceptional.isAffineExceptional_or_exists {domain : ι ↪ F} {f g : ι → F}
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
  · simp [coeff_sub, coeff_C_mul, coeff_eq_zero_of_degree_lt hV]
  · classical
    refine (Nat.sub_le_sub_left hloss A).trans ((Nat.sub_le_sub_right hA _).trans
      ((Finset.le_card_sdiff _ _).trans (Finset.card_le_card fun i hi ↦ ?_)))
    obtain ⟨hiP, hiL⟩ := Finset.mem_sdiff.mp hi
    simp only [agreementLoss, Finset.mem_filter, hiP, true_and, not_or, not_not] at hiL
    rw [mem_commonPolynomialAgreementSet]
    simp only [eval_sub, eval_mul, eval_C, hiL.1, hiL.2]
    exact ⟨by ring, trivial⟩

/-- Two distinct pairs of degree at most `d` share at most `d` common agreement points.

On a shared point both first polynomials agree, and so do both second ones.

One of the two differences is a nonzero polynomial of degree at most `d`. -/
theorem card_inter_commonPolynomialAgreementSet_le [DecidableEq ι] (domain : ι ↪ F)
    (f g : ι → F) {d : ℕ} {F₀ G₀ F₁ G₁ : F[X]} (hF₀ : F₀.degree ≤ d) (hG₀ : G₀.degree ≤ d)
    (hF₁ : F₁.degree ≤ d) (hG₁ : G₁.degree ≤ d) (hne : (F₀, G₀) ≠ (F₁, G₁)) :
    #(commonPolynomialAgreementSet domain f g F₀ G₀ ∩
      commonPolynomialAgreementSet domain f g F₁ G₁) ≤ d := by
  have key : ∀ p : F[X], p ≠ 0 → p.degree ≤ d → ∀ S : Finset ι,
      (∀ i ∈ S, p.eval (domain i) = 0) → #S ≤ d := fun p hp hd S hS ↦ by
    rw [← Finset.card_map domain]
    refine (card_le_degree_of_subset_roots fun x hx ↦ ?_).trans (natDegree_le_iff_degree_le.mpr hd)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_roots hp).mpr (hS i hi)
  by_cases hF : F₀ = F₁
  · have hG : G₀ - G₁ ≠ 0 := sub_ne_zero.mpr fun hG ↦ hne (by rw [hF, hG])
    refine key _ hG ((degree_sub_le _ _).trans (max_le hG₀ hG₁)) _ fun i hi ↦ ?_
    simp only [Finset.mem_inter, mem_commonPolynomialAgreementSet] at hi
    simp [hi.1.2, hi.2.2]
  · refine key _ (sub_ne_zero.mpr hF) ((degree_sub_le _ _).trans (max_le hF₀ hF₁)) _
      fun i hi ↦ ?_
    simp only [Finset.mem_inter, mem_commonPolynomialAgreementSet] at hi
    simp [hi.1.1, hi.2.1]

open Classical in
/-- Few values of `θ` are bad: the Johnson bound for set families.

A bad `θ` comes with a pair `F₀, G₀` of degree at most `d`, with `deg G₀ = d`.

The pair agrees with `(f, g)` on at least `L` points, and `[X^d] F₀ + θ [X^d] G₀ = 0`.

The pair fixes `θ`, so distinct bad values give distinct pairs. -/
theorem card_badEqualDegreeChallenges_mul_le [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    (d L : ℕ) :
    #{θ : F | ∃ F₀ G₀ : F[X], F₀.degree ≤ d ∧ G₀.degree = d ∧
        F₀.coeff d + θ * G₀.coeff d = 0 ∧
        L ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀)} *
        (L * L - Fintype.card ι * d) ≤ Fintype.card ι * (L - d) := by
  set T : Finset F := {θ : F | ∃ F₀ G₀ : F[X], F₀.degree ≤ d ∧ G₀.degree = d ∧
        F₀.coeff d + θ * G₀.coeff d = 0 ∧
        L ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀)}
  have hT : ∀ θ ∈ T, ∃ F₀ G₀ : F[X], F₀.degree ≤ d ∧ G₀.degree = d ∧
      F₀.coeff d + θ * G₀.coeff d = 0 ∧
      L ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀) := fun θ hθ ↦ by
    simpa [T] using hθ
  choose! F₀ G₀ hF hG hc hL using hT
  refine Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le T
    (fun θ ↦ commonPolynomialAgreementSet domain f g (F₀ θ) (G₀ θ)) L d hL ?_
  intro θ hθ θ' hθ' hne
  refine card_inter_commonPolynomialAgreementSet_le domain f g (hF θ hθ) (hG θ hθ).le
    (hF θ' hθ') (hG θ' hθ').le fun heq ↦ hne ?_
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj heq
  have hlead : (G₀ θ).coeff d ≠ 0 := by
    rw [← (natDegree_eq_of_degree_eq_some (hG θ hθ))]
    exact leadingCoeff_ne_zero.mpr fun h0 ↦ by simpa [h0] using hG θ hθ
  have := (hc θ hθ).trans (hc θ' hθ').symm
  rw [h₁, h₂] at this
  exact mul_right_cancel₀ (h₂ ▸ hlead) (add_left_cancel this)

/-- With one point of agreement loss, the equal-degree error is at most `ε_aff + ℓ₀ / q`.

Here `ℓ₀ = n (A - 1 - d) / ((A - 1)² - n d)` is the Johnson list size. -/
theorem equalDegreeMCAError_le [Fintype F] (domain : ι ↪ F) {d A : ℕ} (hdA : d + 1 < A)
    (hJ : Fintype.card ι * d < (A - 1) ^ 2) :
    equalDegreeMCAError domain d A 1 ≤ affineMCAError domain d A 1 +
      (Fintype.card ι : ℝ) * ((A : ℝ) - 1 - d) / (((A : ℝ) - 1) ^ 2 - Fintype.card ι * d) /
        Fintype.card F := by
  classical
  refine ciSup_le fun w ↦ ?_
  obtain ⟨f, g⟩ := w
  set q : ℝ := (Fintype.card F : ℝ) with hq_def
  set n : ℕ := Fintype.card ι
  set E := affineMCAError domain d A 1
  have hq : 0 < q := by positivity
  -- The challenges `θ` for which some pair of degree `d` explains a candidate.
  set B : Finset F := {θ : F | ∃ F₀ G₀ : F[X], F₀.degree ≤ d ∧ G₀.degree = d ∧
    F₀.coeff d + θ * G₀.coeff d = 0 ∧
    A - 1 ≤ #(commonPolynomialAgreementSet domain f g F₀ G₀)} with hB_def
  set X₁ : Finset (F × F × F) := {c | ∃ P,
    IsAffineExceptional domain g (fun i ↦ f i + c.1 * g i) d A 1 c.2.1 c.2.2 P}
  set X₂ : Finset (F × F × F) := {c | c.1 ∈ B}
  have hsub : ({c | ∃ P, IsEqualDegreeExceptional domain f g d A 1 c.1 c.2.1 c.2.2 P} :
      Finset (F × F × F)) ⊆ X₁ ∪ X₂ := by
    intro c hc
    obtain ⟨P, hP⟩ := (Finset.mem_filter.mp hc).2
    rcases hP.isAffineExceptional_or_exists with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, P, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)
  have hX₁ : (#X₁ : ℝ) ≤ q ^ 3 * E := by
    have hsum : #X₁ = ∑ θ : F, #{c : F × F | ∃ P,
        IsAffineExceptional domain g (fun i ↦ f i + θ * g i) d A 1 c.1 c.2 P} := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      simp only [Finset.card_filter]
    rw [hsum, Nat.cast_sum]
    calc (∑ θ : F, (#{c : F × F | ∃ P,
          IsAffineExceptional domain g (fun i ↦ f i + θ * g i) d A 1 c.1 c.2 P} : ℝ))
        ≤ ∑ _θ : F, q ^ 2 * E := Finset.sum_le_sum fun θ _ ↦ by
          have := le_affineMCAError domain d A 1 g (fun i ↦ f i + θ * g i)
          rw [div_le_iff₀ (by positivity)] at this
          linarith
      _ = q ^ 3 * E := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hq_def]
          ring
  have hX₂ : (#X₂ : ℝ) = #B * q ^ 2 := by
    have : X₂ = B ×ˢ (Finset.univ : Finset (F × F)) := by
      ext c
      simp [X₂]
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_prod]
    push_cast
    ring
  -- The Johnson bound on the bad values of `θ`.
  have hA1 : 1 ≤ A := by omega
  have hden_nat : n * d ≤ (A - 1) * (A - 1) := by rw [← sq]; exact hJ.le
  have hden : (0 : ℝ) < ((A : ℝ) - 1) ^ 2 - n * d := by
    have : ((n * d : ℕ) : ℝ) < (((A - 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hJ
    push_cast [hA1] at this
    linarith
  have hB : (#B : ℝ) ≤ n * ((A : ℝ) - 1 - d) / (((A : ℝ) - 1) ^ 2 - n * d) := by
    rw [le_div_iff₀ hden]
    have h := card_badEqualDegreeChallenges_mul_le domain f g d (A - 1)
    have h' : ((#B * ((A - 1) * (A - 1) - n * d) : ℕ) : ℝ) ≤ ((n * (A - 1 - d) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [hA1, hden_nat, show d ≤ A - 1 by omega] at h'
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc (#{c : F × F × F | ∃ P, IsEqualDegreeExceptional domain f g d A 1 c.1 c.2.1 c.2.2 P} : ℝ)
      ≤ #(X₁ ∪ X₂) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ #X₁ + #X₂ := by exact_mod_cast Finset.card_union_le _ _
    _ ≤ q ^ 3 * E + n * ((A : ℝ) - 1 - d) / (((A : ℝ) - 1) ^ 2 - n * d) * q ^ 2 := by
        rw [hX₂]
        gcongr
    _ = (E + n * ((A : ℝ) - 1 - d) / (((A : ℝ) - 1) ^ 2 - n * d) / q) * q ^ 3 := by
        field_simp

end ReedSolomon

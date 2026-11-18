/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Polynomial agreement sets

These definitions record all coordinates where polynomial explanations match received words.
They use an arbitrary finite coordinate type, so a domain indexed by `Fin n`, a finite subtype,
or a chosen basis enumeration uses the same API. Neither definition imposes a degree bound:
Reed–Solomon statements must supply their strict message-degree hypotheses separately.

## Main statements

* `polynomialAgreementSet` records agreement with one polynomial.
* `commonPolynomialAgreementSet` records simultaneous agreement with two polynomials on the
  same coordinates. Its cardinality for fixed witnesses is not the maximum common agreement.
* `card_polynomialAgreementSet` identifies the single-polynomial count with `Code.agree`.
* `polynomialAgreementSet_map` preserves the agreement set under an injective ring hom.
* `card_polynomialAgreement_map` preserves the agreement count on any finite indexed domain,
  including one with repeated points.
* `commonPolynomialAgreementSet_eq_inter` identifies the common set with an intersection.
* `card_inter_commonPolynomialAgreementSet_le` bounds common agreement of distinct polynomial pairs.
* `interleavedCommonAgreementSet` records common agreement in every row of two tuples.
* `card_inter_interleavedCommonAgreementSet_le` bounds it for distinct pairs of tuples.
* `mul_lt_sq_ceil_sqrt_add_mul_sub_one` gives the Johnson condition at the threshold
  `⌈(√ρ + η) n⌉`.

These are exact finite sets, with no decoding threshold, probability convention, or
mutual-correlated-agreement hypothesis.
The Johnson condition follows the proof of Theorem 5.1 of [CWYZ26].

## References

* [DKT26]
* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The full set of positions where `P` agrees with a received word. -/
def polynomialAgreementSet {F : Type*} [Semiring F] [DecidableEq F] {ι : Type*} [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ P.eval (domain i) = received i

/-- The positions where two message polynomials simultaneously agree with two received words. -/
def commonPolynomialAgreementSet {F : Type*} [Semiring F] [DecidableEq F] {ι : Type*} [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (F₀ G₀ : F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i

/-- Membership in the agreement set is exactly the evaluation equality. -/
@[simp] theorem mem_polynomialAgreementSet
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) (i : ι) :
    i ∈ polynomialAgreementSet domain received P ↔ P.eval (domain i) = received i := by
  simp [polynomialAgreementSet]

/-- Common agreement keeps both equalities at the same coordinate. -/
@[simp] theorem mem_commonPolynomialAgreementSet
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (P Q : F[X]) (i : ι) :
    i ∈ commonPolynomialAgreementSet domain f g P Q ↔
      P.eval (domain i) = f i ∧ Q.eval (domain i) = g i := by
  simp [commonPolynomialAgreementSet]

/-- The common set is the intersection of the two individual agreement sets. -/
theorem commonPolynomialAgreementSet_eq_inter
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    (domain : ι ↪ F) (f g : ι → F) (P Q : F[X]) :
    commonPolynomialAgreementSet domain f g P Q =
      polynomialAgreementSet domain f P ∩ polynomialAgreementSet domain g Q := by
  ext i
  simp

/-- Polynomial agreement counts are the usual agreement counts of evaluation words. -/
theorem card_polynomialAgreementSet
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) :
    (polynomialAgreementSet domain received P).card =
      Code.agree (evalOnPoints domain P) received := rfl

/-- Applying an injective ring hom `φ` to the evaluation points, the received word, and the
coefficients of `P` does not change the agreement set. -/
theorem polynomialAgreementSet_map
    {F E ι : Type*} [Semiring F] [Semiring E] [DecidableEq F] [DecidableEq E] [Fintype ι]
    (domain : ι ↪ F) (φ : F →+* E) (hφ : Function.Injective φ)
    (received : ι → F) (P : F[X]) :
    polynomialAgreementSet (domain.trans ⟨φ, hφ⟩) (fun i ↦ φ (received i)) (P.map φ) =
      polynomialAgreementSet domain received P := by
  ext i
  simp [eval_map, eval₂_at_apply, hφ.eq_iff]

/-- An injective ring hom preserves the number of agreement positions for any finite indexed
domain, including domains with repeated values. -/
theorem card_polynomialAgreement_map
    {F E ι : Type*} [Semiring F] [Semiring E] [DecidableEq F] [DecidableEq E] [Fintype ι]
    (φ : F →+* E) (hφ : Function.Injective φ) (domain received : ι → F) (P : F[X]) :
    (Finset.univ.filter fun i ↦ (P.map φ).eval (φ (domain i)) = φ (received i)).card =
      (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card := by
  simp only [Polynomial.eval_map_apply, hφ.eq_iff]

open scoped Finset

/-- Two distinct pairs of degree at most `d` share at most `d` common agreement points.

On a shared point both first polynomials agree, and so do both second ones.
One of the two differences is a nonzero polynomial of degree at most `d`. -/
theorem card_inter_commonPolynomialAgreementSet_le
    {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι] (domain : ι ↪ F)
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

/-- The positions where every row of `F₀` and `G₀` agrees with the matching rows of `f` and `g`. -/
def interleavedCommonAgreementSet {F : Type*} [Semiring F] [DecidableEq F] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (domain : ι ↪ F) (f g : κ → ι → F) (F₀ G₀ : κ → F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ r, (F₀ r).eval (domain i) = f r i ∧ (G₀ r).eval (domain i) = g r i

/-- Shared common agreement keeps both equalities in every row at the same coordinate. -/
@[simp] theorem mem_interleavedCommonAgreementSet
    {F ι κ : Type*} [Semiring F] [DecidableEq F] [Fintype ι] [Fintype κ]
    (domain : ι ↪ F) (f g : κ → ι → F) (F₀ G₀ : κ → F[X]) (i : ι) :
    i ∈ interleavedCommonAgreementSet domain f g F₀ G₀ ↔
      ∀ r, (F₀ r).eval (domain i) = f r i ∧ (G₀ r).eval (domain i) = g r i := by
  simp [interleavedCommonAgreementSet]

/-- Two distinct pairs of polynomial tuples of degree at most `d` share at most `d` common
agreement points.

Some row differs, and the shared common set lies in the common set of that row. -/
theorem card_inter_interleavedCommonAgreementSet_le
    {F : Type*} [Field F] [DecidableEq F] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (domain : ι ↪ F) (f g : κ → ι → F) {d : ℕ} {F₀ G₀ F₁ G₁ : κ → F[X]}
    (hF₀ : ∀ r, (F₀ r).degree ≤ d) (hG₀ : ∀ r, (G₀ r).degree ≤ d)
    (hF₁ : ∀ r, (F₁ r).degree ≤ d) (hG₁ : ∀ r, (G₁ r).degree ≤ d) (hne : (F₀, G₀) ≠ (F₁, G₁)) :
    #(interleavedCommonAgreementSet domain f g F₀ G₀ ∩
      interleavedCommonAgreementSet domain f g F₁ G₁) ≤ d := by
  obtain ⟨r, hr⟩ : ∃ r, (F₀ r, G₀ r) ≠ (F₁ r, G₁ r) := by
    by_contra h
    push Not at h
    exact hne (Prod.ext (funext fun r ↦ (Prod.mk.inj (h r)).1)
      (funext fun r ↦ (Prod.mk.inj (h r)).2))
  refine (Finset.card_le_card fun i hi ↦ ?_).trans
    (card_inter_commonPolynomialAgreementSet_le domain (f r) (g r) (hF₀ r) (hG₀ r) (hF₁ r)
      (hG₁ r) hr)
  simp only [Finset.mem_inter, mem_interleavedCommonAgreementSet,
    mem_commonPolynomialAgreementSet] at hi ⊢
  exact ⟨hi.1 r, hi.2 r⟩

/-- At the threshold `A = ⌈(√ρ + η) n⌉`, the Johnson condition `n d < (A - 1)²` holds.

Here `1 ≤ d < n`, `ρ = d / n`, `0 < η < 1`, and `n η² ≥ 4 / ρ`; the subtraction is in `ℕ`.
The last condition gives `n η > 1`, so `A - 1 > √ρ n = √(n d)`. -/
theorem mul_lt_sq_ceil_sqrt_add_mul_sub_one {n d : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < n)
    (hη : 0 < η) (hη1 : η < 1) (hn : 4 / ((d : ℝ) / n) ≤ n * η ^ 2) :
    n * d < (⌈(√((d : ℝ) / n) + η) * n⌉₊ - 1) ^ 2 := by
  set A := ⌈(√((d : ℝ) / n) + η) * n⌉₊
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hdn
  have hρ0 : (0 : ℝ) < (d : ℝ) / n := div_pos (by exact_mod_cast hd) hn0
  have hρ1 : (d : ℝ) / n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hdn.le)
  have h4 : (4 : ℝ) ≤ 4 / ((d : ℝ) / n) := by
    rw [le_div_iff₀ hρ0]
    linarith
  have hηn : 1 < η * n := by nlinarith
  have hAle : (√((d : ℝ) / n) + η) * n ≤ A := Nat.le_ceil _
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) < A := by nlinarith [Real.sqrt_nonneg ((d : ℝ) / n)]
    exact_mod_cast this
  have hsq : √((d : ℝ) / n) ^ 2 = (d : ℝ) / n := Real.sq_sqrt hρ0.le
  have hlt : √((d : ℝ) / n) * n < (A : ℝ) - 1 := by linarith
  have hreal : (n : ℝ) * d < ((A : ℝ) - 1) ^ 2 := by
    have h0 : 0 ≤ √((d : ℝ) / n) * n := by positivity
    calc (n : ℝ) * d = (√((d : ℝ) / n) * n) ^ 2 := by
          rw [mul_pow, hsq]
          field_simp
      _ < ((A : ℝ) - 1) ^ 2 := by gcongr
  have : ((n * d : ℕ) : ℝ) < (((A - 1) ^ 2 : ℕ) : ℝ) := by
    push_cast [hA1]
    exact hreal
  exact_mod_cast this

end
end ReedSolomon

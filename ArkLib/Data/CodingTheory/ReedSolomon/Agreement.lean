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

These are exact finite sets, with no decoding threshold, probability convention, or
mutual-correlated-agreement hypothesis.

## References

* [DKT26]
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

end
end ReedSolomon

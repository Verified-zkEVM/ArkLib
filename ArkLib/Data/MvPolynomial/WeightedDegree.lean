/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nasqret, Jieyi Long, Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.Finsupp.Option
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted degrees of products and divisors

For multivariate polynomials over a semiring without zero divisors, natural weighted total degree
is additive on nonzero products. No weight is required to be positive. Consequently, a finite
family whose product divides a nonzero polynomial satisfies an additive weighted-degree budget.

The proof appends a new variable with exponent equal to the weighted degree of each monomial,
while preserving all original exponents. This injective substitution prevents cancellation even
when some weights are zero. Ordinary variable-degree additivity then gives weighted additivity.
The variable type is arbitrary; in particular the results apply uniformly to every `Fin n`.

## Implementation references

Adapted from `nasqret`, `ContactFactorCaps.lean`, lines 28–122, in the Apache-2.0 licensed
proximity-prize development:
https://github.com/proximity-prize/proximity-prize/blob/b3fac81ad2b1ee609672b04bd3c3ee1ca5c06884/ProximityPrize/SubmissionLower/ContactFactorCaps.lean

Finite-product and divisibility accounting is adapted from Jieyi Long (`jieyilong`),
`ContactCumulativeWeightedDegreeResearch.lean`, lines 16–50:
https://github.com/proximity-prize/proximity-prize/blob/695ff8319bdf7d0666149d8db84daaa30f8b88eb/ProximityPrize/SubmissionLower/ContactCumulativeWeightedDegreeResearch.lean

Changes: replace separate `Fin 3` and `Fin 4` constructions by an `Option`-variable embedding;
weaken field assumptions to a commutative semiring without zero divisors; use native Mathlib
weighted-degree and variable-degree APIs without copying the donor's `LocalMathlib` hierarchy.
-/

namespace MvPolynomial

noncomputable section

variable {σ R : Type*}

private def weightedDegreeEmbedding (w : σ → ℕ) : (σ →₀ ℕ) →+ (Option σ →₀ ℕ) where
  toFun d := d.optionElim (Finsupp.weight w d)
  map_zero' := by ext i; cases i <;> simp
  map_add' d e := by ext i; cases i <;> simp

private theorem weightedDegreeEmbedding_injective (w : σ → ℕ) :
    Function.Injective (weightedDegreeEmbedding w) := by
  intro d e h
  have := congrArg Finsupp.some h
  simpa [weightedDegreeEmbedding] using this

variable [CommSemiring R]

private def weightedDegreeLift (w : σ → ℕ) :
    MvPolynomial σ R →+* MvPolynomial (Option σ) R :=
  AddMonoidAlgebra.mapDomainRingHom R (weightedDegreeEmbedding w)

private theorem weightedDegreeLift_injective (w : σ → ℕ) :
    Function.Injective (weightedDegreeLift (R := R) w) :=
  AddMonoidAlgebra.mapDomain_injective (weightedDegreeEmbedding_injective w)

private theorem degreeOf_weightedDegreeLift (w : σ → ℕ) (p : MvPolynomial σ R) :
    (weightedDegreeLift w p).degreeOf none = weightedTotalDegree w p := by
  classical
  have hs : (weightedDegreeLift w p).support = p.support.image (weightedDegreeEmbedding w) :=
    Finsupp.mapDomain_support_of_injective (weightedDegreeEmbedding_injective w) _
  rw [degreeOf_eq_sup, hs, Finset.sup_image]
  simp [Function.comp_def, weightedDegreeEmbedding, weightedTotalDegree]

variable [NoZeroDivisors R]

/-- Natural weighted degree is additive on nonzero products, including for zero weights. -/
theorem weightedTotalDegree_mul (w : σ → ℕ) (p q : MvPolynomial σ R)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedTotalDegree w (p * q) = weightedTotalDegree w p + weightedTotalDegree w q := by
  have hp' : weightedDegreeLift w p ≠ 0 :=
    fun h ↦ hp (weightedDegreeLift_injective w (h.trans (map_zero _).symm))
  have hq' : weightedDegreeLift w q ≠ 0 :=
    fun h ↦ hq (weightedDegreeLift_injective w (h.trans (map_zero _).symm))
  rw [← degreeOf_weightedDegreeLift w (p * q), map_mul, degreeOf_mul_eq hp' hq',
    degreeOf_weightedDegreeLift, degreeOf_weightedDegreeLift]

/-- Natural weighted degree is additive on any finite indexed product of nonzero polynomials. -/
theorem weightedTotalDegree_prod {ι : Type*} (w : σ → ℕ) (s : Finset ι)
    (f : ι → MvPolynomial σ R) (hf : ∀ i ∈ s, f i ≠ 0) :
    weightedTotalDegree w (∏ i ∈ s, f i) = ∑ i ∈ s, weightedTotalDegree w (f i) := by
  have hf' : ∀ i ∈ s, weightedDegreeLift w (f i) ≠ 0 := by
    intro i hi h
    exact hf i hi (weightedDegreeLift_injective w (h.trans (map_zero _).symm))
  rw [← degreeOf_weightedDegreeLift w (∏ i ∈ s, f i), map_prod, degreeOf_prod_eq s _ hf']
  simp only [degreeOf_weightedDegreeLift]

/-- Divisibility into a nonzero polynomial bounds natural weighted degree. -/
theorem weightedTotalDegree_le_of_dvd (w : σ → ℕ) {p q : MvPolynomial σ R}
    (h : p ∣ q) (hq : q ≠ 0) : weightedTotalDegree w p ≤ weightedTotalDegree w q := by
  obtain ⟨r, rfl⟩ := h
  rw [weightedTotalDegree_mul _ _ _ (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq)]
  exact Nat.le_add_right _ _

/-- A product-divisibility certificate bounds the sum of actual weighted factor degrees.
Repeated indices are counted with multiplicity; the weight function may vanish anywhere. -/
theorem sum_weightedTotalDegree_le_of_prod_dvd {ι : Type*} (w : σ → ℕ) (s : Finset ι)
    (f : ι → MvPolynomial σ R) {p : MvPolynomial σ R} (hp : p ≠ 0)
    (h : (∏ i ∈ s, f i) ∣ p) :
    (∑ i ∈ s, weightedTotalDegree w (f i)) ≤ weightedTotalDegree w p := by
  let := nontrivial_of_ne p 0 hp
  have hf : ∀ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mp (ne_zero_of_dvd_ne_zero hp h)
  rw [← weightedTotalDegree_prod w s f hf]
  exact weightedTotalDegree_le_of_dvd w h hp

end

end MvPolynomial

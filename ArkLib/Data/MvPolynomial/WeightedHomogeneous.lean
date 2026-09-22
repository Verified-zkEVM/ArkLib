/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightedOrder
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneity under substitution and support filters

This file proves two closure properties of `MvPolynomial.IsWeightedHomogeneous` that Mathlib does
not state.

* A substitution `bind₁ f` sends a `w`-homogeneous polynomial of degree `n` to a `v`-homogeneous
  polynomial of degree `n` whenever every generator image `f i` is `v`-homogeneous of degree
  `w i`. So a grading-preserving substitution restricts to a linear map between the graded
  pieces `weightedHomogeneousSubmodule`.
* A support filter `filterSupport p`, and in particular a weighted truncation, keeps a subset of
  the monomials and therefore preserves homogeneity for every weight.

Weights take values in an arbitrary additive commutative monoid and the coefficients form an
arbitrary commutative semiring.

## Main statements

* `MvPolynomial.IsWeightedHomogeneous.bind₁`
* `MvPolynomial.IsWeightedHomogeneous.filterSupport`,
  `MvPolynomial.IsWeightedHomogeneous.weightedTruncation`
* `MvPolynomial.bind₁_mem_weightedHomogeneousSubmodule`
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ τ R M : Type*} [CommSemiring R] [AddCommMonoid M]

/-- A substitution whose generator images are homogeneous of the degrees of their generators
preserves homogeneity. If `f i` is `v`-homogeneous of degree `w i` for every `i`, then
`bind₁ f φ` is `v`-homogeneous of degree `n` whenever `φ` is `w`-homogeneous of degree `n`: a
monomial `x^e` of `w`-degree `∑ e_i w_i` goes to `∏ f_i^(e_i)`, of `v`-degree `∑ e_i w_i`. The
hypothesis is needed for every generator that occurs in `φ`: sending a degree-one variable to a
constant breaks homogeneity. -/
theorem IsWeightedHomogeneous.bind₁ {w : σ → M} {v : τ → M} {f : σ → MvPolynomial τ R}
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i)) {φ : MvPolynomial σ R} {n : M}
    (hφ : φ.IsWeightedHomogeneous w n) :
    (MvPolynomial.bind₁ f φ).IsWeightedHomogeneous v n := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R v n
  | add p q _ _ hp hq => simpa using hp.add hq
  | monomial e r he =>
      rw [bind₁_monomial, ← he]
      have hprod := IsWeightedHomogeneous.prod e.support (fun i => f i ^ e i)
        (fun i => e i • w i) (w := v) fun i _ => (hf i).pow (e i)
      simpa [Finsupp.weight_apply, Finsupp.sum] using (isWeightedHomogeneous_C v r).mul hprod

/-- The submodule form of `IsWeightedHomogeneous.bind₁`. -/
theorem bind₁_mem_weightedHomogeneousSubmodule {w : σ → M} {v : τ → M}
    {f : σ → MvPolynomial τ R} (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i)) {n : M}
    {φ : MvPolynomial σ R} (hφ : φ ∈ weightedHomogeneousSubmodule R w n) :
    MvPolynomial.bind₁ f φ ∈ weightedHomogeneousSubmodule R v n := by
  rw [mem_weightedHomogeneousSubmodule] at hφ ⊢
  exact hφ.bind₁ hf

/-- A support filter preserves weighted homogeneity for every weight and every predicate, since
it only discards monomials. -/
theorem IsWeightedHomogeneous.filterSupport {w : σ → M} {φ : MvPolynomial σ R} {n : M}
    (hφ : φ.IsWeightedHomogeneous w n) (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    (MvPolynomial.filterSupport (R := R) p φ).IsWeightedHomogeneous w n := by
  intro e he
  rw [coeff_filterSupport] at he
  split_ifs at he with h
  · exact hφ he
  · exact absurd rfl he

/-- A weighted truncation preserves homogeneity with respect to any other weight. -/
theorem IsWeightedHomogeneous.weightedTruncation {w : σ → M} {φ : MvPolynomial σ R} {n : M}
    (hφ : φ.IsWeightedHomogeneous w n) (u : σ → ℕ) (m : ℕ) :
    (MvPolynomial.weightedTruncation (R := R) u m φ).IsWeightedHomogeneous w n :=
  hφ.filterSupport _

end MvPolynomial

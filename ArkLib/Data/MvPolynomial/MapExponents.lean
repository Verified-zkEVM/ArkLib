/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightedOrder

/-!
# Relabelling the exponents of a multivariate polynomial

An additive map `f : (σ →₀ ℕ) →+ (τ →₀ ℕ)` on exponent vectors induces the algebra homomorphism
`mapExponents f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R` sending `monomial e c` to
`monomial (f e) c`. It is the substitution sending each variable `X i` to the monomial
`X^(f (single i 1))` (`mapExponents_eq_bind₁`), so a substitution of variables by monomials with
coefficient one can be studied through its action on exponents.

When `f` is injective, `mapExponents f` is injective over every coefficient semiring. Support
filters commute with the relabelling: filtering the image by `p` is the image of filtering by
`p ∘ f`. In particular, if `f` carries the weight `w` to the weight `v`, then truncation below
`v`-weight `m` after relabelling is relabelling after truncation below `w`-weight `m`.

## Main statements

* `MvPolynomial.mapExponents_monomial`, `MvPolynomial.mapExponents_eq_bind₁`
* `MvPolynomial.mapExponents_injective`
* `MvPolynomial.filterSupport_mapExponents`,
  `MvPolynomial.weightedTruncation_mapExponents`
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-- The algebra homomorphism induced by an additive map on exponent vectors: `monomial e c`
goes to `monomial (f e) c`. -/
def mapExponents (f : (σ →₀ ℕ) →+ (τ →₀ ℕ)) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  AddMonoidAlgebra.mapDomainAlgHom R R f

/-- `mapExponents f` sends `monomial e c` to `monomial (f e) c`. -/
@[simp]
theorem mapExponents_monomial (f : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (e : σ →₀ ℕ) (c : R) :
    mapExponents f (monomial e c) = monomial (f e) c :=
  AddMonoidAlgebra.mapDomain_single

/-- The relabelling is the substitution sending `X i` to the monomial of exponent
`f (single i 1)`. -/
theorem mapExponents_eq_bind₁ (f : (σ →₀ ℕ) →+ (τ →₀ ℕ)) :
    mapExponents (R := R) f = bind₁ fun i => monomial (f (Finsupp.single i 1)) 1 := by
  refine algHom_ext fun i => ?_
  rw [bind₁_X_right, X, mapExponents_monomial]

/-- An injective relabelling of exponents is injective on polynomials, over every coefficient
semiring. -/
theorem mapExponents_injective {f : (σ →₀ ℕ) →+ (τ →₀ ℕ)} (hf : Function.Injective f) :
    Function.Injective (mapExponents (R := R) f) :=
  AddMonoidAlgebra.mapDomain_injective hf

/-- A support filter applied to one monomial keeps it or deletes it. -/
theorem filterSupport_monomial (p : (σ →₀ ℕ) → Prop) [DecidablePred p] (e : σ →₀ ℕ) (c : R) :
    filterSupport (R := R) p (monomial e c) = if p e then monomial e c else 0 := by
  classical
  ext u
  rw [coeff_filterSupport]
  by_cases hue : e = u
  · subst hue
    split_ifs <;> simp
  · have hu : (monomial e c : MvPolynomial σ R).coeff u = 0 := by simp [coeff_monomial, hue]
    split_ifs <;> simp [hu]

/-- Filtering after relabelling is relabelling after filtering by the pulled-back predicate. No
injectivity is needed: all exponents in one fibre of `f` satisfy `p ∘ f` together. -/
theorem filterSupport_mapExponents (f : (σ →₀ ℕ) →+ (τ →₀ ℕ)) (p : (τ →₀ ℕ) → Prop)
    [DecidablePred p] (F : MvPolynomial σ R) :
    filterSupport p (mapExponents f F) = mapExponents f (filterSupport (fun e => p (f e)) F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial e c =>
      rw [mapExponents_monomial, filterSupport_monomial, filterSupport_monomial]
      split_ifs <;> simp
  | add F G hF hG => simp only [map_add, hF, hG]

/-- If `f` carries the weight `w` to the weight `v`, that is `(f e).weight v = e.weight w` for
every exponent `e`, then truncation below `v`-weight `m` commutes with the relabelling. -/
theorem weightedTruncation_mapExponents {w : σ → ℕ} {v : τ → ℕ} (f : (σ →₀ ℕ) →+ (τ →₀ ℕ))
    (hf : ∀ e, (f e).weight v = e.weight w) (m : ℕ) (F : MvPolynomial σ R) :
    weightedTruncation v m (mapExponents f F) = mapExponents f (weightedTruncation w m F) := by
  rw [weightedTruncation, filterSupport_mapExponents]
  simp only [hf]
  rfl

end MvPolynomial

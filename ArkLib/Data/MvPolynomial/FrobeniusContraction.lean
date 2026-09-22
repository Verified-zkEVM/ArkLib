/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FrobeniusContraction
public import ArkLib.ToMathlib.MvPolynomial.RootContraction
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Frobenius contraction in one variable of a multivariate polynomial

View a polynomial `F` in the variables `Option σ` as a univariate polynomial in the distinguished
variable `none` through `MvPolynomial.optionEquivLeft`. Let the coefficient ring `R` have no zero
divisors and characteristic `p`. If `F` is irreducible of positive degree in `none`, then
`F = rootExpansion (p ^ e) G` for an irreducible `G` whose partial derivative in `none` is
nonzero. The degree of `G` in `none` times `p ^ e` is the degree of `F` in `none`, and the degree
of `G` in every other variable is at most that of `F`. The same holds in exponential
characteristic `p`; in characteristic zero `p = 1` and `G = F`.

When `R` is a unique factorization domain, the polynomial ring `MvPolynomial σ R` is a GCD
domain. An irreducible `G` of positive degree in `none` then stays irreducible over the fraction
field of `MvPolynomial σ R` by Gauss's lemma, and it is separable there when its partial
derivative in `none` is nonzero.

## Main statements

* `MvPolynomial.exists_irreducible_frobeniusContraction`: the terminal contraction in
  characteristic `p`.
* `MvPolynomial.exists_irreducible_frobeniusContraction_expChar`: the same in exponential
  characteristic `p`.
* `MvPolynomial.irreducible_map_optionEquivLeft_fractionRing` and
  `MvPolynomial.separable_map_optionEquivLeft_fractionRing`: passage to the fraction field of the
  coefficient ring.
* `MvPolynomial.exists_frobeniusContraction_fractionRing`: over a unique factorization domain,
  the terminal polynomial is irreducible and separable over that fraction field.
-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Transport of a univariate Frobenius contraction of `optionEquivLeft R σ F` to `F`. -/
private theorem frobeniusContraction_of_optionEquivLeft {s : ℕ} (hs : s ≠ 0)
    {F : MvPolynomial (Option σ) R} {H : Polynomial (MvPolynomial σ R)}
    (hder : Polynomial.derivative H ≠ 0)
    (hHF : Polynomial.expand (MvPolynomial σ R) s H = optionEquivLeft R σ F)
    (hdeg : H.natDegree * s = (optionEquivLeft R σ F).natDegree)
    (hpos : 0 < H.natDegree) (hirr : Irreducible H) :
    pderiv none ((optionEquivLeft R σ).symm H) ≠ 0 ∧
      rootExpansion s ((optionEquivLeft R σ).symm H) = F ∧
      ((optionEquivLeft R σ).symm H).degreeOf none * s = F.degreeOf none ∧
      0 < ((optionEquivLeft R σ).symm H).degreeOf none ∧
      Irreducible ((optionEquivLeft R σ).symm H) ∧
      ∀ j : σ, ((optionEquivLeft R σ).symm H).degreeOf (some j) ≤ F.degreeOf (some j) := by
  have hG : optionEquivLeft R σ ((optionEquivLeft R σ).symm H) = H :=
    AlgEquiv.apply_symm_apply _ H
  have hcontract : (optionEquivLeft R σ).symm H = rootContraction s F := by
    rw [rootContraction, ← hHF, Polynomial.contract_expand s hs]
  refine ⟨?_, ?_, ?_, ?_, hirr.map (optionEquivLeft R σ).symm, fun j ↦ ?_⟩
  · intro hzero
    apply hder
    rw [← hG, ← optionEquivLeft_pderiv_none, hzero, map_zero]
  · rw [rootExpansion, hG, hHF, AlgEquiv.symm_apply_apply]
  · rw [← natDegree_optionEquivLeft, hG, hdeg, natDegree_optionEquivLeft]
  · rwa [← natDegree_optionEquivLeft, hG]
  · rw [hcontract]
    exact degreeOf_rootContraction_some_le hs F j

section NoZeroDivisors

variable [NoZeroDivisors R] (p : ℕ)

/-- In characteristic `p` without zero divisors, an irreducible polynomial `F` of positive degree
in `none` is `rootExpansion (p ^ e) G` for an irreducible `G` with nonzero partial derivative in
`none`. The degree of `G` in `none` times `p ^ e` is the degree of `F` in `none`, and the degree
of `G` in every variable `some j` is at most that of `F`. -/
theorem exists_irreducible_frobeniusContraction [CharP R p] {F : MvPolynomial (Option σ) R}
    (hFpos : 0 < F.degreeOf none) (hF : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) R,
      pderiv none G ≠ 0 ∧
      rootExpansion (p ^ e) G = F ∧
      G.degreeOf none * p ^ e = F.degreeOf none ∧
      0 < G.degreeOf none ∧
      Irreducible G ∧
      ∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j) := by
  have hPpos : 0 < (optionEquivLeft R σ F).natDegree := by
    rwa [natDegree_optionEquivLeft]
  obtain ⟨e, H, hder, hHF, hdeg, hpos, hirr⟩ :=
    Polynomial.exists_irreducible_frobeniusContraction p hPpos (hF.map (optionEquivLeft R σ))
  have hs : p ^ e ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdeg
    omega
  exact ⟨e, _, frobeniusContraction_of_optionEquivLeft hs hder hHF hdeg hpos hirr⟩

/-- In exponential characteristic `p` without zero divisors, an irreducible polynomial `F` of
positive degree in `none` is `rootExpansion (p ^ e) G` for an irreducible `G` with nonzero partial
derivative in `none`. The degree of `G` in `none` times `p ^ e` is the degree of `F` in `none`,
and the degree of `G` in every variable `some j` is at most that of `F`. -/
theorem exists_irreducible_frobeniusContraction_expChar [ExpChar R p]
    {F : MvPolynomial (Option σ) R} (hFpos : 0 < F.degreeOf none) (hF : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) R,
      pderiv none G ≠ 0 ∧
      rootExpansion (p ^ e) G = F ∧
      G.degreeOf none * p ^ e = F.degreeOf none ∧
      0 < G.degreeOf none ∧
      Irreducible G ∧
      ∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j) := by
  have hPpos : 0 < (optionEquivLeft R σ F).natDegree := by
    rwa [natDegree_optionEquivLeft]
  obtain ⟨e, H, hder, hHF, hdeg, hpos, hirr⟩ :=
    Polynomial.exists_irreducible_frobeniusContraction_expChar p hPpos
      (hF.map (optionEquivLeft R σ))
  have hs : p ^ e ≠ 0 := pow_ne_zero e (expChar_pos R p).ne'
  exact ⟨e, _, frobeniusContraction_of_optionEquivLeft hs hder hHF hdeg hpos hirr⟩

end NoZeroDivisors

section FractionRing

variable [IsDomain R] [UniqueFactorizationMonoid R] {L : Type*} [Field L]
  [Algebra (MvPolynomial σ R) L] [IsFractionRing (MvPolynomial σ R) L]

/-- Over a unique factorization domain `R`, an irreducible polynomial of positive degree in `none`
stays irreducible as a univariate polynomial over the fraction field of `MvPolynomial σ R`. -/
theorem irreducible_map_optionEquivLeft_fractionRing {G : MvPolynomial (Option σ) R}
    (hG : Irreducible G) (hpos : 0 < G.degreeOf none) :
    Irreducible ((optionEquivLeft R σ G).map (algebraMap (MvPolynomial σ R) L)) := by
  have hGirr := hG.map (optionEquivLeft R σ)
  have hdeg : (optionEquivLeft R σ G).natDegree ≠ 0 := by
    rw [natDegree_optionEquivLeft]
    exact hpos.ne'
  exact ((hGirr.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map).mp hGirr

/-- Over a unique factorization domain `R`, an irreducible polynomial with nonzero partial
derivative in `none` is separable as a univariate polynomial over the fraction field of
`MvPolynomial σ R`. -/
theorem separable_map_optionEquivLeft_fractionRing {G : MvPolynomial (Option σ) R}
    (hG : Irreducible G) (hder : pderiv none G ≠ 0) :
    ((optionEquivLeft R σ G).map (algebraMap (MvPolynomial σ R) L)).Separable := by
  refine Polynomial.separable_map_of_irreducible_of_derivative_ne_zero _
    (hG.map (optionEquivLeft R σ)) ?_
  rwa [← optionEquivLeft_pderiv_none, ne_eq,
    map_eq_zero_iff _ (optionEquivLeft R σ).injective]

variable (p : ℕ) [CharP R p]

/-- Over a unique factorization domain of characteristic `p`, the terminal polynomial `G` of
`exists_irreducible_frobeniusContraction` is irreducible and separable as a univariate
polynomial in `none` over the fraction field `L` of `MvPolynomial σ R`. -/
theorem exists_frobeniusContraction_fractionRing {F : MvPolynomial (Option σ) R}
    (hFpos : 0 < F.degreeOf none) (hF : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) R,
      pderiv none G ≠ 0 ∧
      rootExpansion (p ^ e) G = F ∧
      G.degreeOf none * p ^ e = F.degreeOf none ∧
      0 < G.degreeOf none ∧
      Irreducible G ∧
      (∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j)) ∧
      Irreducible ((optionEquivLeft R σ G).map (algebraMap (MvPolynomial σ R) L)) ∧
      ((optionEquivLeft R σ G).map (algebraMap (MvPolynomial σ R) L)).Separable := by
  obtain ⟨e, G, hder, hGF, hdeg, hpos, hirr, hother⟩ :=
    exists_irreducible_frobeniusContraction p hFpos hF
  exact ⟨e, G, hder, hGF, hdeg, hpos, hirr, hother,
    irreducible_map_optionEquivLeft_fractionRing hirr hpos,
    separable_map_optionEquivLeft_fractionRing hirr hder⟩

end FractionRing

end MvPolynomial

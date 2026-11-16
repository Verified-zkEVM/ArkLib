/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LineEvaluation
public import ArkLib.Data.Polynomial.FractionFieldResultant
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.Data.Polynomial.ResultantSpecialization
public import ArkLib.Data.Polynomial.SpecializationAvoidance
public import ArkLib.ToMathlib.MvPolynomial.RootContraction

/-!
# Lines through the roots of a trivariate polynomial

A trivariate `G(X, Y, Z)` is read as a polynomial in `Z` over `E[X][Y]`.

Along a line `Y = α + β X`, a nonzero `G` free of `Z` vanishes for at most `deg_Y G` lines.

The `Z`-discriminant of `R` is a polynomial in `Y` of degree at most `h (h - 1)`.

Here `h` is the `(Y, Z)`-degree of `R`.

Where the discriminant does not vanish on the line, every root of `R` along the line is simple.

It is a resultant with declared degrees, so this holds even if the leading `Z`-coefficient
vanishes on the line.

The nested presentation is noncomputable because Mathlib's polynomial rings are.

## Main definitions

* `ReedSolomon.affineNested`: the presentation as a polynomial in `Z` over `E[X][Y]`.
* `ReedSolomon.affineDiscriminant`: the `Z`-discriminant as a polynomial in `Y` over `E[X]`.

## Main statements

* `ReedSolomon.affineLineEval_eq_nested`: evaluation along a line through the presentation.
* `ReedSolomon.card_filter_affineLine_eq_zero_le`: a nonzero `G` free of `Z` vanishes on at
  most `deg_Y G` lines.
* `ReedSolomon.affineDiscriminant_ne_zero`: the discriminant of an irreducible `R` with
  nonzero `Z`-derivative is nonzero.
* `ReedSolomon.natDegree_affineDiscriminant_le`: its `Y`-degree is at most `h (h - 1)`.
* `ReedSolomon.affineLineEval_pderiv_ne_zero`: off its zeros, roots along the line are simple.

## References

These are the ingredients of Lemma 4.3 of [CWYZ26].

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

variable {E : Type*} [Field E]

/-- Two variables as nested polynomials: `X 1` is the outer variable, `X 0` the inner one. -/
noncomputable def affineNestedInner : MvPolynomial (Fin 2) E ≃ₐ[E] E[X][X] :=
  (MvPolynomial.renameEquiv E (Equiv.swap 0 1)).trans <|
    (MvPolynomial.finSuccEquiv E 1).trans <|
      Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv E (Fin 1))

/-- Constants stay constants. -/
@[simp] theorem affineNestedInner_C (a : E) :
    affineNestedInner (MvPolynomial.C a : MvPolynomial (Fin 2) E) = C (C a) := by
  simp [affineNestedInner, MvPolynomial.finSuccEquiv_apply]

/-- The variable `X 1` becomes the outer variable. -/
@[simp] theorem affineNestedInner_X_one :
    affineNestedInner (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) E) = X := by
  simp [affineNestedInner, MvPolynomial.finSuccEquiv_apply]

/-- The variable `X 0` becomes the inner variable. -/
@[simp] theorem affineNestedInner_X_zero :
    affineNestedInner (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) E) = C X := by
  simp only [affineNestedInner, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_X, Equiv.swap_apply_left]
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp

/-- A trivariate polynomial as a polynomial in `Z` over `E[X][Y]`. -/
noncomputable def affineNested : MvPolynomial AffineVar E ≃ₐ[E] E[X][X][X] :=
  (MvPolynomial.optionEquivLeft E (Fin 2)).trans (Polynomial.mapAlgEquiv affineNestedInner)

/-- Constants stay constants. -/
@[simp] theorem affineNested_C (a : E) :
    affineNested (MvPolynomial.C a : MvPolynomial AffineVar E) = C (C (C a)) := by
  simp [affineNested]

/-- `Z` is the outer variable. -/
@[simp] theorem affineNested_X_none :
    affineNested (MvPolynomial.X none : MvPolynomial AffineVar E) = X := by
  simp [affineNested]

/-- `X` is the innermost variable. -/
@[simp] theorem affineNested_X_x :
    affineNested (MvPolynomial.X (some 0) : MvPolynomial AffineVar E) = C (C X) := by
  simp [affineNested]

/-- `Y` is the middle variable. -/
@[simp] theorem affineNested_X_y :
    affineNested (MvPolynomial.X (some 1) : MvPolynomial AffineVar E) = C X := by
  simp [affineNested]

/-- The presentation splits off `Z` first, then nests the remaining two variables. -/
theorem affineNested_apply (G : MvPolynomial AffineVar E) :
    affineNested G =
      (MvPolynomial.optionEquivLeft E (Fin 2) G).map (affineNestedInner (E := E)).toRingHom :=
  rfl

/-- The image of a monomial `a X^i Y^j Z^k`. -/
theorem affineNested_monomial (m : AffineVar →₀ ℕ) (a : E) :
    affineNested (MvPolynomial.monomial m a) =
      C (C (C a * X ^ m (some 0)) * X ^ m (some 1)) * X ^ m none := by
  rw [MvPolynomial.monomial_eq, map_mul, affineNested_C,
    Finsupp.prod_fintype _ _ (by simp), map_prod]
  simp [Fintype.prod_option, Fin.prod_univ_two]
  ring

/-- The presentation as a sum over the support. -/
theorem affineNested_eq_sum (G : MvPolynomial AffineVar E) :
    affineNested G = ∑ m ∈ G.support,
      C (C (C (G.coeff m) * X ^ m (some 0)) * X ^ m (some 1)) * X ^ m none := by
  conv_lhs => rw [G.as_sum, map_sum]
  simp only [affineNested_monomial]

/-- The degree in `Z` is preserved. -/
theorem natDegree_affineNested (G : MvPolynomial AffineVar E) :
    (affineNested G).natDegree = G.degreeOf none := by
  rw [affineNested_apply, natDegree_map_eq_of_injective affineNestedInner.injective,
    MvPolynomial.natDegree_optionEquivLeft]

/-- The partial derivative in `Z` becomes the outer derivative. -/
theorem derivative_affineNested (G : MvPolynomial AffineVar E) :
    (affineNested G).derivative = affineNested (MvPolynomial.pderiv none G) := by
  rw [affineNested_apply, affineNested_apply, derivative_map,
    MvPolynomial.optionEquivLeft_pderiv_none]

/-- The `Z^i`-coefficient collects the monomials of `Z`-exponent `i`. -/
theorem coeff_affineNested (G : MvPolynomial AffineVar E) (i : ℕ) :
    (affineNested G).coeff i = ∑ m ∈ G.support,
      if i = m none then C (C (G.coeff m) * X ^ m (some 0)) * X ^ m (some 1) else 0 := by
  rw [affineNested_eq_sum, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]

/-- The `Z^i`-coefficient has `Y`-degree at most `b` when every monomial of `Z`-exponent `i` has
`Y`-exponent at most `b`. -/
theorem natDegree_coeff_affineNested_le_of_forall {G : MvPolynomial AffineVar E} {i b : ℕ}
    (h : ∀ m ∈ G.support, m none = i → m (some 1) ≤ b) :
    ((affineNested G).coeff i).natDegree ≤ b := by
  rw [coeff_affineNested]
  refine natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
  split_ifs with hi
  · exact (natDegree_C_mul_X_pow_le _ _).trans (h m hm hi.symm)
  · simp

/-- Every `Z`-coefficient has `Y`-degree at most `deg_Y G`. -/
theorem natDegree_coeff_affineNested_le (G : MvPolynomial AffineVar E) (i : ℕ) :
    ((affineNested G).coeff i).natDegree ≤ G.degreeOf (some 1) :=
  natDegree_coeff_affineNested_le_of_forall fun _ hm _ ↦
    MvPolynomial.le_degreeOf_of_mem_support (some 1) hm

/-- The `(Y, Z)`-weight of a monomial is its `Y`-exponent plus its `Z`-exponent. -/
theorem weight_affineYZWeight (m : AffineVar →₀ ℕ) :
    Finsupp.weight affineYZWeight m = m none + m (some 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_option, Fin.sum_univ_two]

/-- A monomial of `G` has `Y`- plus `Z`-exponent at most the `(Y, Z)`-degree of `G`. -/
theorem add_le_weightedTotalDegree_affineYZWeight {G : MvPolynomial AffineVar E}
    {m : AffineVar →₀ ℕ} (hm : m ∈ G.support) :
    m none + m (some 1) ≤ G.weightedTotalDegree affineYZWeight :=
  weight_affineYZWeight m ▸ MvPolynomial.le_weightedTotalDegree affineYZWeight hm

/-- The `Z`-degree is at most the `(Y, Z)`-degree. -/
theorem degreeOf_none_le_weightedTotalDegree (G : MvPolynomial AffineVar E) :
    G.degreeOf none ≤ G.weightedTotalDegree affineYZWeight :=
  MvPolynomial.degreeOf_le_iff.mpr fun _ hm ↦
    (Nat.le_add_right _ _).trans (add_le_weightedTotalDegree_affineYZWeight hm)

/-- For `i ≤ deg_Z G`, `i` plus the `Y`-degree of the `Z^i`-coefficient is at most the
`(Y, Z)`-degree. -/
theorem add_natDegree_coeff_affineNested_le (G : MvPolynomial AffineVar E) {i : ℕ}
    (hi : i ≤ G.degreeOf none) :
    i + ((affineNested G).coeff i).natDegree ≤ G.weightedTotalDegree affineYZWeight := by
  have hle := hi.trans (degreeOf_none_le_weightedTotalDegree G)
  have h := natDegree_coeff_affineNested_le_of_forall (G := G) (i := i)
    (b := G.weightedTotalDegree affineYZWeight - i) fun m hm hmi ↦ by
      have := add_le_weightedTotalDegree_affineYZWeight hm
      omega
  omega

/-- Evaluating along the line substitutes `α + β X` for `Y` in the coefficients, then `P` for
`Z`. -/
theorem affineLineEval_eq_nested (α β : E) (P : E[X]) (G : MvPolynomial AffineVar E) :
    affineLineEval α β P G =
      ((affineNested G).map (Polynomial.evalRingHom (affineMultiplier α β))).eval P := by
  induction G using MvPolynomial.induction_on with
  | C a => simp [affineLineEval]
  | add G H hG hH => simp [hG, hH]
  | mul_X G v hG =>
    rcases v with _ | i
    · simp [hG]
    · fin_cases i <;> simp [hG]

/-- Distinct pairs `(α, β)` give distinct lines `α + β X`. -/
theorem affineMultiplier_injective :
    Function.Injective fun c : E × E ↦ affineMultiplier c.1 c.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h0 := congrArg (coeff · 0) h
  have h1 := congrArg (coeff · 1) h
  simp only [affineMultiplier, coeff_add, coeff_C, coeff_C_mul, coeff_X] at h0 h1
  simp at h0 h1
  simp [h0, h1]

open Classical in
/-- A nonzero `G` free of `Z` vanishes along at most `deg_Y G` lines indexed injectively by `S`.

Each such line `Y = α + β X` is a root of `G` as a polynomial in `Y` over `E[X]`. -/
theorem card_filter_affineLine_eq_zero_le {F : Type*} {G : MvPolynomial AffineVar E}
    (hG : G ≠ 0) (hZ : G.degreeOf none = 0) (S : Finset (F × F)) (φ : F × F → E × E)
    (hφ : φ.Injective) :
    (S.filter fun c ↦ affineLineEval (φ c).1 (φ c).2 0 G = 0).card ≤ G.degreeOf (some 1) := by
  set g := (affineNested G).coeff 0
  have hC : affineNested G = C g :=
    eq_C_of_natDegree_eq_zero ((natDegree_affineNested G).trans hZ)
  have hg : g ≠ 0 := by
    intro h0
    apply hG
    apply affineNested.injective
    rw [hC, h0, map_zero, map_zero]
  refine le_trans ?_ (natDegree_coeff_affineNested_le G 0)
  refine card_le_natDegree_of_injOn_of_eval_eq_zero hg
    (x := fun c ↦ affineMultiplier (φ c).1 (φ c).2)
    ((affineMultiplier_injective.comp hφ).injOn) fun c hc ↦ ?_
  have := (Finset.mem_filter.mp hc).2
  rwa [affineLineEval_eq_nested, hC, map_C, eval_C, coe_evalRingHom] at this

/-- The `Z`-discriminant, as a polynomial in `Y` over `E[X]`.

It is the resultant of `R` and its `Z`-derivative with declared degrees `deg_Z R` and
`deg_Z R - 1`. -/
noncomputable def affineDiscriminant (R : MvPolynomial AffineVar E) : E[X][X] :=
  resultant (affineNested R) (affineNested R).derivative (affineNested R).natDegree
    ((affineNested R).natDegree - 1)

/-- An irreducible `R` with nonzero `Z`-derivative has a nonzero discriminant. -/
theorem affineDiscriminant_ne_zero {R : MvPolynomial AffineVar E} (hirr : Irreducible R)
    (hder : MvPolynomial.pderiv none R ≠ 0) : affineDiscriminant R ≠ 0 := by
  refine resultant_derivative_ne_zero_of_irreducible _ (hirr.map affineNested) ?_
  rw [derivative_affineNested]
  exact (map_ne_zero_iff _ affineNested.injective).mpr hder

/-- From `r + b² ≤ (2b - 1) h` and `b ≤ h`, conclude `r ≤ h (h - 1)`. -/
private theorem le_of_add_sq_le_of_le {r b h : ℕ} (hb : b ≤ h)
    (hr : r + b ^ 2 ≤ (2 * b - 1) * h) : r ≤ h * (h - 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hb
  rcases b with _ | k
  · simp at hr
    simp [hr]
  · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hr
    rw [show k + 1 + t - 1 = k + t by omega]
    nlinarith

/-- If `R` has `(Y, Z)`-degree at most `h`, its discriminant has `Y`-degree at most
`h (h - 1)`. -/
theorem natDegree_affineDiscriminant_le {R : MvPolynomial AffineVar E} {h : ℕ}
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    (affineDiscriminant R).natDegree ≤ h * (h - 1) := by
  have hb : (affineNested R).natDegree ≤ h := by
    rw [natDegree_affineNested]
    exact (degreeOf_none_le_weightedTotalDegree R).trans hR
  have hres := natDegree_resultant_derivative_padded_add_sq_le (affineNested R)
    (affineNested R).natDegree h fun i hi ↦ by
      rw [natDegree_affineNested] at hi
      exact (add_natDegree_coeff_affineNested_le R hi).trans hR
  exact le_of_add_sq_le_of_le hb hres

/-- If the discriminant does not vanish on the line, a root `P` of `R` along it is simple.

The hypothesis `0 < deg_Z R` is needed: for `R` free of `Z` the discriminant is `1`. -/
theorem affineLineEval_pderiv_ne_zero {R : MvPolynomial AffineVar E} {α β : E} {P : E[X]}
    (hpos : 0 < R.degreeOf none) (hroot : affineLineEval α β P R = 0)
    (hdisc : (affineDiscriminant R).eval (affineMultiplier α β) ≠ 0) :
    affineLineEval α β P (MvPolynomial.pderiv none R) ≠ 0 := by
  rw [affineLineEval_eq_nested] at hroot ⊢
  rw [← derivative_affineNested, ← derivative_map]
  exact eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero
    (evalRingHom (affineMultiplier α β)) (affineNested R) le_rfl
    (by rwa [natDegree_affineNested]) hdisc P hroot

end ReedSolomon

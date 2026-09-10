/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas
public import CompPoly.Bivariate.CMvEquiv
public import ArkLib.ToCompPoly.Multivariate.Eval
public import ArkLib.Data.Polynomial.Differential.Basic
/-!
# Executable bivariate-to-multivariate conversion

`CBivariate` stores a polynomial in `Y` whose coefficients are polynomials in `X`. The ordinary
root-finding code expects a `CMvPolynomial 2` with `X` at index zero and `Y` at index one. The
constructor below traverses the two computable supports and records exactly that ordering.
-/

@[expose] public section

namespace CompPoly.CBivariate

open CPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- Exponent vector `X^i Y^j` in ordinary decoder variable order. -/
def ordinaryMonomial (i j : ℕ) : CMvMonomial 2 :=
  Vector.ofFn (Fin.cases i (fun _ => j))

theorem toFinsupp_ordinaryMonomial (i j : ℕ) :
    (ordinaryMonomial i j).toFinsupp =
      Finsupp.single 0 i + Finsupp.single 1 j := by
  ext index
  fin_cases index
  · simp only [ordinaryMonomial, CMvMonomial.toFinsupp, Finsupp.coe_mk,
      Vector.get_ofFn, Finsupp.add_apply, Finsupp.single_apply]
    simp
  · simp only [ordinaryMonomial, CMvMonomial.toFinsupp, Finsupp.coe_mk,
      Vector.get_ofFn, Finsupp.add_apply, Finsupp.single_apply]
    simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, zero_ne_one, ↓reduceIte, zero_add]
    convert
      (Fin.cases_succ (motive := fun _ : Fin 2 => ℕ) (zero := i)
        (succ := fun _ : Fin 1 => j) 0) using 1
    apply congrArg (Fin.cases i (fun _ : Fin 1 => j))
    apply Fin.ext
    rfl

/-- Executably convert `Q(X,Y)` to a concrete multivariate polynomial with variables `[X,Y]`. -/
def toOrdinaryCMv (Q : CBivariate F) : CMvPolynomial 2 F :=
  ∑ j ∈ Q.supportY,
    ∑ i ∈ (Q.val.coeff j).support,
      CMvPolynomial.monomial (ordinaryMonomial i j)
        (CPolynomial.coeff (Q.val.coeff j) i)

omit [DecidableEq F] in
/-- Substituting a mathematical polynomial for variable one recovers `Q(X,P(X))`. -/
theorem eval₂_fromCMvPolynomial_toOrdinaryCMv (Q : CBivariate F) (P : Polynomial F) :
    MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (fromCMvPolynomial (toOrdinaryCMv Q)) =
      (CBivariate.toPoly Q).eval P := by
  classical
  rw [toOrdinaryCMv, CMvPolynomial.fromCMvPolynomial_sum]
  simp_rw [CMvPolynomial.fromCMvPolynomial_sum,
    CMvPolynomial.fromCMvPolynomial_monomial,
    toFinsupp_ordinaryMonomial, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_monomial]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, support_toPoly_outer]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_toPoly_Y]
  have hprod (i : ℕ) :
      (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j).prod
        (fun index exponent => ![Polynomial.X, P] index ^ exponent) =
        Polynomial.X ^ i * P ^ j := by
    rw [Finsupp.prod_add_index]
    · rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro index _
      simp only [pow_zero]
    · intro index _ left right
      exact pow_add _ left right
  simp_rw [hprod]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  rw [Polynomial.as_sum_support (Q.val.coeff j).toPoly,
    ← CPolynomial.support_toPoly]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  exact congrArg (Polynomial.monomial i)
    (CPolynomial.coeff_toPoly (Q.val.coeff j) i)

omit [DecidableEq F] in
/-- A CompPoly root equation is the ordinary decoder's multivariate solution equation. -/
theorem solution_toOrdinaryCMv_iff (Q : CBivariate F) (P : Polynomial F) :
    CBivariate.composeY Q ⟨P.toImpl, CPolynomial.Raw.isCanonical_toImpl P⟩ = 0 ↔
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (fromCMvPolynomial (toOrdinaryCMv Q)) = 0 := by
  classical
  rw [← CPolynomial.toPoly_eq_zero_iff]
  rw [GuruswamiSudan.composeY_toPoly, CPolynomial.toPoly_mk_toImpl]
  rw [eval₂_fromCMvPolynomial_toOrdinaryCMv]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- At differential order zero, the semantic equation specializes to ordinary composition. -/
theorem differentialSpecialization_orderZero (Q : CPoly.CMvPolynomial 2 F)
    (P : Polynomial F) :
    PolynomialDifferential.differentialSpecialization
        (MvPolynomial.rename (Fin.cases none some) (CPoly.fromCMvPolynomial Q)) P =
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
        (CPoly.fromCMvPolynomial Q) := by
  rw [PolynomialDifferential.differentialSpecialization]
  change MvPolynomial.eval₂ Polynomial.C _
      (MvPolynomial.rename _ (CPoly.fromCMvPolynomial Q)) = _
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext index
  refine Fin.cases ?_ (fun j => ?_) index
  · rfl
  · fin_cases j
    simp only [Function.comp_apply, Fin.cases_succ, Polynomial.hasseDeriv_zero]
    change P = P
    rfl

end CompPoly.CBivariate

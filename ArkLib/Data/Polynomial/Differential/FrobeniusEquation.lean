/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Basic
public import ArkLib.Data.MvPolynomial.FrobeniusContraction
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import ArkLib.ToMathlib.MvPolynomial.RootContraction
/-!
# Frobenius contraction of ordinary differential equations

This module identifies an ordinary differential polynomial with a bivariate polynomial whose
coordinates represent the root and the challenge. It proves degree and evaluation laws for this
identification, then contracts an irreducible equation in its root coordinate and transports its
specialized roots through polynomial expansion.

## Main statements

* `ordinaryFlatten` and `ordinaryUnflatten` identify ordinary differential polynomials with
  bivariate polynomials.
* Their evaluation, derivative, and degree laws describe the flattened coordinates.
* `CoeffNatDegreeLE` bounds the degrees of the polynomial coefficients of an equation.
* `exists_frobeniusEquation` produces an irreducible equation with nonzero root derivative while
  preserving challenge-height and independent-degree bounds.
* `frobeniusSpecialization_eq_zero` transports specialized roots to the contracted equation.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial
open MvPolynomial

namespace PolynomialDifferential

noncomputable section

/-- The ordinary root and challenge coordinates as variables of a bivariate polynomial. -/
def flatVariableEquiv : (JetVariable 0 ⊕ Unit) ≃ Option (Fin 2) where
  toFun
    | Sum.inl none => some 0
    | Sum.inl (some _) => none
    | Sum.inr _ => some 1
  invFun
    | none => Sum.inl (some 0)
    | some i => Fin.cases (Sum.inl none) (fun _ => Sum.inr ()) i
  left_inv x := by
    rcases x with (x | x)
    · rcases x with (_ | i)
      · rfl
      · fin_cases i
        rfl
    · rcases x with ⟨⟩
      rfl
  right_inv x := by
    rcases x with (_ | i)
    · rfl
    · fin_cases i <;> rfl

/-- Reorders the ordinary differential variables with the root coordinate first. -/
def rootFirstEquiv : JetVariable 0 ≃ Option Unit where
  toFun
    | none => some ()
    | some _ => none
  invFun
    | none => some 0
    | some _ => none
  left_inv x := by
    rcases x with (_ | i)
    · rfl
    · fin_cases i
      rfl
  right_inv x := by
    rcases x with (_ | i)
    · rfl
    · rcases i with ⟨⟩
      rfl

/-- Identifies the two ordinary base coordinates with `Fin 2`. -/
def baseVariableEquiv : (Unit ⊕ Unit) ≃ Fin 2 where
  toFun
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  invFun i := Fin.cases (Sum.inl ()) (fun _ => Sum.inr ()) i
  left_inv x := by rcases x with (⟨⟩ | ⟨⟩) <;> rfl
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · fin_cases j
      rfl

/-- Flattens the root and challenge variables of a polynomial-valued polynomial. -/
def baseFlatten (E : Type*) [CommSemiring E] :
    MvPolynomial Unit E[X] ≃ₐ[E] MvPolynomial (Fin 2) E :=
  (MvPolynomial.mapAlgEquiv Unit
      (MvPolynomial.uniqueAlgEquiv E Unit).symm).trans
    ((MvPolynomial.sumAlgEquiv E Unit Unit).symm.trans
      (MvPolynomial.renameEquiv E baseVariableEquiv))

/-- Flattens the ordinary root and challenge variables into two polynomial variables. -/
def ordinaryFlatten (E : Type*) [CommSemiring E] :
    DifferentialPolynomial E[X] 0 ≃ₐ[E] MvPolynomial (Option (Fin 2)) E :=
  (MvPolynomial.mapAlgEquiv (JetVariable 0)
      (MvPolynomial.uniqueAlgEquiv E Unit).symm).trans
    ((MvPolynomial.sumAlgEquiv E (JetVariable 0) Unit).symm.trans
      (MvPolynomial.renameEquiv E flatVariableEquiv))

section Ordinary

variable {E : Type*} [CommSemiring E]

/-- Flattening preserves constants. -/
@[simp] theorem ordinaryFlatten_C (a : E) :
    ordinaryFlatten E (MvPolynomial.C (Polynomial.C a) : DifferentialPolynomial E[X] 0) =
      MvPolynomial.C a := by
  simp [ordinaryFlatten]

/-- The independent variable maps to the first ordinary coordinate. -/
@[simp] theorem ordinaryFlatten_X :
    ordinaryFlatten E (MvPolynomial.X none : DifferentialPolynomial E[X] 0) =
      MvPolynomial.X (some 0) := by
  simp [ordinaryFlatten, flatVariableEquiv]

/-- The root variable maps to the distinguished flattened coordinate. -/
@[simp] theorem ordinaryFlatten_Y :
    ordinaryFlatten E (MvPolynomial.X (some 0) : DifferentialPolynomial E[X] 0) =
      MvPolynomial.X none := by
  simp [ordinaryFlatten, flatVariableEquiv]

/-- The coefficient polynomial variable maps to the challenge coordinate. -/
@[simp] theorem ordinaryFlatten_coeff_X :
    ordinaryFlatten E (MvPolynomial.C Polynomial.X : DifferentialPolynomial E[X] 0) =
      MvPolynomial.X (some 1) := by
  simp [ordinaryFlatten, flatVariableEquiv]

private theorem ordinaryFlatCases_one {R : Type*} (t z : R) :
    Fin.cases t (fun _ : Fin 1 ↦ z) (1 : Fin 2) = z := rfl

/-- Flattening sends a coefficient monomial to a power of the challenge variable. -/
theorem ordinaryFlatten_C_monomial (n : ℕ) (a : E) :
    ordinaryFlatten E
        (MvPolynomial.C (Polynomial.monomial n a) : DifferentialPolynomial E[X] 0) =
      MvPolynomial.C a * MvPolynomial.X (some 1) ^ n := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, ordinaryFlatten_C, ordinaryFlatten_coeff_X]

/-- The flattened form of a coefficient polynomial has zero root derivative. -/
theorem ordinaryFlatten_pderiv_C (r : E[X]) :
    MvPolynomial.pderiv none
      (ordinaryFlatten E (MvPolynomial.C r : DifferentialPolynomial E[X] 0)) = 0 := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [ordinaryFlatten, flatVariableEquiv]

/-- Evaluation of the flattened polynomial agrees with ordinary differential evaluation. -/
theorem eval_ordinaryFlatten (Q : DifferentialPolynomial E[X] 0) (t y z : E) :
    MvPolynomial.eval
        (fun o => o.elim y (fun i => Fin.cases t (fun _ => z) i))
        (ordinaryFlatten E Q) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun o => o.elim t (fun _ => y)) Q := by
  have hhom :
      (MvPolynomial.eval
          (fun o => o.elim y (fun i => Fin.cases t (fun _ => z) i))).comp
          (ordinaryFlatten E).toRingHom =
        MvPolynomial.eval₂Hom (Polynomial.evalRingHom z)
          (fun o => o.elim t (fun _ => y)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      induction r using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]
      | monomial n a =>
          simp [ordinaryFlatten_C_monomial, ordinaryFlatCases_one]
    · intro i
      rcases i with (_ | i)
      · simp [ordinaryFlatten, flatVariableEquiv]
      · fin_cases i
        simp [ordinaryFlatten, flatVariableEquiv]
  exact DFunLike.congr_fun hhom Q

/-- The ring-hom evaluation law for `ordinaryFlatten`. -/
theorem eval₂_ordinaryFlatten
    {S : Type*} [CommSemiring S] (f : E →+* S)
    (Q : DifferentialPolynomial E[X] 0) (t y z : S) :
    MvPolynomial.eval₂ f
        (fun o => o.elim y (fun i => Fin.cases t (fun _ => z) i))
        (ordinaryFlatten E Q) =
      MvPolynomial.eval₂ (Polynomial.eval₂RingHom f z)
        (fun o => o.elim t (fun _ => y)) Q := by
  have hhom :
      (MvPolynomial.eval₂Hom f
          (fun o => o.elim y (fun i => Fin.cases t (fun _ => z) i))).comp
          (ordinaryFlatten E).toRingHom =
        MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom f z)
          (fun o => o.elim t (fun _ => y)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      induction r using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]
      | monomial n a =>
          simp [ordinaryFlatten_C_monomial, ordinaryFlatCases_one]
    · intro i
      rcases i with (_ | i)
      · simp [ordinaryFlatten, flatVariableEquiv]
      · fin_cases i
        simp [ordinaryFlatten, flatVariableEquiv]
  exact DFunLike.congr_fun hhom Q

/-- The inverse of `ordinaryFlatten`. -/
def ordinaryUnflatten (E : Type*) [CommSemiring E] :
    MvPolynomial (Option (Fin 2)) E ≃ₐ[E] DifferentialPolynomial E[X] 0 :=
  (ordinaryFlatten E).symm

/-- Evaluation after unflattening agrees with evaluation in the flattened coordinates. -/
theorem eval_ordinaryUnflatten
    (H : MvPolynomial (Option (Fin 2)) E) (t y z : E) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun o : JetVariable 0 => o.elim t (fun _ => y))
        (ordinaryUnflatten E H) =
      MvPolynomial.eval
        (fun o => o.elim y (fun i => Fin.cases t (fun _ => z) i)) H := by
  rw [← eval_ordinaryFlatten (ordinaryUnflatten E H) t y z]
  simp [ordinaryUnflatten]

/-- The ring-hom evaluation law for `ordinaryUnflatten`. -/
theorem eval₂_ordinaryUnflatten
    {S : Type*} [CommSemiring S] (f : E →+* S)
    (H : MvPolynomial (Option (Fin 2)) E) (t y z : S) :
    MvPolynomial.eval₂ (Polynomial.eval₂RingHom f z)
        (fun o : JetVariable 0 => o.elim t (fun _ => y))
        (ordinaryUnflatten E H) =
      MvPolynomial.eval₂ f
        (fun o => o.elim y (fun i => Fin.cases t (fun _ => z) i)) H := by
  rw [← eval₂_ordinaryFlatten f (ordinaryUnflatten E H) t y z]
  simp [ordinaryUnflatten]

/-- Flattening carries the root partial derivative to the distinguished partial derivative. -/
theorem ordinaryFlatten_pderiv_root
    (Q : DifferentialPolynomial E[X] 0) :
    ordinaryFlatten E (MvPolynomial.pderiv (some 0) Q) =
      MvPolynomial.pderiv none (ordinaryFlatten E Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.pderiv_C, map_zero] using (ordinaryFlatten_pderiv_C a).symm
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
    rcases j with (_ | j)
    · simp [hP]
    · fin_cases j
      simp [hP, mul_comm, add_comm]

/-- Unflattening carries the distinguished partial derivative back to the root variable. -/
theorem ordinaryUnflatten_pderiv_root
    (H : MvPolynomial (Option (Fin 2)) E) :
    ordinaryUnflatten E (MvPolynomial.pderiv none H) =
      MvPolynomial.pderiv (some 0) (ordinaryUnflatten E H) := by
  apply (ordinaryFlatten E).injective
  rw [ordinaryFlatten_pderiv_root]
  simp [ordinaryUnflatten]

/-- The flattened equation, viewed as a univariate polynomial, has the root coordinate as its
variable. -/
theorem rootPolynomial_ordinaryFlatten
    (Q : DifferentialPolynomial E[X] 0) :
    optionEquivLeft E (Fin 2) (ordinaryFlatten E Q) =
      Polynomial.map (baseFlatten E).toRingEquiv.toRingHom
        (optionEquivLeft E[X] Unit
          (MvPolynomial.rename rootFirstEquiv Q)) := by
  have hhom :
      (optionEquivLeft E (Fin 2)).toRingHom.comp
          (ordinaryFlatten E).toRingHom =
        (Polynomial.mapRingHom (baseFlatten E).toRingEquiv.toRingHom).comp
          ((optionEquivLeft E[X] Unit).toRingHom.comp
            (MvPolynomial.rename rootFirstEquiv).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      induction r using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]
      | monomial n a =>
          simp [ordinaryFlatten, baseFlatten, flatVariableEquiv,
            baseVariableEquiv, rootFirstEquiv]
    · intro o
      rcases o with (_ | i)
      · simp [ordinaryFlatten, baseFlatten, flatVariableEquiv,
          baseVariableEquiv, rootFirstEquiv]
      · fin_cases i
        simp [ordinaryFlatten, baseFlatten, flatVariableEquiv,
          baseVariableEquiv, rootFirstEquiv]
  exact DFunLike.congr_fun hhom Q

/-- Flattening preserves the degree of the root variable. -/
theorem degreeOf_none_ordinaryFlatten
    (Q : DifferentialPolynomial E[X] 0) :
    (ordinaryFlatten E Q).degreeOf none = Q.degreeOf (some 0) := by
  rw [← natDegree_optionEquivLeft E, rootPolynomial_ordinaryFlatten]
  rw [Polynomial.natDegree_map_eq_of_injective (baseFlatten E).injective]
  rw [natDegree_optionEquivLeft]
  simpa [rootFirstEquiv] using
    degreeOf_rename_of_injective rootFirstEquiv.injective (some 0) (p := Q)

/-- The inverse flattening formula for a multivariate monomial. -/
theorem ordinaryUnflatten_monomial
    (m : Option (Fin 2) →₀ ℕ) (c : E) :
    ordinaryUnflatten E (MvPolynomial.monomial m c) =
      MvPolynomial.C (Polynomial.C c * Polynomial.X ^ m (some 1)) *
        MvPolynomial.X none ^ m (some 0) *
        MvPolynomial.X (some 0) ^ m none := by
  classical
  apply (ordinaryFlatten E).injective
  simp only [ordinaryUnflatten, AlgEquiv.apply_symm_apply, map_mul, map_pow,
    ordinaryFlatten_X, ordinaryFlatten_Y]
  simp [ordinaryFlatten, flatVariableEquiv, MvPolynomial.monomial_eq,
    Finsupp.prod_fintype]
  ring

/-- A monomial's coefficient degree after unflattening is bounded by its challenge exponent. -/
theorem coeffNatDegreeLE_ordinaryUnflatten_monomial
    (m : Option (Fin 2) →₀ ℕ) (c : E) :
    CoeffNatDegreeLE (ordinaryUnflatten E (MvPolynomial.monomial m c)) (m (some 1)) := by
  classical
  rw [ordinaryUnflatten_monomial]
  intro d
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial]
  simp only [mul_one,
    MvPolynomial.coeff_monomial]
  split_ifs with hd
  · by_cases hc : c = 0
    · subst c
      simp
    · rw [Polynomial.natDegree_C_mul_X_pow (m (some 1)) c hc]
  · simp

/-- A challenge-degree bound gives a coefficient-degree bound after unflattening. -/
theorem coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le
    (H : MvPolynomial (Option (Fin 2)) E) {h : ℕ}
    (hdegree : H.degreeOf (some 1) ≤ h) :
    CoeffNatDegreeLE (ordinaryUnflatten E H) h := by
  classical
  have hsum : ordinaryUnflatten E H =
      ∑ m ∈ H.support,
        ordinaryUnflatten E (MvPolynomial.monomial m (H.coeff m)) := by
    conv_lhs => rw [MvPolynomial.as_sum H]
    simp only [map_sum]
  intro d
  rw [hsum, MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  exact (coeffNatDegreeLE_ordinaryUnflatten_monomial m
    (H.coeff m) d).trans
      ((MvPolynomial.monomial_le_degreeOf (some 1) hm).trans hdegree)

/-- Flattening a coefficient polynomial has challenge degree at most its univariate degree. -/
theorem degreeOf_challenge_ordinaryFlatten_C_le [Nontrivial E] (c : E[X]) :
    (ordinaryFlatten E
      (MvPolynomial.C c : DifferentialPolynomial E[X] 0)).degreeOf (some 1) ≤
        c.natDegree := by
  classical
  have hsum : ordinaryFlatten E
      (MvPolynomial.C c : DifferentialPolynomial E[X] 0) =
      ∑ n ∈ c.support,
        ordinaryFlatten E
          (MvPolynomial.C (Polynomial.monomial n (c.coeff n)) :
            DifferentialPolynomial E[X] 0) := by
    conv_lhs => rw [← Polynomial.sum_monomial_eq c]
    simp only [Polynomial.sum_def, map_sum]
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le (some 1) c.support
    (fun n => ordinaryFlatten E
      (MvPolynomial.C (Polynomial.monomial n (c.coeff n)) :
        DifferentialPolynomial E[X] 0))).trans
  apply Finset.sup_le
  intro n hn
  simpa [ordinaryFlatten, flatVariableEquiv] using (MvPolynomial.degreeOf_C_mul_le
    (MvPolynomial.X (some 1) ^ n) (some 1) (c.coeff n)).trans
      ((MvPolynomial.degreeOf_X_self_pow (R := E) (some 1) n).le.trans
        (Polynomial.le_natDegree_of_ne_zero
          (n := n) (p := c) (Polynomial.mem_support_iff.mp hn)))

/-- Flattening sends a differential monomial to the product of its variable powers. -/
theorem ordinaryFlatten_monomial
    (m : JetVariable 0 →₀ ℕ) (c : E[X]) :
    ordinaryFlatten E (MvPolynomial.monomial m c) =
      ordinaryFlatten E
          (MvPolynomial.C c : DifferentialPolynomial E[X] 0) *
        MvPolynomial.X (some 0) ^ m none *
        MvPolynomial.X none ^ m (some 0) := by
  classical
  simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype,
    ordinaryFlatten, flatVariableEquiv]
  ring

/-- A coefficient-degree bound gives a challenge-coordinate degree bound after flattening. -/
theorem degreeOf_challenge_ordinaryFlatten_le
    [Nontrivial E] (Q : DifferentialPolynomial E[X] 0) {h : ℕ}
    (hQ : CoeffNatDegreeLE Q h) :
    (ordinaryFlatten E Q).degreeOf (some 1) ≤ h := by
  classical
  have hsum : ordinaryFlatten E Q =
      ∑ m ∈ Q.support,
        ordinaryFlatten E (MvPolynomial.monomial m (Q.coeff m)) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [map_sum]
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le (some 1) Q.support
    (fun m => ordinaryFlatten E
      (MvPolynomial.monomial m (Q.coeff m)))).trans
  apply Finset.sup_le
  intro m hm
  rw [ordinaryFlatten_monomial]
  have hT : (MvPolynomial.X (some 0) ^ m none :
      MvPolynomial (Option (Fin 2)) E).degreeOf (some 1) = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (by simp)
  have hY : (MvPolynomial.X none ^ m (some 0) :
      MvPolynomial (Option (Fin 2)) E).degreeOf (some 1) = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (by simp)
  calc
    _ ≤ ((ordinaryFlatten E
        (MvPolynomial.C (Q.coeff m) :
          DifferentialPolynomial E[X] 0)) *
        MvPolynomial.X (some 0) ^ m none).degreeOf (some 1) +
          (MvPolynomial.X none ^ m (some 0) :
            MvPolynomial (Option (Fin 2)) E).degreeOf (some 1) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ ((ordinaryFlatten E
        (MvPolynomial.C (Q.coeff m) :
          DifferentialPolynomial E[X] 0)).degreeOf (some 1) +
          (MvPolynomial.X (some 0) ^ m none :
            MvPolynomial (Option (Fin 2)) E).degreeOf (some 1)) + 0 := by
      rw [hY]
      exact Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) 0
    _ = (ordinaryFlatten E
        (MvPolynomial.C (Q.coeff m) :
          DifferentialPolynomial E[X] 0)).degreeOf (some 1) := by rw [hT]; omega
    _ ≤ (Q.coeff m).natDegree :=
      degreeOf_challenge_ordinaryFlatten_C_le (Q.coeff m)
    _ ≤ h := hQ m

/-- Flattening a coefficient polynomial gives degree zero in the independent coordinate. -/
theorem degreeOf_independent_ordinaryFlatten_C
    (c : E[X]) :
    (ordinaryFlatten E
      (MvPolynomial.C c : DifferentialPolynomial E[X] 0)).degreeOf (some 0) = 0 := by
  classical
  have hsum : ordinaryFlatten E
      (MvPolynomial.C c : DifferentialPolynomial E[X] 0) =
      ∑ n ∈ c.support,
        ordinaryFlatten E
          (MvPolynomial.C (Polynomial.monomial n (c.coeff n)) :
            DifferentialPolynomial E[X] 0) := by
    conv_lhs => rw [← Polynomial.sum_monomial_eq c]
    simp only [Polynomial.sum_def, map_sum]
  apply Nat.eq_zero_of_le_zero
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le (some 0) c.support
    (fun n => ordinaryFlatten E
      (MvPolynomial.C (Polynomial.monomial n (c.coeff n)) :
        DifferentialPolynomial E[X] 0))).trans
  apply Finset.sup_le
  intro n hn
  simpa [ordinaryFlatten, flatVariableEquiv] using Nat.eq_zero_of_le_zero
    ((MvPolynomial.degreeOf_C_mul_le
      (MvPolynomial.X (some 1) ^ n) (some 0) (c.coeff n)).trans
        ((MvPolynomial.degreeOf_X_pow_of_ne n (by simp)).le))

/-- Flattening does not increase the degree of the independent variable. -/
theorem degreeOf_independent_ordinaryFlatten_le
    [Nontrivial E] (Q : DifferentialPolynomial E[X] 0) :
    (ordinaryFlatten E Q).degreeOf (some 0) ≤ Q.degreeOf none := by
  classical
  have hsum : ordinaryFlatten E Q =
      ∑ m ∈ Q.support,
        ordinaryFlatten E (MvPolynomial.monomial m (Q.coeff m)) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [map_sum]
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le (some 0) Q.support
    (fun m => ordinaryFlatten E
      (MvPolynomial.monomial m (Q.coeff m)))).trans
  apply Finset.sup_le
  intro m hm
  rw [ordinaryFlatten_monomial]
  have hY : (MvPolynomial.X none ^ m (some 0) :
      MvPolynomial (Option (Fin 2)) E).degreeOf (some 0) = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (by simp)
  calc
    _ ≤ ((ordinaryFlatten E
        (MvPolynomial.C (Q.coeff m) :
          DifferentialPolynomial E[X] 0)) *
        MvPolynomial.X (some 0) ^ m none).degreeOf (some 0) +
          (MvPolynomial.X none ^ m (some 0) :
            MvPolynomial (Option (Fin 2)) E).degreeOf (some 0) :=
      MvPolynomial.degreeOf_mul_le (some 0)
        ((ordinaryFlatten E
          (MvPolynomial.C (Q.coeff m) :
            DifferentialPolynomial E[X] 0)) *
          MvPolynomial.X (some 0) ^ m none)
        (MvPolynomial.X none ^ m (some 0))
    _ = ((ordinaryFlatten E
        (MvPolynomial.C (Q.coeff m) :
          DifferentialPolynomial E[X] 0)) *
        MvPolynomial.X (some 0) ^ m none).degreeOf (some 0) + 0 := by rw [hY]
    _ ≤ ((ordinaryFlatten E
        (MvPolynomial.C (Q.coeff m) :
          DifferentialPolynomial E[X] 0)).degreeOf (some 0) +
        (MvPolynomial.X (some 0) ^ m none :
          MvPolynomial (Option (Fin 2)) E).degreeOf (some 0)) + 0 := by
      exact Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) 0
    _ = m none := by
      rw [degreeOf_independent_ordinaryFlatten_C,
        MvPolynomial.degreeOf_X_self_pow]
      omega
    _ ≤ Q.degreeOf none := MvPolynomial.monomial_le_degreeOf none hm

/-- Unflattening does not increase the independent-variable degree. -/
theorem degreeOf_independent_ordinaryUnflatten_le
    [Nontrivial E] (H : MvPolynomial (Option (Fin 2)) E) :
    (ordinaryUnflatten E H).degreeOf none ≤ H.degreeOf (some 0) := by
  classical
  have hsum : ordinaryUnflatten E H =
      ∑ m ∈ H.support,
        ordinaryUnflatten E (MvPolynomial.monomial m (H.coeff m)) := by
    conv_lhs => rw [MvPolynomial.as_sum H]
    simp only [map_sum]
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le none H.support
    (fun m => ordinaryUnflatten E
      (MvPolynomial.monomial m (H.coeff m)))).trans
  apply Finset.sup_le
  intro m hm
  rw [ordinaryUnflatten_monomial]
  have hY : (MvPolynomial.X (some 0) ^ m none :
      DifferentialPolynomial E[X] 0).degreeOf none = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (by simp)
  calc
    _ ≤ ((MvPolynomial.C
          (Polynomial.C (H.coeff m) * Polynomial.X ^ m (some 1)) *
        MvPolynomial.X none ^ m (some 0) :
          DifferentialPolynomial E[X] 0).degreeOf none) + 0 := by
      simpa only [hY] using MvPolynomial.degreeOf_mul_le none
        (MvPolynomial.C
            (Polynomial.C (H.coeff m) * Polynomial.X ^ m (some 1)) *
          MvPolynomial.X none ^ m (some 0) :
          DifferentialPolynomial E[X] 0)
        (MvPolynomial.X (some 0) ^ m none)
    _ ≤ ((MvPolynomial.C
          (Polynomial.C (H.coeff m) * Polynomial.X ^ m (some 1)) :
          DifferentialPolynomial E[X] 0).degreeOf none +
        (MvPolynomial.X none ^ m (some 0) :
          DifferentialPolynomial E[X] 0).degreeOf none) + 0 := by
      exact Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) 0
    _ = m (some 0) := by
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow]
      omega
    _ ≤ H.degreeOf (some 0) := MvPolynomial.monomial_le_degreeOf (some 0) hm

/-- Flattening preserves the degree of the independent variable. -/
theorem degreeOf_some_zero_ordinaryFlatten
    [Nontrivial E] (Q : DifferentialPolynomial E[X] 0) :
    (ordinaryFlatten E Q).degreeOf (some 0) = Q.degreeOf none := by
  apply Nat.le_antisymm (degreeOf_independent_ordinaryFlatten_le Q)
  simpa [ordinaryUnflatten] using
    degreeOf_independent_ordinaryUnflatten_le (ordinaryFlatten E Q)

/-- Differential specialization equals evaluation of the flattened equation. -/
theorem differentialSpecialization_map_eq_eval₂_flatten
    (Q : DifferentialPolynomial E[X] 0) (P : E[X]) (z : E) :
    differentialSpecialization (MvPolynomial.map (Polynomial.evalRingHom z) Q) P =
      MvPolynomial.eval₂ Polynomial.C
        (fun o => o.elim P (fun i => Fin.cases Polynomial.X (fun _ => Polynomial.C z) i))
        (ordinaryFlatten E Q) := by
  have hhom :
      (differentialSpecializationHom P).toRingHom.comp
          (MvPolynomial.map (σ := JetVariable 0) (Polynomial.evalRingHom z)) =
        (MvPolynomial.eval₂Hom Polynomial.C
            (fun o => o.elim P
              (fun i => Fin.cases Polynomial.X (fun _ => Polynomial.C z) i))).comp
          (ordinaryFlatten E).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      induction r using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, hp, hq]
      | monomial n a =>
          simp [differentialSpecializationHom, ordinaryFlatten_C_monomial,
            ordinaryFlatCases_one]
    · intro o
      rcases o with (_ | i)
      · simp [differentialSpecializationHom, ordinaryFlatten, flatVariableEquiv]
      · fin_cases i
        simp [differentialSpecializationHom, ordinaryFlatten, flatVariableEquiv]
  exact DFunLike.congr_fun hhom Q

/-- Evaluating a specialization agrees with the flattened evaluation. -/
theorem eval_differentialSpecialization_map_eq_flatten
    (Q : DifferentialPolynomial E[X] 0) (P : E[X]) (z x : E) :
    (differentialSpecialization (MvPolynomial.map (Polynomial.evalRingHom z) Q) P).eval x =
      MvPolynomial.eval
        (fun o => o.elim (P.eval x) (fun i => Fin.cases x (fun _ => z) i))
        (ordinaryFlatten E Q) := by
  rw [eval_differentialSpecialization, jetEvaluation, MvPolynomial.eval_map,
    eval_ordinaryFlatten]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext o
  rcases o with (_ | i)
  · rfl
  · fin_cases i
    simp [polynomialJet, Polynomial.hasseJet]

/-- Expanding a specialization expands the root and independent coordinates of the flattening. -/
theorem expand_differentialSpecialization_map_eq_eval₂_flatten
    (Q : DifferentialPolynomial E[X] 0) (P : E[X]) (z : E) (s : ℕ) :
    Polynomial.expand E s
        (differentialSpecialization (MvPolynomial.map (Polynomial.evalRingHom z) Q) P) =
      MvPolynomial.eval₂ Polynomial.C
        (fun o => o.elim (Polynomial.expand E s P)
          (fun i => Fin.cases (Polynomial.X ^ s) (fun _ => Polynomial.C z) i))
        (ordinaryFlatten E Q) := by
  rw [differentialSpecialization_map_eq_eval₂_flatten]
  change (Polynomial.expand E s).toRingHom
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun o => o.elim P
          (fun i => Fin.cases Polynomial.X (fun _ => Polynomial.C z) i))
        (ordinaryFlatten E Q)) = _
  rw [MvPolynomial.map_eval₂Hom]
  apply MvPolynomial.eval₂Hom_congr
  · ext a
    simp
  · funext o
    rcases o with (_ | i)
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
  · rfl

end Ordinary

section Frobenius

variable {E : Type*} [CommRing E]

/-- The transported specialization raised to `p ^ e` equals the expanded original
specialization. -/
theorem frobeniusSpecialization_pow
    (p e : ℕ) [ExpChar E p] [PerfectRing E p]
    (Q : DifferentialPolynomial E[X] 0)
    (G : MvPolynomial (Option (Fin 2)) E)
    (hroot : rootExpansion (p ^ e) G = ordinaryFlatten E Q)
    (P : E[X]) (w : E) :
    differentialSpecialization
          (MvPolynomial.map (Polynomial.evalRingHom w)
            (ordinaryUnflatten E (inverseFrobeniusTwist p e G)))
          (Polynomial.expand E (p ^ e) P) ^ (p ^ e) =
      Polynomial.expand E (p ^ e)
        (differentialSpecialization
          (MvPolynomial.map (Polynomial.evalRingHom (w ^ (p ^ e))) Q) P) := by
  rw [differentialSpecialization_map_eq_eval₂_flatten]
  simp only [ordinaryUnflatten, AlgEquiv.apply_symm_apply]
  change (MvPolynomial.eval₂Hom Polynomial.C
      (fun o => o.elim (Polynomial.expand E (p ^ e) P)
        (fun i => Fin.cases Polynomial.X (fun _ => Polynomial.C w) i))
      (inverseFrobeniusTwist p e G)) ^ (p ^ e) = _
  rw [← map_pow, inverseFrobeniusTwist_pow]
  change MvPolynomial.eval₂ Polynomial.C
      (fun o => o.elim (Polynomial.expand E (p ^ e) P)
        (fun i => Fin.cases Polynomial.X (fun _ => Polynomial.C w) i))
      (MvPolynomial.expand (p ^ e) G) = _
  rw [MvPolynomial.eval₂_expand]
  rw [expand_differentialSpecialization_map_eq_eval₂_flatten]
  rw [← hroot, eval₂_rootExpansion]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext o
  rcases o with (_ | i)
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp

/-- A zero original specialization gives a zero transported specialization. -/
theorem frobeniusSpecialization_eq_zero
    (p e : ℕ) [NoZeroDivisors E] [ExpChar E p] [PerfectRing E p]
    (Q : DifferentialPolynomial E[X] 0)
    (G : MvPolynomial (Option (Fin 2)) E)
    (hroot : rootExpansion (p ^ e) G = ordinaryFlatten E Q)
    (P : E[X]) (w : E)
    (hQ : differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom (w ^ (p ^ e))) Q) P = 0) :
    differentialSpecialization
        (MvPolynomial.map (Polynomial.evalRingHom w)
          (ordinaryUnflatten E (inverseFrobeniusTwist p e G)))
        (Polynomial.expand E (p ^ e) P) = 0 := by
  apply eq_zero_of_pow_eq_zero (n := p ^ e)
  rw [frobeniusSpecialization_pow p e Q G hroot P w, hQ, map_zero]

/-- An irreducible ordinary equation can be contracted in its root coordinate and pulled back
through inverse Frobenius.  The pulled equation has nonzero root derivative, preserves the
advertised challenge height, and transports every specialized polynomial root. -/
theorem exists_frobeniusEquation
    (p : ℕ) [Nontrivial E] [NoZeroDivisors E] [ExpChar E p] [PerfectRing E p]
    {Q : DifferentialPolynomial E[X] 0}
    (hQpos : 0 < Q.degreeOf (some 0)) (hQirr : Irreducible Q)
    {h : ℕ} (hQheight : CoeffNatDegreeLE Q h) :
    ∃ e : ℕ, ∃ H : DifferentialPolynomial E[X] 0,
      Irreducible H ∧
      MvPolynomial.pderiv (some 0) H ≠ 0 ∧
      H.degreeOf (some 0) * (p ^ e) = Q.degreeOf (some 0) ∧
      H.degreeOf none ≤ Q.degreeOf none ∧
      CoeffNatDegreeLE H h ∧
      ∀ (P : E[X]) (w : E),
        differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom (w ^ (p ^ e))) Q) P = 0 →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom w) H)
              (Polynomial.expand E (p ^ e) P) = 0 := by
  have hflatpos : 0 < (ordinaryFlatten E Q).degreeOf none := by
    rwa [degreeOf_none_ordinaryFlatten]
  have hflatirr : Irreducible (ordinaryFlatten E Q) :=
    hQirr.map (ordinaryFlatten E)
  obtain ⟨e, G, hGder, hroot, hGdegree, _hGpos, hGirr, hGother⟩ :=
    MvPolynomial.exists_irreducible_frobeniusContraction_expChar p hflatpos hflatirr
  have hTwistIrr : Irreducible (inverseFrobeniusTwist p e G) :=
    (MvPolynomial.irreducible_inverseFrobeniusTwist_iff p e (G := G)).2 hGirr
  have hTwistDer : MvPolynomial.pderiv none (inverseFrobeniusTwist p e G) ≠ 0 :=
    (MvPolynomial.pderiv_inverseFrobeniusTwist_ne_zero_iff p e G none).2 hGder
  have hTwistDegree (i : Option (Fin 2)) :
      (inverseFrobeniusTwist p e G).degreeOf i = G.degreeOf i :=
    MvPolynomial.degreeOf_inverseFrobeniusTwist p e G i
  let H : DifferentialPolynomial E[X] 0 :=
    ordinaryUnflatten E (inverseFrobeniusTwist p e G)
  have hflattenH :
      ordinaryFlatten E H = inverseFrobeniusTwist p e G := by
    simp only [H, ordinaryUnflatten, AlgEquiv.apply_symm_apply]
  have hHirr : Irreducible H := by
    simpa only [H] using hTwistIrr.map (ordinaryUnflatten E)
  have hHder : MvPolynomial.pderiv (some 0) H ≠ 0 := by
    rw [← ordinaryUnflatten_pderiv_root]
    intro hz
    apply hTwistDer
    apply (ordinaryUnflatten E).injective
    simpa using hz
  have hHrootdegree :
      H.degreeOf (some 0) * (p ^ e) = Q.degreeOf (some 0) := by
    rw [← degreeOf_none_ordinaryFlatten, hflattenH,
      hTwistDegree none, hGdegree, degreeOf_none_ordinaryFlatten]
  have hHTdegree : H.degreeOf none ≤ Q.degreeOf none := by
    calc
      _ = (inverseFrobeniusTwist p e G).degreeOf (some 0) := by
        rw [← degreeOf_some_zero_ordinaryFlatten H, hflattenH]
      _ = G.degreeOf (some 0) := hTwistDegree (some 0)
      _ ≤ (ordinaryFlatten E Q).degreeOf (some 0) := hGother 0
      _ = Q.degreeOf none := degreeOf_some_zero_ordinaryFlatten Q
  have hHheight : CoeffNatDegreeLE H h := by
    apply coeffNatDegreeLE_ordinaryUnflatten_of_degreeOf_le
    rw [hTwistDegree (some 1)]
    exact (hGother 1).trans
      (degreeOf_challenge_ordinaryFlatten_le Q hQheight)
  refine ⟨e, H, hHirr, hHder, hHrootdegree, hHTdegree, hHheight, ?_⟩
  intro P w hQroot
  exact frobeniusSpecialization_eq_zero p e Q G hroot P w hQroot

end Frobenius
end
end PolynomialDifferential

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Basic
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorHeight
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusFactor
/-!
# Frobenius pullback for ordinary differential equations

An ordinary symbolic differential equation has one independent variable, one root variable, and
one polynomial challenge in its coefficients.  This file flattens those three coordinates, removes
all Frobenius powers from the root coordinate of an irreducible equation, twists the terminal
coefficients by inverse Frobenius, and converts the result back to an ordinary equation.

The resulting equation is irreducible, has nonzero root derivative, retains the challenge-height
and independent-degree bounds, and transports specialized polynomial roots under
`Polynomial.expand`.
This is an algebraic transport theorem; it does not prove incidence or agreement bounds.
-/

@[expose] public section

open PolynomialDifferential
open Polynomial
open MvPolynomial

namespace ReedSolomon.HiddenDerivative

noncomputable section

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

def baseFlatten (E : Type*) [CommSemiring E] :
    MvPolynomial Unit E[X] ≃ₐ[E] MvPolynomial (Fin 2) E :=
  (MvPolynomial.mapAlgEquiv Unit
      (MvPolynomial.uniqueAlgEquiv E Unit).symm).trans
    ((MvPolynomial.sumAlgEquiv E Unit Unit).symm.trans
      (MvPolynomial.renameEquiv E baseVariableEquiv))

def ordinaryFlatten (E : Type*) [CommSemiring E] :
    DifferentialPolynomial E[X] 0 ≃ₐ[E] MvPolynomial (Option (Fin 2)) E :=
  (MvPolynomial.mapAlgEquiv (JetVariable 0)
      (MvPolynomial.uniqueAlgEquiv E Unit).symm).trans
    ((MvPolynomial.sumAlgEquiv E (JetVariable 0) Unit).symm.trans
      (MvPolynomial.renameEquiv E flatVariableEquiv))

variable {E : Type*} [Field E]

@[simp] theorem ordinaryFlatten_C (a : E) :
    ordinaryFlatten E (MvPolynomial.C (Polynomial.C a) : DifferentialPolynomial E[X] 0) =
      MvPolynomial.C a := by
  simp [ordinaryFlatten]

@[simp] theorem ordinaryFlatten_X :
    ordinaryFlatten E (MvPolynomial.X none : DifferentialPolynomial E[X] 0) =
      MvPolynomial.X (some 0) := by
  simp [ordinaryFlatten, flatVariableEquiv]

@[simp] theorem ordinaryFlatten_Y :
    ordinaryFlatten E (MvPolynomial.X (some 0) : DifferentialPolynomial E[X] 0) =
      MvPolynomial.X none := by
  simp [ordinaryFlatten, flatVariableEquiv]

@[simp] theorem ordinaryFlatten_coeff_X :
    ordinaryFlatten E (MvPolynomial.C Polynomial.X : DifferentialPolynomial E[X] 0) =
      MvPolynomial.X (some 1) := by
  simp [ordinaryFlatten, flatVariableEquiv]

theorem ordinaryFlatCases_one {R : Type*} (t z : R) :
    Fin.cases t (fun _ : Fin 1 ↦ z) (1 : Fin 2) = z := rfl

theorem ordinaryFlatten_C_monomial (n : ℕ) (a : E) :
    ordinaryFlatten E
        (MvPolynomial.C (Polynomial.monomial n a) : DifferentialPolynomial E[X] 0) =
      MvPolynomial.C a * MvPolynomial.X (some 1) ^ n := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [map_mul, map_pow, ordinaryFlatten_C, ordinaryFlatten_coeff_X]

theorem ordinaryFlatten_pderiv_C (r : E[X]) :
    MvPolynomial.pderiv none
      (ordinaryFlatten E (MvPolynomial.C r : DifferentialPolynomial E[X] 0)) = 0 := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [ordinaryFlatten, flatVariableEquiv]

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

def ordinaryUnflatten (E : Type*) [CommSemiring E] :
    MvPolynomial (Option (Fin 2)) E ≃ₐ[E] DifferentialPolynomial E[X] 0 :=
  (ordinaryFlatten E).symm

theorem eval_ordinaryUnflatten
    (H : MvPolynomial (Option (Fin 2)) E) (t y z : E) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (fun o : JetVariable 0 => o.elim t (fun _ => y))
        (ordinaryUnflatten E H) =
      MvPolynomial.eval
        (fun o => o.elim y (fun i => Fin.cases t (fun _ => z) i)) H := by
  rw [← eval_ordinaryFlatten (ordinaryUnflatten E H) t y z]
  simp [ordinaryUnflatten]

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

theorem ordinaryUnflatten_pderiv_root
    (H : MvPolynomial (Option (Fin 2)) E) :
    ordinaryUnflatten E (MvPolynomial.pderiv none H) =
      MvPolynomial.pderiv (some 0) (ordinaryUnflatten E H) := by
  apply (ordinaryFlatten E).injective
  rw [ordinaryFlatten_pderiv_root]
  simp [ordinaryUnflatten]

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

theorem degreeOf_none_ordinaryFlatten
    (Q : DifferentialPolynomial E[X] 0) :
    (ordinaryFlatten E Q).degreeOf none = Q.degreeOf (some 0) := by
  rw [← natDegree_optionEquivLeft E, rootPolynomial_ordinaryFlatten]
  rw [Polynomial.natDegree_map_eq_of_injective (baseFlatten E).injective]
  rw [natDegree_optionEquivLeft]
  simpa [rootFirstEquiv] using
    degreeOf_rename_of_injective rootFirstEquiv.injective (some 0) (p := Q)

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

theorem challengeHeightLE_ordinaryUnflatten_monomial
    (m : Option (Fin 2) →₀ ℕ) (c : E) :
    ChallengeHeightLE (ordinaryUnflatten E (MvPolynomial.monomial m c)) (m (some 1)) := by
  classical
  rw [ordinaryUnflatten_monomial]
  intro d
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul]
  simp only [mul_one,
    MvPolynomial.coeff_monomial]
  split_ifs with hd
  · by_cases hc : c = 0
    · subst c
      simp
    · rw [Polynomial.natDegree_C_mul_X_pow (m (some 1)) c hc]
  · simp

theorem challengeHeightLE_ordinaryUnflatten_of_degreeOf_le
    (H : MvPolynomial (Option (Fin 2)) E) {h : ℕ}
    (hdegree : H.degreeOf (some 1) ≤ h) :
    ChallengeHeightLE (ordinaryUnflatten E H) h := by
  classical
  have hsum : ordinaryUnflatten E H =
      ∑ m ∈ H.support,
        ordinaryUnflatten E (MvPolynomial.monomial m (MvPolynomial.coeff m H)) := by
    conv_lhs => rw [MvPolynomial.as_sum H]
    simp only [map_sum]
  intro d
  rw [hsum, MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  exact (challengeHeightLE_ordinaryUnflatten_monomial m
    (MvPolynomial.coeff m H) d).trans
      ((MvPolynomial.monomial_le_degreeOf (some 1) hm).trans hdegree)

theorem degreeOf_challenge_ordinaryFlatten_C_le (c : E[X]) :
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

theorem degreeOf_challenge_ordinaryFlatten_le
    (Q : DifferentialPolynomial E[X] 0) {h : ℕ}
    (hQ : ChallengeHeightLE Q h) :
    (ordinaryFlatten E Q).degreeOf (some 1) ≤ h := by
  classical
  have hsum : ordinaryFlatten E Q =
      ∑ m ∈ Q.support,
        ordinaryFlatten E (MvPolynomial.monomial m (MvPolynomial.coeff m Q)) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [map_sum]
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le (some 1) Q.support
    (fun m => ordinaryFlatten E
      (MvPolynomial.monomial m (MvPolynomial.coeff m Q)))).trans
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
        (MvPolynomial.C (MvPolynomial.coeff m Q) :
          DifferentialPolynomial E[X] 0)) *
        MvPolynomial.X (some 0) ^ m none).degreeOf (some 1) +
          (MvPolynomial.X none ^ m (some 0) :
            MvPolynomial (Option (Fin 2)) E).degreeOf (some 1) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ ((ordinaryFlatten E
        (MvPolynomial.C (MvPolynomial.coeff m Q) :
          DifferentialPolynomial E[X] 0)).degreeOf (some 1) +
          (MvPolynomial.X (some 0) ^ m none :
            MvPolynomial (Option (Fin 2)) E).degreeOf (some 1)) + 0 := by
      rw [hY]
      exact Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) 0
    _ = (ordinaryFlatten E
        (MvPolynomial.C (MvPolynomial.coeff m Q) :
          DifferentialPolynomial E[X] 0)).degreeOf (some 1) := by rw [hT]; omega
    _ ≤ (MvPolynomial.coeff m Q).natDegree :=
      degreeOf_challenge_ordinaryFlatten_C_le (MvPolynomial.coeff m Q)
    _ ≤ h := hQ m

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

theorem degreeOf_independent_ordinaryFlatten_le
    (Q : DifferentialPolynomial E[X] 0) :
    (ordinaryFlatten E Q).degreeOf (some 0) ≤ Q.degreeOf none := by
  classical
  have hsum : ordinaryFlatten E Q =
      ∑ m ∈ Q.support,
        ordinaryFlatten E (MvPolynomial.monomial m (MvPolynomial.coeff m Q)) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [map_sum]
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le (some 0) Q.support
    (fun m => ordinaryFlatten E
      (MvPolynomial.monomial m (MvPolynomial.coeff m Q)))).trans
  apply Finset.sup_le
  intro m hm
  rw [ordinaryFlatten_monomial]
  have hY : (MvPolynomial.X none ^ m (some 0) :
      MvPolynomial (Option (Fin 2)) E).degreeOf (some 0) = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (by simp)
  calc
    _ ≤ ((ordinaryFlatten E
        (MvPolynomial.C (MvPolynomial.coeff m Q) :
          DifferentialPolynomial E[X] 0)) *
        MvPolynomial.X (some 0) ^ m none).degreeOf (some 0) +
          (MvPolynomial.X none ^ m (some 0) :
            MvPolynomial (Option (Fin 2)) E).degreeOf (some 0) :=
      MvPolynomial.degreeOf_mul_le (some 0)
        ((ordinaryFlatten E
          (MvPolynomial.C (MvPolynomial.coeff m Q) :
            DifferentialPolynomial E[X] 0)) *
          MvPolynomial.X (some 0) ^ m none)
        (MvPolynomial.X none ^ m (some 0))
    _ = ((ordinaryFlatten E
        (MvPolynomial.C (MvPolynomial.coeff m Q) :
          DifferentialPolynomial E[X] 0)) *
        MvPolynomial.X (some 0) ^ m none).degreeOf (some 0) + 0 := by rw [hY]
    _ ≤ ((ordinaryFlatten E
        (MvPolynomial.C (MvPolynomial.coeff m Q) :
          DifferentialPolynomial E[X] 0)).degreeOf (some 0) +
        (MvPolynomial.X (some 0) ^ m none :
          MvPolynomial (Option (Fin 2)) E).degreeOf (some 0)) + 0 := by
      exact Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) 0
    _ = m none := by
      rw [degreeOf_independent_ordinaryFlatten_C,
        MvPolynomial.degreeOf_X_self_pow]
      omega
    _ ≤ Q.degreeOf none := MvPolynomial.monomial_le_degreeOf none hm

theorem degreeOf_independent_ordinaryUnflatten_le
    (H : MvPolynomial (Option (Fin 2)) E) :
    (ordinaryUnflatten E H).degreeOf none ≤ H.degreeOf (some 0) := by
  classical
  have hsum : ordinaryUnflatten E H =
      ∑ m ∈ H.support,
        ordinaryUnflatten E (MvPolynomial.monomial m (MvPolynomial.coeff m H)) := by
    conv_lhs => rw [MvPolynomial.as_sum H]
    simp only [map_sum]
  rw [hsum]
  apply (MvPolynomial.degreeOf_sum_le none H.support
    (fun m => ordinaryUnflatten E
      (MvPolynomial.monomial m (MvPolynomial.coeff m H)))).trans
  apply Finset.sup_le
  intro m hm
  rw [ordinaryUnflatten_monomial]
  have hY : (MvPolynomial.X (some 0) ^ m none :
      DifferentialPolynomial E[X] 0).degreeOf none = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (by simp)
  calc
    _ ≤ ((MvPolynomial.C
          (Polynomial.C (MvPolynomial.coeff m H) * Polynomial.X ^ m (some 1)) *
        MvPolynomial.X none ^ m (some 0) :
          DifferentialPolynomial E[X] 0).degreeOf none) + 0 := by
      simpa only [hY] using MvPolynomial.degreeOf_mul_le none
        (MvPolynomial.C
            (Polynomial.C (MvPolynomial.coeff m H) * Polynomial.X ^ m (some 1)) *
          MvPolynomial.X none ^ m (some 0) :
          DifferentialPolynomial E[X] 0)
        (MvPolynomial.X (some 0) ^ m none)
    _ ≤ ((MvPolynomial.C
          (Polynomial.C (MvPolynomial.coeff m H) * Polynomial.X ^ m (some 1)) :
          DifferentialPolynomial E[X] 0).degreeOf none +
        (MvPolynomial.X none ^ m (some 0) :
          DifferentialPolynomial E[X] 0).degreeOf none) + 0 := by
      exact Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) 0
    _ = m (some 0) := by
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow]
      omega
    _ ≤ H.degreeOf (some 0) := MvPolynomial.monomial_le_degreeOf (some 0) hm

theorem degreeOf_some_zero_ordinaryFlatten
    (Q : DifferentialPolynomial E[X] 0) :
    (ordinaryFlatten E Q).degreeOf (some 0) = Q.degreeOf none := by
  apply Nat.le_antisymm (degreeOf_independent_ordinaryFlatten_le Q)
  simpa [ordinaryUnflatten] using
    degreeOf_independent_ordinaryUnflatten_le (ordinaryFlatten E Q)

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

theorem map_rootExpansion
    {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : ℕ) (G : MvPolynomial (Option ι) R) :
    MvPolynomial.map f (rootExpansion s G) =
      rootExpansion s (MvPolynomial.map f G) := by
  apply (optionEquivLeft S ι).injective
  rw [← map_optionEquivLeft]
  simp [rootExpansion, Polynomial.map_expand, map_optionEquivLeft]

theorem eval₂_rootExpansion
    {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (s : ℕ) (G : MvPolynomial (Option ι) R)
    (x : ι → S) (y : S) :
    MvPolynomial.eval₂ f (fun o => o.elim y x) (rootExpansion s G) =
      MvPolynomial.eval₂ f (fun o => o.elim (y ^ s) x) G := by
  rw [MvPolynomial.eval₂_eq_eval_map, map_rootExpansion,
    eval_rootExpansion, ← MvPolynomial.eval₂_eq_eval_map]

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

theorem frobeniusSpecialization_pow
    (p e : ℕ) [ExpChar E p] [PerfectField E]
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

theorem frobeniusSpecialization_eq_zero
    (p e : ℕ) [ExpChar E p] [PerfectField E]
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
    (p : ℕ) [ExpChar E p] [PerfectField E]
    {Q : DifferentialPolynomial E[X] 0}
    (hQpos : 0 < Q.degreeOf (some 0)) (hQirr : Irreducible Q)
    {h : ℕ} (hQheight : ChallengeHeightLE Q h) :
    ∃ e : ℕ, ∃ H : DifferentialPolynomial E[X] 0,
      Irreducible H ∧
      MvPolynomial.pderiv (some 0) H ≠ 0 ∧
      H.degreeOf (some 0) * (p ^ e) = Q.degreeOf (some 0) ∧
      H.degreeOf none ≤ Q.degreeOf none ∧
      ChallengeHeightLE H h ∧
      ∀ (P : E[X]) (w : E),
        differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom (w ^ (p ^ e))) Q) P = 0 →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom w) H)
              (Polynomial.expand E (p ^ e) P) = 0 := by
  let L := FractionRing (MvPolynomial (Fin 2) E)
  have hflatpos : 0 < (ordinaryFlatten E Q).degreeOf none := by
    rwa [degreeOf_none_ordinaryFlatten]
  have hflatirr : Irreducible (ordinaryFlatten E Q) :=
    hQirr.map (ordinaryFlatten E)
  obtain ⟨e, G, hroot, hGder, hGdegree, hGirr, hGother,
      _hGprimitive, _hGmapirr, _hGmapder, _hGmapsep, _hGmapdegree⟩ :=
    MvPolynomial.exists_frobeniusFactor_expChar
      (K := E) (L := L) p hflatpos hflatirr
  obtain ⟨hTwistIrr, hTwistDer, hTwistDegree⟩ :=
    MvPolynomial.inverseFrobeniusTwist_preserves_factor_expChar
      (K := E) p e hGirr hGder
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
  have hHheight : ChallengeHeightLE H h := by
    apply challengeHeightLE_ordinaryUnflatten_of_degreeOf_le
    rw [hTwistDegree (some 1)]
    exact (hGother 1).trans
      (degreeOf_challenge_ordinaryFlatten_le Q hQheight)
  refine ⟨e, H, hHirr, hHder, hHrootdegree, hHTdegree, hHheight, ?_⟩
  intro P w hQroot
  exact frobeniusSpecialization_eq_zero p e Q G hroot P w hQroot

/-- A nonconstant-coefficient canary: the root-linear equation `Y + W` carries the symbolic
challenge `W` in its coefficients and is transported together with every polynomial root. -/
theorem frobeniusEquation_nonconstant_coefficient_canary
    (p : ℕ) [ExpChar E p] [PerfectField E] :
    ∃ e : ℕ, ∃ H : DifferentialPolynomial E[X] 0,
      Irreducible H ∧
      MvPolynomial.pderiv (some 0) H ≠ 0 ∧
      H.degreeOf (some 0) * (p ^ e) = 1 ∧
      H.degreeOf none = 0 ∧
      ChallengeHeightLE H 1 ∧
      ∀ (P : E[X]) (w : E),
        differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom (w ^ (p ^ e)))
              (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
                DifferentialPolynomial E[X] 0)) P = 0 →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom w) H)
              (Polynomial.expand E (p ^ e) P) = 0 := by
  let Q : DifferentialPolynomial E[X] 0 :=
    MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X
  have hflat :
      ordinaryFlatten E Q =
        MvPolynomial.X none + MvPolynomial.X (some 1) := by
    simp only [Q, map_add, ordinaryFlatten_Y, ordinaryFlatten_coeff_X]
  have hpoly :
      optionEquivLeft E (Fin 2) (ordinaryFlatten E Q) =
        Polynomial.X + Polynomial.C (MvPolynomial.X 1) := by
    simp only [hflat, map_add, optionEquivLeft_X_none, optionEquivLeft_X_some]
  have hpolyirr : Irreducible
      (Polynomial.X + Polynomial.C (MvPolynomial.X 1) :
        Polynomial (MvPolynomial (Fin 2) E)) := by
    simpa only [map_neg, sub_neg_eq_add] using
      Polynomial.irreducible_X_sub_C
        (-(MvPolynomial.X 1 : MvPolynomial (Fin 2) E))
  have hflatirr : Irreducible (ordinaryFlatten E Q) := by
    have hi := hpolyirr.map (optionEquivLeft E (Fin 2)).symm
    rw [← hpoly] at hi
    simpa only [AlgEquiv.symm_apply_apply] using hi
  have hQirr : Irreducible Q := by
    simpa only [Q, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using
      hflatirr.map (ordinaryUnflatten E)
  have hQdegree : Q.degreeOf (some 0) = 1 := by
    rw [← degreeOf_none_ordinaryFlatten, ← natDegree_optionEquivLeft, hflat]
    simp
  have hQindependent : Q.degreeOf none = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (MvPolynomial.degreeOf_add_le none
      (MvPolynomial.X (some 0) : DifferentialPolynomial E[X] 0)
      (MvPolynomial.C Polynomial.X)).trans (by
        apply max_le
        · exact (MvPolynomial.degreeOf_X_of_ne (by simp)).le
        · exact (MvPolynomial.degreeOf_C _ _).le)
  have hQheight : ChallengeHeightLE Q 1 := by
    intro m
    simp only [Q, MvPolynomial.coeff_add]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · by_cases hm : m = Finsupp.single (some 0) 1
      · subst m
        simp
      · rw [MvPolynomial.coeff_X, if_neg (Ne.symm hm)]
        simp
    · by_cases hm : m = 0
      · subst m
        simp
      · rw [MvPolynomial.coeff_C, if_neg (Ne.symm hm)]
        simp
  obtain ⟨e, H, hHirr, hHder, hHdegree, hHindependent, hHheight, htransport⟩ :=
    exists_frobeniusEquation p (Q := Q) (by omega) hQirr hQheight
  refine ⟨e, H, hHirr, hHder, hHdegree.trans hQdegree,
    Nat.eq_zero_of_le_zero (hHindependent.trans_eq hQindependent),
    hHheight, ?_⟩
  simpa only [Q] using htransport

end
end ReedSolomon.HiddenDerivative

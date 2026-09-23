/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Multivariate polynomials with univariate polynomial coefficients

A polynomial `P : MvPolynomial σ R[X]` has two kinds of degree: the degree in the variables `σ`,
and the degree in `X` of its coefficients. Mathlib's `MvPolynomial.optionEquivRight` identifies
`MvPolynomial σ R[X]` with `MvPolynomial (Option σ) R`, where the variable `none` is `X`.

This file records both degrees.

* `MvPolynomial.CoeffNatDegreeLE P h` says that every coefficient of `P` has `natDegree ≤ h`. It
  is closed under sums and products (the bounds add), and under substitution of polynomials whose
  coefficients are constants, which includes formal differentiation.
* `MvPolynomial.jointTotalDegree P` is the total degree of `P` read in `MvPolynomial (Option σ) R`,
  so that `X` counts as one more variable. It is at most `h + P.totalDegree` when every
  coefficient has degree at most `h`, and cleared substitutions satisfy a monomialwise bound.

The file also shows that `MvPolynomial.optionEquivLeft` commutes with coefficient maps.

## Main statements

* `MvPolynomial.map_optionEquivLeft`: `optionEquivLeft` commutes with `MvPolynomial.map`.
* `MvPolynomial.aeval_map_optionEquivRight` and
  `MvPolynomial.aeval_optionEquivRight_symm`: evaluation through the flattened variable
  equivalence.
* `MvPolynomial.CoeffNatDegreeLE` and its closure lemmas, including
  `MvPolynomial.CoeffNatDegreeLE.map_coefficients`, `MvPolynomial.CoeffNatDegreeLE.aeval` and
  `MvPolynomial.CoeffNatDegreeLE.pderiv`.
* `MvPolynomial.jointTotalDegree`, its ring-operation bounds, `jointTotalDegree_C_le`,
  `jointTotalDegree_le_of_natDegree_coeff_le` and its form
  `CoeffNatDegreeLE.jointTotalDegree_le`, and `jointTotalDegree_clearedSubstitution_le`.

## References
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open scoped BigOperators

/-! ### Coefficient maps and `optionEquivLeft` -/

/-- Moving the variable `none` out as the polynomial variable commutes with a coefficient map. -/
theorem map_optionEquivLeft {A B σ : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (Q : MvPolynomial (Option σ) A) :
    Polynomial.map (map f) (optionEquivLeft A σ Q) = optionEquivLeft B σ (map f Q) := by
  have he : (Polynomial.mapRingHom (map f)).comp (optionEquivLeft A σ).toRingHom =
      (optionEquivLeft B σ).toRingHom.comp (map f) := by
    ext a : 2
    · simp
    · cases a <;> simp
  exact DFunLike.congr_fun he Q

variable {R σ τ : Type*} [CommSemiring R]

/-! ### The inverse of `optionEquivRight` on generators -/

/-- The inverse of `optionEquivRight` sends the variable `i` to the variable `some i`. -/
@[simp]
theorem optionEquivRight_symm_X (i : σ) :
    (optionEquivRight R σ).symm (X i) = X (some i) := by
  apply (optionEquivRight R σ).injective
  simp

/-- The inverse of `optionEquivRight` sends a constant `p : R[X]` to `p` evaluated at the variable
`none`. -/
@[simp]
theorem optionEquivRight_symm_C (p : Polynomial R) :
    (optionEquivRight R σ).symm (C p) = Polynomial.aeval (X none) p := by
  apply (optionEquivRight R σ).injective
  rw [AlgEquiv.apply_symm_apply, ← Polynomial.aeval_algHom_apply, optionEquivRight_X_none]
  have h := Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom R (Polynomial R) (MvPolynomial σ (Polynomial R))) Polynomial.X p
  simpa [Polynomial.aeval_X_left_apply, algebraMap_eq] using h.symm

/-- Evaluating a flattened polynomial after specializing its distinguished variable is the same
as evaluating the original polynomial in all its variables. -/
theorem aeval_map_optionEquivRight {A σ : Type*} [CommSemiring A] [Algebra R A]
    (x : Option σ → A) (p : MvPolynomial (Option σ) R) :
    aeval (fun j ↦ x (some j))
      (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom
        (optionEquivRight R σ p)) =
        aeval x p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    cases i <;> simp

/-- Evaluating the inverse flattened-variable equivalence first evaluates the distinguished
polynomial variable, then evaluates the remaining variables. -/
theorem aeval_optionEquivRight_symm {A σ : Type*} [CommSemiring A] [Algebra R A]
    (x : Option σ → A) (p : MvPolynomial σ (Polynomial R)) :
    aeval x ((optionEquivRight R σ).symm p) =
      aeval (fun j ↦ x (some j))
        (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom p) := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (aeval_map_optionEquivRight (R := R) x ((optionEquivRight R σ).symm p)).symm

/-! ### Degree bounds on the coefficients -/

/-- Every coefficient of `P : MvPolynomial σ R[X]` has `natDegree` at most `h`. -/
def CoeffNatDegreeLE (P : MvPolynomial σ (Polynomial R)) (h : ℕ) : Prop :=
  ∀ m, (P.coeff m).natDegree ≤ h

/-- A constant `p` has coefficient degree at most `h` when `p.natDegree ≤ h`. -/
theorem coeffNatDegreeLE_C {p : Polynomial R} {h : ℕ} (hp : p.natDegree ≤ h) :
    CoeffNatDegreeLE (C p : MvPolynomial σ (Polynomial R)) h := by
  classical
  intro m
  rw [coeff_C]
  split_ifs
  · exact hp
  · simp

/-- A variable has coefficient degree zero. -/
theorem coeffNatDegreeLE_X (i : σ) :
    CoeffNatDegreeLE (X i : MvPolynomial σ (Polynomial R)) 0 := by
  classical
  intro m
  rw [coeff_X]
  split_ifs <;> simp

/-- A polynomial with coefficients in `R`, mapped into `R[X]`, has coefficient degree zero. -/
theorem coeffNatDegreeLE_map_C (P : MvPolynomial σ R) :
    CoeffNatDegreeLE (map Polynomial.C P) 0 := by
  intro m
  rw [coeff_map, Polynomial.natDegree_C]

/-- The zero polynomial has coefficient degree zero. -/
theorem coeffNatDegreeLE_zero (h : ℕ) :
    CoeffNatDegreeLE (0 : MvPolynomial σ (Polynomial R)) h := by
  intro m
  simp

/-- A finite sum has coefficient degree at most `h` when every summand does. -/
theorem coeffNatDegreeLE_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ (Polynomial R)) {h : ℕ}
    (hP : ∀ i ∈ s, CoeffNatDegreeLE (P i) h) : CoeffNatDegreeLE (∑ i ∈ s, P i) h := by
  intro m
  rw [coeff_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi ↦ hP i hi m

namespace CoeffNatDegreeLE

variable {P Q : MvPolynomial σ (Polynomial R)} {a b : ℕ}

/-- The degree bound can be increased. -/
theorem mono (hP : CoeffNatDegreeLE P a) (h : a ≤ b) : CoeffNatDegreeLE P b :=
  fun m ↦ (hP m).trans h

/-- Sums keep a common coefficient degree bound. -/
theorem add (hP : CoeffNatDegreeLE P a) (hQ : CoeffNatDegreeLE Q a) :
    CoeffNatDegreeLE (P + Q) a := by
  intro m
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP m) (hQ m))

/-- Coefficient degree bounds add under products. -/
theorem mul (hP : CoeffNatDegreeLE P a) (hQ : CoeffNatDegreeLE Q b) :
    CoeffNatDegreeLE (P * Q) (a + b) := by
  classical
  intro m
  rw [coeff_mul]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ ↦
    Polynomial.natDegree_mul_le_of_le (hP p.1) (hQ p.2)

/-- The `n`-th power multiplies the coefficient degree bound by `n`. -/
theorem pow (hP : CoeffNatDegreeLE P a) (n : ℕ) : CoeffNatDegreeLE (P ^ n) (n * a) := by
  induction n with
  | zero => simpa using coeffNatDegreeLE_C (σ := σ) (p := (1 : Polynomial R)) (h := 0) (by simp)
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hP

/-- Substituting polynomials whose coefficients are constants keeps the coefficient degree
bound. -/
theorem aeval (hP : CoeffNatDegreeLE P a) (f : σ → MvPolynomial τ (Polynomial R))
    (hf : ∀ i, CoeffNatDegreeLE (f i) 0) : CoeffNatDegreeLE (MvPolynomial.aeval f P) a := by
  classical
  rw [P.as_sum, map_sum]
  apply coeffNatDegreeLE_sum
  intro m _
  rw [aeval_monomial]
  have hp : CoeffNatDegreeLE (m.prod fun i k ↦ f i ^ k) 0 := by
    rw [Finsupp.prod]
    induction m.support using Finset.induction_on with
    | empty =>
      simpa using coeffNatDegreeLE_C (σ := τ) (p := (1 : Polynomial R)) (h := 0) (by simp)
    | insert i s _ ih =>
      rw [Finset.prod_insert ‹_›]
      simpa using ((hf i).pow (m i)).mul ih
  simpa using (coeffNatDegreeLE_C (σ := τ) (hP m)).mul hp

/-- Formal differentiation keeps the coefficient degree bound. -/
theorem pderiv (hP : CoeffNatDegreeLE P a) (i : σ) :
    CoeffNatDegreeLE (MvPolynomial.pderiv i P) a := by
  intro m
  have hc : ((m i : Polynomial R) + 1) = Polynomial.C ((m i : R) + 1) := by simp
  rw [coeff_pderiv, hc]
  exact Polynomial.natDegree_mul_le_of_le (hP (m + Finsupp.single i 1))
    (Polynomial.natDegree_C _).le

end CoeffNatDegreeLE

/-- Mapping the coefficient polynomials along a ring homomorphism does not increase their
`natDegree` bound. -/
theorem CoeffNatDegreeLE.map_coefficients {S : Type*} [CommSemiring S]
    (f : R →+* S) (P : MvPolynomial σ (Polynomial R)) {h : ℕ}
    (hP : CoeffNatDegreeLE P h) :
    CoeffNatDegreeLE (MvPolynomial.map (Polynomial.mapRingHom f) P) h := by
  intro m
  rw [MvPolynomial.coeff_map]
  exact Polynomial.natDegree_map_le.trans (hP m)

/-! ### Joint total degree -/

/-- A power of a variable has total degree at most its exponent, also over the zero ring. -/
private theorem totalDegree_X_pow_le {K ι : Type*} [CommSemiring K] (i : ι) (n : ℕ) :
    (X i ^ n : MvPolynomial ι K).totalDegree ≤ n := by
  rw [X_pow_eq_monomial]
  exact (totalDegree_monomial_le _ _).trans (by simp)

/-- The total degree of `P : MvPolynomial σ R[X]` when the variable of the coefficients counts
as one more variable: the total degree of `(optionEquivRight R σ).symm P`. -/
def jointTotalDegree (P : MvPolynomial σ (Polynomial R)) : ℕ :=
  ((optionEquivRight R σ).symm P).totalDegree

/-- A constant from `R` has joint total degree zero. -/
@[simp]
theorem jointTotalDegree_C_C (a : R) :
    jointTotalDegree (C (Polynomial.C a) : MvPolynomial σ (Polynomial R)) = 0 := by
  simp [jointTotalDegree]

/-- A variable has joint total degree one. -/
@[simp]
theorem jointTotalDegree_X [Nontrivial R] (i : σ) :
    jointTotalDegree (X i : MvPolynomial σ (Polynomial R)) = 1 := by
  simp [jointTotalDegree]

/-- The joint total degree of a sum is at most the larger joint total degree. -/
theorem jointTotalDegree_add_le (P Q : MvPolynomial σ (Polynomial R)) :
    jointTotalDegree (P + Q) ≤ max (jointTotalDegree P) (jointTotalDegree Q) := by
  simp only [jointTotalDegree, map_add]
  exact totalDegree_add _ _

/-- The joint total degree of a product is at most the sum of the joint total degrees. -/
theorem jointTotalDegree_mul_le (P Q : MvPolynomial σ (Polynomial R)) :
    jointTotalDegree (P * Q) ≤ jointTotalDegree P + jointTotalDegree Q := by
  simp only [jointTotalDegree, map_mul]
  exact totalDegree_mul _ _

/-- The joint total degree of `P ^ n` is at most `n` times that of `P`. -/
theorem jointTotalDegree_pow_le (P : MvPolynomial σ (Polynomial R)) (n : ℕ) :
    jointTotalDegree (P ^ n) ≤ n * jointTotalDegree P := by
  simp only [jointTotalDegree, map_pow]
  exact totalDegree_pow _ _

/-- A finite sum has joint total degree at most `d` when every summand does. -/
theorem jointTotalDegree_finsetSum_le {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ (Polynomial R)) {d : ℕ}
    (hP : ∀ i ∈ s, jointTotalDegree (P i) ≤ d) :
    jointTotalDegree (∑ i ∈ s, P i) ≤ d := by
  simp only [jointTotalDegree, map_sum]
  exact totalDegree_finsetSum_le hP

/-- A constant `p : R[X]` has joint total degree at most `p.natDegree`. -/
theorem jointTotalDegree_C_le (p : Polynomial R) :
    jointTotalDegree (C p : MvPolynomial σ (Polynomial R)) ≤ p.natDegree := by
  classical
  have he : Polynomial.aeval (X none : MvPolynomial (Option σ) R) p =
      ∑ n ∈ p.support, C (p.coeff n) * X none ^ n := by
    conv_lhs => rw [p.as_sum_support]
    simp [map_sum, Polynomial.aeval_monomial, algebraMap_eq]
  rw [jointTotalDegree, optionEquivRight_symm_C, he]
  apply totalDegree_finsetSum_le
  intro n hn
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X_pow_le _ _).trans (Polynomial.le_natDegree_of_mem_supp n hn)

/-- If every coefficient of `P` has `natDegree ≤ h`, the joint total degree of `P` is at most
`h + P.totalDegree`. -/
theorem jointTotalDegree_le_of_natDegree_coeff_le (P : MvPolynomial σ (Polynomial R)) (h : ℕ)
    (hcoeff : ∀ m ∈ P.support, (P.coeff m).natDegree ≤ h) :
    jointTotalDegree P ≤ h + P.totalDegree := by
  classical
  have he : (optionEquivRight R σ).symm P =
      ∑ m ∈ P.support, (optionEquivRight R σ).symm (C (P.coeff m)) *
        ∏ i ∈ m.support, (X (some i) : MvPolynomial (Option σ) R) ^ m i := by
    conv_lhs => rw [P.as_sum]
    simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
      optionEquivRight_symm_X]
  rw [jointTotalDegree, he]
  apply totalDegree_finsetSum_le
  intro m hm
  have hc := (jointTotalDegree_C_le (σ := σ) (P.coeff m)).trans (hcoeff m hm)
  have hp : (∏ i ∈ m.support, (X (some i) : MvPolynomial (Option σ) R) ^ m i).totalDegree ≤
      m.sum (fun _ e ↦ e) := by
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact totalDegree_X_pow_le _ _
  exact (totalDegree_mul _ _).trans (Nat.add_le_add hc (hp.trans (le_totalDegree hm)))

/-- If every coefficient of `P` has `natDegree ≤ h`, the joint total degree of `P` is at most
`h + P.totalDegree`. -/
theorem CoeffNatDegreeLE.jointTotalDegree_le {P : MvPolynomial σ (Polynomial R)} {h : ℕ}
    (hP : CoeffNatDegreeLE P h) : jointTotalDegree P ≤ h + P.totalDegree :=
  jointTotalDegree_le_of_natDegree_coeff_le P h fun m _ ↦ hP m

/-- The joint total degree of a cleared substitution with coefficient map `C`. If `S` has joint
total degree at most `b`, each `N i` has joint total degree at most `d i * b + 1`, every monomial
of `Q` fits the budget `H`, and every monomial `m` of `Q` satisfies
`jointTotalDegree (C (Q.coeff m)) + degree m ≤ v`, then the numerator has joint total degree at
most `H * b + v`. The last hypothesis is monomialwise, so it measures the coefficient degree and
the monomial degree together. -/
theorem jointTotalDegree_clearedSubstitution_le
    (S : MvPolynomial σ (Polynomial R)) (N : τ → MvPolynomial σ (Polynomial R))
    (d : τ → ℕ) (H b v : ℕ) (Q : MvPolynomial τ (Polynomial R))
    (hS : jointTotalDegree S ≤ b)
    (hN : ∀ i, jointTotalDegree (N i) ≤ d i * b + 1)
    (hden : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hQ : ∀ m ∈ Q.support,
      jointTotalDegree (C (Q.coeff m) : MvPolynomial σ (Polynomial R)) + m.degree ≤ v) :
    jointTotalDegree (clearedSubstitution C S N d H Q) ≤ H * b + v := by
  unfold jointTotalDegree
  change ((optionEquivRight R σ).symm.toRingHom
    (clearedSubstitution C S N d H Q)).totalDegree ≤ _
  rw [ringHom_clearedSubstitution]
  exact totalDegree_clearedSubstitution_le_of_coeff _ _ _ d H b v Q hS hN hden hQ

section CommRing

variable {A : Type*} [CommRing A]

/-- Negation does not change the joint total degree. -/
@[simp]
theorem jointTotalDegree_neg (P : MvPolynomial σ (Polynomial A)) :
    jointTotalDegree (-P) = jointTotalDegree P := by
  simp only [jointTotalDegree, map_neg]
  exact totalDegree_neg _

/-- The joint total degree of a difference is at most the larger joint total degree. -/
theorem jointTotalDegree_sub_le (P Q : MvPolynomial σ (Polynomial A)) :
    jointTotalDegree (P - Q) ≤ max (jointTotalDegree P) (jointTotalDegree Q) := by
  simp only [jointTotalDegree, map_sub]
  exact totalDegree_sub _ _

end CommRing

end

end MvPolynomial

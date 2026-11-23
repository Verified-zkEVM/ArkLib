/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Power moments for multivariate polynomials

A bounded-degree polynomial coefficient can be represented linearly by coordinates for the
powers of one distinguished variable. The power-moment map evaluates those coordinates at the
corresponding powers and leaves the other variables unchanged.

## Main statements

* `MvPolynomial.powerMomentMap`, `powerMomentIdeal`, and `powerMomentIdeal_isPrime` describe the
  polynomial parametrization of the power-moment coordinates.
* `MvPolynomial.coefficientPowerLift` and `polynomialPowerLift` construct linear lifts of bounded
  polynomial coefficients and multivariate polynomials.
* The map theorems recover the original polynomials, and the total-degree bounds control the lifts.
* `chunkedCoefficientPowerLift` and `chunkedPolynomialPowerLift` represent coefficients of degree
  at most `M * D` using degree-`D` moment coordinates, with total-degree bounds `M + 1` and
  `B + M + 1`.

## References

* [DKT26]
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open Polynomial

variable {R : Type*} [CommSemiring R]

/-- Coordinates for powers through degree `D` together with the remaining variables. -/
abbrev PowerMomentIndex (D : ℕ) (σ : Type*) := Sum (Fin (D + 1)) σ

/-- Evaluate power coordinates at powers of one variable and preserve the other coordinates. -/
def powerMomentMap {σ : Type*} (D : ℕ) :
    MvPolynomial (PowerMomentIndex D σ) R →ₐ[R] MvPolynomial (Option σ) R :=
  MvPolynomial.aeval fun i ↦ i.elim
    (fun j ↦ (MvPolynomial.X none) ^ j.val) (fun j ↦ MvPolynomial.X (some j))

/-- The ideal of polynomial relations satisfied by the power-moment coordinates. -/
def powerMomentIdeal {σ : Type*} (D : ℕ) :
    Ideal (MvPolynomial (PowerMomentIndex D σ) R) :=
  RingHom.ker (powerMomentMap (R := R) (σ := σ) D).toRingHom

/-- The power-moment ideal is prime when the coefficient semiring is a domain. -/
theorem powerMomentIdeal_isPrime {σ : Type*} [IsDomain R] (D : ℕ) :
    (powerMomentIdeal (R := R) (σ := σ) D).IsPrime :=
  RingHom.ker_isPrime (powerMomentMap (R := R) (σ := σ) D).toRingHom

/-- A positive power degree makes the power-moment map surjective. -/
theorem powerMomentMap_surjective {σ : Type*} (D : ℕ) (hD : 0 < D) :
    Function.Surjective (powerMomentMap (R := R) (σ := σ) D) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, by simp [powerMomentMap]⟩
  | add P Q hP hQ =>
      obtain ⟨P', rfl⟩ := hP
      obtain ⟨Q', rfl⟩ := hQ
      exact ⟨P' + Q', by simp⟩
  | mul_X P i hP =>
      obtain ⟨P', rfl⟩ := hP
      cases i with
      | none =>
          exact ⟨P' * MvPolynomial.X (Sum.inl ⟨1, by omega⟩), by
            simp [powerMomentMap]⟩
      | some i => exact ⟨P' * MvPolynomial.X (Sum.inr i), by simp [powerMomentMap]⟩

/-- Linearize a polynomial in the power coordinates through degree `D`. Coefficients above
degree `D` are dropped, so the lift is faithful exactly when `p.natDegree ≤ D`
(`powerMomentMap_coefficientPowerLift`). -/
def coefficientPowerLift {σ : Type*} (D : ℕ) (p : R[X]) :
    MvPolynomial (PowerMomentIndex D σ) R :=
  ∑ j : Fin (D + 1), MvPolynomial.C (p.coeff j.val) *
    MvPolynomial.X (Sum.inl j)

/-- Evaluating a coefficient lift recovers the polynomial at the distinguished variable. -/
theorem powerMomentMap_coefficientPowerLift {σ : Type*} (D : ℕ) (p : R[X])
    (hp : p.natDegree ≤ D) :
    powerMomentMap (R := R) (σ := σ) D (coefficientPowerLift (R := R) D p) =
      Polynomial.aeval (MvPolynomial.X none : MvPolynomial (Option σ) R) p := by
  classical
  rw [coefficientPowerLift, map_sum]
  simp only [map_mul, powerMomentMap, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Sum.elim_inl]
  change (∑ j : Fin (D + 1), MvPolynomial.C (p.coeff j.val) *
    (MvPolynomial.X none : MvPolynomial (Option σ) R) ^ j.val) = _
  rw [Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum_range' (algebraMap R (MvPolynomial (Option σ) R))
      (by omega : p.natDegree < D + 1) (MvPolynomial.X none)]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ MvPolynomial.C (p.coeff j) *
      (MvPolynomial.X none : MvPolynomial (Option σ) R) ^ j) (D + 1)

/-- Lift each polynomial coefficient of a multivariate polynomial into power coordinates. -/
def polynomialPowerLift {σ : Type*} (D : ℕ) (P : MvPolynomial σ (R[X])) :
    MvPolynomial (PowerMomentIndex D σ) R :=
  ∑ m ∈ P.support,
    coefficientPowerLift (R := R) D (P.coeff m) *
      ∏ i ∈ m.support, MvPolynomial.X (Sum.inr i) ^ m i

private theorem powerMomentMap_coefficientwiseLift {σ : Type*} (D : ℕ)
    (lift : R[X] → MvPolynomial (PowerMomentIndex D σ) R) (P : MvPolynomial σ (R[X]))
    (hlift : ∀ m ∈ P.support,
      powerMomentMap (R := R) (σ := σ) D (lift (P.coeff m)) =
        Polynomial.aeval (MvPolynomial.X none : MvPolynomial (Option σ) R) (P.coeff m)) :
    powerMomentMap (R := R) (σ := σ) D
        (∑ m ∈ P.support, lift (P.coeff m) *
          ∏ i ∈ m.support, MvPolynomial.X (Sum.inr i) ^ m i) =
      (optionEquivRight R σ).symm P := by
  classical
  rw [map_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
    optionEquivRight_symm_C, optionEquivRight_symm_X]
  apply Finset.sum_congr rfl
  intro m hm
  change powerMomentMap (R := R) (σ := σ) D
      (lift (P.coeff m)) * _ = _
  rw [hlift m hm]
  simp [powerMomentMap]

/-- The power-moment map sends a lifted polynomial to its flattened form. -/
theorem powerMomentMap_polynomialPowerLift {σ : Type*} (D : ℕ)
    (P : MvPolynomial σ (R[X])) (hP : CoeffNatDegreeLE P D) :
    powerMomentMap (R := R) (σ := σ) D (polynomialPowerLift (R := R) D P) =
      (optionEquivRight R σ).symm P := by
  classical
  rw [polynomialPowerLift]
  exact powerMomentMap_coefficientwiseLift (R := R) (σ := σ) D
    (coefficientPowerLift (R := R) (σ := σ) D) P
    (fun m _ ↦ powerMomentMap_coefficientPowerLift (R := R) (σ := σ) D _ (hP m))

/-- Every bounded coefficient lift has total degree at most one. -/
theorem coefficientPowerLift_totalDegree_le_one {σ : Type*} [Nontrivial R] (D : ℕ)
    (p : R[X]) :
    (coefficientPowerLift (R := R) (σ := σ) D p).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

private theorem totalDegree_coefficientwiseLift_sum_le {σ : Type*} [Nontrivial R]
    (D B L : ℕ) (lift : R[X] → MvPolynomial (PowerMomentIndex D σ) R)
    (P : MvPolynomial σ (R[X])) (hlift : ∀ m ∈ P.support, (lift (P.coeff m)).totalDegree ≤ L)
    (hdeg : P.totalDegree ≤ B) :
    (∑ m ∈ P.support, lift (P.coeff m) *
      ∏ i ∈ m.support, MvPolynomial.X (Sum.inr i) ^ m i).totalDegree ≤ B + L := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hc := hlift m hm
  have hj : (∏ i ∈ m.support,
      (MvPolynomial.X (Sum.inr i) : MvPolynomial (PowerMomentIndex D σ) R) ^ m i).totalDegree ≤
      m.sum fun _ e ↦ e := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    simp [Finsupp.sum, MvPolynomial.totalDegree_X_pow]
  exact (Nat.add_le_add hc (hj.trans (MvPolynomial.le_totalDegree hm))).trans (by omega)

/-- A bounded polynomial lift has total degree at most one plus its original variable degree. -/
theorem polynomialPowerLift_totalDegree_le {σ : Type*} [Nontrivial R] (D B : ℕ)
    (P : MvPolynomial σ (R[X])) (hdeg : P.totalDegree ≤ B) :
    (polynomialPowerLift (R := R) D P).totalDegree ≤ B + 1 := by
  rw [polynomialPowerLift]
  exact totalDegree_coefficientwiseLift_sum_le (R := R) (σ := σ) D B 1
    (coefficientPowerLift (R := R) (σ := σ) D) P
    (fun _ _ ↦ coefficientPowerLift_totalDegree_le_one (R := R) (σ := σ) D _) hdeg

/-! ### Chunked power-moment lifts -/

/-- Represent a polynomial using degree-`D` power-moment coordinates. The exponent is split into
quotient and remainder upon division by `D`; the total-degree bound
`chunkedCoefficientPowerLift_totalDegree_le` assumes `p.natDegree ≤ M * D`. -/
def chunkedCoefficientPowerLift {σ : Type*} (D : ℕ) (hD : 0 < D) (p : R[X]) :
    MvPolynomial (PowerMomentIndex D σ) R :=
  ∑ j ∈ Finset.range (p.natDegree + 1),
    MvPolynomial.C (p.coeff j) *
      MvPolynomial.X (Sum.inl ⟨D, Nat.lt_succ_self D⟩) ^ (j / D) *
      MvPolynomial.X (Sum.inl ⟨j % D, (Nat.mod_lt j hD).trans_le (Nat.le_succ D)⟩)

/-- Evaluating a chunked coefficient lift recovers its polynomial. -/
theorem powerMomentMap_chunkedCoefficientPowerLift {σ : Type*} (D : ℕ) (hD : 0 < D)
    (p : R[X]) :
    powerMomentMap (R := R) (σ := σ) D
        (chunkedCoefficientPowerLift (R := R) (σ := σ) D hD p) =
      Polynomial.aeval (MvPolynomial.X none : MvPolynomial (Option σ) R) p := by
  classical
  rw [chunkedCoefficientPowerLift, map_sum]
  simp only [map_mul, map_pow, powerMomentMap, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Sum.elim_inl]
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, mul_assoc, ← pow_add]
  have he : D * (j / D) + j % D = j := by
    simpa only [Nat.add_comm] using (Nat.mod_add_div j D)
  rw [he]
  simp only [MvPolynomial.algebraMap_eq]

/-- Lift every polynomial coefficient of a multivariate polynomial using chunked power moments. -/
def chunkedPolynomialPowerLift {σ : Type*} (D : ℕ) (hD : 0 < D)
    (P : MvPolynomial σ (R[X])) : MvPolynomial (PowerMomentIndex D σ) R :=
  ∑ m ∈ P.support,
    chunkedCoefficientPowerLift (R := R) (σ := σ) D hD (P.coeff m) *
      ∏ i ∈ m.support, MvPolynomial.X (Sum.inr i) ^ m i

/-- The power-moment map sends a chunked lift to the flattened polynomial. -/
theorem powerMomentMap_chunkedPolynomialPowerLift {σ : Type*} (D : ℕ) (hD : 0 < D)
    (P : MvPolynomial σ (R[X])) :
    powerMomentMap (R := R) (σ := σ) D
        (chunkedPolynomialPowerLift (R := R) (σ := σ) D hD P) =
      (optionEquivRight R σ).symm P := by
  rw [chunkedPolynomialPowerLift]
  exact powerMomentMap_coefficientwiseLift (R := R) (σ := σ) D
    (chunkedCoefficientPowerLift (R := R) (σ := σ) D hD) P
    (fun _ _ ↦ powerMomentMap_chunkedCoefficientPowerLift (R := R) (σ := σ) D hD _)

/-- A chunked coefficient lift has total degree at most `M + 1`. -/
theorem chunkedCoefficientPowerLift_totalDegree_le {σ : Type*} [Nontrivial R]
    (D M : ℕ) (hD : 0 < D) (p : R[X]) (hp : p.natDegree ≤ M * D) :
    (chunkedCoefficientPowerLift (R := R) (σ := σ) D hD p).totalDegree ≤ M + 1 := by
  classical
  rw [chunkedCoefficientPowerLift]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply (Nat.add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl).trans
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow,
    MvPolynomial.totalDegree_X, zero_add, add_le_add_iff_right]
  have hjdeg : j ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjMD : j ≤ M * D := hjdeg.trans hp
  have hq : j / D ≤ M := Nat.div_le_of_le_mul (by
    simpa [Nat.mul_comm] using hjMD)
  omega

/-- A polynomial of jet degree at most `B` and coefficient degree at most `M * D` has a
chunked lift of total degree at most `B + M + 1`. -/
theorem chunkedPolynomialPowerLift_totalDegree_le {σ : Type*} [Nontrivial R]
    (D M B : ℕ) (hD : 0 < D) (P : MvPolynomial σ (R[X]))
    (hP : CoeffNatDegreeLE P (M * D)) (hdeg : P.totalDegree ≤ B) :
    (chunkedPolynomialPowerLift (R := R) (σ := σ) D hD P).totalDegree ≤ B + M + 1 := by
  rw [chunkedPolynomialPowerLift]
  have hbound := totalDegree_coefficientwiseLift_sum_le (R := R) (σ := σ) D B
    (M + 1) (chunkedCoefficientPowerLift (R := R) (σ := σ) D hD) P
    (fun m _ ↦ chunkedCoefficientPowerLift_totalDegree_le (R := R) (σ := σ) D M hD _ (hP m))
    hdeg
  omega

end

end MvPolynomial

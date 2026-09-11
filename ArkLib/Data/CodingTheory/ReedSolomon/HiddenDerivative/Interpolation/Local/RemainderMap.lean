/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Contact

/-!
# The normalized backward-Taylor remainder map

The manuscript states the local interpolation condition directly with the free remainder
appearing as `T^(d+1) V`.  The rank calculation uses the equivalent error coordinate
`E = T^d V`, in which the same term is written `T E` and rows are graded by contact order.

This file connects those two presentations over an arbitrary commutative ring.  Normalizing the
error sends a monomial exponent `(i,u,beta)` to `(i+d*u,u,beta)`.  This exponent map is injective,
so truncation by ordinary `T`-degree after normalization is exactly the old low-contact
projection before normalization.  Consequently the direct remainder map and the existing
constraint matrix have identical kernels; all rank and certificate proofs may continue to use
the contact coordinates.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Polynomial

variable {R : Type*} [CommRing R]
variable {d m : ℕ}

/-- Exponent relabeling induced by `E ↦ T^d E`. -/
def normalizeLocalExponent (d : ℕ) :
    (LocalVariable d →₀ ℕ) →+ (LocalVariable d →₀ ℕ) where
  toFun e := e + Finsupp.single (localT d) (d * e (localE d))
  map_zero' := by simp
  map_add' e f := by
    ext v
    simp [mul_add, add_assoc, add_left_comm]

@[simp]
theorem normalizeLocalExponent_apply_T (d : ℕ) (e : LocalVariable d →₀ ℕ) :
    normalizeLocalExponent d e (localT d) = e (localT d) + d * e (localE d) := by
  simp [normalizeLocalExponent, localT, localE, localAux]

@[simp]
theorem normalizeLocalExponent_apply_E (d : ℕ) (e : LocalVariable d →₀ ℕ) :
    normalizeLocalExponent d e (localE d) = e (localE d) := by
  simp [normalizeLocalExponent, localT, localE, localAux]

@[simp]
theorem normalizeLocalExponent_apply_Y (d : ℕ) (e : LocalVariable d →₀ ℕ) (j : Fin d) :
    normalizeLocalExponent d e (localY j) = e (localY j) := by
  simp [normalizeLocalExponent, localT, localY, localE, localAux]

/-- The row relabeling `(i,u,beta) ↦ (i+d*u,u,beta)` is injective. -/
theorem normalizeLocalExponent_injective (d : ℕ) :
    Function.Injective (normalizeLocalExponent d) := by
  intro e f h
  ext v
  rcases v with _ | (_ | j)
  · have hT := congrArg (fun g ↦ g (localT d)) h
    have hE := congrArg (fun g ↦ g (localE d)) h
    change normalizeLocalExponent d e (localT d) =
      normalizeLocalExponent d f (localT d) at hT
    change normalizeLocalExponent d e (localE d) =
      normalizeLocalExponent d f (localE d) at hE
    rw [normalizeLocalExponent_apply_T, normalizeLocalExponent_apply_T] at hT
    rw [normalizeLocalExponent_apply_E, normalizeLocalExponent_apply_E] at hE
    change e (localT d) = f (localT d)
    rw [hE] at hT
    exact Nat.add_right_cancel hT
  · have hE := congrArg (fun g ↦ g (localE d)) h
    change normalizeLocalExponent d e (localE d) =
      normalizeLocalExponent d f (localE d) at hE
    change e (localE d) = f (localE d)
    simpa only [normalizeLocalExponent_apply_E] using hE
  · have hY := congrArg (fun g ↦ g (localY j)) h
    change normalizeLocalExponent d e (localY j) =
      normalizeLocalExponent d f (localY j) at hY
    change e (localY j) = f (localY j)
    simpa only [normalizeLocalExponent_apply_Y] using hY

@[simp]
private theorem normalizeLocalExponent_single_T (d : ℕ) :
    normalizeLocalExponent d (Finsupp.single (localT d) 1) =
      Finsupp.single (localT d) 1 := by
  ext v
  rcases v with _ | (_ | j) <;>
    simp [normalizeLocalExponent, localT, localE, localAux]

@[simp]
private theorem normalizeLocalExponent_single_E (d : ℕ) :
    normalizeLocalExponent d (Finsupp.single (localE d) 1) =
      Finsupp.single (localE d) 1 + Finsupp.single (localT d) d := by
  ext v
  rcases v with _ | (_ | j) <;>
    simp [normalizeLocalExponent, localT, localE, localAux]

@[simp]
private theorem normalizeLocalExponent_single_Y (d : ℕ) (j : Fin d) :
    normalizeLocalExponent d (Finsupp.single (localY j) 1) =
      Finsupp.single (localY j) 1 := by
  ext v
  rcases v with _ | (_ | k) <;>
    simp [normalizeLocalExponent, localT, localE, localAux, localY]

/-- Monomial-domain presentation of error normalization. -/
def normalizeErrorByExponent (d : ℕ) :
    LocalPolynomial R d →ₐ[R] LocalPolynomial R d :=
  AddMonoidAlgebra.mapDomainAlgHom R R (normalizeLocalExponent d)

theorem normalizeError_eq_normalizeErrorByExponent (d : ℕ) :
    normalizeError (R := R) d = normalizeErrorByExponent d := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | (_ | j)
  · change normalizeError d (MvPolynomial.X (localT d)) =
      normalizeErrorByExponent d (MvPolynomial.X (localT d))
    rw [normalizeError_T]
    change MvPolynomial.X (localT d) =
      AddMonoidAlgebra.mapDomain (normalizeLocalExponent d)
        (AddMonoidAlgebra.single (Finsupp.single (localT d) 1) 1)
    rw [AddMonoidAlgebra.mapDomain_single, normalizeLocalExponent_single_T]
    rfl
  · change normalizeError d (MvPolynomial.X (localE d)) =
      normalizeErrorByExponent d (MvPolynomial.X (localE d))
    rw [normalizeError_E]
    change MvPolynomial.X (localT d) ^ d * MvPolynomial.X (localE d) =
      AddMonoidAlgebra.mapDomain (normalizeLocalExponent d)
        (AddMonoidAlgebra.single (Finsupp.single (localE d) 1) 1)
    rw [AddMonoidAlgebra.mapDomain_single, normalizeLocalExponent_single_E]
    rw [MvPolynomial.X_pow_eq_monomial]
    change MvPolynomial.monomial (Finsupp.single (localT d) d) 1 *
        MvPolynomial.monomial (Finsupp.single (localE d) 1) 1 =
      MvPolynomial.monomial
        (Finsupp.single (localE d) 1 + Finsupp.single (localT d) d) 1
    rw [MvPolynomial.monomial_mul]
    simp [add_comm]
  · change normalizeError d (MvPolynomial.X (localY j)) =
      normalizeErrorByExponent d (MvPolynomial.X (localY j))
    rw [normalizeError_Y]
    change MvPolynomial.X (localY j) =
      AddMonoidAlgebra.mapDomain (normalizeLocalExponent d)
        (AddMonoidAlgebra.single (Finsupp.single (localY j) 1) 1)
    rw [AddMonoidAlgebra.mapDomain_single, normalizeLocalExponent_single_Y]
    rfl

/-- Error normalization is injective over every coefficient ring. -/
theorem normalizeError_injective (d : ℕ) :
    Function.Injective (normalizeError (R := R) d) := by
  rw [normalizeError_eq_normalizeErrorByExponent]
  exact AddMonoidAlgebra.mapDomain_injective (normalizeLocalExponent_injective d)

/-- Error normalization turns contact order into ordinary `T`-degree. -/
theorem normalizeLocalExponent_T_eq_contact (d : ℕ) (e : LocalVariable d →₀ ℕ) :
    normalizeLocalExponent d e (localT d) = localContactOrder d e := by
  rw [normalizeLocalExponent_apply_T]
  simp [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option,
    localContactWeight, localT, localE, localAux, mul_comm]

private theorem filterLocalMonomials_monomial
    (predicate : (LocalVariable d →₀ ℕ) → Prop) [DecidablePred predicate]
    (e : LocalVariable d →₀ ℕ) (c : R) :
    filterLocalMonomials (R := R) predicate (MvPolynomial.monomial e c) =
      if predicate e then MvPolynomial.monomial e c else 0 := by
  by_cases he : predicate e
  · rw [if_pos he]
    ext u
    rw [coeff_filterLocalMonomials]
    by_cases hue : u = e
    · subst u
      simp [he, MvPolynomial.coeff_monomial]
    · simp [MvPolynomial.coeff_monomial, Ne.symm hue]
  · rw [if_neg he]
    ext u
    rw [coeff_filterLocalMonomials]
    by_cases hue : u = e
    · subst u
      simp [he]
    · simp [MvPolynomial.coeff_monomial, Ne.symm hue]

private theorem normalizeError_monomial (d : ℕ)
    (e : LocalVariable d →₀ ℕ) (c : R) :
    normalizeError d (MvPolynomial.monomial e c) =
      MvPolynomial.monomial (normalizeLocalExponent d e) c := by
  rw [normalizeError_eq_normalizeErrorByExponent, normalizeErrorByExponent,
    AddMonoidAlgebra.mapDomainAlgHom_apply]
  exact AddMonoidAlgebra.mapDomain_single

/-- Truncating the normalized remainder is the normalization of the old contact projection. -/
theorem truncateLocalT_normalizeError (m : ℕ) (F : LocalPolynomial R d) :
    truncateLocalT (R := R) (d := d) m (normalizeError d F) =
      normalizeError d (projectLowContact m F) := by
  classical
  rw [F.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [normalizeError_monomial]
  change filterLocalMonomials (fun u ↦ u (localT d) < m)
      (MvPolynomial.monomial (normalizeLocalExponent d e) (MvPolynomial.coeff e F)) =
    normalizeError d
      (filterLocalMonomials (fun u ↦ localContactOrder d u < m)
        (MvPolynomial.monomial e (MvPolynomial.coeff e F)))
  rw [filterLocalMonomials_monomial, filterLocalMonomials_monomial]
  by_cases he : localContactOrder d e < m
  · have ht : normalizeLocalExponent d e (localT d) < m := by
      rw [normalizeLocalExponent_T_eq_contact]
      exact he
    rw [if_pos he, normalizeError_monomial, if_pos ht]
  · have ht : ¬normalizeLocalExponent d e (localT d) < m := by
      rw [normalizeLocalExponent_T_eq_contact]
      exact he
    rw [if_neg he, map_zero, if_neg ht]

/-- Direct local remainder constraint with the free error occurring as `T^(d+1) V`, reduced
modulo `T^m`. -/
def normalizedLocalConstraintAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (truncateLocalT (R := R) (d := d) m).comp
    (normalizedLocalSubstitution d center received).toLinearMap

/-- The direct remainder map is the normalized image of the contact-coordinate map. -/
theorem normalizedLocalConstraintAt_eq_normalize_localConstraintAt
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    normalizedLocalConstraintAt m center received Q =
      normalizeError d (localConstraintAt m center received Q) := by
  change truncateLocalT m (normalizedLocalSubstitution d center received Q) =
    normalizeError d (projectLowContact m (unscaledLocalSubstitution d center received Q))
  rw [normalizedLocalSubstitution_eq_normalize_comp_unscaled]
  change truncateLocalT m
      (normalizeError d (unscaledLocalSubstitution d center received Q)) = _
  rw [truncateLocalT_normalizeError]

/-- The manuscript's direct backward-Taylor remainder constraints and the retained
contact-coordinate constraints have exactly the same kernel. -/
theorem normalizedLocalConstraintAt_eq_zero_iff
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    normalizedLocalConstraintAt m center received Q = 0 ↔
      SatisfiesLocalConstraints m center received Q := by
  rw [normalizedLocalConstraintAt_eq_normalize_localConstraintAt,
    SatisfiesLocalConstraints]
  constructor
  · intro h
    apply normalizeError_injective d
    simpa using h
  · intro h
    rw [h]
    simp

/-- Kernel equality underlying reuse of the retained contact-coordinate matrices. -/
theorem normalizedLocalConstraintAt_ker_eq_localConstraintAt
    (m : ℕ) (center received : R) :
    LinearMap.ker (normalizedLocalConstraintAt (d := d) m center received) =
      LinearMap.ker (localConstraintAt (d := d) m center received) := by
  ext Q
  rw [LinearMap.mem_ker, LinearMap.mem_ker, normalizedLocalConstraintAt_eq_zero_iff]
  rfl

/-- The direct remainder map also has exactly the kernel of the existing coefficient matrix. -/
theorem normalizedLocalConstraintAt_ker_eq_coordinates
    (m : ℕ) (center received : R) :
    LinearMap.ker (normalizedLocalConstraintAt (d := d) m center received) =
      LinearMap.ker (localConstraintCoordinatesAt (d := d) m center received) := by
  ext Q
  rw [LinearMap.mem_ker, LinearMap.mem_ker, normalizedLocalConstraintAt_eq_zero_iff,
    satisfiesLocalConstraints_iff_coordinates_eq_zero]

/-- A direct remainder constraint at an agreement gives the manuscript's local multiplicity
conclusion over every commutative coefficient ring. -/
theorem X_sub_C_pow_dvd_differentialSpecialization_of_normalizedLocalConstraint
    (Q : DifferentialPolynomial R d) (P : R[X]) (center received : R)
    (hP : P.eval center = received)
    (hQ : normalizedLocalConstraintAt m center received Q = 0) :
    (Polynomial.X - Polynomial.C center) ^ m ∣ differentialSpecialization Q P := by
  exact X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P center received hP
    ((normalizedLocalConstraintAt_eq_zero_iff m center received Q).mp hQ)

end ReedSolomon.HiddenDerivative

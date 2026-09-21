/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Kai Zhe Zheng
-/
module

public import ArkLib.Data.MvPolynomial.WeightedDegree
public import ArkLib.Data.Polynomial.Differential.Basic
public import ArkLib.ToMathlib.MvPolynomial.PDeriv

/-!
# Degree budgets for finite-jet polynomial relations

This file supplies the degree measures used by interpolation and differential root finding:

* `jetDegree` is the individual degree in one formal jet variable;
* `differentialWeightedDegree` controls specialization at a polynomial of bounded degree;
* `totalJetDegree` measures the jet part of one monomial exponent, while `jetTotalDegree` lifts
  that measure to a differential polynomial.

The distinguished variable `X` has weight one for specialization and weight zero for total jet
degree. A jet variable `Y_j` has specialization weight `D - j`, which may be zero. The
specialization bounds remain valid at that boundary, but a zero weight does not give a
finite-dimensional bounded-support space without a separate coordinate cap.

The core definitions and specialization bounds are ported from the differential and
specialization modules at ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
The total-jet-degree API is extracted from
`HiddenDerivative/RootFinding/Counting/TotalJetDegreeRootCount.lean` at the same revision.
Ordinary partial-derivative exactness remains governed by the explicit cast hypotheses in
`ArkLib.ToMathlib.MvPolynomial.PDeriv`; the characteristic-free bounds in this file do not assert
that a separant is nonzero.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d D : ℕ}

/-! ### Individual jet degree and separants -/

/-- The individual degree in the formal Hasse variable `Y_j`. -/
def jetDegree [CommSemiring F] (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) : ℕ :=
  Q.degreeOf (some j)

/-- Formal partial derivative of `Q` in the Hasse variable `Y_j`. -/
def separant [CommSemiring F] (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    DifferentialPolynomial F d :=
  MvPolynomial.pderiv (some j) Q

/-! ### Specialization-weighted degree -/

/-- Root-specialization weight: `X` has weight one and `Y_j` has weight `D - j`. -/
def differentialWeight (D : ℕ) : JetVariable d → ℕ
  | none => 1
  | some j => D - j

@[simp]
theorem differentialWeight_none (D : ℕ) : differentialWeight (d := d) D none = 1 :=
  rfl

@[simp]
theorem differentialWeight_some (D : ℕ) (j : Fin (d + 1)) :
    differentialWeight D (some j) = D - j :=
  rfl

/-- If the derivative order is below the ambient degree, every jet variable has positive
root-specialization weight. -/
theorem differentialWeight_some_pos_of_order_lt_degree {D : ℕ} (h : d < D)
    (j : Fin (d + 1)) : 0 < differentialWeight D (some j) := by
  simp only [differentialWeight_some]
  have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
  omega

/-- At the boundary `D = d`, the top Hasse variable has weight zero. -/
theorem differentialWeight_top_eq_zero (d : ℕ) :
    differentialWeight d (some (Fin.last d)) = 0 := by
  simp [differentialWeight]

/-- Weighted degree controlling the degree after differential specialization. -/
def differentialWeightedDegree [CommSemiring F] (D : ℕ) (Q : DifferentialPolynomial F d) :
    ℕ :=
  Q.weightedTotalDegree (differentialWeight D)

/-- An injective coefficient map preserves root-specialization weighted degree exactly. -/
theorem differentialWeightedDegree_map_eq [CommSemiring F] {E : Type*} [CommSemiring E] {D : ℕ}
    (f : F →+* E) (hf : Function.Injective f) (Q : DifferentialPolynomial F d) :
    differentialWeightedDegree D (MvPolynomial.map f Q) = differentialWeightedDegree D Q := by
  unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective Q hf]

/-- Every polynomial substituted for a differential variable has degree at most that variable's
root-specialization weight. -/
theorem natDegree_differentialVariable_le [CommSemiring F] (P : F[X])
    (hP : P.natDegree ≤ D) (v : JetVariable d) :
    (match v with
      | none => X
      | some j => hasseDeriv j P).natDegree ≤ differentialWeight D v := by
  cases v with
  | none => exact Polynomial.natDegree_X_le
  | some j =>
      exact (Polynomial.natDegree_hasseDeriv_le P j.val).trans
        (Nat.sub_le_sub_right hP j.val)

/-- Differential specialization cannot increase degree past the corresponding weighted total
degree. This includes the zero polynomial and zero-weight jet variables. -/
theorem natDegree_differentialSpecialization_le [CommSemiring F]
    (Q : DifferentialPolynomial F d) (P : F[X]) (hP : P.natDegree ≤ D) :
    (differentialSpecialization Q P).natDegree ≤ differentialWeightedDegree D Q := by
  rw [differentialSpecialization, differentialSpecializationHom,
    differentialWeightedDegree]
  exact MvPolynomial.natDegree_aeval_le_weightedTotalDegree_of_le
    (differentialWeight (d := d) D)
    (fun v : JetVariable d ↦ match v with
      | none => X
      | some j => hasseDeriv j P)
    Q (natDegree_differentialVariable_le P hP)

/-- The specialization of a separant saves the full `D - j` weight of its differentiated jet. -/
theorem natDegree_differentialSpecialization_separant_le_sub [CommSemiring F]
    (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) (P : F[X])
    (hP : P.natDegree ≤ D) :
    (differentialSpecialization (separant Q j) P).natDegree ≤
      differentialWeightedDegree D Q - (D - j.val) :=
  (natDegree_differentialSpecialization_le (separant Q j) P hP).trans
    (MvPolynomial.weightedTotalDegree_pderiv_le_sub
      (differentialWeight D) (some j) Q)

/-- Specializing a separant has degree at most the original differential polynomial's weighted
degree. -/
theorem natDegree_differentialSpecialization_separant_le [CommSemiring F]
    (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) (P : F[X])
    (hP : P.natDegree ≤ D) :
    (differentialSpecialization (separant Q j) P).natDegree ≤
      differentialWeightedDegree D Q :=
  (natDegree_differentialSpecialization_le (separant Q j) P hP).trans
    (MvPolynomial.weightedTotalDegree_pderiv_le
      (differentialWeight D) (some j) Q)

/-! ### Total degree in jet variables -/

/-- Weight zero on `X` and weight one on every formal jet variable. -/
def jetDegreeWeight : JetVariable d → ℕ
  | none => 0
  | some _ => 1

@[simp]
theorem jetDegreeWeight_none : jetDegreeWeight (d := d) none = 0 :=
  rfl

@[simp]
theorem jetDegreeWeight_some (j : Fin (d + 1)) : jetDegreeWeight (some j) = 1 :=
  rfl

/-- Total jet degree of a monomial exponent; the distinguished `X` exponent is ignored. -/
def totalJetDegree (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight jetDegreeWeight u

/-- The total jet degree is the sum of the exponents of `Y₀, ..., Y_d`. -/
theorem totalJetDegree_eq_sum (u : JetVariable d →₀ ℕ) :
    totalJetDegree u = ∑ j : Fin (d + 1), u (some j) := by
  classical
  simp [totalJetDegree, jetDegreeWeight, Finsupp.weight_apply, Finsupp.sum_fintype,
    Fintype.sum_option]

/-- The weight formulation agrees with the exponent-level definition used by interpolation. -/
theorem totalJetDegree_eq_degree_some (u : JetVariable d →₀ ℕ) :
    totalJetDegree u = Finsupp.degree u.some := by
  classical
  simp [totalJetDegree, jetDegreeWeight, Finsupp.weight_eq_sum,
    Finsupp.degree_eq_sum, Fintype.sum_option]

/-- Total degree in jet variables only; the distinguished `X` variable has weight zero. -/
def jetTotalDegree [CommSemiring F] (Q : DifferentialPolynomial F d) : ℕ :=
  Q.weightedTotalDegree jetDegreeWeight

/-- Support-wise characterization of total jet degree. -/
theorem jetTotalDegree_le_iff [CommSemiring F] (Q : DifferentialPolynomial F d) (Δ : ℕ) :
    jetTotalDegree Q ≤ Δ ↔ ∀ u ∈ Q.support, totalJetDegree u ≤ Δ := by
  classical
  unfold jetTotalDegree MvPolynomial.weightedTotalDegree totalJetDegree
  simp [Finset.sup_le_iff]

/-- Every individual jet degree is bounded by total jet degree. -/
theorem jetDegree_le_total [CommSemiring F] (Q : DifferentialPolynomial F d)
    (j : Fin (d + 1)) : jetDegree Q j ≤ jetTotalDegree Q := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro u hu
  have htotal := (jetTotalDegree_le_iff Q _).mp le_rfl u hu
  rw [totalJetDegree_eq_sum] at htotal
  exact (Finset.single_le_sum (fun k _ ↦ Nat.zero_le (u (some k)))
    (Finset.mem_univ j)).trans htotal

/-- Every formal separant lowers total jet degree by at least one. -/
theorem separant_total_le [CommSemiring F] (Q : DifferentialPolynomial F d)
    (j : Fin (d + 1)) :
    jetTotalDegree (separant Q j) ≤ jetTotalDegree Q - 1 :=
  MvPolynomial.weightedTotalDegree_pderiv_le_sub jetDegreeWeight (some j) Q

end

end PolynomialDifferential

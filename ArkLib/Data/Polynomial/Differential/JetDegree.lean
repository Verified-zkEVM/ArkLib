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

Ordinary partial-derivative exactness remains governed by the explicit cast hypotheses in
`ArkLib.ToMathlib.MvPolynomial.PDeriv`; the characteristic-free bounds in this file do not assert
that a separant is nonzero.

The initial equation `initialJetEquation center Q` is the specialization of `Q` at `X = center`,
viewed as a polynomial in the initial jet coordinates. Its coefficient maps, evaluation, total
degree, and all-coordinate partial-derivative law are developed here so both chain witnesses and
Taylor charts use the same specialization.

## Main statements

* `initialJetEquation`, `map_initialJetEquation`, `aeval_initialJetEquation`,
  `aeval_map_initialJetEquation`, `totalDegree_initialJetEquation_le`, and
  `pderiv_initialJetEquation`: the shared initial equation and its basic laws.
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

/-- The distinguished variable `X` has specialization weight one. -/
@[simp]
theorem differentialWeight_none (D : ℕ) : differentialWeight (d := d) D none = 1 :=
  rfl

/-- The jet variable `Y_j` has specialization weight `D - j`. -/
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

/-- The distinguished variable `X` has jet-degree weight zero. -/
@[simp]
theorem jetDegreeWeight_none : jetDegreeWeight (d := d) none = 0 :=
  rfl

/-- Every jet variable `Y_j` has jet-degree weight one. -/
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

section CommSemiring

variable {R : Type*} [CommSemiring R] {r : ℕ}

open MvPolynomial

/-- The differential polynomial `Q` with the independent variable set to `center`, as a
polynomial in the initial jet coordinates `Y_0, ..., Y_r`. -/
def initialJetEquation (center : R) (Q : DifferentialPolynomial R r) :
    MvPolynomial (Fin (r + 1)) R :=
  MvPolynomial.aeval (fun i ↦ i.elim (C center) X) Q

/-- Mapping coefficients sends the initial equation to the initial equation of the mapped
differential polynomial. -/
theorem map_initialJetEquation {S : Type*} [CommSemiring S] (f : R →+* S) (center : R)
    (Q : DifferentialPolynomial R r) :
    map f (initialJetEquation center Q) = initialJetEquation (f center) (map f Q) := by
  simp only [initialJetEquation, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq,
    MvPolynomial.map_eval₂]
  congr 1
  funext i
  cases i <;> simp

/-- Evaluating the initial equation at a jet is `jetEvaluation` of `Q` at `center`. -/
theorem aeval_initialJetEquation (center : R) (Q : DifferentialPolynomial R r)
    (jet : Fin (r + 1) → R) :
    MvPolynomial.aeval jet (initialJetEquation center Q) = jetEvaluation Q center jet := by
  have he : (MvPolynomial.aeval jet).comp
      (MvPolynomial.aeval (fun i : Option (Fin (r + 1)) ↦ i.elim (C center) X)) =
      MvPolynomial.aeval (fun i ↦ match i with
        | none => center | some j => jet j) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun he Q

/-- Evaluating the mapped initial equation agrees with evaluating the mapped differential
polynomial at the mapped center. -/
theorem aeval_map_initialJetEquation {S : Type*} [CommSemiring S] (f : R →+* S)
    (center : R) (Q : DifferentialPolynomial R r) (jet : Fin (r + 1) → S) :
    MvPolynomial.aeval jet (map f (initialJetEquation center Q)) =
      jetEvaluation (map f Q) (f center) jet := by
  rw [map_initialJetEquation]
  exact aeval_initialJetEquation (f center) (map f Q) jet

/-- Setting the independent variable to a constant does not increase the total jet degree. -/
theorem totalDegree_initialJetEquation_le (center : R) (Q : DifferentialPolynomial R r) :
    (initialJetEquation center Q).totalDegree ≤ jetTotalDegree Q := by
  rw [← weightedTotalDegree_one]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none => simp
  | some j =>
    simp only [Option.elim_some, weightedTotalDegree_one]
    exact (totalDegree_monomial_le _ _).trans (by simp)

/-- Taking a partial derivative of the initial equation in `Y_j` gives the initial equation of
the separant in `Y_j`. -/
theorem pderiv_initialJetEquation (center : R) (Q : DifferentialPolynomial R r)
    (j : Fin (r + 1)) :
    pderiv j (initialJetEquation center Q) = initialJetEquation center (separant Q j) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [initialJetEquation, separant]
  | add P Q hP hQ => simpa [initialJetEquation, separant] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [initialJetEquation, separant] at hP
    cases i with
    | none =>
      simp only [aeval_eq_bind₁] at hP
      simp [initialJetEquation, separant, hP]
    | some i =>
      simp only [initialJetEquation, separant, map_mul, MvPolynomial.aeval_X,
        pderiv_mul, pderiv_X, map_add]
      rw [hP]
      by_cases hi : i = j
      · subst i
        simp
      · simp [hi]

end CommSemiring

end

end PolynomialDifferential

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.BaseChange
import ArkLib.Data.Polynomial.Differential.ChainWitness
import ArkLib.Data.Polynomial.Differential.DerivativeDescent
import ArkLib.Data.Polynomial.Differential.DirectRegularLift
import ArkLib.Data.Polynomial.Differential.FirstOrderStageSum
import ArkLib.Data.Polynomial.Differential.JetPrefix
import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation
import ArkLib.Data.Polynomial.Differential.RationalTaylor
import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
import ArkLib.Data.Polynomial.Differential.RecursiveCount
import ArkLib.Data.Polynomial.Differential.RegularIteration
import ArkLib.Data.Polynomial.Differential.RegularJetCount
import ArkLib.Data.Polynomial.Differential.RegularLift
import ArkLib.Data.Polynomial.Differential.SeparantChain
import ArkLib.Data.Polynomial.Differential.ShiftedJet
import ArkLib.Data.Polynomial.Differential.SingularRecursion
import ArkLib.Data.Polynomial.Differential.TaylorChart
import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
import ArkLib.Data.Polynomial.Differential.TaylorIndexWeight
import ArkLib.Data.Polynomial.Differential.TaylorResidual
import ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount
import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for polynomial differential modules

Concrete instances check coefficient transport, derivative descent, regular lifting and Taylor
reconstruction, alongside representative finite-field counting bounds.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial Finset

/-! ### Coefficient maps -/

/-- The map `ℚ → ℚ` preserves the jet degree of `Y₀ ^ 2`. -/
example :
    jetDegree (MvPolynomial.map (RingHom.id ℚ)
      (X (some 0) ^ 2 : DifferentialPolynomial ℚ 0)) 0 = 2 := by
  rw [jetDegree_map_eq (RingHom.id ℚ).injective]
  simp [jetDegree]

/-! ### A concrete chain witness -/

private abbrev linearEquation0 : DifferentialPolynomial ℚ 0 := X (some 0)

private theorem highestActiveJet_linearEquation0 : highestActiveJet linearEquation0 = some 0 := by
  cases h : highestActiveJet linearEquation0 with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, linearEquation0, jetDegree] at this
  | some j =>
      fin_cases j
      rfl

/-- The zero polynomial gives a regular chain witness for `Y₀ = 0` at the origin. -/
example : ChainWitness linearEquation0 0 0 := by
  refine .regular highestActiveJet_linearEquation0 ?_ ?_
  · simp [linearEquation0, differentialSpecialization, differentialSpecializationHom]
  · simp [linearEquation0, separant, jetEvaluation, pderiv_X]

/-! ### Derivative descent -/

/-- `Y₁ ^ 2 * Y₀` in depth `1`. -/
private abbrev cubicEquation : DifferentialPolynomial ℚ 1 :=
  X (some 1) ^ 2 * X (some 0)

private theorem cubicEquation_eq_monomial :
    cubicEquation = monomial (Finsupp.single (some 1) 2 + Finsupp.single (some 0) 1) 1 := by
  rw [cubicEquation, X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]

private theorem jetDegree_cubicEquation (j : Fin 2) :
    jetDegree cubicEquation j = if j = 1 then 2 else 1 := by
  classical
  rw [jetDegree, cubicEquation_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero]
  fin_cases j <;> simp

/-- The full descent of `Y₁ ^ 2 * Y₀` in `Y₁` is `2 * Y₀`. -/
example : derivativeDescent cubicEquation 1 = 2 * X (some 0) := by
  rw [derivativeDescent, jetDegree_cubicEquation]
  simp [jetDerivative, sq, pderiv_X]
  ring

/-! ### Direct regular iteration -/

/-- The equation `y' = y`, as the differential polynomial `Y₁ - Y₀`. -/
private abbrev expEquation : DifferentialPolynomial ℚ 1 :=
  X (some 1) - X (some 0)

private theorem differentialSpecialization_expEquation (P : Polynomial ℚ) :
    differentialSpecialization expEquation P = Polynomial.derivative P - P := by
  simp [expEquation, differentialSpecialization, differentialSpecializationHom,
    Polynomial.hasseDeriv_one]

private theorem slope_expEquation (k : ℕ) (P : Polynomial ℚ) :
    ((k + 1).choose 1 : ℚ) * jetEvaluation (separant expEquation (Fin.last 1)) 0
      (polynomialJet 0 P) = k + 1 := by
  simp [separant, jetEvaluation, expEquation, pderiv_X, Fin.last]

/-- One direct step for `y' = y` from `1 + X` adds `X ^ 2 / 2`. -/
example : regularIterate expEquation 0 (1 + Polynomial.X) 1 =
    1 + Polynomial.X + Polynomial.C (1 / 2) * Polynomial.X ^ 2 := by
  have hres : (shiftedJetSubstitution 0 (1 + Polynomial.X) expEquation).coeff 1 = -1 := by
    rw [← taylor_differentialSpecialization, differentialSpecialization_expEquation]
    simp
  rw [regularIterate_succ, regularIterate_zero, regularLift, regularLiftCoefficient,
    slope_expEquation, hres, Polynomial.hassePerturbation, Ring.inverse_eq_inv]
  norm_num

/-! ### Highest active jet -/

/-- `Y₁ * X` in depth `2`. -/
private abbrev productEquation : DifferentialPolynomial ℚ 2 :=
  X (some 1) * X none

private theorem jetDegree_productEquation (j : Fin 3) :
    jetDegree productEquation j = if j = 1 then 1 else 0 := by
  classical
  rw [jetDegree, degreeOf_mul_X_of_ne _ (Option.some_ne_none j), degreeOf_X]
  simp

/-- The computed highest active jet of `Y₁ * X` is `Y₁`. -/
example : highestActiveJet productEquation = some 1 := by
  have hactive : activeJets productEquation = {1} := by
    ext j
    by_cases h : j = 1 <;> simp [DependsOnJet, jetDegree_productEquation, h]
  have hne : (activeJets productEquation).Nonempty := by simp [hactive]
  rw [highestActiveJet_eq_some_max _ hne]
  simp [hactive]

/-! ### Rational Taylor coefficients -/

/-- The equation `y' = 2x`, as the differential polynomial `Y₁ - 2X`. -/
private abbrev taylorLinearEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1) - 2 * X none

/-- `X ^ 2` solves `y' = 2x` over every commutative ring. -/
private theorem differentialSpecialization_taylorLinearEquation {F : Type*} [CommRing F] :
    differentialSpecialization (taylorLinearEquation F) (Polynomial.X ^ 2) = 0 := by
  simp [taylorLinearEquation, differentialSpecialization, differentialSpecializationHom,
    Polynomial.hasseDeriv_one, one_add_one_eq_two, Polynomial.C_ofNat]

/-- The separant of `Y₁ - 2X` is `1`. -/
private theorem jetEvaluation_separant_taylorLinearEquation {F : Type*} [CommRing F]
    [Nontrivial F] (jet : Fin 2 → F) :
    jetEvaluation (separant (taylorLinearEquation F) (Fin.last 1)) 0 jet = 1 := by
  simp [separant, jetEvaluation, taylorLinearEquation, pderiv_X, Fin.last]

private theorem choose_one_ne_zero (i : ℕ) (hi : 1 < i) : (i.choose 1 : ℚ) ≠ 0 := by
  rw [Nat.choose_one_right]
  exact_mod_cast (by omega : i ≠ 0)

/-- Over `ℚ`, the rational coefficient of `x ^ 2` from the jet of `X ^ 2` is `1`. -/
example : rationalTaylorCoefficient 0 (taylorLinearEquation ℚ)
    (polynomialJet 0 (Polynomial.X ^ 2)) 2 = 1 := by
  rw [rationalTaylorCoefficient_eq_solution 0 (taylorLinearEquation ℚ) (Polynomial.X ^ 2)
    (differentialSpecialization_taylorLinearEquation)
    (by rw [jetEvaluation_separant_taylorLinearEquation]; norm_num) 2
    (fun i hi hi2 ↦ by
      obtain rfl : i = 2 := by omega
      exact choose_one_ne_zero 2 (by omega))]
  simp [Polynomial.coeff_X_pow]

/-! ### Numerators over an algebra -/

/-- The equation `y' = t y`, as `Y₁ - t Y₀` over `ℚ[t]`. -/
private abbrev scaledExpEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some 1) - C Polynomial.X * X (some 0)

/-- The numerator of `y' = t y` specializes at `t = 0` to that of `y' = 0`. -/
example :
    map (Polynomial.aeval (0 : ℚ)).toRingHom
        (rationalTaylorNumeratorOver ℚ 0 scaledExpEquation 2) =
      rationalTaylorNumerator 0 (X (some 1) : DifferentialPolynomial ℚ 1) 2 := by
  rw [map_rationalTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]
  simp [scaledExpEquation]

/-! ### Regular-jet count -/

/-- In the box containing only the zero jet, `Y₀ = 0` has one regular jet over `ZMod 3`. -/
example :
    #{jet ∈ Fintype.piFinset (fun _ : Fin 1 ↦ ({0} : Finset (ZMod 3))) |
      IsRegularJet (X (some 0) : DifferentialPolynomial (ZMod 3) 0) 0 0 jet} ≤ 1 := by
  have h := card_filter_isRegularJet_le
    (X (some 0) : DifferentialPolynomial (ZMod 3) 0) 0 0 ({0} : Finset (ZMod 3))
  simpa [jetDegree] using h

/-! ### Separant chains and regular recursion -/

/-- A separant chain exists for `Y₀ ^ 2` over `ℚ`. -/
example : ∃ stages terminal,
    SeparantChain (X (some 0) ^ 2 : DifferentialPolynomial ℚ 0) stages terminal :=
  exists_separantChain_of_ringChar (by simp)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

private abbrev squareEquation : DifferentialPolynomial ℚ 0 := X (some 0) ^ 2

private theorem differentialSpecialization_squareEquation_zero :
    differentialSpecialization squareEquation 0 = 0 := by
  rw [← differentialSpecializationHom_apply, map_pow, differentialSpecializationHom_apply,
    differentialSpecialization_jet, map_zero, zero_pow two_ne_zero]

/-- The solution `0` of `Y₀ ^ 2 = 0` reaches a regular recursion leaf over `ℚ`. -/
example : Nonempty (RegularRecursionLeaf squareEquation 0) :=
  exists_regularRecursionLeaf (by simp [squareEquation])
    (fun _ ↦ jetDegreeCastsNeZero_of_ringChar (Or.inl ringChar.eq_zero))
    differentialSpecialization_squareEquation_zero

/-! ### Taylor reconstruction -/

private theorem degree_X_sq_lt_three : (Polynomial.X ^ 2 : Polynomial ℚ).degree < 3 := by
  rw [Polynomial.degree_X_pow]
  exact_mod_cast (by norm_num : 2 < 3)

/-- The rational Taylor reconstruction of the solution `X ^ 2` to `y' = 2x` is `X ^ 2`. -/
example : rationalTaylorPolynomial 0 (taylorLinearEquation ℚ) 3
    (polynomialJet 0 (Polynomial.X ^ 2)) = Polynomial.X ^ 2 :=
  rationalTaylorPolynomial_polynomialJet 0 _ _ differentialSpecialization_taylorLinearEquation
    (by rw [jetEvaluation_separant_taylorLinearEquation]; norm_num) degree_X_sq_lt_three
    (fun i hi _ ↦ choose_one_ne_zero i hi)

/-! ### Index weight -/

/-- The first-order equation `Q = Y₁`. -/
private abbrev firstJet : DifferentialPolynomial ℚ 1 := X (some 1)

private theorem weightedTotalDegree_firstJet :
    firstJet.weightedTotalDegree (indexWeight 2) = 1 := by
  rw [weightedTotalDegree_indexWeight_eq_jetDegree_one, jetDegree, degreeOf_X_self]

private theorem firstJet_residual_coeff_one :
    (optionEquivLeft ℚ (Fin 3) (universalTaylorResidual 3 0 firstJet)).coeff 1 =
      C 2 * X 2 := by
  have hres : universalTaylorResidual 3 (0 : ℚ) firstJet = universalTaylorJet 3 1 := by
    simp [universalTaylorResidual, firstJet]
  rw [hres, optionEquivLeft_universalTaylorJet, Polynomial.hasseDeriv_coeff]
  simp [Fin.sum_univ_three, Polynomial.coeff_monomial]
  rfl

/-- The index-weight bound is attained by `c₂` in the coefficient of `ξ` for `Y₁`. -/
example :
    Finsupp.single (2 : Fin 3) 1 ∈
        ((optionEquivLeft ℚ (Fin 3) (universalTaylorResidual 3 0 firstJet)).coeff 1).support ∧
      Finsupp.weight Fin.val (Finsupp.single (2 : Fin 3) 1) =
        1 + firstJet.weightedTotalDegree (indexWeight 2) := by
  refine ⟨?_, by simp [Finsupp.weight_single, weightedTotalDegree_firstJet]⟩
  rw [firstJet_residual_coeff_one, mem_support_iff, X, C_mul_monomial, coeff_monomial]
  norm_num

/-! ### Total-jet-degree count -/

/-- The equation `y' = 0` over `F`. -/
private abbrev constantDerivativeEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1)

private theorem jetTotalDegree_constantDerivativeEquation_le {F : Type*} [CommRing F]
    [Nontrivial F] : jetTotalDegree (constantDerivativeEquation F) ≤ 1 := by
  refine (jetTotalDegree_le_iff _ 1).mpr fun u hu ↦ ?_
  rw [MvPolynomial.support_X, mem_singleton] at hu
  rw [hu]
  simp [totalJetDegree_eq_sum, Fin.sum_univ_two]

private theorem differentialWeightedDegree_constantDerivativeEquation {F : Type*} [CommRing F]
    [Nontrivial F] : differentialWeightedDegree 2 (constantDerivativeEquation F) = 1 := by
  unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_X]
  simp [Finsupp.weight_apply]

private theorem castsNeZero_constantDerivativeEquation {F : Type*} [CommRing F] [Nontrivial F]
    (j : Fin 2) : JetDegreeCastsNeZero (constantDerivativeEquation F) j := by
  intro k hk hkj
  have hdeg : jetDegree (constantDerivativeEquation F) j ≤ 1 :=
    (jetDegree_le_total _ j).trans jetTotalDegree_constantDerivativeEquation_le
  obtain rfl : k = 1 := by omega
  simp

/-- Over `ZMod 3`, `y' = 0` has at most three solutions of degree at most `2`. -/
example : Nat.card (BoundedSolution (constantDerivativeEquation (ZMod 3)) 2) ≤ 3 := by
  have h : Nat.card (BoundedSolution (constantDerivativeEquation (ZMod 3)) 2) *
      (Nat.card (ZMod 3) - 0) ≤ Nat.card (ZMod 3) *
        (jetTotalDegree (constantDerivativeEquation (ZMod 3)) * Nat.card (ZMod 3) ^ 1) :=
    BoundedSolution.natCard_mul_sub_le_jetTotalDegree_mul (MvPolynomial.X_ne_zero _)
      castsNeZero_constantDerivativeEquation (H := 0)
      (fun k s ↦ natCast_choose_ne_zero_of_ringChar (F := ZMod 3) (D := 2) (s := s)
        (Or.inr (by rw [ZMod.ringChar_zmod_n]; decide)) k)
      (by rw [differentialWeightedDegree_constantDerivativeEquation])
  rw [Nat.card_zmod, Nat.sub_zero] at h
  have htotal := jetTotalDegree_constantDerivativeEquation_le (F := ZMod 3)
  have hbound : 3 * (jetTotalDegree (constantDerivativeEquation (ZMod 3)) * 3 ^ 1) ≤ 3 * 3 := by
    rw [pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

end

end PolynomialDifferential

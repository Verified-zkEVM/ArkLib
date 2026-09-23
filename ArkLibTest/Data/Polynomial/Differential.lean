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
import Mathlib.FieldTheory.Finite.Extension
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

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2

/-- The injective map from `ZMod 2` to its degree-two extension preserves the jet degree of
`Y₀ ^ 2`. -/
example :
    jetDegree (MvPolynomial.map (algebraMap (ZMod 2) E₄)
      (X (some 0) ^ 2 : DifferentialPolynomial (ZMod 2) 0)) 0 = 2 := by
  rw [jetDegree_map_eq (algebraMap (ZMod 2) E₄).injective]
  simp [jetDegree]

/-- Differential specialization commutes with the coefficient extension `ZMod 2 → E₄` on
`Q = X + Y₀` at `P = X + 1`; both sides evaluate to `1`. -/
example :
    let f := algebraMap (ZMod 2) E₄
    let Q : DifferentialPolynomial (ZMod 2) 0 :=
      MvPolynomial.X none + MvPolynomial.X (some 0)
    let P : Polynomial (ZMod 2) := Polynomial.X + 1
    (differentialSpecialization Q P).map f = 1 ∧
      (differentialSpecialization Q P).map f =
        differentialSpecialization (MvPolynomial.map f Q) (P.map f) := by
  intro f Q P
  refine ⟨?_, map_differentialSpecialization f Q P⟩
  have h2 : (Polynomial.X + (Polynomial.X + 1) : Polynomial (ZMod 2)) = 1 := by
    rw [← add_assoc, ← two_mul,
      show (2 : Polynomial (ZMod 2)) = Polynomial.C 2 from rfl,
      show (2 : ZMod 2) = 0 by decide, Polynomial.C_0, zero_mul, zero_add]
  simp [Q, P, differentialSpecialization, differentialSpecializationHom, h2]

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

/-! ### First-order chain charge -/

private abbrev orderZeroEquation : DifferentialPolynomial ℚ 1 := X (some 0)

private theorem jetDegree_orderZeroEquation (j : Fin 2) :
    jetDegree orderZeroEquation j = if j = 0 then 1 else 0 := by
  classical
  rw [jetDegree, degreeOf_X]
  simp

private theorem jetTotalDegree_orderZeroEquation : jetTotalDegree orderZeroEquation = 1 := by
  change MvPolynomial.weightedTotalDegree jetDegreeWeight
    (monomial (Finsupp.single (some (0 : Fin 2)) 1) (1 : ℚ)) = 1
  rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero]
  simp [Finsupp.weight_apply, jetDegreeWeight]

private theorem highestActiveJet_orderZeroEquation :
    highestActiveJet orderZeroEquation = some 0 := by
  cases h : highestActiveJet orderZeroEquation with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, orderZeroEquation, jetDegree] at this
  | some j =>
      have hj := (isHighestActiveJet_of_highestActiveJet_eq_some h).1
      fin_cases j
      · rfl
      · simp [DependsOnJet, jetDegree_orderZeroEquation] at hj

private theorem orderZeroChain :
    SeparantChain orderZeroEquation [(orderZeroEquation, 0)] (C 1) := by
  refine .active 0 (X_ne_zero _) highestActiveJet_orderZeroEquation ?_
  have hsep : separant orderZeroEquation 0 = C 1 := by simp [separant, pderiv_X]
  rw [hsep]
  refine .terminal (by simp) ((highestActiveJet_eq_none_iff _).mpr fun j hj ↦ ?_)
  simp [DependsOnJet, jetDegree] at hj

/-- The bound is attained by the one-stage chain `Y₀` with charges `c₀ j = j` and
`c₁ j r = j + r`. -/
example :
    ([(orderZeroEquation, (0 : Fin 2))].map
      (firstOrderStageCharge (fun j ↦ (j : ℚ)) fun j r ↦ (j + r : ℚ))).sum ≤
        firstOrderStageCap (fun j ↦ (j : ℚ)) (fun j r ↦ (j + r : ℚ)) 1 0 :=
  orderZeroChain.sum_firstOrderStageCharge_le jetTotalDegree_orderZeroEquation.le
    (by simp [jetDegree_orderZeroEquation]) (fun j ↦ by positivity)
    (fun j r ↦ by positivity) (fun _ _ h ↦ by exact_mod_cast h)
    (fun _ h ↦ by simp only [add_le_add_iff_right]; exact_mod_cast h)
    (fun h _ ↦ by simp only [add_le_add_iff_left]; exact_mod_cast h) (fun j ↦ by simp)

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

/-- The residual coefficients of `1 + X` and `1 + X + X ^ 2` for `y' = y` differ by `2`. -/
example : (shiftedJetSubstitution 0 (1 + Polynomial.X + Polynomial.X ^ 2) expEquation).coeff 1 -
    (shiftedJetSubstitution 0 (1 + Polynomial.X) expEquation).coeff 1 = 2 := by
  rw [coeff_shiftedJetSubstitution_sub_eq_of_taylor_coeff_eq (k := 1) one_pos expEquation 0
    (fun i hi ↦ by
      have hi' : i = 0 ∨ i = 1 := by omega
      rcases hi' with rfl | rfl <;> simp [Polynomial.coeff_X, Polynomial.coeff_one])]
  simp [separant, jetEvaluation, expEquation, pderiv_X, Fin.last,
    Polynomial.coeff_X, Polynomial.coeff_one]

/-- The unique coefficient lifting `1 + X` for `y' = y` to residual order `2` is `1 / 2`. -/
example (γ : ℚ) :
    Polynomial.X ^ 2 ∣ shiftedJetSubstitution 0
      (1 + Polynomial.X + Polynomial.hassePerturbation 0 γ 2) expEquation ↔ γ = 1 / 2 := by
  have hres : Polynomial.X ∣ shiftedJetSubstitution 0 (1 + Polynomial.X) expEquation := by
    rw [← taylor_differentialSpecialization, differentialSpecialization_expEquation]
    simp
  have hslope : IsUnit ((2 : ℚ) * jetEvaluation (separant expEquation (Fin.last 1)) 0
      (polynomialJet 0 (1 + Polynomial.X))) := by
    norm_num [separant, jetEvaluation, expEquation, pderiv_X, Fin.last]
  have hres : Polynomial.X ^ 1 ∣ shiftedJetSubstitution 0 (1 + Polynomial.X) expEquation := by
    rw [pow_one]
    exact hres
  have hlift := existsUnique_regularLiftCoefficient (k := 1) one_pos expEquation 0
    (1 + Polynomial.X) hres hslope
  have hhalf : Polynomial.X ^ 2 ∣ shiftedJetSubstitution 0
      (1 + Polynomial.X + Polynomial.hassePerturbation 0 (1 / 2) 2) expEquation := by
    rw [← taylor_differentialSpecialization, differentialSpecialization_expEquation]
    refine ⟨-Polynomial.C (1 / 2), ?_⟩
    simp only [Polynomial.hassePerturbation, map_zero, sub_zero, Polynomial.derivative_add,
      Polynomial.derivative_one, Polynomial.derivative_X, Polynomial.derivative_C_mul_X_pow]
    norm_num
  exact ⟨fun h ↦ hlift.unique h hhalf, fun h ↦ h ▸ hhalf⟩

private abbrev constEquation₂ : DifferentialPolynomial ℚ 2 := X (some 1)

private theorem isHighestActiveJet_constEquation₂ : IsHighestActiveJet constEquation₂ 1 := by
  classical
  refine ⟨by simp [DependsOnJet, constEquation₂, jetDegree], fun j hj ↦ ?_⟩
  simp [DependsOnJet, constEquation₂, jetDegree, degreeOf_X, hj.ne']

/-- For `y' = 0` stored at depth `2`, the unique lift at `Y₁` is `γ = 0`. -/
example (γ : ℚ) :
    (Polynomial.X - Polynomial.C 0) ^ 2 ∣ differentialSpecialization constEquation₂
      (1 + Polynomial.hassePerturbation 0 γ 2) ↔ γ = 0 := by
  have hlift := existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet (k := 1)
    one_pos constEquation₂ isHighestActiveJet_constEquation₂ 0 1
    (by simp [differentialSpecialization, differentialSpecializationHom])
    (by simp [separant, jetEvaluation, constEquation₂, pderiv_X])
  have hzero : (Polynomial.X - Polynomial.C 0) ^ 2 ∣ differentialSpecialization
      constEquation₂ (1 + Polynomial.hassePerturbation 0 (0 : ℚ) 2) := by
    rw [Polynomial.hassePerturbation, map_zero, zero_mul, add_zero]
    simp [differentialSpecialization, differentialSpecializationHom]
  constructor
  · exact fun h ↦ hlift.unique h hzero
  · rintro rfl
    exact hzero

/-! ### Highest active jet -/

/-- `Y₁ * X` in depth `2`. -/
private abbrev productEquation : DifferentialPolynomial ℚ 2 :=
  X (some 1) * X none

private theorem jetDegree_productEquation (j : Fin 3) :
    jetDegree productEquation j = if j = 1 then 1 else 0 := by
  classical
  rw [jetDegree, degreeOf_mul_X_of_ne _ (Option.some_ne_none j), degreeOf_X]
  simp

private theorem highestActiveJet_productEquation : highestActiveJet productEquation = some 1 := by
  have hactive : activeJets productEquation = {1} := by
    ext j
    by_cases h : j = 1 <;> simp [DependsOnJet, jetDegree_productEquation, h]
  have hne : (activeJets productEquation).Nonempty := by simp [hactive]
  rw [highestActiveJet_eq_some_max _ hne]
  simp [hactive]

/-- The computed highest active jet of `Y₁ * X` is `Y₁`. -/
example : highestActiveJet productEquation = some 1 := highestActiveJet_productEquation

/-- The equation `Y₁ * X` in depth `2` has a prefix presentation at its highest active jet. -/
example : ∃ Q' : DifferentialPolynomial ℚ 1,
    rename (jetPrefixEmbedding (1 : Fin 3)) Q' = productEquation :=
  exists_prefixDifferentialPolynomial productEquation
    (isHighestActiveJet_of_highestActiveJet_eq_some highestActiveJet_productEquation)

/-- The presentation of `Y₁ * X` at depth `1` exists. -/
example : Nonempty (JetPrefixPresentation productEquation 1) :=
  nonempty_jetPrefixPresentation _
    (isHighestActiveJet_of_highestActiveJet_eq_some highestActiveJet_productEquation)

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

/-! ### Joint-degree numerator bound -/

private theorem jetTotalDegree_one_le :
    jetTotalDegree (1 : DifferentialPolynomial (Polynomial ℚ) 1) = 0 := by
  simpa using (jetTotalDegree_le_iff (1 : DifferentialPolynomial (Polynomial ℚ) 1) 0).mpr
    (by simp [totalJetDegree])

private theorem coeffNatDegreeLE_one :
    CoeffNatDegreeLE (1 : DifferentialPolynomial (Polynomial ℚ) 1) 0 := by
  simpa using coeffNatDegreeLE_C (σ := JetVariable 1) (p := (1 : Polynomial ℚ)) (by simp)

/-- The constant equation `1` has rational Taylor numerator of joint degree at most `1` at
index `2`. -/
example :
    jointTotalDegree
      (rationalTaylorNumeratorOver ℚ (Polynomial.C 0)
        (1 : DifferentialPolynomial (Polynomial ℚ) 1) 2) ≤ 1 := by
  simpa using jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE 0
    (1 : DifferentialPolynomial (Polynomial ℚ) 1) 0 0 jetTotalDegree_one_le.le coeffNatDegreeLE_one
      2

/-! ### Shifted jets -/

private abbrev shiftedEquation : DifferentialPolynomial ℚ 1 :=
  X (some 0) - X none * X (some 1)

/-- At center `0`, the shifted residual of `Y₀ - X Y₁` on `X ^ 2` is `-X ^ 2`. -/
example : shiftedJetSubstitution 0 (Polynomial.X ^ 2) shiftedEquation =
    -(Polynomial.X ^ 2) := by
  change shiftedJetSubstitution 0 (Polynomial.X ^ 2)
      (MvPolynomial.X (some 0) - MvPolynomial.X none * MvPolynomial.X (some 1)) = _
  rw [map_sub, map_mul, shiftedJetSubstitution_Y_zero, shiftedJetSubstitution_X,
    shiftedJetSubstitution_Y]
  simp
  ring

/-! ### Regular-jet count -/

private abbrev squareEquation3 : DifferentialPolynomial (ZMod 3) 0 := X (some 0) ^ 2 - 1

private theorem jetDegree_squareEquation3_le : jetDegree squareEquation3 0 ≤ 2 := by
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · exact (degreeOf_pow_le _ _ _).trans (by simp)
  · rw [← C_1, degreeOf_C]
    exact Nat.zero_le _

private theorem isRegularJet_squareEquation3 (c : ZMod 3) (hc : c ^ 2 = 1) (hc0 : c ≠ 0) :
    IsRegularJet squareEquation3 0 0 ![c] := by
  refine ⟨?_, ?_⟩
  · simp [jetEvaluation_eq_eval, hc]
  · simp only [separant, jetEvaluation_eq_eval, squareEquation3, map_sub,
      Derivation.leibniz_pow, pderiv_X_self, Derivation.map_one_eq_zero, sub_zero, smul_eq_mul,
      mul_one, nsmul_eq_mul, map_mul, map_natCast, eval_X, jetAssignment_some,
      Matrix.cons_val_fin_one, Nat.reduceSub, pow_one]
    exact mul_ne_zero (by decide) hc0

/-- `Y₀ ^ 2 - 1 = 0` over `ZMod 3` has exactly two regular jets at `0`, attaining the degree
bound. -/
example :
    #{jet ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (univ : Finset (ZMod 3))) |
      IsRegularJet squareEquation3 0 0 jet} = 2 := by
  refine le_antisymm ?_ ?_
  · have h := card_filter_isRegularJet_le squareEquation3 0 0 univ
    rw [pow_zero, mul_one] at h
    exact h.trans jetDegree_squareEquation3_le
  · have hsub : ({![1], ![2]} : Finset (Fin 1 → ZMod 3)) ⊆
        {jet ∈ Fintype.piFinset (fun _ : Fin 1 ↦ (univ : Finset (ZMod 3))) |
          IsRegularJet squareEquation3 0 0 jet} := by
      intro jet hjet
      simp only [mem_insert, mem_singleton] at hjet
      refine mem_filter.mpr ⟨by simp, ?_⟩
      rcases hjet with rfl | rfl
      · exact isRegularJet_squareEquation3 1 (by decide) (by decide)
      · exact isRegularJet_squareEquation3 2 (by decide) (by decide)
    exact (card_le_card hsub).trans_eq' (by decide)

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

/-! ### Recursive degree count -/

/-- For `Y₀ + Y₁`, total jet degree is bounded by the sum of the individual jet degrees. -/
example :
    jetTotalDegree (X (some 0) + X (some 1) : DifferentialPolynomial ℚ 1) ≤
      ∑ j : Fin 2, jetDegree (X (some 0) + X (some 1) : DifferentialPolynomial ℚ 1) j :=
  jetTotalDegree_le_sum_jetDegree _

/-! ### Witness count -/

private abbrev linearBoundedEquation : DifferentialPolynomial (ZMod 3) 0 := X (some 0)

private theorem highestActiveJet_linearBoundedEquation :
    highestActiveJet linearBoundedEquation = some 0 := by
  cases h : highestActiveJet linearBoundedEquation with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, linearBoundedEquation, jetDegree] at this
  | some j =>
      fin_cases j
      rfl

/-- The one regular bounded solution `0` of `Y₀ = 0` attains the `ZMod 3` witness-count bound. -/
example :
    1 * (Nat.card (ZMod 3) - 0) ≤
      Nat.card (ZMod 3) *
        (jetDegree linearBoundedEquation 0 * Nat.card (ZMod 3) ^ 0) := by
  have h := card_mul_sub_le_of_isHighestActiveJet (D := 0) (H := 0) linearBoundedEquation
    (isHighestActiveJet_of_highestActiveJet_eq_some highestActiveJet_linearBoundedEquation)
    ({(0 : Polynomial (ZMod 3))} : Finset (Polynomial (ZMod 3)))
    (by simp [linearBoundedEquation, differentialSpecialization,
      differentialSpecializationHom])
    (by
      intro P hP
      simp only [mem_singleton] at hP
      subst P
      simp)
    (by intro k hk hkD; omega)
    (by
      rw [differentialWeightedDegree,
        show differentialWeight (d := 0) 0 = Pi.single none 1 by
          funext v
          cases v with
          | none => simp [differentialWeight]
          | some j => simp [differentialWeight]]
      rw [MvPolynomial.weightedTotalDegree_piSingle]
      rw [linearBoundedEquation, MvPolynomial.degreeOf_X_of_ne (by decide)]
      simp)
    (by simp [linearBoundedEquation, separant, pderiv_X, differentialSpecialization,
      differentialSpecializationHom])
  exact h

/-! ### A common regular center and Taylor-chart geometry -/

private theorem aeval_initialJetEquation_taylorLinearEquation (jet : Fin 2 → ℚ) :
    aeval jet (initialJetEquation 0 (taylorLinearEquation ℚ)) = jet 1 := by
  rw [aeval_initialJetEquation]
  simp [jetEvaluation, taylorLinearEquation]

private theorem aeval_initialJetSeparant_taylorLinearEquation (jet : Fin 2 → ℚ) :
    aeval jet (initialJetSeparant 0 (taylorLinearEquation ℚ)) = 1 := by
  rw [aeval_initialJetSeparant, jetEvaluation_separant_taylorLinearEquation]

private theorem highTaylorCutsIdeal_two_two_le (I : Ideal (MvPolynomial (Fin 2) ℚ)) :
    highTaylorCutsIdeal 0 (taylorLinearEquation ℚ) 2 2 4 ≤ I :=
  (highTaylorCutsIdeal_le_iff 0 _).mpr fun _ h2 hl ↦ absurd hl (by omega)

/-- For `y' = 2x`, agreement at `0` and `1` leaves at most one regular jet in the length-two
Taylor chart. -/
example :
    (regularAgreementCutLocus ⊥ 0 (taylorLinearEquation ℚ) 2 4 ![0, 1] ![0, 1]).Subsingleton :=
  regularAgreementCutLocus_subsingleton 0 _ (taylorExponentSufficient_two_mul 1 2)
    (by norm_num) (highTaylorCutsIdeal_two_two_le ⊥) _ _
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all) (by norm_num)

/-- The zero jet for `y' = 2x` belongs to a concrete high-cut prime component family. -/
example : ∃ P ∈ highTaylorPrimeFamily 0 (taylorLinearEquation ℚ) 1 1 0,
    (![0, 0] : Fin 2 → ℚ) ∈ zeroLocus ℚ P := by
  exact exists_mem_highTaylorPrimeFamily_of_regular 0 (taylorLinearEquation ℚ) ![0, 0]
    (by rw [aeval_initialJetEquation_taylorLinearEquation]; simp)
    (by rw [aeval_initialJetSeparant_taylorLinearEquation]; norm_num)
    (by intro l hkl hlK; omega)

end

end PolynomialDifferential

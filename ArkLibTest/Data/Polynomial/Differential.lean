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
import ArkLib.Data.Polynomial.Differential.FrobeniusEquation
import ArkLib.Data.Polynomial.Differential.JetPrefix
import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation
import ArkLib.Data.Polynomial.Differential.RationalTaylor
import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
import ArkLib.Data.Polynomial.Differential.RecursiveCount
import ArkLib.Data.Polynomial.Differential.RegularIteration
import ArkLib.Data.Polynomial.Differential.RegularJetCount
import ArkLib.Data.Polynomial.Differential.RegularLift
import ArkLib.Data.Polynomial.Differential.RootPresentation
import ArkLib.Data.Polynomial.Differential.SeparantChain
import ArkLib.Data.Polynomial.Differential.ShiftedJet
import ArkLib.Data.Polynomial.Differential.SingularRecursion
import ArkLib.Data.Polynomial.Differential.TaylorChart
import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
import ArkLib.Data.Polynomial.Differential.TaylorIndexWeight
import ArkLib.Data.Polynomial.Differential.TaylorResidual
import ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount
import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for polynomial differential modules

Concrete instances check coefficient transport, derivative descent, regular lifting and Taylor
reconstruction, alongside representative finite-field counting bounds.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial Finset

private abbrev zeroJetEquation (F : Type*) [CommRing F] (d : ℕ) :
    DifferentialPolynomial F d := X (some 0)

private abbrev constantDerivativeEquation (F : Type*) [CommRing F] :
    DifferentialPolynomial F 1 := X (some 1)

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

/-- A finite family over `ℤ` has a common regular center after mapping into `ℚ`. -/
example : ∃ center : ℚ, ∀ P ∈ ({(0 : Polynomial ℤ)} : Finset (Polynomial ℤ)),
    jetEvaluation
      (separant
        (MvPolynomial.map (Int.castRingHom ℚ)
          (((MvPolynomial.X none ^ 2 + 1) * MvPolynomial.X (some 0)) :
            DifferentialPolynomial ℤ 0)) 0)
      center (polynomialJet center (P.map (Int.castRingHom ℚ))) ≠ 0 := by
  let Q : DifferentialPolynomial ℤ 0 :=
    (MvPolynomial.X none ^ 2 + 1) * MvPolynomial.X (some 0)
  have hne : (Polynomial.X ^ 2 + 1 : Polynomial ℤ) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial ℤ ↦ p.coeff 2) h
    norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_one] at hc
  have hregular : ∀ P ∈ ({(0 : Polynomial ℤ)} : Finset (Polynomial ℤ)),
      differentialSpecialization (separant Q 0) P ≠ 0 := by
    intro P hP
    have hP0 : P = 0 := Finset.mem_singleton.mp hP
    subst P
    simpa [Q, separant, differentialSpecialization, differentialSpecializationHom] using hne
  simpa [Q] using exists_forall_jetEvaluation_ne_zero_map (Int.castRingHom ℚ)
    Int.cast_injective Q {0} 0 hregular

/-! ### Concrete Hasse jets and specialization degree -/

private abbrev naturalBase : Polynomial ℕ := Polynomial.X ^ 2 + 2 * Polynomial.X + 3

private abbrev naturalDirection : Polynomial ℕ :=
  2 * Polynomial.X ^ 2 + Polynomial.X + 1

/-- Concrete order-zero, first, and second Hasse jets over `ℕ` record an affine sum. -/
example :
    polynomialJet (d := 2) 0 naturalBase = ![3, 2, 1] ∧
      polynomialJet (d := 2) 0 naturalDirection = ![1, 1, 2] ∧
      polynomialJet (d := 2) 0 (naturalBase + Polynomial.C 3 * naturalDirection) =
        ![6, 5, 7] := by
  constructor
  · ext j
    fin_cases j <;>
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] <;>
      norm_num [naturalBase, Polynomial.taylor, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  constructor
  · ext j
    fin_cases j <;>
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] <;>
      norm_num [naturalDirection, Polynomial.taylor, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_one]
  · ext j
    fin_cases j <;>
      rw [polynomialJet, Polynomial.hasseJet_eq_taylor_coeff] <;>
      norm_num [naturalBase, naturalDirection, Polynomial.taylor, Polynomial.coeff_X,
        Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_one]

private def exactDegreeEquation : DifferentialPolynomial ℚ 1 :=
  MvPolynomial.X none ^ 2 * MvPolynomial.X (some (Fin.last 1)) ^ 3

private theorem hasseDeriv_one_X_five :
    Polynomial.hasseDeriv 1 (Polynomial.X ^ 5 : Polynomial ℚ) =
      Polynomial.C 5 * Polynomial.X ^ 4 := by
  rw [Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
  norm_num
  rw [← Polynomial.C_mul_X_pow_eq_monomial]

/-- The monomial `X² Y₁³` attains its specialization degree bound at `P = X ^ 5`. -/
example :
    (differentialSpecialization exactDegreeEquation (Polynomial.X ^ 5)).natDegree = 14 ∧
      (differentialSpecialization exactDegreeEquation (Polynomial.X ^ 5)).natDegree ≤
        differentialWeightedDegree 5 exactDegreeEquation := by
  constructor
  · have hspec :
        differentialSpecialization exactDegreeEquation (Polynomial.X ^ 5) =
          Polynomial.X ^ 2 * (Polynomial.C 5 * Polynomial.X ^ 4) ^ 3 := by
      rw [exactDegreeEquation, differentialSpecialization, map_mul, map_pow, map_pow]
      simp only [differentialSpecializationHom, MvPolynomial.aeval_X, Fin.last]
      rw [hasseDeriv_one_X_five]
    rw [hspec]
    rw [Polynomial.natDegree_mul (by simp) (by norm_num), Polynomial.natDegree_pow,
      Polynomial.natDegree_pow, Polynomial.natDegree_mul (by norm_num) (by simp),
      Polynomial.natDegree_pow]
    norm_num
  · exact natDegree_differentialSpecialization_le exactDegreeEquation
      (Polynomial.X ^ 5) (by simp)

/-! ### A concrete chain witness -/

private theorem highestActiveJet_zeroJetEquation_Q0 :
    highestActiveJet (zeroJetEquation ℚ 0) = some 0 := by
  cases h : highestActiveJet (zeroJetEquation ℚ 0) with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, zeroJetEquation, jetDegree] at this
  | some j =>
      fin_cases j
      rfl

/-- The zero polynomial gives a regular chain witness for `Y₀ = 0` at the origin. -/
example : ChainWitness (zeroJetEquation ℚ 0) 0 0 := by
  refine .regular highestActiveJet_zeroJetEquation_Q0 ?_ ?_
  · simp [zeroJetEquation, differentialSpecialization, differentialSpecializationHom]
  · simp [zeroJetEquation, separant, jetEvaluation, pderiv_X]

/-- Every point is a chain witness for the zero solution of `Y₀ = 0`. -/
example : ∃ R : Polynomial ℚ, R ≠ 0 ∧ R.natDegree ≤
    differentialWeightedDegree 0 (zeroJetEquation ℚ 0) ∧
    ∀ a, R.eval a ≠ 0 → ChainWitness (zeroJetEquation ℚ 0) 0 a := by
  refine exists_chainWitness (D := 0) (Q := zeroJetEquation ℚ 0) ?_ ?_ ?_ ?_
  · simp [zeroJetEquation]
  · intro j
    exact jetDegreeCastsNeZero_of_ringChar (Or.inl ringChar.eq_zero)
  · simp [zeroJetEquation, differentialSpecialization, differentialSpecializationHom]
  · simp

/-! ### First-order chain charge -/

private theorem jetDegree_orderZeroEquation (j : Fin 2) :
    jetDegree (zeroJetEquation ℚ 1) j = if j = 0 then 1 else 0 := by
  classical
  rw [jetDegree, degreeOf_X]
  simp

private theorem jetTotalDegree_orderZeroEquation :
    jetTotalDegree (zeroJetEquation ℚ 1) = 1 := by
  change MvPolynomial.weightedTotalDegree jetDegreeWeight
    (monomial (Finsupp.single (some (0 : Fin 2)) 1) (1 : ℚ)) = 1
  rw [MvPolynomial.weightedTotalDegree_monomial _ _ _ one_ne_zero]
  simp [Finsupp.weight_apply, jetDegreeWeight]

private theorem highestActiveJet_orderZeroEquation :
    highestActiveJet (zeroJetEquation ℚ 1) = some 0 := by
  cases h : highestActiveJet (zeroJetEquation ℚ 1) with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, zeroJetEquation, jetDegree] at this
  | some j =>
      have hj := (isHighestActiveJet_of_highestActiveJet_eq_some h).1
      fin_cases j
      · rfl
      · simp [DependsOnJet, jetDegree_orderZeroEquation] at hj

private theorem orderZeroChain :
    SeparantChain (zeroJetEquation ℚ 1) [(zeroJetEquation ℚ 1, 0)] (C 1) := by
  refine .active 0 (X_ne_zero _) highestActiveJet_orderZeroEquation ?_
  have hsep : separant (zeroJetEquation ℚ 1) 0 = C 1 := by simp [separant, pderiv_X]
  rw [hsep]
  refine .terminal (by simp) ((highestActiveJet_eq_none_iff _).mpr fun j hj ↦ ?_)
  simp [DependsOnJet, jetDegree] at hj

/-- The bound is attained by the one-stage chain `Y₀` with charges `c₀ j = j` and
`c₁ j r = j + r`. -/
example :
    ([(zeroJetEquation ℚ 1, (0 : Fin 2))].map
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

private theorem regularIterate_expEquation_one : regularIterate expEquation 0 (1 + Polynomial.X) 1 =
    1 + Polynomial.X + Polynomial.C (1 / 2) * Polynomial.X ^ 2 := by
  have hres : (shiftedJetSubstitution 0 (1 + Polynomial.X) expEquation).coeff 1 = -1 := by
    rw [← taylor_differentialSpecialization, differentialSpecialization_expEquation]
    simp
  rw [regularIterate_succ, regularIterate_zero, regularLift, regularLiftCoefficient,
    slope_expEquation, hres, Polynomial.hassePerturbation, Ring.inverse_eq_inv]
  norm_num

private theorem differentialSpecialization_regularIterate_expEquation_one :
    differentialSpecialization expEquation (regularIterate expEquation 0 (1 + Polynomial.X) 1) =
      -(Polynomial.C (1 / 2) * Polynomial.X ^ 2) := by
  rw [regularIterate_expEquation_one, differentialSpecialization_expEquation]
  simp only [Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_X,
    Polynomial.derivative_C_mul_X_pow]
  norm_num

/-- `y' = y` has no polynomial solution of degree at most `2` with jet `(1, 1)` at `0`. -/
example : ¬∃ P : Polynomial ℚ, P.degree ≤ 2 ∧
    differentialSpecialization expEquation P = 0 ∧
      polynomialJet (d := 1) 0 P = polynomialJet 0 (1 + Polynomial.X) := by
  rintro ⟨P, hdegree, hsolution, hjet⟩
  have hP₀ : (1 + Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by norm_num
  have hslope : ∀ k, 0 < k → k + 1 ≤ 2 →
      IsUnit (((k + 1).choose 1 : ℚ) *
        jetEvaluation (separant expEquation (Fin.last 1)) 0
          (polynomialJet 0 (1 + Polynomial.X))) := by
    intro k hk hkD
    have hk1 : k = 1 := by omega
    subst k
    rw [slope_expEquation]
    norm_num
  obtain ⟨hPiter, -, -⟩ := (solution_iff_eq_regularIterate expEquation 0 (D := 2)
    hP₀ hslope P).mp ⟨hdegree, hsolution, hjet⟩
  rw [hPiter, differentialSpecialization_regularIterate_expEquation_one, neg_eq_zero] at hsolution
  have hcoeff := congrArg (Polynomial.coeff · 2) hsolution
  simp at hcoeff

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

/-! ### Symbolic Taylor-chart equations -/

private abbrev parameterEquation : DifferentialPolynomial (Polynomial ℚ) 1 := X (some 1)

private abbrev parameterizedEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  C (Polynomial.X + 1) * X (some 1) + X none

private abbrev independentVariableEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  X (none : Option (Fin 1))

private abbrev rationalId : ℚ →ₐ[ℚ] ℚ := AlgHom.id ℚ ℚ

/-- The mapped agreement equation for `Y₁` at parameter `2` is `Y₀ + 2Y₁ - 2`. -/
example :
    map (Polynomial.aeval (2 : ℚ)).toRingHom
        (taylorAgreementEquationOver (F := ℚ) (0 : Polynomial ℚ) parameterEquation 2
          Polynomial.X Polynomial.X) =
      X (0 : Fin 2) + C (2 : ℚ) * X (1 : Fin 2) - C (2 : ℚ) := by
  have hnum0 : commonTaylorNumeratorOver ℚ (0 : Polynomial ℚ) parameterEquation 4 0 =
      X (0 : Fin 2) := by
    simp [commonTaylorNumeratorOver, rationalTaylorNumeratorOver, parameterEquation,
      initialJetSeparant, separant]
  have hnum1 : commonTaylorNumeratorOver ℚ (0 : Polynomial ℚ) parameterEquation 4 1 =
      X (1 : Fin 2) := by
    simp [commonTaylorNumeratorOver, rationalTaylorNumeratorOver, parameterEquation,
      initialJetSeparant, separant]
  have hcut : taylorAgreementEquationOver (F := ℚ) (0 : Polynomial ℚ) parameterEquation 2
      Polynomial.X Polynomial.X =
        X (0 : Fin 2) + C Polynomial.X * X (1 : Fin 2) - C Polynomial.X := by
    simp [taylorAgreementEquationOver, hnum0, hnum1, initialJetSeparant,
      parameterEquation, separant]
  rw [hcut]
  simp only [map_sub, map_add, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Polynomial.aeval_X]

/-- The initial equation for `(X + 1)Y₁ + X` maps to `3Y₁ + 2` at parameter `2`. -/
example :
    map (Polynomial.aeval (2 : ℚ)).toRingHom
        (initialJetEquation (Polynomial.X : Polynomial ℚ) parameterizedEquation) =
      C (3 : ℚ) * X (1 : Fin 2) + C (2 : ℚ) := by
  norm_num [initialJetEquation, parameterizedEquation]
  rw [← C_1, ← C_add]
  norm_num

private abbrev constantJetEquation : DifferentialPolynomial ℚ 1 := X (some 1)

private def constantJet : Fin 2 → ℚ := fun i ↦ if i.val = 0 then 1 else 0

/-- At the regular jet `(1, 0)`, the mapped symbolic agreement equation vanishes. -/
example :
    aeval constantJet
        (map rationalId.toRingHom
          (taylorAgreementEquationOver (F := ℚ) 0 constantJetEquation 1 4 1)) = 0 := by
  have hS : aeval constantJet
      (map rationalId.toRingHom (initialJetSeparant 0 constantJetEquation)) ≠ 0 := by
    norm_num [rationalId, map_initialJetSeparant, initialJetSeparant, separant,
      constantJetEquation, constantJet]
  apply (aeval_map_taylorAgreementEquationOver_eq_zero_iff (F := ℚ) rationalId
    0 constantJetEquation 1 constantJet hS 4 1).2
  have h0 : rationalTaylorCoefficient 0 constantJetEquation constantJet 0 = 1 := by
    simpa [constantJet] using
      rationalTaylorCoefficient_initial 0 constantJetEquation constantJet ⟨0, by omega⟩
  rw [eval_rationalTaylorPolynomial, Fin.sum_univ_one]
  simp [h0]

private abbrev scaledEquation : DifferentialPolynomial ℚ 0 :=
  C (2 : ℚ) * X (some 0) - X none

private abbrev scaledSolution : Polynomial ℚ := Polynomial.C (1 / 2 : ℚ) * Polynomial.X

private def zeroJet0 : Fin 1 → ℚ := fun _ ↦ 0

private theorem initialJetSeparant_scaledEquation :
    aeval zeroJet0 (initialJetSeparant 0 scaledEquation) = 2 := by
  norm_num [initialJetSeparant, separant, scaledEquation, zeroJet0]

private theorem rationalTaylorCoefficient_scaledEquation_one :
    rationalTaylorCoefficient 0 scaledEquation zeroJet0 1 = (1 / 2 : ℚ) := by
  have hsolution : differentialSpecialization scaledEquation scaledSolution = 0 := by
    simp only [differentialSpecialization, differentialSpecializationHom, Nat.reduceAdd,
      Fin.val_eq_zero, Polynomial.hasseDeriv_zero, scaledSolution, one_div, LinearMap.id_coe,
      id_eq, scaledEquation, Fin.isValue, map_sub, map_mul, algHom_C,
      Polynomial.algebraMap_eq, aeval_X]
    rw [← mul_assoc, ← Polynomial.C_mul]
    norm_num
  have hsolutionJet : polynomialJet 0 scaledSolution = zeroJet0 := by
    funext i
    fin_cases i
    simp [polynomialJet, scaledSolution, zeroJet0]
  have hsep : jetEvaluation (separant scaledEquation (Fin.last 0)) 0
      (polynomialJet 0 scaledSolution) ≠ 0 := by
    rw [hsolutionJet]
    norm_num [jetEvaluation, separant, scaledEquation, zeroJet0]
  rw [← hsolutionJet, rationalTaylorCoefficient_eq_solution 0 scaledEquation scaledSolution
      hsolution hsep 1 (by intro i hi hle; simp)]
  norm_num [scaledSolution]

/-- The common-numerator reconstruction theorem computes coefficient `1` of `X / 2`. -/
example :
    aeval zeroJet0 (map rationalId.toRingHom
      (commonTaylorNumeratorOver ℚ 0 scaledEquation 4 1)) = 8 := by
  have hSval : aeval zeroJet0 (map rationalId.toRingHom
      (initialJetSeparant 0 scaledEquation)) = 2 := by
    simpa [rationalId] using initialJetSeparant_scaledEquation
  have hS : aeval zeroJet0 (map rationalId.toRingHom
      (initialJetSeparant 0 scaledEquation)) ≠ 0 := by
    rw [hSval]
    norm_num
  have hcoeff : (Polynomial.taylor 0
      (rationalTaylorPolynomial 0 scaledEquation 2 zeroJet0)).coeff 1 = (1 / 2 : ℚ) := by
    rw [coeff_taylor_rationalTaylorPolynomial]
    simp [rationalTaylorCoefficient_scaledEquation_one]
  have hnum := aeval_map_commonTaylorNumeratorOver_reconstruction (F := ℚ) rationalId
    0 scaledEquation 2 zeroJet0 hS ⟨1, by omega⟩
  have hcoeff' : (Polynomial.taylor (rationalId 0)
      (rationalTaylorPolynomial (rationalId 0)
        (map rationalId.toRingHom scaledEquation) 2 zeroJet0)).coeff 1 = (1 / 2 : ℚ) := by
    simpa [rationalId] using hcoeff
  rw [hSval, hcoeff'] at hnum
  norm_num at hnum ⊢
  exact hnum

/-- Symbolic high cuts for `Y₁` at the zero jet force the reconstruction to have degree below
one. -/
example :
    (rationalTaylorPolynomial 0 (X (some 1) : DifferentialPolynomial ℚ 1) 2 constantJet).degree
      < 1 := by
  have hS : aeval constantJet (map (Polynomial.aeval (0 : ℚ)).toRingHom
      (initialJetSeparant 0 parameterEquation)) ≠ 0 := by
    rw [map_initialJetSeparant]
    norm_num [initialJetSeparant, separant, parameterEquation, constantJet]
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val →
      aeval constantJet (map (Polynomial.aeval (0 : ℚ)).toRingHom
        (commonTaylorNumeratorOver ℚ 0 parameterEquation 4 l.val)) = 0 := by
    intro l hl
    have hl1 : l = 1 := by fin_cases l <;> simp_all
    subst l
    rw [map_commonTaylorNumeratorOver_eq]
    norm_num [commonTaylorNumerator, rationalTaylorNumerator, initialJetSeparant, separant,
      parameterEquation, constantJet]
  simpa [parameterEquation] using
    degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts (F := ℚ)
      (Polynomial.aeval (0 : ℚ)) 0 parameterEquation 2 1 constantJet hS hhigh

/-- A nonconstant center contributes its parameter degree to the initial equation. -/
example : jointTotalDegree (initialJetEquation Polynomial.X independentVariableEquation) ≤ 1 := by
  have hjet : jetTotalDegree independentVariableEquation ≤ 0 := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    simp only [independentVariableEquation, support_X, Finset.mem_singleton] at hu
    subst u
    simp [totalJetDegree, Finsupp.weight_single]
  have hEq : initialJetEquation Polynomial.X independentVariableEquation = C Polynomial.X := by
    simp [initialJetEquation, independentVariableEquation]
  have hcoeff :
      CoeffNatDegreeLE (initialJetEquation Polynomial.X independentVariableEquation) 1 := by
    rw [hEq]
    exact coeffNatDegreeLE_C (p := Polynomial.X) (by simp)
  exact jointTotalDegree_initialJetEquation_le Polynomial.X independentVariableEquation 0 1 hjet
    (fun m _ ↦ hcoeff m)

private abbrev parameterizedJetEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  C (Polynomial.X + 1) * X (some (1 : Fin 2))

/-- The agreement degree bound applies to a positive-length chart with parameter-dependent input. -/
example :
    jointTotalDegree (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0)
      parameterizedJetEquation 1 (Polynomial.C 0)
        (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)) ≤ 3 := by
  have hC :
      (C (Polynomial.X + 1) : DifferentialPolynomial (Polynomial ℚ) 1).weightedTotalDegree
        jetDegreeWeight ≤ 0 := by
    exact (weightedTotalDegree_C jetDegreeWeight (Polynomial.X + 1)).le
  have hY :
      (X (some (1 : Fin 2)) : DifferentialPolynomial (Polynomial ℚ) 1).weightedTotalDegree
          jetDegreeWeight ≤ 1 := by
    rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    simp only [support_X, Finset.mem_singleton] at hm
    subst m
    simp [Finsupp.weight_single, jetDegreeWeight]
  have hjet : jetTotalDegree parameterizedJetEquation ≤ 1 := by
    change parameterizedJetEquation.weightedTotalDegree jetDegreeWeight ≤ 1
    change (C (Polynomial.X + 1) * X (some (1 : Fin 2))).weightedTotalDegree jetDegreeWeight ≤ 1
    exact (weightedTotalDegree_mul_le jetDegreeWeight (C (Polynomial.X + 1))
      (X (some (1 : Fin 2)))).trans (Nat.add_le_add hC hY)
  have hQ : CoeffNatDegreeLE parameterizedJetEquation 1 := by
    change CoeffNatDegreeLE (C (Polynomial.X + 1) * X (some (1 : Fin 2))) 1
    exact (coeffNatDegreeLE_C (p := Polynomial.X + 1) (by simp)).mul
      (coeffNatDegreeLE_X (some (1 : Fin 2)))
  simpa using
    jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE (F := ℚ) (r := 1)
      0 0 0 1 parameterizedJetEquation 1 1 1 hjet hQ

private abbrev firstDerivativeEquationOverPoly : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some (1 : Fin 2))

private def nonzeroConstantJet : Fin 2 → ℚ := fun i ↦ if i.val = 0 then 1 else 0

/-- For `Y₁` at the regular jet `(1, 0)`, the symbolic cuts force coefficient `1` to vanish. -/
example :
    (Polynomial.taylor (0 : ℚ)
      (rationalTaylorPolynomial (0 : ℚ)
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom firstDerivativeEquationOverPoly)
        2 nonzeroConstantJet)).coeff 0 = 1 ∧
    (Polynomial.taylor (0 : ℚ)
      (rationalTaylorPolynomial (0 : ℚ)
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom firstDerivativeEquationOverPoly)
        2 nonzeroConstantJet)).coeff 1 = 0 := by
  have hS : aeval nonzeroConstantJet
      (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
        (initialJetSeparant (Polynomial.C (0 : ℚ)) firstDerivativeEquationOverPoly)) ≠ 0 := by
    rw [map_initialJetSeparant]
    simp [firstDerivativeEquationOverPoly, initialJetSeparant, separant]
  have hcuts : ∀ l : Fin 2, ¬2 ∣ l.val →
      aeval nonzeroConstantJet
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
          (commonTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ)) firstDerivativeEquationOverPoly
            4 l.val)) = 0 := by
    intro l hl
    fin_cases l
    · exact (hl (by decide)).elim
    · rw [map_commonTaylorNumeratorOver, commonTaylorNumeratorOver,
        rationalTaylorNumeratorOver_eq]
      simp [rationalTaylorNumerator, firstDerivativeEquationOverPoly, initialJetSeparant,
        separant, nonzeroConstantJet]
  have hcoeff0 : rationalTaylorCoefficient (0 : ℚ)
      (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom firstDerivativeEquationOverPoly)
      nonzeroConstantJet 0 = 1 := by
    simpa [nonzeroConstantJet] using rationalTaylorCoefficient_initial (0 : ℚ)
      (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom firstDerivativeEquationOverPoly)
      nonzeroConstantJet ⟨0, by omega⟩
  have hSparse := sparse_rationalTaylorPolynomial_of_symbolic_cuts
    (φ := Polynomial.aeval (R := ℚ) (0 : ℚ)) (center := Polynomial.C (0 : ℚ))
    (Q := firstDerivativeEquationOverPoly) (K := 2) (s := 2) (τ := 4)
    (hτ := taylorExponentSufficient_two_mul 1 2) (jet := nonzeroConstantJet) hS hcuts
  constructor
  · rw [coeff_taylor_rationalTaylorPolynomial]
    exact hcoeff0
  · simpa using hSparse 1 (by decide)

/-! ### Joint-degree numerator bound -/

/-- The equation `y' + t y = 0`, as `Y₁ + t Y₀` over `ℚ[t]`. -/
private abbrev positiveScaledEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some 1) + C Polynomial.X * X (some 0)

private theorem jetTotalDegree_positiveScaledEquation_le :
    jetTotalDegree positiveScaledEquation ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  rcases Finset.mem_union.mp (support_add hu) with hu | hu
  · rw [support_X, Finset.mem_singleton] at hu
    simp [hu, totalJetDegree_eq_sum, Finsupp.single_apply]
  · rw [C_mul_X_eq_monomial] at hu
    rw [Finset.mem_singleton.mp (support_monomial_subset hu)]
    simp [totalJetDegree_eq_sum, Finsupp.single_apply]

private theorem coeffNatDegreeLE_positiveScaledEquation :
    CoeffNatDegreeLE positiveScaledEquation 1 :=
  ((coeffNatDegreeLE_X _).mono (by norm_num)).add
    ((coeffNatDegreeLE_C (by simp)).mul (coeffNatDegreeLE_X _))

/-- At index `2`, the numerator for `Y₁ + t Y₀` at center `0` has joint degree at most `2`. -/
example :
    jointTotalDegree
      (rationalTaylorNumeratorOver ℚ (Polynomial.C 0) positiveScaledEquation 2) ≤ 2 := by
  simpa using jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE 0
    positiveScaledEquation 1 1 jetTotalDegree_positiveScaledEquation_le
    coeffNatDegreeLE_positiveScaledEquation 2

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
private theorem weightedTotalDegree_constantDerivativeEquation_Q :
    (constantDerivativeEquation ℚ).weightedTotalDegree (indexWeight 2) = 1 := by
  rw [weightedTotalDegree_indexWeight_eq_jetDegree_one, jetDegree, degreeOf_X_self]

private theorem firstJet_residual_coeff_one :
    (optionEquivLeft ℚ (Fin 3)
      (universalTaylorResidual 3 0 (constantDerivativeEquation ℚ))).coeff 1 =
      C 2 * X 2 := by
  have hres : universalTaylorResidual 3 (0 : ℚ) (constantDerivativeEquation ℚ) =
      universalTaylorJet 3 1 := by
    simp [universalTaylorResidual, constantDerivativeEquation]
  rw [hres, optionEquivLeft_universalTaylorJet, Polynomial.hasseDeriv_coeff]
  simp [Fin.sum_univ_three, Polynomial.coeff_monomial]
  rfl

/-- The index-weight bound is attained by `c₂` in the coefficient of `ξ` for `Y₁`. -/
example :
    Finsupp.single (2 : Fin 3) 1 ∈
        ((optionEquivLeft ℚ (Fin 3)
          (universalTaylorResidual 3 0 (constantDerivativeEquation ℚ))).coeff 1).support ∧
      Finsupp.weight Fin.val (Finsupp.single (2 : Fin 3) 1) =
        1 + (constantDerivativeEquation ℚ).weightedTotalDegree (indexWeight 2) := by
  refine ⟨?_, by simp [Finsupp.weight_single, weightedTotalDegree_constantDerivativeEquation_Q]⟩
  rw [firstJet_residual_coeff_one, mem_support_iff, X, C_mul_monomial, coeff_monomial]
  norm_num

/-- Evaluating the first displacement coefficient of the `Y₀` residual recovers the chosen
coefficient of the polynomial prefix. -/
private abbrev residualCoefficients : ℕ → ℚ := fun i ↦ if i = 0 then 3 else 5

example :
    aeval (fun i : Fin 2 ↦ residualCoefficients i.val)
      ((optionEquivLeft ℚ (Fin 2)
        (universalTaylorResidual 2 0 (X (some 0) : DifferentialPolynomial ℚ 0))).coeff 1) = 5 := by
  rw [aeval_universalTaylorResidual_coeff (center := 0) (c := residualCoefficients)
    (K := 2) (h := 1) (Q := X (some 0))]
  simp [Polynomial.centeredCoefficientPrefix, residualCoefficients]

/-- Mapping the zeroth residual coefficient through `ℤ → ZMod 2` agrees with the mapped
equation. -/
example :
    MvPolynomial.map (Int.castRingHom (ZMod 2))
      ((optionEquivLeft ℤ (Fin 2)
        (universalTaylorResidual 2 0 (X (some 1) : DifferentialPolynomial ℤ 1))).coeff 0) =
    (optionEquivLeft (ZMod 2) (Fin 2)
      (universalTaylorResidual 2 0
        (MvPolynomial.map (Int.castRingHom (ZMod 2))
          (X (some 1) : DifferentialPolynomial ℤ 1)))).coeff 0 := by
  rw [map_universalTaylorResidual_coeff]
  simp

/-! ### Total-jet-degree count -/

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

/-- Over `ZMod 3`, `y' = 0` has exactly three solutions of degree at most `2`: the constants. -/
example : Nat.card (BoundedSolution (constantDerivativeEquation (ZMod 3)) 2) = 3 := by
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
  have hupper : Nat.card (BoundedSolution (constantDerivativeEquation (ZMod 3)) 2) ≤ 3 := by
    omega
  let solution : ZMod 3 → BoundedSolution (constantDerivativeEquation (ZMod 3)) 2 := fun c ↦
    ⟨⟨Polynomial.C c, by
        rw [Polynomial.mem_degreeLT]
        exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)⟩,
      by simp [constantDerivativeEquation, differentialSpecialization,
        differentialSpecializationHom]⟩
  have hinj : Function.Injective solution := by
    intro c c' hcc'
    exact Polynomial.C_injective (congrArg
      (fun P : BoundedSolution (constantDerivativeEquation (ZMod 3)) 2 ↦ P.polynomial) hcc')
  have hlower : 3 ≤ Nat.card (BoundedSolution (constantDerivativeEquation (ZMod 3)) 2) := by
    simpa [Nat.card_zmod] using Nat.card_le_card_of_injective solution hinj
  exact Nat.le_antisymm hupper hlower

/-! ### Recursive degree count -/

private def sumEquation : DifferentialPolynomial ℚ 1 := X (some 0) + X (some 1)

private theorem mem_support_sumEquation (j : Fin 2) :
    Finsupp.single (some j) 1 ∈ sumEquation.support := by
  fin_cases j <;> simp [sumEquation, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X,
    Finsupp.single_eq_single_iff]

/-- For `Y₀ + Y₁`, total jet degree is `1` while the individual degrees sum to `2`. -/
example : jetTotalDegree sumEquation = 1 ∧ ∑ j : Fin 2, jetDegree sumEquation j = 2 := by
  have hdeg (j : Fin 2) : jetDegree sumEquation j = 1 := by
    refine le_antisymm ?_ ?_
    · refine MvPolynomial.degreeOf_le_iff.mpr fun u hu ↦ ?_
      have hsub := MvPolynomial.support_add hu
      simp only [MvPolynomial.support_X, mem_union, mem_singleton] at hsub
      rcases hsub with rfl | rfl <;> simp [Finsupp.single_apply] <;> split_ifs <;> simp
    · have h := MvPolynomial.monomial_le_degreeOf (some j) (mem_support_sumEquation j)
      rw [Finsupp.single_eq_same] at h
      exact h
  refine ⟨le_antisymm ?_ ((hdeg 0).symm.le.trans (jetDegree_le_total _ 0)), by simp [hdeg]⟩
  refine (jetTotalDegree_le_iff _ 1).mpr fun u hu ↦ ?_
  have hsub := MvPolynomial.support_add hu
  simp only [MvPolynomial.support_X, mem_union, mem_singleton] at hsub
  rcases hsub with rfl | rfl <;> simp [totalJetDegree_eq_sum, Fin.sum_univ_two]

/-! ### Witness count -/

private theorem highestActiveJet_linearBoundedEquation :
    highestActiveJet (zeroJetEquation (ZMod 3) 0) = some 0 := by
  cases h : highestActiveJet (zeroJetEquation (ZMod 3) 0) with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, zeroJetEquation, jetDegree] at this
  | some j =>
      fin_cases j
      rfl

/-- The one regular bounded solution `0` of `Y₀ = 0` attains the `ZMod 3` witness-count bound. -/
example :
    1 * (Nat.card (ZMod 3) - 0) ≤
      Nat.card (ZMod 3) *
        (jetDegree (zeroJetEquation (ZMod 3) 0) 0 * Nat.card (ZMod 3) ^ 0) := by
  have h := card_mul_sub_le_of_isHighestActiveJet (D := 0) (H := 0)
    (zeroJetEquation (ZMod 3) 0)
    (isHighestActiveJet_of_highestActiveJet_eq_some highestActiveJet_linearBoundedEquation)
    ({(0 : Polynomial (ZMod 3))} : Finset (Polynomial (ZMod 3)))
    (by simp [zeroJetEquation, differentialSpecialization,
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
      rw [zeroJetEquation, MvPolynomial.degreeOf_X_of_ne (by decide)]
      simp)
    (by simp [zeroJetEquation, separant, pderiv_X, differentialSpecialization,
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

/-- The incidence bound is attained by the single regular zero jet of `Y₀` over an algebraic
closure. -/
example :
    (((({![0]} : Finset (Fin 1 → AlgebraicClosure ℚ)).card : ℕ) : ℚ)) ≤
      jetTotalDegree (zeroJetEquation (AlgebraicClosure ℚ) 0) *
        (((Fintype.card (Fin 1) * rationalTaylorCutDegreeBound
          (zeroJetEquation (AlgebraicClosure ℚ) 0) 2 : ℕ) : ℚ) / ((1 - 1 + 1 : ℕ) : ℚ)) ^ 0 := by
  let F := AlgebraicClosure ℚ
  let Q : DifferentialPolynomial F 0 := zeroJetEquation F 0
  let domain : Fin 1 → F := fun _ ↦ 0
  let received : Fin 1 → F := fun _ ↦ 0
  let S : Finset (Fin 1 → F) := {![0]}
  have hinj : Function.Injective domain := by
    intro i j _
    exact Subsingleton.elim i j
  have hS : ∀ jet ∈ S, aeval jet (initialJetEquation 0 Q) = 0 ∧
      aeval jet (initialJetSeparant 0 Q) ≠ 0 ∧
      ∀ l, 1 ≤ l → l < 1 → aeval jet (commonTaylorNumerator 0 Q 2 l) = 0 := by
    intro jet hjet
    have hj : jet = ![(0 : F)] := Finset.mem_singleton.mp hjet
    subst jet
    refine ⟨?_, ?_, ?_⟩
    · simp [Q, zeroJetEquation, initialJetEquation]
    · simp [Q, zeroJetEquation, initialJetSeparant, separant]
    · intro l hl hlK
      omega
  have hA : ∀ jet ∈ S, 1 ≤
      {i : Fin 1 | aeval jet
        (taylorAgreementEquation 0 Q 1 2 (domain i) (received i)) = 0}.ncard := by
    intro jet hjet
    have hj : jet = ![(0 : F)] := Finset.mem_singleton.mp hjet
    subst jet
    have hsol : differentialSpecialization Q (0 : Polynomial F) = 0 := by
      simp [Q, zeroJetEquation, differentialSpecialization, differentialSpecializationHom]
    have hsep : jetEvaluation (separant Q (Fin.last 0)) 0
        (polynomialJet 0 (0 : Polynomial F)) ≠ 0 := by
      simp [Q, zeroJetEquation, separant, jetEvaluation, pderiv_X]
    have hdegree : (0 : Polynomial F).degree < 1 := by simp
    have hbin : ∀ i, 0 < i → i < 1 → (i.choose 0 : F) ≠ 0 := by
      intro i hi hiK
      omega
    have hcut' (i : Fin 1) : aeval (polynomialJet 0 (0 : Polynomial F))
        (taylorAgreementEquation 0 Q 1 2 (domain i) (received i)) = 0 := by
      rw [aeval_taylorAgreementEquation_polynomialJet_eq_zero_iff 0 Q 0 hsol hsep
        (taylorExponentSufficient_two_mul 0 1) hdegree hbin]
      simp [domain, received]
    have hjet0 : polynomialJet 0 (0 : Polynomial F) = ![(0 : F)] := by
      funext j
      fin_cases j
      simp [polynomialJet]
    have hcut (i : Fin 1) : aeval ![(0 : F)]
        (taylorAgreementEquation 0 Q 1 2 (domain i) (received i)) = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval, hjet0] using hcut' i
    simp [hcut]
  have h := card_le_of_highTaylorCuts_of_agreement (center := (0 : F)) Q
    (taylorExponentSufficient_two_mul 0 1) (by decide) domain received hinj
    (A := 1) (by decide) (by decide) S hS hA
  simpa [S, Q, zeroJetEquation, rationalTaylorCutDegreeBound] using h

/-! ### Frobenius flattening -/

private abbrev frobeniusEquationExample :
    DifferentialPolynomial (Polynomial (ZMod 2)) 0 := X (some 0)

private abbrev frobeniusSquareEquation :
    DifferentialPolynomial (Polynomial (ZMod 2)) 0 := X (some 0) ^ 2

/-- The flattened equation evaluates to `7` at the root, independent-variable, and challenge
values `2`, `3`, and `5`. -/
example :
    MvPolynomial.eval
        (fun o : Option (Fin 2) => o.elim (2 : ℚ) (fun i => Fin.cases 3 (fun _ => 5) i))
        (ordinaryFlatten ℚ
          (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
            DifferentialPolynomial (Polynomial ℚ) 0)) = 7 := by
  rw [eval_ordinaryFlatten]
  norm_num [differentialSpecialization, differentialSpecializationHom]

/-- Expanding the specialization of `Y₀ + W` at `W = 2` sends the root `X` to `X² + 2`. -/
example :
    Polynomial.expand ℚ 2
      (differentialSpecialization
        (MvPolynomial.map (Polynomial.evalRingHom (2 : ℚ))
          (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
            DifferentialPolynomial (Polynomial ℚ) 0)) Polynomial.X) =
      Polynomial.X ^ 2 + Polynomial.C 2 := by
  have hflat : ordinaryFlatten ℚ
      (MvPolynomial.X (some 0) + MvPolynomial.C Polynomial.X :
        DifferentialPolynomial (Polynomial ℚ) 0) =
        MvPolynomial.X none + MvPolynomial.X (some 1) := by
    simp
  have hcase :
      Fin.cases (Polynomial.X ^ 2 : Polynomial ℚ)
        (fun _ : Fin 1 => Polynomial.C 2)
        (1 : Fin 2) = Polynomial.C 2 := by
    rw [show (1 : Fin 2) = Fin.succ 0 by norm_num, Fin.cases_succ]
  rw [expand_differentialSpecialization_map_eq_eval₂_flatten, hflat]
  simp [MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, hcase]

/-- The fixed characteristic-two equation `Y₀` satisfies the Frobenius contraction existence
statement. -/
example :
      ∃ e : ℕ, ∃ H : DifferentialPolynomial (Polynomial (ZMod 2)) 0,
      Irreducible H ∧
      MvPolynomial.pderiv (some 0) H ≠ 0 ∧
      H.degreeOf (some 0) * (2 ^ e) = frobeniusEquationExample.degreeOf (some 0) ∧
      H.degreeOf none ≤ frobeniusEquationExample.degreeOf none ∧
      MvPolynomial.CoeffNatDegreeLE H 0 ∧
      ∀ (P : Polynomial (ZMod 2)) (w : ZMod 2),
        differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom (w ^ (2 ^ e)))
              frobeniusEquationExample) P = 0 →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom w) H)
              (Polynomial.expand (ZMod 2) (2 ^ e) P) = 0 := by
  apply exists_frobeniusEquation (E := ZMod 2) 2 (Q := frobeniusEquationExample)
  · simp [frobeniusEquationExample]
  · apply MvPolynomial.irreducible_of_totalDegree_eq_one
    · simp [frobeniusEquationExample]
    · intro c hc
      apply isUnit_of_dvd_one
      have h := hc (Finsupp.single (some (0 : Fin 1)) 1)
      simpa [frobeniusEquationExample] using h
  · exact MvPolynomial.coeffNatDegreeLE_X (some 0)

/-- A concrete zero specialization is transported through the fixed characteristic-two
Frobenius twist. -/
example :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom ((0 : ZMod 2) ^ (2 ^ 1)))
        frobeniusSquareEquation)
      (0 : Polynomial (ZMod 2)) = 0 ∧
    differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom (0 : ZMod 2))
        (ordinaryUnflatten (ZMod 2)
          (inverseFrobeniusTwist 2 1
            (MvPolynomial.X none : MvPolynomial (Option (Fin 2)) (ZMod 2)))))
      (Polynomial.expand (ZMod 2) (2 ^ 1) (0 : Polynomial (ZMod 2))) = 0 := by
  have hflat : ordinaryFlatten (ZMod 2) frobeniusSquareEquation =
      (MvPolynomial.X none : MvPolynomial (Option (Fin 2)) (ZMod 2)) ^ 2 := by
    simp [frobeniusSquareEquation]
  have hroot : rootExpansion (2 ^ 1)
      (MvPolynomial.X none : MvPolynomial (Option (Fin 2)) (ZMod 2)) =
      ordinaryFlatten (ZMod 2) frobeniusSquareEquation := by
    rw [hflat]
    norm_num only [pow_one]
    simp [rootExpansion, optionEquivLeft_X_none]
  have hQ : differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom ((0 : ZMod 2) ^ (2 ^ 1)))
        frobeniusSquareEquation)
      (0 : Polynomial (ZMod 2)) = 0 := by
    norm_num only [pow_one, zero_pow (by decide : 2 ≠ 0)]
    simp [frobeniusSquareEquation, differentialSpecialization,
      differentialSpecializationHom]
  exact ⟨hQ, frobeniusSpecialization_eq_zero 2 1 frobeniusSquareEquation
    (MvPolynomial.X none : MvPolynomial (Option (Fin 2)) (ZMod 2)) hroot 0 0 hQ⟩

/-! ### Ordinary root presentations -/

private abbrev rationalRootEquation : DifferentialPolynomial (Polynomial ℚ) 0 := X (some 0)

/-- For the concrete irreducible equation `Y₀` over `ℚ[X]`, the exceptional set is empty. -/
example :
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 0 ∧
      ∀ w ∉ exceptional, ∀ P : Polynomial ℚ,
        differentialSpecialization
            (challengeSpecialization rationalRootEquation w) P = 0 →
          differentialSpecialization
            (separant (challengeSpecialization rationalRootEquation w) (Fin.last 0)) P ≠ 0 := by
  have hirr : Irreducible rationalRootEquation := by
    apply MvPolynomial.irreducible_of_totalDegree_eq_one
    · simp [rationalRootEquation]
    · intro c hc
      apply isUnit_of_dvd_one
      have h := hc (Finsupp.single (some (0 : Fin 1)) 1)
      simpa [rationalRootEquation] using h
  have hpos : 0 < rationalRootEquation.degreeOf (some 0) := by
    simp [rationalRootEquation]
  have hder : MvPolynomial.pderiv (some 0) rationalRootEquation ≠ 0 := by
    simp [rationalRootEquation]
  have hheight : MvPolynomial.CoeffNatDegreeLE rationalRootEquation 0 := by
    simpa [rationalRootEquation] using
      MvPolynomial.coeffNatDegreeLE_X (R := ℚ) (σ := JetVariable 0) (some 0)
  simpa [rationalRootEquation] using
    exists_exceptional_ordinary_separant hirr hpos hder hheight

end

end PolynomialDifferential

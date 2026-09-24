/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.BaseChange
import ArkLib.Data.Polynomial.Differential.ChainWitness
import ArkLib.Data.Polynomial.Differential.ContentExceptions
import ArkLib.Data.Polynomial.Differential.DerivativeDescent
import ArkLib.Data.Polynomial.Differential.DirectRegularLift
import ArkLib.Data.Polynomial.Differential.FirstOrderStageSum
import ArkLib.Data.Polynomial.Differential.FrobeniusEquation
import ArkLib.Data.Polynomial.Differential.FrobeniusTaylorWitness
import ArkLib.Data.Polynomial.Differential.JetPrefix
import ArkLib.Data.Polynomial.Differential.JetPrefixPresentation
import ArkLib.Data.Polynomial.Differential.RationalTaylor
import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
import ArkLib.Data.Polynomial.Differential.RationalTaylorDerivativeDegree
import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
import ArkLib.Data.Polynomial.Differential.RecursiveCount
import ArkLib.Data.Polynomial.Differential.RetainedCurve
import ArkLib.Data.Polynomial.Differential.RegularIteration
import ArkLib.Data.Polynomial.Differential.RegularJetCount
import ArkLib.Data.Polynomial.Differential.RegularLift
import ArkLib.Data.Polynomial.Differential.RootPresentation
import ArkLib.Data.Polynomial.Differential.SeparantChain
import ArkLib.Data.Polynomial.Differential.ShiftedJet
import ArkLib.Data.Polynomial.Differential.SingularRecursion
import ArkLib.Data.Polynomial.Differential.TaylorChart
import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
import ArkLib.Data.Polynomial.Differential.TaylorChartBaseChange
import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
import ArkLib.Data.Polynomial.Differential.TaylorIndexWeight
import ArkLib.Data.Polynomial.Differential.TaylorResidual
import ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount
import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Defs
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

private def zeroJetBoundedRoot : BoundedSolution (zeroJetEquation ℚ 0) 0 :=
  ⟨⟨0, by simp⟩, by simp⟩

private abbrev constantDerivativeEquation (F : Type*) [CommRing F] :
    DifferentialPolynomial F 1 := X (some 1)

private def constantJet {F : Type*} [Zero F] [One F] : Fin 2 → F :=
  fun i ↦ if i.val = 0 then 1 else 0

private def zeroJetVector {F : Type*} [Zero F] (n : ℕ) : Fin n → F := fun _ ↦ 0

private theorem highestActiveJet_zeroJetEquation {F : Type*} [CommRing F] [Nontrivial F] :
    highestActiveJet (zeroJetEquation F 0) = some 0 := by
  cases h : highestActiveJet (zeroJetEquation F 0) with
  | none =>
      have := (highestActiveJet_eq_none_iff _).mp h 0
      simp [DependsOnJet, zeroJetEquation, jetDegree] at this
  | some j =>
      fin_cases j
      rfl

private theorem highestActiveJet_constantDerivativeEquation_Q :
    highestActiveJet (constantDerivativeEquation ℚ) = some 1 := by
  have hactive : activeJets (constantDerivativeEquation ℚ) = {1} := by
    ext j
    fin_cases j
    · rw [mem_activeJets]
      change 0 < jetDegree (constantDerivativeEquation ℚ) (0 : Fin 2) ↔
        (0 : Fin 2) ∈ ({1} : Finset (Fin 2))
      rw [jetDegree, constantDerivativeEquation, MvPolynomial.degreeOf_X_of_ne (by decide)]
      norm_num
    · rw [mem_activeJets]
      change 0 < jetDegree (constantDerivativeEquation ℚ) (1 : Fin 2) ↔
        (1 : Fin 2) ∈ ({1} : Finset (Fin 2))
      rw [jetDegree, constantDerivativeEquation, MvPolynomial.degreeOf_X_self]
      norm_num
  have hne : (activeJets (constantDerivativeEquation ℚ)).Nonempty := by simp [hactive]
  rw [highestActiveJet_eq_some_max _ hne]
  simp [hactive]

private theorem jetTotalDegree_constantDerivativeEquation_le {F : Type*} [CommRing F]
    [Nontrivial F] : jetTotalDegree (constantDerivativeEquation F) ≤ 1 := by
  refine (jetTotalDegree_le_iff _ 1).mpr fun u hu ↦ ?_
  rw [MvPolynomial.support_X, mem_singleton] at hu
  rw [hu]
  simp [totalJetDegree_eq_sum, Fin.sum_univ_two]

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

open Classical in
/-- Mapping the nonempty regular solution family `{X}` through `ZMod 2 → E₄` preserves its
degree, equation, and nonzero separant. -/
example :
    let f := algebraMap (ZMod 2) E₄
    let Q : DifferentialPolynomial (ZMod 2) 0 := X (some 0) - X none
    ∀ P ∈ ({(Polynomial.X : Polynomial (ZMod 2))} : Finset (Polynomial (ZMod 2))).image
        (Polynomial.map f),
      P.degree < 2 ∧ differentialSpecialization (MvPolynomial.map f Q) P = 0 ∧
        differentialSpecialization (separant (MvPolynomial.map f Q) 0) P ≠ 0 := by
  classical
  intro f Q
  refine map_regularSolutionFamily f.injective Q {Polynomial.X} 0 2 ?_ ?_ ?_
  · intro P hP
    simp only [Finset.mem_singleton] at hP
    subst P
    norm_num
  · intro P hP
    simp only [Finset.mem_singleton] at hP
    subst P
    simp [Q, differentialSpecialization, differentialSpecializationHom]
  · intro P hP
    simp only [Finset.mem_singleton] at hP
    subst P
    simp [Q, separant, differentialSpecialization, differentialSpecializationHom, pderiv_X]

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

/-- The zero polynomial gives a regular chain witness for `Y₀ = 0` at the origin. -/
example : ChainWitness (zeroJetEquation ℚ 0) 0 0 := by
  refine .regular (highestActiveJet_zeroJetEquation (F := ℚ)) ?_ ?_
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

private abbrev challengeEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  C Polynomial.X * X (some 0)

private theorem separant_challengeEquation : separant challengeEquation 0 = C Polynomial.X := by
  simp [separant, pderiv_X]

private theorem natDegree_coeff_challengeEquation_le (u : JetVariable 0 →₀ ℕ) :
    (challengeEquation.coeff u).natDegree ≤ 1 := by
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

private theorem challengeChain :
    SeparantChain challengeEquation [(challengeEquation, (0 : Fin 1))] (C Polynomial.X) := by
  have hjet : jetDegree challengeEquation 0 = 1 := by
    rw [jetDegree, (degreeOf_mul_X_eq_degreeOf_add_one_iff _ _).mpr
      (by simp [Polynomial.X_ne_zero]), degreeOf_C]
  have hactive : activeJets challengeEquation = {0} := by
    ext j
    fin_cases j
    rw [mem_activeJets]
    change 0 < jetDegree challengeEquation (0 : Fin 1) ↔ (0 : Fin 1) ∈ ({0} : Finset (Fin 1))
    rw [hjet]
    norm_num
  have hhighest : highestActiveJet challengeEquation = some 0 := by
    rw [highestActiveJet_eq_some_max challengeEquation (by simp [hactive])]
    simp [hactive]
  refine .active 0 (by simp [Polynomial.X_ne_zero])
    hhighest ?_
  rw [separant_challengeEquation]
  refine .terminal (by simp [Polynomial.X_ne_zero]) ?_
  apply (highestActiveJet_eq_none_iff _).mpr
  intro j
  simp [DependsOnJet, jetDegree, MvPolynomial.degreeOf_C]

/-- The `X · Y₀` chain over `ℚ[X]` has at most one exceptional specialization value. -/
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧
    ∀ z ∉ exceptional, ∀ P : Polynomial ℚ,
      differentialSpecialization
        (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) challengeEquation) P = 0 →
      ∃ stage ∈ [(challengeEquation, (0 : Fin 1))],
        differentialSpecialization
          (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) stage.1) P = 0 ∧
        differentialSpecialization
          (separant (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) z) stage.1)
            stage.2) P ≠ 0 :=
  challengeChain.exists_finset_regular_stage natDegree_coeff_challengeEquation_le
    (RingHom.id ℚ) Function.injective_id

/-! ### First-order chain charge -/

private theorem constantDerivativeChain :
    SeparantChain (constantDerivativeEquation ℚ)
      [(constantDerivativeEquation ℚ, (1 : Fin 2))] (C 1) := by
  refine .active 1 (X_ne_zero _) highestActiveJet_constantDerivativeEquation_Q ?_
  have hsep : separant (constantDerivativeEquation ℚ) 1 = C 1 := by
    simp [separant, constantDerivativeEquation, pderiv_X]
  rw [hsep]
  refine .terminal (by simp) ((highestActiveJet_eq_none_iff _).mpr fun j hj ↦ ?_)
  simp [DependsOnJet, jetDegree] at hj

/-- The `Y₁` stage is charged against the first-order cap with `M = 1`. -/
example :
    ([(constantDerivativeEquation ℚ, (1 : Fin 2))].map
      (firstOrderStageCharge (fun j ↦ (j : ℚ)) fun j r ↦ (j + r : ℚ))).sum ≤
        firstOrderStageCap (fun j ↦ (j : ℚ)) (fun j r ↦ (j + r : ℚ)) 1 1 :=
  constantDerivativeChain.sum_firstOrderStageCharge_le
    jetTotalDegree_constantDerivativeEquation_le
    (by simp [constantDerivativeEquation, jetDegree]) (fun j ↦ by positivity)
    (fun j r ↦ by positivity) (fun _ _ h ↦ by exact_mod_cast h)
    (fun _ h ↦ by simp only [add_le_add_iff_right]; exact_mod_cast h)
    (fun h _ ↦ by simp only [add_le_add_iff_left]; exact_mod_cast h)
    (fun j ↦ by simp)

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

/-- The descent of `Y₁ ^ 2 * Y₀` is nonzero and has no active jet at or above `Y₁`. -/
example : derivativeDescent cubicEquation 1 ≠ 0 ∧
    ∀ j, DependsOnJet (derivativeDescent cubicEquation 1) j → j < 1 := by
  have hactive : activeJets cubicEquation = {0, 1} := by
    ext j
    fin_cases j <;> simp [DependsOnJet, jetDegree_cubicEquation]
  have hhighest : highestActiveJet cubicEquation = some 1 := by
    simpa [hactive] using highestActiveJet_eq_some_max cubicEquation (by simp [hactive])
  have hcast := jetDegreeCastsNeZero_of_jetTotalDegree_charGuard (Q := cubicEquation)
    (ν := jetTotalDegree cubicEquation) le_rfl (Or.inl ringChar.eq_zero) 1
  exact derivativeDescent_spec_of_highestActiveJet_eq_some hhighest hcast
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
example : ∃! γ : ℚ, Polynomial.X ^ 2 ∣ shiftedJetSubstitution 0
    (1 + Polynomial.X + Polynomial.hassePerturbation 0 γ 2) expEquation := by
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
  exact ⟨1 / 2, hhalf, fun γ h ↦ hlift.unique h hhalf⟩

private abbrev constEquation₂ : DifferentialPolynomial ℚ 2 := X (some 1)

private theorem isHighestActiveJet_constEquation₂ : IsHighestActiveJet constEquation₂ 1 := by
  classical
  refine ⟨by simp [DependsOnJet, constEquation₂, jetDegree], fun j hj ↦ ?_⟩
  simp [DependsOnJet, constEquation₂, jetDegree, degreeOf_X, hj.ne']

/-- For `y' = 0` stored at depth `2`, the unique lift at `Y₁` is `γ = 0`. -/
example : ∃! γ : ℚ,
    (Polynomial.X - Polynomial.C 0) ^ 2 ∣ differentialSpecialization constEquation₂
      (1 + Polynomial.hassePerturbation 0 γ 2) := by
  have hlift := existsUnique_regularLiftCoefficient_centered_of_isHighestActiveJet (k := 1)
    one_pos constEquation₂ isHighestActiveJet_constEquation₂ 0 1
    (by simp [differentialSpecialization, differentialSpecializationHom])
    (by simp [separant, jetEvaluation, constEquation₂, pderiv_X])
  have hzero : (Polynomial.X - Polynomial.C 0) ^ 2 ∣ differentialSpecialization
      constEquation₂ (1 + Polynomial.hassePerturbation 0 (0 : ℚ) 2) := by
    rw [Polynomial.hassePerturbation, map_zero, zero_mul, add_zero]
    simp [differentialSpecialization, differentialSpecializationHom]
  exact ⟨0, hzero, fun γ h ↦ hlift.unique h hzero⟩

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

/-- The numerator of `y' = t y` specializes at the nonzero parameter `t = 5`. -/
example :
    map (Polynomial.aeval (5 : ℚ)).toRingHom
        (rationalTaylorNumeratorOver ℚ 0 scaledExpEquation 2) =
      rationalTaylorNumerator 0
        (X (some 1) - C (5 : ℚ) * X (some 0) : DifferentialPolynomial ℚ 1) 2 := by
  rw [map_rationalTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]
  simp [scaledExpEquation]

/-! ### Symbolic Taylor-chart equations -/

private abbrev independentVariableEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  X (none : Option (Fin 1))

private abbrev rationalId : ℚ →ₐ[ℚ] ℚ := AlgHom.id ℚ ℚ

/-- The mapped agreement equation for `Y₁` at parameter `2` is `Y₀ + 2Y₁ - 2`. -/
example :
    map (Polynomial.aeval (2 : ℚ)).toRingHom
        (taylorAgreementEquationOver (F := ℚ) (0 : Polynomial ℚ)
          (constantDerivativeEquation (Polynomial ℚ)) 2 Polynomial.X Polynomial.X (τ := 4)) =
      X (0 : Fin 2) + C (2 : ℚ) * X (1 : Fin 2) - C (2 : ℚ) := by
  have hnum0 :
      commonTaylorNumeratorOver ℚ (0 : Polynomial ℚ)
        (constantDerivativeEquation (Polynomial ℚ)) 4 0 =
      X (0 : Fin 2) := by
    simp [commonTaylorNumeratorOver, rationalTaylorNumeratorOver, constantDerivativeEquation,
      initialJetSeparant, separant]
  have hnum1 :
      commonTaylorNumeratorOver ℚ (0 : Polynomial ℚ)
        (constantDerivativeEquation (Polynomial ℚ)) 4 1 =
      X (1 : Fin 2) := by
    simp [commonTaylorNumeratorOver, rationalTaylorNumeratorOver, constantDerivativeEquation,
      initialJetSeparant, separant]
  have hcut :
      taylorAgreementEquationOver (F := ℚ) (0 : Polynomial ℚ)
        (constantDerivativeEquation (Polynomial ℚ)) 2 Polynomial.X Polynomial.X (τ := 4) =
        X (0 : Fin 2) + C Polynomial.X * X (1 : Fin 2) - C Polynomial.X := by
    simp [taylorAgreementEquationOver, hnum0, hnum1, initialJetSeparant,
      constantDerivativeEquation, separant]
  rw [hcut]
  simp only [map_sub, map_add, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Polynomial.aeval_X]

/-- At the regular jet `(1, 0)`, the mapped symbolic agreement equation vanishes. -/
example :
    aeval (constantJet (F := ℚ))
        (map rationalId.toRingHom
          (taylorAgreementEquationOver (F := ℚ) (0 : ℚ) (constantDerivativeEquation ℚ)
            1 (4 : ℚ) 1 (τ := 2))) = 0 := by
  have hS : aeval (constantJet (F := ℚ))
      (map rationalId.toRingHom (initialJetSeparant (0 : ℚ)
        (constantDerivativeEquation ℚ))) ≠ 0 := by
    norm_num [rationalId, map_initialJetSeparant, initialJetSeparant, separant,
      constantDerivativeEquation, constantJet]
  apply (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent (F := ℚ) rationalId _ _ 1 2
    (taylorExponentSufficient_two_mul 1 1) (constantJet (F := ℚ)) hS (4 : ℚ) (1 : ℚ)).2
  have h0 : rationalTaylorCoefficient (0 : ℚ) (constantDerivativeEquation ℚ)
      (constantJet (F := ℚ)) 0 = 1 := by
    simpa [constantJet] using
      rationalTaylorCoefficient_initial 0 (constantDerivativeEquation ℚ)
        (constantJet (F := ℚ)) ⟨0, by omega⟩
  rw [eval_rationalTaylorPolynomial, Fin.sum_univ_one]
  simp [h0]

private abbrev scaledEquation : DifferentialPolynomial ℚ 0 :=
  C (2 : ℚ) * X (some 0) - X none

private abbrev scaledSolution : Polynomial ℚ := Polynomial.C (1 / 2 : ℚ) * Polynomial.X

private theorem initialJetSeparant_scaledEquation :
    aeval (zeroJetVector (F := ℚ) 1) (initialJetSeparant (0 : ℚ) scaledEquation) = 2 := by
  norm_num [initialJetSeparant, separant, scaledEquation, zeroJetVector]

private theorem rationalTaylorCoefficient_scaledEquation_one :
    rationalTaylorCoefficient (0 : ℚ) scaledEquation (zeroJetVector (F := ℚ) 1) 1 =
      (1 / 2 : ℚ) := by
  have hsolution : differentialSpecialization scaledEquation scaledSolution = 0 := by
    simp only [differentialSpecialization, differentialSpecializationHom, Nat.reduceAdd,
      Fin.val_eq_zero, Polynomial.hasseDeriv_zero, scaledSolution, one_div, LinearMap.id_coe,
      id_eq, scaledEquation, Fin.isValue, map_sub, map_mul, algHom_C,
      Polynomial.algebraMap_eq, aeval_X]
    rw [← mul_assoc, ← Polynomial.C_mul]
    norm_num
  have hsolutionJet : polynomialJet 0 scaledSolution = zeroJetVector (F := ℚ) 1 := by
    funext i
    fin_cases i
    simp [polynomialJet, scaledSolution, zeroJetVector]
  have hsep : jetEvaluation (separant scaledEquation (Fin.last 0)) 0
      (polynomialJet 0 scaledSolution) ≠ 0 := by
    rw [hsolutionJet]
    norm_num [jetEvaluation, separant, scaledEquation, zeroJetVector]
  rw [← hsolutionJet, rationalTaylorCoefficient_eq_solution 0 scaledEquation scaledSolution
      hsolution hsep 1 (by intro i hi hle; simp)]
  norm_num [scaledSolution]

/-- The common-numerator reconstruction theorem computes coefficient `1` of `X / 2`. -/
example :
    aeval (zeroJetVector (F := ℚ) 1) (map rationalId.toRingHom
      (commonTaylorNumeratorOver ℚ 0 scaledEquation 4 1)) = 8 := by
  have hSval : aeval (zeroJetVector (F := ℚ) 1) (map rationalId.toRingHom
      (initialJetSeparant 0 scaledEquation)) = 2 := by
    simpa [rationalId] using initialJetSeparant_scaledEquation
  have hS : aeval (zeroJetVector (F := ℚ) 1) (map rationalId.toRingHom
      (initialJetSeparant 0 scaledEquation)) ≠ 0 := by
    rw [hSval]
    norm_num
  have hcoeff : (Polynomial.taylor 0
      (rationalTaylorPolynomial 0 scaledEquation 2 (zeroJetVector (F := ℚ) 1))).coeff 1 =
        (1 / 2 : ℚ) := by
    rw [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix]
    simp [rationalTaylorCoefficient_scaledEquation_one]
  have hnum := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent (F := ℚ)
    rationalId 0 scaledEquation 2 4 (taylorExponentSufficient_two_mul 0 2)
    (zeroJetVector (F := ℚ) 1) hS ⟨1, by omega⟩
  have hcoeff' : (Polynomial.taylor (rationalId 0)
      (rationalTaylorPolynomial (rationalId 0)
        (map rationalId.toRingHom scaledEquation) 2 (zeroJetVector (F := ℚ) 1))).coeff 1 =
        (1 / 2 : ℚ) := by
    simpa [rationalId] using hcoeff
  rw [hSval, hcoeff'] at hnum
  norm_num at hnum ⊢
  exact hnum

/-- Symbolic high cuts for `Y₁` at the zero jet force the reconstruction to have degree below
one. -/
example :
    (rationalTaylorPolynomial 0 (X (some 1) : DifferentialPolynomial ℚ 1) 2
      (constantJet (F := ℚ))).degree
      < 1 := by
  have hS : aeval (constantJet (F := ℚ)) (map (Polynomial.aeval (0 : ℚ)).toRingHom
      (initialJetSeparant 0 (constantDerivativeEquation (Polynomial ℚ)))) ≠ 0 := by
    rw [map_initialJetSeparant]
    norm_num [initialJetSeparant, separant, constantDerivativeEquation, constantJet]
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val →
      aeval (constantJet (F := ℚ)) (map (Polynomial.aeval (0 : ℚ)).toRingHom
        (commonTaylorNumeratorOver ℚ 0
          (constantDerivativeEquation (Polynomial ℚ)) 4 l.val)) = 0 := by
    intro l hl
    have hl1 : l = 1 := by fin_cases l <;> simp_all
    subst l
    rw [map_commonTaylorNumeratorOver_eq]
    norm_num [commonTaylorNumerator, rationalTaylorNumerator, initialJetSeparant, separant,
      constantDerivativeEquation, constantJet]
  simpa [constantDerivativeEquation] using
    degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent (F := ℚ)
      (Polynomial.aeval (0 : ℚ)) 0 (constantDerivativeEquation (Polynomial ℚ)) 2 1 4
      (taylorExponentSufficient_two_mul 1 2) (constantJet (F := ℚ)) hS hhigh

example : jointTotalDegree (initialJetEquation Polynomial.X independentVariableEquation) ≤ 1 := by
  simp [jointTotalDegree, initialJetEquation, independentVariableEquation]

/-- The equation `(y')² + t y = 0`, as `Y₁² + t Y₀` over `ℚ[t]`. -/
private abbrev recursiveEq : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some 1) ^ 2 + C Polynomial.X * X (some 0)
private theorem recursiveJet_le : jetTotalDegree recursiveEq ≤ 2 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  rcases Finset.mem_union.mp (support_add hu) with hu | hu
  · rw [support_X_pow, Finset.mem_singleton] at hu
    simp [hu, totalJetDegree_eq_sum, Finsupp.single_apply]
  · rw [C_mul_X_eq_monomial] at hu
    rw [Finset.mem_singleton.mp (support_monomial_subset hu)]
    simp [totalJetDegree_eq_sum, Finsupp.single_apply]
private theorem recursiveHeight : CoeffNatDegreeLE recursiveEq 1 :=
  (((coeffNatDegreeLE_X _).pow 2).mono (by norm_num)).add
    ((coeffNatDegreeLE_C (by simp)).mul (coeffNatDegreeLE_X _))
private theorem recursiveDerivativeDegree : recursiveEq.degreeOf (some 1) ≤ 2 :=
  (jetDegree_le_total recursiveEq 1).trans recursiveJet_le
/-- The agreement degree bound applies to a positive-length chart with parameter-dependent input. -/
example :
    jointTotalDegree (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0)
      recursiveEq 3 (Polynomial.C 1)
      (Polynomial.C 0 + Polynomial.X * Polynomial.C 1) (τ := 6)) ≤ 13 := by
  simpa using jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE_and_exponent
    (F := ℚ) (r := 1) 0 1 0 1 recursiveEq 2 1 3 6
    (taylorExponentSufficient_two_mul 1 3) recursiveJet_le recursiveHeight
private abbrev flat (p : MvPolynomial (Fin 2) (Polynomial ℚ)) :=
  (optionEquivRight ℚ (Fin 2)).symm p
private abbrev rect (h v : ℕ) := restrictBidegree (Fin 2) ℚ h v
example : flat (initialJetEquation (Polynomial.C 0) recursiveEq) ∈ rect 1 2 ∧
    flat (initialJetSeparant (Polynomial.C 0) recursiveEq) ∈ rect 1 1 ∧
    flat (initialJetEquation (Polynomial.C 0) recursiveEq) ∈
      restrictCappedBidegree (Fin 2) ℚ 1 1 2 2 ∧
    (initialJetEquation (Polynomial.C 0) recursiveEq).degreeOf (Fin.last 1) ≤ 2 := by
  exact ⟨initialJetEquation_mem_restrictBidegree 0 recursiveEq 1 2 recursiveHeight
    recursiveJet_le, ⟨initialJetSeparant_mem_restrictBidegree 0 recursiveEq 1 2 recursiveHeight
    recursiveJet_le, ⟨initialJetEquation_mem_restrictCappedBidegree 0 recursiveEq 1 2 2
    recursiveHeight recursiveJet_le recursiveDerivativeDegree,
    (degreeOf_initialJetEquation_le _ _).trans recursiveDerivativeDegree⟩⟩⟩

example : ((optionEquivRight ℚ (Fin 2)).symm
      (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) recursiveEq 1
        (Polynomial.C 1) (0 : Polynomial ℚ) (τ := 6)) ∈
      restrictCappedBidegree (Fin 2) ℚ 1 6 7 6 ∧
    (optionEquivRight ℚ (Fin 2)).symm
      (commonTaylorNumeratorOver ℚ (Polynomial.C 0) recursiveEq 6 0) ∈
        restrictCappedBidegree (Fin 2) ℚ 1 6 7 6) ∧
    (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) recursiveEq 1
      (Polynomial.C 1) (0 : Polynomial ℚ) (τ := 6)).degreeOf 1 ≤ 6 := by
  exact ⟨⟨taylorAgreementEquationOver_mem_restrictCappedBidegree 0 1 0 recursiveEq 0 1 2 2 1 6
      (by intro l; omega) (by simp) recursiveHeight (by norm_num) (by norm_num) recursiveJet_le
      recursiveDerivativeDegree,
    commonTaylorNumeratorOver_mem_restrictCappedBidegree 0 recursiveEq 1 2 2 1 6
      (by intro l; omega) recursiveHeight (by norm_num) recursiveJet_le (by norm_num)
      recursiveDerivativeDegree 0⟩,
    (by simpa using (degreeOf_taylorAgreementEquationOver_firstOrder (F := ℚ) (Polynomial.C 0)
      (Polynomial.C 1) (Polynomial.C 0) recursiveEq 2 1 6 (by intro l; omega) (by norm_num)
      recursiveDerivativeDegree))⟩

/-- For `Y₁` at the regular jet `(1, 0)`, the symbolic cuts force coefficient `1` to vanish. -/
example :
    (Polynomial.taylor (0 : ℚ)
      (rationalTaylorPolynomial (0 : ℚ)
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
          (constantDerivativeEquation (Polynomial ℚ)))
        2 (constantJet (F := ℚ)))).coeff 0 = 1 ∧
    (Polynomial.taylor (0 : ℚ)
      (rationalTaylorPolynomial (0 : ℚ)
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
          (constantDerivativeEquation (Polynomial ℚ)))
        2 (constantJet (F := ℚ)))).coeff 1 = 0 := by
  have hS : aeval (constantJet (F := ℚ))
      (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
        (initialJetSeparant (Polynomial.C (0 : ℚ))
          (constantDerivativeEquation (Polynomial ℚ)))) ≠ 0 := by
    rw [map_initialJetSeparant]
    simp [constantDerivativeEquation, initialJetSeparant, separant]
  have hcuts : ∀ l : Fin 2, ¬2 ∣ l.val →
      aeval (constantJet (F := ℚ))
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
          (commonTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ))
            (constantDerivativeEquation (Polynomial ℚ))
            4 l.val)) = 0 := by
    intro l hl
    fin_cases l
    · exact (hl (by decide)).elim
    · rw [map_commonTaylorNumeratorOver, commonTaylorNumeratorOver,
        rationalTaylorNumeratorOver_eq]
      simp [rationalTaylorNumerator, constantDerivativeEquation, initialJetSeparant,
        separant, constantJet]
  have hSparse := sparse_rationalTaylorPolynomial_of_symbolic_cuts
    (φ := Polynomial.aeval (R := ℚ) (0 : ℚ)) (center := Polynomial.C (0 : ℚ))
    (Q := (constantDerivativeEquation (Polynomial ℚ))) (K := 2) (s := 2) (τ := 4)
    (hτ := taylorExponentSufficient_two_mul 1 2) (jet := constantJet (F := ℚ)) hS hcuts
  constructor
  · rw [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix]
    simpa [constantJet] using rationalTaylorCoefficient_initial (0 : ℚ)
      (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
        (constantDerivativeEquation (Polynomial ℚ)))
        (constantJet (F := ℚ)) ⟨0, by omega⟩
  · simpa using hSparse 1 (by decide)

private abbrev padded := commonTaylorNumeratorOver ℚ (Polynomial.C 0) recursiveEq 6 2
/-- Recursive degree bounds for the separant and Taylor numerators of `Y₁² + t Y₀`. -/
example :
    (initialJetSeparant (Polynomial.C 0) recursiveEq).degreeOf (Fin.last 1) ≤
      recursiveEq.degreeOf (some (Fin.last 1)) - 1 ∧
    (rationalTaylorNumeratorOver ℚ (Polynomial.C 0) recursiveEq 2).degreeOf
      (Fin.last 1) ≤ 3 ∧
    (commonTaylorNumeratorOver ℚ (Polynomial.C 0) recursiveEq 6 2).degreeOf
      (Fin.last 1) ≤ 8 ∧
    jointTotalDegree (rationalTaylorNumeratorOver ℚ (Polynomial.C 0) recursiveEq 2) ≤ 3 ∧
    flat padded ∈ rect 6 7 := by
  have hQ := (weightedTotalDegree_indexWeight_eq_jetDegree_one recursiveEq).trans_le
    ((jetDegree_le_total recursiveEq 1).trans recursiveJet_le)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact degreeOf_initialJetSeparant_le (Polynomial.C 0) recursiveEq
  · simpa using degreeOf_rationalTaylorNumeratorOver_le (F := ℚ) (r := 1)
      (Polynomial.C 0) recursiveEq 2 (by norm_num) (by norm_num) hQ 2
  · simpa using degreeOf_commonTaylorNumeratorOver_le (F := ℚ) (r := 1)
      (Polynomial.C 0) recursiveEq 2 3 6 (taylorExponentSufficient_two_mul 1 3)
      (by norm_num) (by norm_num) hQ ⟨2, by decide⟩
  · simpa using jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE 0
      recursiveEq 2 1 recursiveJet_le recursiveHeight 2
  · exact commonTaylorNumeratorOver_mem_restrictBidegree 0 recursiveEq 1 2 3 6
      (taylorExponentSufficient_two_mul 1 3) recursiveHeight
      (by norm_num) recursiveJet_le ⟨2, by decide⟩

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

/-- At the jet of `X²`, the length-three agreement cut accepts `(3, 9)` and rejects `(3, 8)`. -/
example :
    aeval (polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ))
        (taylorAgreementEquation 0 (taylorLinearEquation ℚ) 3 6 3 9) = 0 ∧
      aeval (polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ))
        (taylorAgreementEquation 0 (taylorLinearEquation ℚ) 3 6 3 8) ≠ 0 := by
  have hrec := rationalTaylorPolynomial_polynomialJet 0 (taylorLinearEquation ℚ)
    (Polynomial.X ^ 2) differentialSpecialization_taylorLinearEquation
    (by rw [jetEvaluation_separant_taylorLinearEquation]; norm_num) degree_X_sq_lt_three
    (fun i hi _ ↦ choose_one_ne_zero i hi)
  have hcut := taylorAgreementEquation_eq_zero_iff 0 (taylorLinearEquation ℚ)
    (taylorExponentSufficient_two_mul 1 3) (polynomialJet 0 (Polynomial.X ^ 2))
    (by rw [aeval_initialJetSeparant, jetEvaluation_separant_taylorLinearEquation]; norm_num)
  rw [hcut 3 9, Ne, hcut 3 8, hrec]; norm_num

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

/-- The active formal derivative of `Y₀` is nonzero over `ℚ`. -/
example : separant (zeroJetEquation ℚ 0) 0 ≠ 0 := by
  apply separant_ne_zero
  norm_num [zeroJetEquation, jetDegree]

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
/-! ### Rational recursive and agreement bounds -/
/-- The singleton root `0` of `Y₀ = 0` satisfies recursive, agreement, and gap bounds. -/
example :
    (({zeroJetBoundedRoot} : Finset
      (BoundedSolution (zeroJetEquation ℚ 0) 0)).card : ℚ) ≤
        (jetTotalDegree (zeroJetEquation ℚ 0) : ℚ) * 1 ∧
      (({zeroJetBoundedRoot} : Finset
        (BoundedSolution (zeroJetEquation ℚ 0) 0)).card : ℚ) ≤ 1 ∧
      (({(0 : Polynomial ℚ)} : Finset (Polynomial ℚ)).card : ℚ) ≤ 1 := by
  classical
  let Q : DifferentialPolynomial ℚ 0 := zeroJetEquation ℚ 0
  let roots : Finset (Polynomial ℚ) := {0}
  let domain : Fin 1 ↪ ℚ := ⟨fun _ ↦ 0, fun i j _ ↦ Subsingleton.elim i j⟩
  let accepts : Polynomial ℚ → Prop := fun P ↦
    P.degree < 1 ∧ 1 ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = 0).card
  let boundedRoots : Finset (BoundedSolution Q 0) := {zeroJetBoundedRoot}
  have hQ : Q ≠ 0 := by simp [Q, zeroJetEquation]
  have hcast : ∀ j, JetDegreeCastsNeZero Q j := fun j ↦
    jetDegreeCastsNeZero_of_ringChar (Or.inl ringChar.eq_zero)
  have hdegree : jetTotalDegree Q ≤ 1 := by
    simpa [Q, zeroJetEquation, jetDegree] using jetTotalDegree_le_sum_jetDegree Q
  have hbin : ∀ r, r ≤ 0 → ∀ i, r < i → i < 1 → (i.choose r : ℚ) ≠ 0 := by omega
  have hsolution : ∀ P ∈ roots, differentialSpecialization Q P = 0 := by
    simp [roots, Q, zeroJetEquation]
  have hmul := card_mul_le_jetTotalDegree_mul hQ hcast roots hsolution (left := 1)
    (cost := 1) (by intro _ _ _ _ _ hs _; simpa [roots] using Finset.card_le_card hs)
  have haccepted : ∀ P ∈ roots, accepts P := by simp [roots, accepts, domain]
  have hregular : RegularBranchRatBudget Q 0 accepts 1 := by
    simpa [Q, zeroJetEquation] using regularBranchRatBudget_of_agreement
      (Q := Q) (D := 0) (K := 1) (k := 1) (ν := 1) (n := 1) (A := 1)
      (by norm_num) (by norm_num) domain (fun _ ↦ 0) (by norm_num)
      (by norm_num) (by norm_num) accepts (by intro P; rfl) hdegree hbin
  have hboundedAccepted : ∀ P ∈ boundedRoots, accepts P.polynomial := by
    intro P hP; simp only [boundedRoots, mem_singleton] at hP; subst P
    simp [BoundedSolution.polynomial, accepts, domain, zeroJetBoundedRoot]
  have hrecursive := boundedSolution_recursive_counting_totalJetDegree Q hQ hcast accepts 1
    (by norm_num) boundedRoots hboundedAccepted hregular
  have hsquare := boundedSolution_card_le_sq_totalJetDegree Q hQ hcast accepts 1 1
    (by norm_num) boundedRoots hboundedAccepted hdegree (by simpa using hregular)
  have hagreementBound : (({(0 : Polynomial ℚ)} : Finset (Polynomial ℚ)).card : ℚ) ≤ 1 := by
    let domain2 : Fin 2 ↪ ℚ := ⟨fun i ↦ i, fun i j h ↦ Fin.ext (Nat.cast_injective h)⟩
    have hgap := finite_solutions_card_le_sq_totalJetDegree_of_agreementGap
      (δ := 1 / 2) (n := 2) (A := 2) Q 2 1 1
      (by norm_num) (by norm_num) hQ hdegree domain2 (fun _ ↦ 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
      (fun P ↦ P.degree < 1 ∧
        2 ≤ (Finset.univ.filter fun i ↦ P.eval (domain2 i) = 0).card)
      (by intro P; rfl) roots hsolution (by simp [roots, domain2])
    norm_num [roots] at hgap ⊢
  have hTaylorBound := card_le_of_regular_solutions_agreement (E := AlgebraicClosure ℚ)
    (n := 1) (A := 1) Q 1 1 2 (taylorExponentSufficient_two_mul 0 1)
    (by norm_num) (by norm_num) domain (fun _ ↦ 0) (by norm_num) (by norm_num)
    roots (by simp [roots]) hsolution
    (by simp [roots, Q, zeroJetEquation, separant, differentialSpecialization,
      differentialSpecializationHom]) (hbin 0 (by omega))
    (by intro P hP; simp_all [roots, accepts, domain])
  refine ⟨?_, ?_, ?_⟩
  · simpa [Q, zeroJetEquation, boundedRoots] using hrecursive
  · norm_num [Q, zeroJetEquation, boundedRoots] at hsquare ⊢
  · norm_num [Q, roots, zeroJetEquation, rationalTaylorCutDegreeBound,
      jetTotalDegree] at hagreementBound hmul hTaylorBound ⊢
/-! ### Witness count -/

/-- The one regular bounded solution `0` of `Y₀ = 0` attains the `ZMod 3` witness-count bound. -/
example :
    1 * (Nat.card (ZMod 3) - 0) ≤
      Nat.card (ZMod 3) *
        (jetDegree (zeroJetEquation (ZMod 3) 0) 0 * Nat.card (ZMod 3) ^ 0) := by
  have h := card_mul_sub_le_of_isHighestActiveJet (D := 0) (H := 0)
    (zeroJetEquation (ZMod 3) 0)
    (isHighestActiveJet_of_highestActiveJet_eq_some
      (highestActiveJet_zeroJetEquation (F := ZMod 3)))
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

private theorem aeval_initialJetSeparant_taylorLinearEquation (jet : Fin 2 → ℚ) :
    aeval jet (initialJetSeparant 0 (taylorLinearEquation ℚ)) = 1 := by
  rw [aeval_initialJetSeparant, jetEvaluation_separant_taylorLinearEquation]

private abbrev indexOneHighCutIdeal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {commonTaylorNumerator 0 (taylorLinearEquation ℚ) 4 1}

private theorem highTaylorCutsIdeal_one_two_le :
    highTaylorCutsIdeal 0 (taylorLinearEquation ℚ) 2 1 4 ≤ indexOneHighCutIdeal := by
  rw [highTaylorCutsIdeal_le_iff 0 _]
  intro l hkl hlK
  have hl : l = 1 := by omega
  subst l
  exact Ideal.subset_span (by simp)

/-- For `y' = 2x`, one agreement point and the index-1 high cut determine the regular jet
in the length-two Taylor chart, and the locus contains the zero jet. -/
example :
    Nonempty (regularAgreementCutLocus indexOneHighCutIdeal 0 (taylorLinearEquation ℚ) 2 4
      (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ : Fin 1 ↦ (0 : ℚ))) ∧
    (regularAgreementCutLocus indexOneHighCutIdeal 0 (taylorLinearEquation ℚ) 2 4
      (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ : Fin 1 ↦ (0 : ℚ))).Subsingleton := by
  let jet := zeroJetVector (F := ℚ) 2
  have hS : aeval jet (initialJetSeparant 0 (taylorLinearEquation ℚ)) ≠ 0 := by
    rw [aeval_initialJetSeparant_taylorLinearEquation]
    norm_num
  have hgen : aeval jet (commonTaylorNumerator 0 (taylorLinearEquation ℚ) 4 1) = 0 := by
    have hc : rationalTaylorCoefficient 0 (taylorLinearEquation ℚ) jet 1 = 0 := by
      simpa [zeroJetVector, jet] using rationalTaylorCoefficient_initial 0
        (taylorLinearEquation ℚ) jet ⟨1, by omega⟩
    rw [aeval_commonTaylorNumerator (center := (0 : ℚ)) (taylorLinearEquation ℚ)
      jet (τ := 4) (l := 1) (by norm_num) hS]
    simp [hc]
  have hjet : jet ∈ zeroLocus ℚ indexOneHighCutIdeal := by
    simpa [indexOneHighCutIdeal, zeroLocus_span] using hgen
  have hcut : aeval jet
      (taylorAgreementEquation 0 (taylorLinearEquation ℚ) 2 4 0 0) = 0 := by
    have hrec : (rationalTaylorPolynomial 0 (taylorLinearEquation ℚ) 2 jet).eval 0 = 0 := by
      rw [eval_rationalTaylorPolynomial]
      simp [rationalTaylorCoefficient_initial, jet, zeroJetVector]
    rw [aeval_taylorAgreementEquation 0 (taylorLinearEquation ℚ)
      (taylorExponentSufficient_two_mul 1 2) jet hS]
    rw [hrec]
    simp
  refine ⟨⟨jet, ⟨hjet, hS, fun _ ↦ hcut⟩⟩, ?_⟩
  exact regularAgreementCutLocus_subsingleton 0 (taylorLinearEquation ℚ)
    (taylorExponentSufficient_two_mul 1 2) (by norm_num) highTaylorCutsIdeal_one_two_le
    (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ : Fin 1 ↦ (0 : ℚ))
    (by intro i j _; exact Subsingleton.elim i j) (by norm_num)

private theorem commonTaylorNumerator_zeroJet_constantDerivativeEquation {F : Type*} [Field F] :
    aeval (zeroJetVector (F := F) 2)
      (commonTaylorNumerator 0 (constantDerivativeEquation F) 4 1) = 0 := by
  have hS : aeval (zeroJetVector (F := F) 2)
      (initialJetSeparant 0 (constantDerivativeEquation F)) ≠ 0 := by
    simp [constantDerivativeEquation, initialJetSeparant, separant]
  have hc : rationalTaylorCoefficient 0 (constantDerivativeEquation F)
      (zeroJetVector (F := F) 2) 1 = 0 := by
    simpa [zeroJetVector] using rationalTaylorCoefficient_initial 0
      (constantDerivativeEquation F) (zeroJetVector (F := F) 2) ⟨1, by omega⟩
  rw [aeval_commonTaylorNumerator (center := (0 : F)) (constantDerivativeEquation F)
    (zeroJetVector (F := F) 2) (τ := 4) (l := 1) (by omega) hS]
  simp [hc]

/-- The zero jet of `Y₁` belongs to a prime component after the nonempty high cut at index `1`. -/
example : ∃ P ∈ highTaylorPrimeFamily 0 (constantDerivativeEquation ℚ) 2 1 4,
    zeroJetVector (F := ℚ) 2 ∈ zeroLocus ℚ P := by
  exact exists_mem_highTaylorPrimeFamily_of_regular 0 (constantDerivativeEquation ℚ)
    (K := 2) (k := 1) (τ := 4) (zeroJetVector (F := ℚ) 2)
    (by simp [initialJetEquation, constantDerivativeEquation, zeroJetVector])
    (by simp [initialJetSeparant, constantDerivativeEquation, separant])
    (by
      intro l hkl hlK
      have hl : l = 1 := by omega
      subst l
      exact commonTaylorNumerator_zeroJet_constantDerivativeEquation)
/-- The zero jet satisfies the capped bound for `Y₁ = 0` and both degree bounds. -/
example :
    (1 : ℚ) ≤ (cappedDegreeMixedVolume 1 1 4 1 : ℚ) ∧
    (commonTaylorNumerator 0 (constantDerivativeEquation ℚ) 4 0).degreeOf 1 ≤ 0 ∧
    (taylorAgreementEquation 0 (constantDerivativeEquation ℚ) 2 4 0 0).degreeOf 1 ≤ 1 := by
  let F := AlgebraicClosure ℚ
  let Q : DifferentialPolynomial F 1 := constantDerivativeEquation F
  let jet : Fin 2 → F := zeroJetVector 2
  let domain : Fin 1 ↪ F := ⟨fun _ ↦ 0, by intro i j _; exact Subsingleton.elim i j⟩
  let received : Fin 1 → F := fun _ ↦ 0
  let S : Finset (Fin 2 → F) := {jet}
  have hS : ∀ jet' ∈ S, aeval jet' (initialJetEquation 0 Q) = 0 ∧
      aeval jet' (initialJetSeparant 0 Q) ≠ 0 ∧
      ∀ l : {l : Fin 2 // 1 ≤ l.val},
        aeval jet' (commonTaylorNumerator 0 Q 4 l.val) = 0 := by
    intro jet' hjet
    obtain rfl := Finset.mem_singleton.mp hjet
    refine ⟨?_, ?_, ?_⟩
    · simp [Q, jet, initialJetEquation, constantDerivativeEquation, zeroJetVector]
    · simp [Q, jet, initialJetSeparant, constantDerivativeEquation, separant]
    · intro l
      simpa [show l.val = 1 by omega] using
        commonTaylorNumerator_zeroJet_constantDerivativeEquation
  have hA : ∀ jet' ∈ S, 1 ≤
      {i : Fin 1 | aeval jet'
        (taylorAgreementEquation 0 Q 2 4 (domain i) (received i)) = 0}.ncard := by
    intro jet' hjet
    obtain rfl := Finset.mem_singleton.mp hjet
    have hsep : aeval jet (initialJetSeparant 0 Q) ≠ 0 := by
      simp [Q, jet, initialJetSeparant, constantDerivativeEquation, separant]
    have hcut (i : Fin 1) : aeval jet
        (taylorAgreementEquation 0 Q 2 4 (domain i) (received i)) = 0 := by
      rw [aeval_taylorAgreementEquation 0 Q (taylorExponentSufficient_two_mul 1 2)
        jet hsep (domain i) (received i)]
      simp [eval_rationalTaylorPolynomial, rationalTaylorCoefficient_initial,
        Q, jet, domain, received, zeroJetVector]
    simp [hcut]
  have hCapped := card_le_of_firstOrderHighTaylorCuts_of_agreement_capped
    (center := (0 : F)) Q (K := 2) (k := 1) (τ := 4) (j := 1) (r := 1) (b := 4)
    (hτ := taylorExponentSufficient_two_mul 1 2) (hK := by decide) (hb := by decide)
    (hc := by decide) (hjb := by decide) (hrc := by decide) (hchart := by decide)
    (hr := by decide) (hjet := by simpa [Q] using jetTotalDegree_constantDerivativeEquation_le)
    (hderiv := by simp [Q, constantDerivativeEquation]) (domain := domain)
    (received := received) (hkA := by decide) (hAn := by decide) (S := S) (hS := hS)
    (hA := hA)
  refine ⟨?_, ?_, ?_⟩
  · norm_num [S, jet, cappedDegreeMixedVolume] at hCapped ⊢
  · simpa using degreeOf_commonTaylorNumerator_firstOrder_le
      (center := (0 : ℚ)) (Q := constantDerivativeEquation ℚ) 1 2 4
      (taylorExponentSufficient_two_mul 1 2) (by decide)
      (by simp [constantDerivativeEquation]) 0
  · simpa using degreeOf_taylorAgreementEquation_firstOrder_le
      (center := (0 : ℚ)) (Q := constantDerivativeEquation ℚ) 1 2 4
      (taylorExponentSufficient_two_mul 1 2) (by decide)
      (by simp [constantDerivativeEquation]) 0 0
/-! ### Frobenius flattening -/

private abbrev frobeniusInseparableEquation :
    DifferentialPolynomial (Polynomial (ZMod 2)) 0 := X none - X (some 0) ^ 2

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
  rw [expand_differentialSpecialization_map_eq_eval₂_flatten]
  simp only [Polynomial.expand_X, Nat.reduceAdd, Fin.isValue, map_add,
    ordinaryFlatten_root, ordinaryFlatten_coeff_X, eval₂_add, eval₂_X,
    Option.elim_none, Option.elim_some, add_right_inj]
  rw [show (1 : Fin 2) = Fin.succ 0 by norm_num, Fin.cases_succ]

/-- Over `ZMod 2`, `X - Y₀ ^ 2` is the irreducible inseparable equation `Y₀ ^ 2 - X`;
Frobenius contraction lowers its root degree. -/
example :
      ∃ e : ℕ, ∃ H : DifferentialPolynomial (Polynomial (ZMod 2)) 0,
      Irreducible H ∧
      MvPolynomial.pderiv (some 0) H ≠ 0 ∧
      H.degreeOf (some 0) * (2 ^ e) =
        frobeniusInseparableEquation.degreeOf (some 0) ∧
      H.degreeOf none ≤ frobeniusInseparableEquation.degreeOf none ∧
      MvPolynomial.CoeffNatDegreeLE H 0 ∧
      ∀ (P : Polynomial (ZMod 2)) (w : ZMod 2),
        differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom (w ^ (2 ^ e)))
              frobeniusInseparableEquation) P = 0 →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom w) H)
              (Polynomial.expand (ZMod 2) (2 ^ e) P) = 0 := by
  apply exists_frobeniusEquation (E := ZMod 2) 2
    (Q := frobeniusInseparableEquation)
  · have hlt :
        (X none : DifferentialPolynomial (Polynomial (ZMod 2)) 0).degreeOf (some 0) <
          (-(X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0)).degreeOf
            (some 0) := by
      rw [MvPolynomial.degreeOf_neg]
      simp [MvPolynomial.degreeOf_X]
    have hsum :
        (X none - X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0).degreeOf
            (some (0 : Fin 1)) =
          (-(X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0)).degreeOf
            (some (0 : Fin 1)) := by
      calc
        _ = (X none + -(X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0)).degreeOf
              (some (0 : Fin 1)) := by simp [sub_eq_add_neg]
        _ = (-(X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0) + X none).degreeOf
              (some (0 : Fin 1)) := congrArg (degreeOf (some (0 : Fin 1))) (add_comm _ _)
        _ = _ := degreeOf_add_eq_of_degreeOf_lt (p := -(X (some 0) ^ 2)) (q := X none) hlt
    rw [frobeniusInseparableEquation]
    exact (by simp [MvPolynomial.degreeOf_neg] :
      0 < (-(X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0)).degreeOf
        (some (0 : Fin 1))).trans_eq hsum.symm
  · have hmap : optionEquivLeft (Polynomial (ZMod 2)) (Fin 1)
        frobeniusInseparableEquation =
          Polynomial.X - Polynomial.C
            (MvPolynomial.X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) (Polynomial (ZMod 2))) := by
      rw [frobeniusInseparableEquation, map_sub, map_pow, optionEquivLeft_X_some,
        optionEquivLeft_X_none]
      rw [← Polynomial.C_pow]
    have hpoly : Irreducible (optionEquivLeft (Polynomial (ZMod 2)) (Fin 1)
        frobeniusInseparableEquation) := by
      rw [hmap]
      exact Polynomial.irreducible_X_sub_C _
    exact (MulEquiv.irreducible_iff
      (x := frobeniusInseparableEquation)
      (optionEquivLeft (Polynomial (ZMod 2)) (Fin 1)).toMulEquiv).mp hpoly
  · have hpower : MvPolynomial.CoeffNatDegreeLE
        (X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0) 0 := by
      simpa using (MvPolynomial.CoeffNatDegreeLE.pow
        (MvPolynomial.coeffNatDegreeLE_X (R := ZMod 2) (some 0)) 2)
    change MvPolynomial.CoeffNatDegreeLE
      (X none + -(X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0)) 0
    have hminus : MvPolynomial.CoeffNatDegreeLE
        (-(X (some 0) ^ 2 : DifferentialPolynomial (Polynomial (ZMod 2)) 0)) 0 := by
      intro m
      simpa only [MvPolynomial.coeff_neg, Polynomial.natDegree_neg] using hpower m
    exact MvPolynomial.CoeffNatDegreeLE.add
      (MvPolynomial.coeffNatDegreeLE_X (R := ZMod 2) none) hminus

private abbrev frobeniusSquareEquation :
    DifferentialPolynomial (Polynomial (ZMod 2)) 0 := X (some 0) ^ 2 - X none ^ 2

/-- The nonzero root `X` of `Y₀ ^ 2 - X ^ 2` transports to a root of the contracted equation. -/
example :
    differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom ((0 : ZMod 2) ^ (2 ^ 1)))
        frobeniusSquareEquation)
      Polynomial.X = 0 ∧
    differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom (0 : ZMod 2))
        (ordinaryUnflatten (ZMod 2)
          (inverseFrobeniusTwist 2 1
            (MvPolynomial.X none - MvPolynomial.X (some (0 : Fin 2)) ^ 2 :
              MvPolynomial (Option (Fin 2)) (ZMod 2)))))
      (Polynomial.expand (ZMod 2) (2 ^ 1) Polynomial.X) = 0 := by
  have hflat : ordinaryFlatten (ZMod 2) frobeniusSquareEquation =
      (MvPolynomial.X none : MvPolynomial (Option (Fin 2)) (ZMod 2)) ^ 2 -
        MvPolynomial.X (some (0 : Fin 2)) ^ 2 := by
    simp [frobeniusSquareEquation]
  have hroot : rootExpansion (2 ^ 1)
      (MvPolynomial.X none - MvPolynomial.X (some (0 : Fin 2)) ^ 2 :
        MvPolynomial (Option (Fin 2)) (ZMod 2)) =
      ordinaryFlatten (ZMod 2) frobeniusSquareEquation := by
    rw [hflat]
    norm_num only [pow_one]
    simp [rootExpansion, optionEquivLeft_X_none, optionEquivLeft_X_some]
  have hQ : differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom ((0 : ZMod 2) ^ (2 ^ 1)))
        frobeniusSquareEquation)
      Polynomial.X = 0 := by
    norm_num only [pow_one, zero_pow (by decide : 2 ≠ 0)]
    simp [frobeniusSquareEquation, differentialSpecialization,
      differentialSpecializationHom]
  exact ⟨hQ, frobeniusSpecialization_eq_zero 2 1 frobeniusSquareEquation
    (MvPolynomial.X none - MvPolynomial.X (some (0 : Fin 2)) ^ 2 :
      MvPolynomial (Option (Fin 2)) (ZMod 2)) hroot Polynomial.X 0 hQ⟩

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

example := (frobeniusExpansion_satisfies_jointTaylorCuts (E := ZMod 2) (X (some 0))
  0 0 0 2 1 2 4 (taylorExponentSufficient_two_mul 0 2)
  (by simpa using (WithBot.bot_lt_coe (2 : ℕ))) (by simp [challengeSpecialization])
  (by simp [initialJetSeparant, challengeSpecialization, separant])).2.2.2 (1 : ZMod 2)
  (Polynomial.X ^ 3 + Polynomial.C (1 : ZMod 2))

/-! ### Ordinary root presentations -/

/-- For the concrete irreducible equation `Y₀` over `ℚ[X]`, the exceptional set is empty. -/
example :
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 0 ∧
      ∀ w ∉ exceptional, ∀ P : Polynomial ℚ,
        differentialSpecialization
          (challengeSpecialization (zeroJetEquation (Polynomial ℚ) 0) w) P = 0 →
          differentialSpecialization
            (separant
              (challengeSpecialization (zeroJetEquation (Polynomial ℚ) 0) w) (Fin.last 0))
            P ≠ 0 := by
  have hirr : Irreducible (zeroJetEquation (Polynomial ℚ) 0) := by
    apply MvPolynomial.irreducible_of_totalDegree_eq_one
    · simp [zeroJetEquation]
    · intro c hc
      apply isUnit_of_dvd_one
      have h := hc (Finsupp.single (some (0 : Fin 1)) 1)
      simpa [zeroJetEquation] using h
  have hpos : 0 < (zeroJetEquation (Polynomial ℚ) 0).degreeOf (some 0) := by
    simp [zeroJetEquation]
  have hder : MvPolynomial.pderiv (some 0) (zeroJetEquation (Polynomial ℚ) 0) ≠ 0 := by
    simp [zeroJetEquation]
  have hheight : MvPolynomial.CoeffNatDegreeLE (zeroJetEquation (Polynomial ℚ) 0) 0 := by
    simpa [zeroJetEquation] using
      MvPolynomial.coeffNatDegreeLE_X (R := ℚ) (σ := JetVariable 0) (some 0)
  simpa [zeroJetEquation] using
    exists_exceptional_ordinary_separant hirr hpos hder hheight

/-! ### Taylor chart coefficient extension -/

/-- A nonempty rational solution family has jets in a common Taylor chart. -/
example : ∃ _center : ℚ, ∃ J : Finset (Fin 1 → ℚ), J.card = 1 := by
  obtain ⟨center, J, hcard, _⟩ := exists_regular_solution_jet_family_of_exponent
    (f := RingHom.id ℚ) (Q := zeroJetEquation ℚ 0) (K := 1) (k := 1) (τ := 2)
    (taylorExponentSufficient_two_mul 0 1) (by norm_num) {0} (A := 1)
    (domain := fun _ : Fin 1 ↦ 0) (received := fun _ ↦ 0)
    (by simp) (by simp [zeroJetEquation, differentialSpecialization,
      differentialSpecializationHom])
    (by simp [zeroJetEquation, separant, differentialSpecialization,
      differentialSpecializationHom]) (by simp) (by simp)
  exact ⟨center, J, by simpa using hcard⟩

/-- A nonempty regular family over `ZMod 2` has a common center in its algebraic closure. -/
example :
    let Q : DifferentialPolynomial (ZMod 2) 0 :=
      (MvPolynomial.X none ^ 2 - MvPolynomial.X none) * MvPolynomial.X (some 0)
    ∃ center : AlgebraicClosure (ZMod 2),
      ∀ P ∈ ({(0 : Polynomial (ZMod 2))} : Finset (Polynomial (ZMod 2))),
        jetEvaluation
          (separant
            (MvPolynomial.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))) Q) 0)
          center
          (polynomialJet center
            (P.map (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))))) ≠ 0 := by
  intro Q
  have hspec : differentialSpecialization (separant Q 0) (0 : Polynomial (ZMod 2)) =
      (Polynomial.X ^ 2 - Polynomial.X : Polynomial (ZMod 2)) := by
    simp [Q, separant, differentialSpecialization, differentialSpecializationHom]
  have hspec_ne : differentialSpecialization (separant Q 0) (0 : Polynomial (ZMod 2)) ≠ 0 := by
    rw [hspec]
    intro h
    have hc := congrArg (fun P : Polynomial (ZMod 2) ↦ P.coeff 2) h
    norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  have hregular : ∀ P ∈ ({(0 : Polynomial (ZMod 2))} : Finset (Polynomial (ZMod 2))),
      differentialSpecialization (separant Q 0) P ≠ 0 := by
    intro P hP
    have hP0 : P = 0 := Finset.mem_singleton.mp hP
    subst P
    exact hspec_ne
  let f : ZMod 2 →+* AlgebraicClosure (ZMod 2) := algebraMap _ _
  exact exists_forall_jetEvaluation_ne_zero_map f f.injective Q {0} 0 hregular

/-- Two distinct regular equations admit a common Taylor center. -/
example :
    let D : Fin 2 → DifferentialPolynomial ℚ 0 :=
      fun i ↦ C (if i = 0 then (1 : ℚ) else 2)
    D 0 ≠ D 1 ∧ ∃ center : ℚ, ∀ i ∈ Finset.univ,
      jetEvaluation (D i) center (polynomialJet center (0 : Polynomial ℚ)) ≠ 0 := by
  intro D
  refine ⟨?_, exists_forall_jetEvaluation_ne_zero_of_family univ D (fun _ ↦ 0) ?_⟩
  · change C 1 ≠ C 2
    exact mt (MvPolynomial.C_inj ℚ 1 2).mp (by norm_num)
  · intro i hi
    fin_cases i <;> simp [D, differentialSpecialization, differentialSpecializationHom]

example :
    ∃ exceptional : Finset ℚ, exceptional.card ≤ 1 ∧ 0 ∈ exceptional := by
  let Q : DifferentialPolynomial (Polynomial ℚ) 0 := MvPolynomial.C Polynomial.X
  have hheight := MvPolynomial.coeffNatDegreeLE_C
    (σ := JetVariable 0) (R := ℚ) (p := Polynomial.X) (h := 1) (by simp)
  obtain ⟨exceptional, hcard, hregular⟩ :=
    exists_exceptional_jet_independent_content Q (by simp [Q]) (by simp [Q]) hheight
  refine ⟨exceptional, hcard, ?_⟩
  by_contra hzero
  have hspec : challengeSpecialization Q 0 = 0 := by simp [Q, challengeSpecialization]
  exact hregular 0 hzero 0 (by rw [hspec]; rfl)

/-! ### Retained curve equations -/

private abbrev retainedCurveEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  C (Polynomial.X + 1) * X (some 1) ^ 2 + X none

example :
    (curveJetView (challengeRetainingRootFirst retainedCurveEquation)).totalDegree =
      jetTotalDegree retainedCurveEquation := by
  rw [curveJetView_totalDegree, fromFlattenedRootFirst_rootFirstChallenge]

example :
    (positiveCurveEquation retainedCurveEquation).degreeOf (some 1) ≤
      retainedCurveEquation.degreeOf (some 1) ∧
    jetTotalDegree (positiveCurveEquation retainedCurveEquation) ≤
      jetTotalDegree retainedCurveEquation ∧
    CoeffNatDegreeLE (positiveCurveEquation retainedCurveEquation)
      (degreeOf (some (some 1))
        (radicalPrimPart none (challengeRetainingRootFirst retainedCurveEquation))) := by
  exact ⟨positiveCurveEquation_yOneDegree_le retainedCurveEquation,
    positiveCurveEquation_jetTotalDegree_le retainedCurveEquation,
    positiveCurveEquation_coeffNatDegreeLE retainedCurveEquation⟩
end
end PolynomialDifferential

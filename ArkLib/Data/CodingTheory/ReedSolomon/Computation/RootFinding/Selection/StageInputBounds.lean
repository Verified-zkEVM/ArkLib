/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsBounds
/-!
# Uniform stage polynomials from initial sizes

Exponent mass already includes every factor cell and every term header. Thus the scalar
interpreter is bounded without inspecting the visited equation or its values. The numerical
bounds below use only addition, multiplication and fixed-degree matrix budgets; their degree
is independent of the derivative order. In particular no additional alphabet power occurs.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.StageRootsMachine

open Polynomial Matrix MvPolynomial PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem factorsSteps_mass (n : ℕ) (fs : List (ℕ × ℕ)) :
    EvaluationMachine.factorsSteps n fs ≤
      (n + 3) * fs.length + (fs.map Prod.snd).sum := by
  induction fs with
  | nil => simp [EvaluationMachine.factorsSteps]
  | cons p fs ih =>
    simp only [EvaluationMachine.factorsSteps, List.length_cons, List.map_cons, List.sum_cons]
    have h := Nat.min_le_right p.1 n
    nlinarith

omit [Field F] [DecidableEq F] in
/-- A value-independent scalar step bound in numerical exponent mass. -/
theorem evaluationSteps_mass (n : ℕ) (ts : List (Term F)) :
    EvaluationMachine.evaluationSteps n ts ≤
      (n + 3) * PartialDerivativeMachine.inputMass ts + 1 := by
  induction ts with
  | nil => simp [EvaluationMachine.evaluationSteps, PartialDerivativeMachine.inputMass]
  | cons t ts ih =>
    have h := factorsSteps_mass n t.2
    have hh : EvaluationMachine.factorsSteps n t.2 + 2 ≤
        (n + 3) * PartialDerivativeMachine.factorMass t.2 := by
      unfold PartialDerivativeMachine.factorMass
      nlinarith only [h, Nat.zero_le (t.2.map Prod.snd).sum,
        Nat.zero_le t.2.length, Nat.zero_le n, Nat.zero_le (n * (t.2.map Prod.snd).sum),
        Nat.zero_le (n * t.2.length)]
    calc
      _ ≤ (n + 3) * PartialDerivativeMachine.factorMass t.2 +
          ((n + 3) * PartialDerivativeMachine.inputMass ts + 1) := Nat.add_le_add hh ih
      _ = _ := by
        simp only [PartialDerivativeMachine.inputMass, List.map_cons, List.sum_cons]
        ring

/-- Uniform fuel for one sample at initial mass M and maximum order d. -/
def sampleFuelBound (D d M : ℕ) : ℕ :=
  (D + 2) * (2 * (d + 1) + 3) + (d + 5) * M + 6

/-- Full primitive sample work, including scalar and jet dispatch. -/
def sampleWorkBound (D d M : ℕ) : ℕ :=
  43 * (D + 2) * (d + 1) + 12 * ((d + 5) * M + 1) + 23

/-- Uniform batch fuel computed from sample count and initial sizes. -/
def batchFuelBound (D d M n : ℕ) : ℕ := n * (sampleFuelBound D d M + 6) + 3

/-- Uniform batch primitive work, including all sample wrappers. -/
def batchWorkBound (D d M n : ℕ) : ℕ :=
  33 * (n + 1) * (sampleWorkBound D d M + sampleFuelBound D d M + 1)

omit [DecidableEq F] in
private theorem sample_bounds (input : ResidualSampleMachine.Input F) (D d M : ℕ)
    (hc : input.coefficients.length ≤ D + 1) (hd : input.order ≤ d)
    (hm : PartialDerivativeMachine.inputMass input.terms ≤ M) :
    ResidualSampleMachine.fuel input ≤ sampleFuelBound D d M ∧
      (ResidualSampleMachine.cost input).total ≤ sampleWorkBound D d M := by
  have he := evaluationSteps_mass (input.order + 2) input.terms
  have he' : ResidualSampleMachine.scalarFuel input ≤ (d + 5) * M + 1 := by
    refine he.trans ?_
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) hm) 1
  constructor
  · unfold ResidualSampleMachine.fuel ResidualSampleMachine.jetFuel sampleFuelBound
    have hj : (input.coefficients.length + 1) * (2 * (input.order + 1) + 3) ≤
        (D + 2) * (2 * (d + 1) + 3) := Nat.mul_le_mul (by omega) (by omega)
    omega
  · refine (ResidualSampleMachine.cost_total_le input).trans ?_
    unfold sampleWorkBound
    have hj := Nat.mul_le_mul (Nat.mul_le_mul_left 43
      (show input.coefficients.length + 1 ≤ D + 2 by omega)) (Nat.add_le_add_right hd 1)
    omega

omit [DecidableEq F] in
/-- Coefficient width, derivative order and exponent mass bound the actual batch budgets. -/
theorem batch_bounds (input : ResidualBatchMachine.Input F) (D d M n : ℕ)
    (hc : input.coefficients.length ≤ D + 1) (hd : input.order ≤ d)
    (hm : PartialDerivativeMachine.inputMass input.terms ≤ M) :
    ResidualBatchMachine.fuel input n ≤ batchFuelBound D d M n ∧
      (ResidualBatchMachine.cost input n).total ≤ batchWorkBound D d M n := by
  obtain ⟨hf, hw⟩ := sample_bounds (ResidualBatchMachine.sampleInput input 0) D d M hc hd hm
  change ResidualBatchMachine.singleFuel input ≤ sampleFuelBound D d M at hf
  change (ResidualBatchMachine.singleCost input).total ≤ sampleWorkBound D d M at hw
  constructor
  · unfold ResidualBatchMachine.fuel batchFuelBound
    gcongr
  · refine (ResidualBatchMachine.cost_total_le input n).trans ?_
    unfold batchWorkBound
    gcongr

/-- Uniform numerical system fuel. -/
def systemFuelBound (D d M L n : ℕ) : ℕ := batchFuelBound D d M n +
  VandermondeMachine.constructionFuel L n + ForwardEchelonMachine.budget n L + 4

/-- Uniform numerical system work. -/
def systemWorkBound (D d M L n : ℕ) : ℕ := batchWorkBound D d M n +
  72 * (n + 1) * (L + 1) + 4 * ForwardEchelonMachine.budget n L +
  3 * (batchFuelBound D d M n + VandermondeMachine.constructionFuel L n) + 19

/-- Uniform numerical residual-coefficient fuel. -/
def recoveryFuelBound (D d M L n : ℕ) : ℕ := systemFuelBound D d M L n +
  ResidualCoefficientMachine.solveBudget L n + L + 5

/-- Uniform numerical residual-coefficient work. -/
def recoveryWorkBound (D d M L n : ℕ) : ℕ := systemWorkBound D d M L n +
  3 * systemFuelBound D d M L n + 4 * ResidualCoefficientMachine.solveBudget L n + 9 * L + 23

/-- Uniform root fuel; the decreasing active order is bounded by using D lift stages. -/
def rootFuelBound (D d M L n : ℕ) : ℕ :=
  D * (2 * recoveryFuelBound D d M L n + 6 * (D + 1) + 30) + 3 +
    (batchFuelBound D d M n + n + 4 + RegularRootMachine.shiftFuel D + 3) + 2

/-- Uniform root work, including all lift, residual-check and translation wrappers. -/
def rootWorkBound (D d M L n : ℕ) : ℕ :=
  D * (2 * recoveryWorkBound D d M L n + 6 * recoveryFuelBound D d M L n +
    40 * (D + 2) + 14 * (D + 1) + 100 +
    3 * (2 * recoveryFuelBound D d M L n + 4 * (D + 1) + 20) +
    40 * (D + 2) + 40) + 16 +
    3 * (D * (2 * recoveryFuelBound D d M L n + 6 * (D + 1) + 30) + 3) +
    (batchWorkBound D d M n + 3 * batchFuelBound D d M n + 6 * n + 15 +
    3 * (batchFuelBound D d M n + n + 4) + 160 * (D + 2) ^ 2 +
    3 * RegularRootMachine.shiftFuel D + 13) + 10

omit [DecidableEq F] in
/-- Both complete root budgets are dominated by the uniform initial-size polynomials. -/
theorem root_bounds (input : RegularRootMachine.Input F) (D d M L n : ℕ)
    (hc : input.coefficients.length = D + 1) (hd : input.order ≤ d)
    (hm : PartialDerivativeMachine.inputMass input.terms ≤ M) :
    RegularRootMachine.fuel input D L n ≤ rootFuelBound D d M L n ∧
      RegularRootMachine.workBound input D L n ≤ rootWorkBound D d M L n := by
  obtain ⟨hf, hw⟩ := batch_bounds input D d M n hc.le hd hm
  have hsf : ResidualSystemMachine.fuel input L n ≤ systemFuelBound D d M L n := by
    unfold ResidualSystemMachine.fuel systemFuelBound
    omega
  have hsw : ResidualSystemMachine.workBound input L n ≤ systemWorkBound D d M L n := by
    unfold ResidualSystemMachine.workBound systemWorkBound
    omega
  have hrf : ResidualCoefficientMachine.fuel input L n ≤ recoveryFuelBound D d M L n := by
    unfold ResidualCoefficientMachine.fuel recoveryFuelBound
    omega
  have hrw : ResidualCoefficientMachine.workBound input L n ≤ recoveryWorkBound D d M L n := by
    unfold ResidualCoefficientMachine.workBound recoveryWorkBound
    omega
  have hlf : RegularLiftMachine.stageFuel input D L n ≤
      2 * recoveryFuelBound D d M L n + 6 * (D + 1) + 30 := by
    unfold RegularLiftMachine.stageFuel DirectCoefficientMachine.fuel
    rw [hc]
    omega
  have hlw : RegularLiftMachine.stageWork input D L n ≤
      2 * recoveryWorkBound D d M L n + 6 * recoveryFuelBound D d M L n +
      40 * (D + 2) + 14 * (D + 1) + 100 +
      3 * (2 * recoveryFuelBound D d M L n + 4 * (D + 1) + 20) +
      40 * (D + 2) + 40 := by
    unfold RegularLiftMachine.stageWork DirectCoefficientMachine.workBound
      DirectCoefficientMachine.fuel
    rw [hc]
    omega
  have hliftf : RegularLiftMachine.fuel input D L n ≤
      D * (2 * recoveryFuelBound D d M L n + 6 * (D + 1) + 30) + 3 := by
    unfold RegularLiftMachine.fuel
    gcongr
    exact Nat.sub_le _ _
  constructor
  · unfold RegularRootMachine.fuel RegularRootMachine.suffixFuel ResidualZeroMachine.fuel
      rootFuelBound
    omega
  · unfold RegularRootMachine.workBound RegularRootMachine.suffixWork RegularRootMachine.zeroWork
      ResidualZeroMachine.fuel rootWorkBound
    have hw' := Nat.mul_le_mul (Nat.sub_le D input.order) hlw
    unfold RegularLiftMachine.workBound
    omega

/-- Uniform per-stage fuel factor: a polynomial of absolute degree at most four. -/
def uniformFuel (D d M L n : ℕ) : ℕ := rootFuelBound D d M L n + D + 11 + 32 * (d + 2) + 20

/-- Uniform per-stage work factor, with the same absolute degree bound. -/
def uniformWork (D d M L n : ℕ) : ℕ := rootWorkBound D d M L n +
  3 * rootFuelBound D d M L n + 40 * (D + d + 2) + 3 * (D + 5) + 30 +
  6 * (rootFuelBound D d M L n + D + 11) + 704 * (d + 2) + 200

/-- Ordered-chain stage factors are uniformly bounded by the original input mass and order. -/
theorem stage_polynomials {d : ℕ} (input : Input F) (D L n : ℕ)
    {ts : List (Term F)} {Q : DifferentialPolynomial F d} {stages : List (Stage F)}
    (hchain : SeparantChainRefinement.OrderedChain ts Q stages) (stage : Stage F)
    (hs : stage ∈ stages) :
    fuelPolynomial input D L n stage ≤
      uniformFuel D d (PartialDerivativeMachine.inputMass ts) L n ∧
    workPolynomial input D L n stage ≤
      uniformWork D d (PartialDerivativeMachine.inputMass ts) L n := by
  cases hsel : stage.selected with
  | none => simp [fuelPolynomial, workPolynomial, hsel, uniformFuel, uniformWork]
  | some pair =>
    obtain ⟨i, e⟩ := pair
    have hd := chain_orders hchain stage hs i e hsel
    obtain ⟨_, hm⟩ := hchain.sizes stage hs
    obtain ⟨hf, hw⟩ := root_bounds
      (JetRootsMachine.budgetInput
        (CenterRootsMachine.centerInput (centerInput input stage (i - 1)) 0) D)
      D d (PartialDerivativeMachine.inputMass ts) L n (by simp [JetRootsMachine.budgetInput,
        JetRootsMachine.rootInput]) hd hm
    simp only [fuelPolynomial, workPolynomial, hsel, JetRootsMachine.itemFuel,
      JetRootsMachine.itemWork, uniformFuel, uniformWork]
    dsimp only [CenterRootsMachine.centerInput, centerInput] at *
    constructor <;> omega

/-- A concrete degree-four majorant, independent of derivative order in its exponent. -/
def sizePolynomial (S : ℕ) : ℕ :=
  55978 * S ^ 4 + 133382 * S ^ 3 + 95665 * S ^ 2 + 25446 * S + 7565

/-- Expanding the diagonal numerical budgets gives the displayed absolute-degree polynomial. -/
theorem sizePolynomial_eq (S : ℕ) :
    uniformFuel S S S S S + uniformWork S S S S S = sizePolynomial S := by
  unfold uniformFuel uniformWork rootFuelBound rootWorkBound recoveryFuelBound
    recoveryWorkBound systemFuelBound systemWorkBound batchFuelBound batchWorkBound
    sampleFuelBound sampleWorkBound RegularRootMachine.shiftFuel
    VandermondeMachine.constructionFuel ForwardEchelonMachine.budget
    ForwardEchelonMachine.stageBudget ResidualCoefficientMachine.solveBudget
    BackSubstitutionMachine.budget sizePolynomial
  ring

/-- Uniform stage fuel and work together are bounded by a degree-four size polynomial. -/
theorem uniform_sum_le (D d M L n S : ℕ) (hD : D ≤ S) (hd : d ≤ S) (hM : M ≤ S)
    (hL : L ≤ S) (hn : n ≤ S) :
    uniformFuel D d M L n + uniformWork D d M L n ≤ sizePolynomial S := by
  rw [← sizePolynomial_eq]
  simp only [uniformFuel, uniformWork, rootFuelBound, rootWorkBound, recoveryFuelBound,
    recoveryWorkBound, systemFuelBound, systemWorkBound, batchFuelBound, batchWorkBound,
    sampleFuelBound, sampleWorkBound, RegularRootMachine.shiftFuel,
    VandermondeMachine.constructionFuel, ForwardEchelonMachine.budget,
    ForwardEchelonMachine.stageBudget, ResidualCoefficientMachine.solveBudget,
    BackSubstitutionMachine.budget]
  gcongr

end ReedSolomon.HiddenDerivative.StageRootsMachine

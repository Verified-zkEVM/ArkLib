/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleExecution
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Bounds
/-!
# One alphabet power bounds the separate-sample budgets

A common numerical size bounds the original sparse equation, both sample lists and the integer
parameters. Both actual initial budgets fit a degree-five polynomial times a single alphabet
power fixed by the original derivative order. The collector remains linear in the record cap.
Physical mass enters through the actual scalar emitter's factor-preservation theorem.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SeparateSampleDecoder

open HiddenDerivative MvPolynomial
open PreparedDecoderMachine (Input Element Term rootInput)
open PartialDerivativeMachine (inputMass)

def collectorFuelDiagonal (S : ℕ) : ℕ :=
  (CanonicalOutputMachine.acceptanceFuelBound S S S S S (S + 1) + 4) * (S + 1) + 4

def collectorWorkDiagonal (S : ℕ) : ℕ :=
  (CanonicalOutputMachine.acceptanceWorkBound S S S S S (S + 1) +
    3 * CanonicalOutputMachine.acceptanceFuelBound S S S S S (S + 1) + 30) * (S + 1) + 16

def fuelDiagonal (S : ℕ) : ℕ :=
  2 * S + 8 + StageRootsMachine.instancePolynomial (7 * S) + collectorFuelDiagonal S

/-- Absolute-degree polynomial for fuel plus primitive work; coefficients are universal. -/
def sizePolynomial (S : ℕ) : ℕ :=
  4704113192 * S ^ 5 + 2282885523 * S ^ 4 + 410453786 * S ^ 3 +
    36335355 * S ^ 2 + 2108647 * S + 91219

/-- Exact expansion of the diagonal root, collector and parent-dispatch bounds. -/
theorem sizePolynomial_eq (S : ℕ) :
    4 * fuelDiagonal S + 18 * S + 34 + StageRootsMachine.instancePolynomial (7 * S) +
      collectorWorkDiagonal S = sizePolynomial S := by
  unfold fuelDiagonal collectorFuelDiagonal collectorWorkDiagonal
    CanonicalOutputMachine.acceptanceFuelBound CanonicalOutputMachine.acceptanceWorkBound
    CanonicalOutputMachine.candidateFuelBound CanonicalGuardMachine.inputFuel
    CanonicalGuardMachine.inputWork CanonicalGuardMachine.inputScanFuel
    CanonicalGuardMachine.inputScanWork StageRootsMachine.batchFuelBound
    StageRootsMachine.batchWorkBound StageRootsMachine.sampleFuelBound
    StageRootsMachine.sampleWorkBound
    StageRootsMachine.instancePolynomial sizePolynomial
  ring

private theorem acceptance_diagonal (w d M g n p S : ℕ) (hw : w ≤ S) (hd : d ≤ S)
    (hM : M ≤ S) (hg : g ≤ S) (hn : n ≤ S) (hp : p ≤ S + 1) :
    CanonicalOutputMachine.acceptanceFuelBound w d M g n p ≤
        CanonicalOutputMachine.acceptanceFuelBound S S S S S (S + 1) ∧
      CanonicalOutputMachine.acceptanceWorkBound w d M g n p ≤
        CanonicalOutputMachine.acceptanceWorkBound S S S S S (S + 1) := by
  unfold CanonicalOutputMachine.acceptanceFuelBound CanonicalOutputMachine.acceptanceWorkBound
    CanonicalOutputMachine.candidateFuelBound CanonicalGuardMachine.inputFuel
    CanonicalGuardMachine.inputWork CanonicalGuardMachine.inputScanFuel
    CanonicalGuardMachine.inputScanWork StageRootsMachine.batchFuelBound
    StageRootsMachine.batchWorkBound StageRootsMachine.sampleFuelBound
    StageRootsMachine.sampleWorkBound
  constructor <;> gcongr

private theorem collector_diagonal (w d M g n Δ R S : ℕ) (hR : 1 ≤ R)
    (hw : w ≤ S) (hd : d ≤ S) (hM : M ≤ S) (hg : g ≤ S) (hn : n ≤ S) (hΔ : Δ ≤ S) :
    CanonicalOutputMachine.inputFuel w d M g n (Δ + 1) ((Δ + 1) * R) ≤
        R * collectorFuelDiagonal S ∧
      CanonicalOutputMachine.inputWork w d M g n (Δ + 1) ((Δ + 1) * R) ≤
        R * collectorWorkDiagonal S := by
  obtain ⟨hf, hb⟩ := acceptance_diagonal w d M g n (Δ + 1) S hw hd hM hg hn (by omega)
  have hf' :
      (CanonicalOutputMachine.acceptanceFuelBound w d M g n (Δ + 1) + 4) * (Δ + 1) ≤
        (CanonicalOutputMachine.acceptanceFuelBound S S S S S (S + 1) + 4) * (S + 1) := by
    gcongr
  have hb' :
      (CanonicalOutputMachine.acceptanceWorkBound w d M g n (Δ + 1) +
        3 * CanonicalOutputMachine.acceptanceFuelBound w d M g n (Δ + 1) + 30) * (Δ + 1) ≤
      (CanonicalOutputMachine.acceptanceWorkBound S S S S S (S + 1) +
        3 * CanonicalOutputMachine.acceptanceFuelBound S S S S S (S + 1) + 30) * (S + 1) := by
    gcongr
  have hfr := Nat.mul_le_mul_right R hf'
  have hbr := Nat.mul_le_mul_right R hb'
  unfold CanonicalOutputMachine.inputFuel CanonicalOutputMachine.inputWork
    collectorFuelDiagonal collectorWorkDiagonal
  constructor <;> nlinarith only [hfr, hbr, hR]

variable {F : Type*} [Field F] {a : F}

/-- Every original numeric size required by the two child budgets is bounded explicitly. -/
structure SizeBounds (input : Input F a) (guards : List (Element F a))
    (ts : List (Term F)) (Δ S : ℕ) : Prop where
  width : input.degree + 1 ≤ S
  order : input.order ≤ S
  mass : inputMass ts ≤ S
  residual : input.residualLength ≤ S
  recovery : input.samples.length ≤ S
  guards : guards.length ≤ S
  rows : input.received.length ≤ S
  delta : Δ ≤ S
  terms : ts.length ≤ S

/-- Fuel and work together retain one original-order alphabet power and absolute degree five. -/
theorem input_bounds_polynomial (input : Input F a) (guards : List (Element F a))
    (ts : List (Term F)) (Δ S : ℕ) (hq : 0 < input.alphabet.length)
    (hs : SizeBounds input guards ts Δ S) :
    fuel input guards ts Δ + workBound input guards ts Δ ≤
      input.alphabet.length ^ (input.order + 2) * sizePolynomial S := by
  let R := input.alphabet.length ^ (input.order + 2)
  let ri := initialRootInput input ts
  have hR : 1 ≤ R := Nat.one_le_pow _ _ hq
  have he := NonzeroInterpolationMachine.embedded_measures a ts
  have hm : inputMass ri.terms ≤ S := by
    simpa only [ri, initialRootInput, rootInput, he.2] using hs.mass
  have ht : ri.terms.length ≤ S := by
    simpa only [ri, initialRootInput, rootInput, he.1] using hs.terms
  have hsize : StageRootsMachine.instanceSize ri input.degree input.residualLength
      input.samples.length Δ ≤ 7 * S := by
    unfold StageRootsMachine.instanceSize
    have := hs.width
    have := hs.order
    have := hs.residual
    have := hs.recovery
    have := hs.delta
    dsimp only [ri, initialRootInput, rootInput]
    dsimp only [ri, initialRootInput, rootInput] at hm ht
    omega
  have hp : StageRootsMachine.instancePolynomial
      (StageRootsMachine.instanceSize ri input.degree input.residualLength input.samples.length Δ) ≤
        StageRootsMachine.instancePolynomial (7 * S) := by
    unfold StageRootsMachine.instancePolynomial
    gcongr
  obtain ⟨hrf, hrw⟩ := StageRootsMachine.input_bounds_polynomial ri input.degree
    input.residualLength input.samples.length Δ hq
  have hrf' : StageRootsMachine.inputFuel ri input.degree input.residualLength
      input.samples.length Δ ≤ R * StageRootsMachine.instancePolynomial (7 * S) :=
    hrf.trans (Nat.mul_le_mul_left R hp)
  have hrw' : StageRootsMachine.inputWork ri input.degree input.residualLength
      input.samples.length Δ ≤ R * StageRootsMachine.instancePolynomial (7 * S) :=
    hrw.trans (Nat.mul_le_mul_left R hp)
  obtain ⟨hcf, hcw⟩ := collector_diagonal (input.degree + 1) input.order (inputMass ri.terms)
    guards.length input.received.length Δ R S hR hs.width hs.order hm hs.guards hs.rows hs.delta
  have hf : fuel input guards ts Δ ≤ R * fuelDiagonal S := by
    have hbase : 2 * ts.length + 8 ≤ R * (2 * S + 8) := by
      have := hs.terms
      nlinarith
    unfold fuel fuelDiagonal recordBound
    change 2 * ts.length + 3 + _ + _ + 5 ≤ _
    dsimp only [ri, R] at hrf' hcf hbase ⊢
    nlinarith only [hbase, hrf', hcf]
  have hb : workBound input guards ts Δ ≤ R *
      (18 * S + 34 + StageRootsMachine.instancePolynomial (7 * S) +
        collectorWorkDiagonal S + 3 * fuelDiagonal S) := by
    have hbase : 18 * ts.length + 34 ≤ R * (18 * S + 34) := by
      have := hs.terms
      nlinarith
    have hsub := Nat.sub_le (fuel input guards ts Δ) 5
    unfold workBound recordBound
    dsimp only [ri, R] at hrw' hcw hf hbase ⊢
    nlinarith only [hbase, hrw', hcw, hf, hsub]
  rw [← sizePolynomial_eq]
  dsimp only [R] at hf hb
  nlinarith only [hf, hb]

/-- A caller-computable size from original data, without any visited records or output lengths. -/
def numericalSize (input : Input F a) (guards : List (Element F a))
    (ts : List (Term F)) (Δ : ℕ) : ℕ :=
  input.degree + 1 + input.order + inputMass ts + input.residualLength + input.samples.length +
    guards.length + input.received.length + Δ + ts.length

/-- The original-input sum discharges all numerical dominance premises. -/
theorem numericalSize_bounds (input : Input F a) (guards : List (Element F a))
    (ts : List (Term F)) (Δ : ℕ) :
    SizeBounds input guards ts Δ (numericalSize input guards ts Δ) := by
  constructor <;> unfold numericalSize <;> omega

/-- Each initial budget fits the same polynomial and the same single alphabet power. -/
theorem budgets_le_polynomial (input : Input F a) (guards : List (Element F a))
    (ts : List (Term F)) (Δ : ℕ) (hq : 0 < input.alphabet.length) :
    let B := input.alphabet.length ^ (input.order + 2) *
      sizePolynomial (numericalSize input guards ts Δ)
    fuel input guards ts Δ ≤ B ∧ workBound input guards ts Δ ≤ B := by
  have h := input_bounds_polynomial input guards ts Δ _ hq
    (numericalSize_bounds input guards ts Δ)
  dsimp only
  constructor <;> omega

end ReedSolomon.ListDecoding.SeparateSampleDecoder

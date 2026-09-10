/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CollectorStageBounds
/-!
# Initial-input execution bounds for the separate-sample decoder

The original equation, alphabet and numerical parameters determine all budgets. Actual
coefficient conversion, root enumeration and collection traces compose into one execution,
including every parent dispatch. No visited-stage or candidate-list size is used to choose
the budget. The bounds are primitive work, not yet a base-field or bit-cost refinement.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SeparateSampleDecoder

open HiddenDerivative PolynomialDifferential
open PreparedDecoderMachine (Input Element Term rootInput)
open MvPolynomial.PartialDerivativeMachine (inputMass)

variable {F : Type*} [Field F] [DecidableEq F] {a : F}

/-- Proof-side initial sparse representation used by both child-budget formulas. -/
def initialRootInput (input : Input F a) (ts : List (Term F)) :
    StageRootsMachine.Input (Element F a) :=
  rootInput input (MvPolynomial.QuadraticInputMachine.embedded ts)

/-- Original alphabet size and degree cap bound the number of visited records. -/
def recordBound (input : Input F a) (Δ : ℕ) : ℕ :=
  (Δ + 1) * input.alphabet.length ^ (input.order + 2)

/-- Initial-input majorant of all three child fuels and five fixed handoffs. -/
def fuel (input : Input F a) (guards : List (Element F a)) (ts : List (Term F)) (Δ : ℕ) : ℕ :=
  2 * ts.length + 3 +
    StageRootsMachine.inputFuel (initialRootInput input ts) input.degree
      input.residualLength input.samples.length Δ +
    CanonicalOutputMachine.inputFuel (input.degree + 1) input.order
      (inputMass (initialRootInput input ts).terms) guards.length input.received.length
      (Δ + 1) (recordBound input Δ) + 5

/-- Work of the same composed execution, including every child wrapper. -/
def workBound (input : Input F a) (guards : List (Element F a))
    (ts : List (Term F)) (Δ : ℕ) : ℕ :=
  18 * ts.length + 11 +
    StageRootsMachine.inputWork (initialRootInput input ts) input.degree
      input.residualLength input.samples.length Δ +
    CanonicalOutputMachine.inputWork (input.degree + 1) input.order
      (inputMass (initialRootInput input ts).terms) guards.length input.received.length
      (Δ + 1) (recordBound input Δ) + 3 * (fuel input guards ts Δ - 5) + 23

/-- The actual driver terminates at an initial-input budget with its exact accumulated work.
The algebraic premises concern the input equation and recovery samples, not desired outputs.
Correct decoding and duplicate freedom require the independent collector exactness theorem. -/
theorem execution_input_budget (input : Input F a) (guards : List (Element F a))
    (ha : ¬IsSquare a) (ts : List (Term F)) (Δ : ℕ)
    (points : Fin input.residualLength ↪ Element F a)
    (hsamples : input.samples = List.ofFn (fun i ↦ points i))
    (hq : 0 < input.alphabet.length) (hdepth : input.order ≤ input.degree) :
    letI := QuadraticAlgebra.fieldOfNonsquare a ha
    ∀ Q : DifferentialPolynomial (Element F a) input.order,
      MvPolynomial.DenseNormalizeMachine.DenseLayout (List.range (input.order + 2))
        (initialRootInput input ts).terms →
      MvPolynomial.EvaluationMachine.sparsePolynomial (initialRootInput input ts).terms =
        MvPolynomial.rename HighestJetTransport.encodeJet Q →
      Q ≠ 0 → (∀ j, jetDegree Q j < ringChar (Element F a)) →
      jetTotalDegree Q ≤ Δ → differentialWeightedDegree input.degree Q < input.residualLength →
      ∃ steps c out, steps ≤ fuel input guards ts Δ ∧
        Trace input guards ha steps (.start ts) c (.done (some out)) ∧
        runFuel input guards ha (fuel input guards ts Δ) (.start ts) = (.done (some out), c) ∧
        c ≤ workBound input guards ts Δ ∧
        ∃ stages records,
          SeparantChainRefinement.OrderedChain (initialRootInput input ts).terms Q stages ∧
          StageRootsMachine.Specification (initialRootInput input ts) input.degree
            input.residualLength input.samples stages [] records ∧
          out = CanonicalOutputMachine.result input.order guards (input.degree + 1)
            input.dimension input.agreement input.received records := by
  let : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨by
    intro r he
    apply ha
    exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using he.symm⟩⟩
  let := QuadraticAlgebra.fieldOfNonsquare a ha
  intro Q hl hQ hne hchar hdeg hweight
  let ri := initialRootInput input ts
  obtain ⟨stages, records, cr, hchain, hlen, hr, _hvisited, hspec, hw, hcount, hcr⟩ :=
    StageRootsMachine.execution_input_budget ri points input.samples hsamples hq hdepth
      Δ Q hl hQ hne hchar hdeg hweight
  obtain ⟨nr, hnr, hrt⟩ := StageRootsMachine.runFuel_refines ri input.degree input.residualLength
    (StageRootsMachine.inputFuel ri input.degree input.residualLength input.samples.length Δ)
    (.start input.samples)
  rw [hr] at hrt
  obtain ⟨no, co, hno, hot, _hor, hco⟩ := CanonicalOutputMachine.generated_runFuel
    ri input.dimension input.agreement Δ input.samples guards input.received
    hchain hlen hspec hw hcount
  obtain ⟨cc, hct, hcc⟩ := MvPolynomial.QuadraticInputMachine.scan_trace
    ts ([] : List (Term (Element F a)))
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hct hcc
  have hp := pipeline_trace input guards ha ts _ records _ (2 * ts.length + 3) nr no co
    cc cr hct hrt hot
  have hsteps : 2 * ts.length + 3 + nr + no + 5 ≤ fuel input guards ts Δ := by
    dsimp only [fuel, recordBound, ri, initialRootInput, rootInput] at hnr hno ⊢
    omega
  refine ⟨_, _, _, hsteps, hp, ?_, ?_, stages, records, hchain, hspec, rfl⟩
  · simpa only [Nat.add_sub_of_le hsteps] using
      hp.runFuel_done (fuel input guards ts Δ - (2 * ts.length + 3 + nr + no + 5))
  · rw [hcc]
    unfold workBound fuel recordBound
    dsimp only [ri, initialRootInput, rootInput] at hnr hno hcr hco ⊢
    omega

end ReedSolomon.ListDecoding.SeparateSampleDecoder

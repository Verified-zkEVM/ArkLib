/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleFieldBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleRestricted
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ExactOutput
/-!
# Exact separate-sample executions with field-size primitive bounds

Each conclusion retains the same output, trace and cost supplied by the existing exactness
proof. The total jet cap is derived from the actual successful interpolation attempt. Numeric
field sizes use the input's actual agreement parameter. These are primitive decoder ledgers:
interpolation and setup work are outside this driver, and restricted base embedding is reported
separately. No outer-decoder or bit-complexity conclusion is asserted.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SeparateSampleFieldExecution

open Polynomial JetHornerMachine HiddenDerivative NonzeroInterpolationMachine PolynomialDifferential
open PreparedDecoderMachine (Input Element)
open SeparateSampleDecoder

variable {F : Type*} [Field F] [DecidableEq F] {a : F} {n : ℕ}

/-- The actual attempt, indexed received data, distinct recovery samples, target width and
semantic characteristic/weight premises required by exact decoding. No jet cap is assumed. -/
structure AttemptPremises (input : Input F a) (interp : Output F) (m : ℕ)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a) : Prop where
  success : (run input.degree input.order m input.agreement input.received).1 = some interp
  rows : input.received = List.ofFn (fun i ↦ (domain i, received i))
  recovery : input.samples = List.ofFn (fun i ↦ points i)
  depth : input.order ≤ input.degree
  dimension : input.dimension ≤ input.degree + 1
  characteristic : IsBelowCharacteristic input.degree
    (sourceOutput (d := input.order) input.degree m input.agreement interp)
  weight : differentialWeightedDegree input.degree
    (sourceOutput (d := input.order) input.degree m input.agreement interp) < input.residualLength

/-- Attempt premises for interpolation with independent strict jet cutoff `J`. -/
structure AttemptPremisesWithBudget (input : Input F a) (interp : Output F) (m J : ℕ)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a) : Prop where
  success : (runWithBudget input.degree input.order m J input.agreement input.received).1 =
    some interp
  rows : input.received = List.ofFn (fun i ↦ (domain i, received i))
  recovery : input.samples = List.ofFn (fun i ↦ points i)
  depth : input.order ≤ input.degree
  dimension : input.dimension ≤ input.degree + 1
  characteristic : IsBelowCharacteristic input.degree
    (sourceOutputWithBudget (d := input.order) input.degree m J input.agreement interp)
  weight : differentialWeightedDegree input.degree
    (sourceOutputWithBudget (d := input.order) input.degree m J input.agreement interp) <
      input.residualLength

/-- Compatibility alias for callers that imported the old implementation-owned contract. -/
abbrev ExactOutput (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (out : List (List F)) : Prop :=
  ReedSolomon.ListDecoding.ExactOutput domain received k A out

/-- One completed initial-fuel execution, its exact charged trace and output specification.
The same steps and cost satisfy the original fuel/work bounds and the displayed sum bound B.
Recovery and guard lists are those stored in the input and supplied to this very execution. -/
def ExactExecution (input : Input F a) (guards : List (Element F a)) (ha : ¬IsSquare a)
    (interp : Output F) (m : ℕ) (domain : Fin n ↪ F) (received : Fin n → F) (B : ℕ) : Prop :=
  ∃ steps c out, steps ≤ fuel input guards interp.terms (2 * m) ∧
    Trace input guards ha steps (.start interp.terms) c (.done (some out)) ∧
    runFuel input guards ha (fuel input guards interp.terms (2 * m)) (.start interp.terms) =
      (.done (some out), c) ∧
    c ≤ workBound input guards interp.terms (2 * m) ∧ steps + c ≤ B ∧
    ExactOutput domain received input.dimension input.agreement out

/-- Exact execution whose root fuel records the independent strict interpolation cutoff `J`. -/
def ExactExecutionWithBudget (input : Input F a) (guards : List (Element F a))
    (ha : ¬IsSquare a) (interp : Output F) (_m J : ℕ) (domain : Fin n ↪ F)
    (received : Fin n → F) (B : ℕ) : Prop :=
  ∃ steps c out, steps ≤ fuel input guards interp.terms J ∧
    Trace input guards ha steps (.start interp.terms) c (.done (some out)) ∧
    runFuel input guards ha (fuel input guards interp.terms J) (.start interp.terms) =
      (.done (some out), c) ∧
    c ≤ workBound input guards interp.terms J ∧ steps + c ≤ B ∧
    ExactOutput domain received input.dimension input.agreement out

/-- Attach a numeric budget to a full-alphabet exact run at strict cutoff `J`. -/
theorem fullWithBudget_bounded (input : Input F a) (ha : ¬IsSquare a) (interp : Output F)
    (m J B : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremisesWithBudget input interp m J domain received points)
    (hall : ∀ x : Element F a, x ∈ input.alphabet) (hn : input.alphabet.Nodup)
    (hb : fuel input input.samples interp.terms J +
      workBound input input.samples interp.terms J ≤ B) :
    ExactExecutionWithBudget input input.samples ha interp m J domain received B := by
  have hjet := (runWithBudget_output_bounds _ _ _ _ _ _ interp hp.success).2.2.le
  obtain ⟨steps, c, out, hs, ht, hr, hc, he⟩ :=
    SeparateSampleExactness.full_attemptWithBudget_exact input ha interp m J J hp.success
      domain received hp.rows points hp.recovery hall hn hp.depth hp.dimension
      hp.characteristic hp.weight hjet
  exact ⟨steps, c, out, hs, ht, hr, hc, (Nat.add_le_add hs hc).trans hb, he⟩

/-- Fixed parameters give a full-alphabet exact run at independent strict cutoff `J`. -/
theorem fullWithBudget_fixed (input : Input F a) (ha : ¬IsSquare a) (interp : Output F)
    (m J q e : ℕ) (hq : 0 < q) (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremisesWithBudget input interp m J domain received points)
    (hs : FieldSizes input input.samples m input.agreement n q e)
    (hall : ∀ x : Element F a, x ∈ input.alphabet) (hn : input.alphabet.Nodup) :
    ExactExecutionWithBudget input input.samples ha interp m J domain received
      (sizePolynomial (fixedSizeCoefficientWithBudget input.order m J) *
        q ^ (e * (input.order + 2) + 10)) := by
  exact fullWithBudget_bounded input ha interp m J _ domain received points hp hall hn
    (fixed_interpolation_budgetWithBudget input input.samples interp m J input.agreement n q e
      hq hs hp.success)

/-- Attach a numeric budget to the same full-alphabet exact run; no second execution is chosen. -/
theorem full_bounded (input : Input F a) (ha : ¬IsSquare a) (interp : Output F) (m B : ℕ)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremises input interp m domain received points)
    (hall : ∀ x : Element F a, x ∈ input.alphabet) (hn : input.alphabet.Nodup)
    (hb : fuel input input.samples interp.terms (2 * m) +
      workBound input input.samples interp.terms (2 * m) ≤ B) :
    ExactExecution input input.samples ha interp m domain received B := by
  have hjet := (run_output_bounds _ _ _ _ _ interp hp.success).2.2.le
  obtain ⟨steps, c, out, hs, ht, hr, hc, he⟩ :=
    SeparateSampleExactness.full_attempt_exact input ha interp m (2 * m) hp.success
      domain received hp.rows points hp.recovery hall hn hp.depth hp.dimension
      hp.characteristic hp.weight hjet
  exact ⟨steps, c, out, hs, ht, hr, hc, (Nat.add_le_add hs hc).trans hb, he⟩

/-- Fixed order and multiplicity give a full-alphabet exact run with one alphabet power. -/
theorem full_fixed (input : Input F a) (ha : ¬IsSquare a) (interp : Output F)
    (m q e : ℕ) (hq : 0 < q) (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremises input interp m domain received points)
    (hs : FieldSizes input input.samples m input.agreement n q e)
    (hall : ∀ x : Element F a, x ∈ input.alphabet) (hn : input.alphabet.Nodup) :
    ExactExecution input input.samples ha interp m domain received
      (sizePolynomial (fixedSizeCoefficient input.order m) * q ^ (e * (input.order + 2) + 10)) := by
  exact full_bounded input ha interp m _ domain received points hp hall hn
    (fixed_interpolation_budget input input.samples interp m input.agreement n q e hq hs hp.success)

/-- Growing multiplicity at order zero gives an exact full-alphabet run with absolute exponent. -/
theorem full_zero (input : Input F a) (ha : ¬IsSquare a) (interp : Output F)
    (m q e : ℕ) (hq : 0 < q) (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremises input interp m domain received points)
    (hs : FieldSizes input input.samples m input.agreement n q e)
    (horder : input.order = 0) (hm : m ≤ n)
    (hall : ∀ x : Element F a, x ∈ input.alphabet) (hn : input.alphabet.Nodup) :
    ExactExecution input input.samples ha interp m domain received
      (sizePolynomial 26 * q ^ (2 * e + 25)) := by
  exact full_bounded input ha interp m _ domain received points hp hall hn
    (zero_interpolation_budget input input.samples interp m input.agreement n q e hq hs
      horder hm hp.success)

variable [Finite F]

/-- Restricted exactness retains its actual embedding charge separately from the same decoder run.
The reduced guard condition and the complete duplicate-free base enumeration remain explicit. -/
theorem restricted_bounded (input : Input F a) (ha : ¬IsSquare a) (interp : Output F) (m B : ℕ)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremises input interp m domain received points)
    (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (embeddingCost : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hembed : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) =
        (.done input.alphabet, embeddingCost))
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length)
    (hb : fuel input input.alphabet interp.terms (2 * m) +
      workBound input input.alphabet interp.terms (2 * m) ≤ B) :
    embeddingCost.total = 16 * base.length + 8 ∧
      ExactExecution input input.alphabet ha interp m domain received B := by
  have hjet := (run_output_bounds _ _ _ _ _ interp hp.success).2.2.le
  obtain ⟨hec, steps, c, out, hs, ht, hr, hc, he⟩ :=
    SeparateSampleRestricted.restricted_attempt_exact input ha interp m (2 * m) hp.success
      domain received hp.rows points hp.recovery base hall hn embeddingCost hembed hp.depth
      hp.dimension hp.characteristic hp.weight hjet hlarge
  exact ⟨hec, steps, c, out, hs, ht, hr, hc, (Nat.add_le_add hs hc).trans hb, he⟩

/-- Restricted exactness and embedding cost for strict interpolation cutoff `J`. -/
theorem restrictedWithBudget_bounded (input : Input F a) (ha : ¬IsSquare a)
    (interp : Output F) (m J B : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremisesWithBudget input interp m J domain received points)
    (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (embeddingCost : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hembed : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) =
        (.done input.alphabet, embeddingCost))
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length)
    (hb : fuel input input.alphabet interp.terms J +
      workBound input input.alphabet interp.terms J ≤ B) :
    embeddingCost.total = 16 * base.length + 8 ∧
      ExactExecutionWithBudget input input.alphabet ha interp m J domain received B := by
  have hjet := (runWithBudget_output_bounds _ _ _ _ _ _ interp hp.success).2.2.le
  obtain ⟨hec, steps, c, out, hs, ht, hr, hc, he⟩ :=
    SeparateSampleRestricted.restricted_attemptWithBudget_exact input ha interp m J J hp.success
      domain received hp.rows points hp.recovery base hall hn embeddingCost hembed hp.depth
      hp.dimension hp.characteristic hp.weight hjet hlarge
  exact ⟨hec, steps, c, out, hs, ht, hr, hc, (Nat.add_le_add hs hc).trans hb, he⟩

/-- Fixed-parameter restricted decoding at independent strict cutoff `J`. -/
theorem restrictedWithBudget_fixed (input : Input F a) (ha : ¬IsSquare a)
    (interp : Output F) (m J q e : ℕ) (hq : 0 < q) (domain : Fin n ↪ F)
    (received : Fin n → F) (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremisesWithBudget input interp m J domain received points)
    (hs : FieldSizes input input.alphabet m input.agreement n q e)
    (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (embeddingCost : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hembed : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) =
        (.done input.alphabet, embeddingCost))
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length) :
    embeddingCost.total = 16 * base.length + 8 ∧
      ExactExecutionWithBudget input input.alphabet ha interp m J domain received
        (sizePolynomial (fixedSizeCoefficientWithBudget input.order m J) *
          q ^ (e * (input.order + 2) + 10)) := by
  exact restrictedWithBudget_bounded input ha interp m J _ domain received points hp base hall hn
    embeddingCost hembed hlarge
    (fixed_interpolation_budgetWithBudget input input.alphabet interp m J input.agreement n q e
      hq hs hp.success)

/-- Fixed-parameter restricted decoding and its field-size budget refer to the identical run. -/
theorem restricted_fixed (input : Input F a) (ha : ¬IsSquare a) (interp : Output F)
    (m q e : ℕ) (hq : 0 < q) (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremises input interp m domain received points)
    (hs : FieldSizes input input.alphabet m input.agreement n q e)
    (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (embeddingCost : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hembed : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) =
        (.done input.alphabet, embeddingCost))
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length) :
    embeddingCost.total = 16 * base.length + 8 ∧
      ExactExecution input input.alphabet ha interp m domain received
        (sizePolynomial (fixedSizeCoefficient input.order m) *
          q ^ (e * (input.order + 2) + 10)) := by
  exact restricted_bounded input ha interp m _ domain received points hp base hall hn
    embeddingCost hembed hlarge
    (fixed_interpolation_budget input input.alphabet interp m input.agreement n q e hq hs
      hp.success)

/-- Order-zero restricted decoding permits growing multiplicity with a universal coefficient. -/
theorem restricted_zero (input : Input F a) (ha : ¬IsSquare a) (interp : Output F)
    (m q e : ℕ) (hq : 0 < q) (domain : Fin n ↪ F) (received : Fin n → F)
    (points : Fin input.residualLength ↪ Element F a)
    (hp : AttemptPremises input interp m domain received points)
    (hs : FieldSizes input input.alphabet m input.agreement n q e)
    (horder : input.order = 0) (hm : m ≤ n)
    (base : List F) (hall : ∀ x : F, x ∈ base) (hn : base.Nodup)
    (embeddingCost : QuadraticAlgebra.BaseEmbeddingMachine.Cost)
    (hembed : QuadraticAlgebra.BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : QuadraticAlgebra.BaseEmbeddingMachine.Configuration F a) =
        (.done input.alphabet, embeddingCost))
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length) :
    embeddingCost.total = 16 * base.length + 8 ∧
      ExactExecution input input.alphabet ha interp m domain received
        (sizePolynomial 26 * q ^ (2 * e + 25)) := by
  exact restricted_bounded input ha interp m _ domain received points hp base hall hn
    embeddingCost hembed hlarge
    (zero_interpolation_budget input input.alphabet interp m input.agreement n q e hq hs
      horder hm hp.success)

end ReedSolomon.ListDecoding.SeparateSampleFieldExecution

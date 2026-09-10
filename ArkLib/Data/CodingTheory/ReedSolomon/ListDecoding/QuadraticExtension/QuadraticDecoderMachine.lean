/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleFieldBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Dispatch.Machine
public import ArkLib.Data.QuadraticAlgebra.CertifiedSetup
public import ArkLib.Data.QuadraticAlgebra.BaseEmbeddingSemantics
/-!
# Interpolation, quadratic setup and executable decoding

The integer-input program runs interpolation, performs the actual certified field setup, chooses
its center alphabet using the returned ambient degree, and executes root recovery and collection.
The restricted branch materializes its base alphabet by the embedding machine. Recovery always
uses the setup's extension samples; only center enumeration and canonical guards change branches.

The decoder fuel is a scalar expression in the original parameters, never a count of candidates
or visited stages. Every child returns its actual primitive ledger. Fixed-size branch/record
handoffs are charged here; computing the scalar fuel expression and lowering the resulting
program to a bit-cost model are separate obligations. This is not yet a bit-complexity theorem.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticDecoderMachine

open HiddenDerivative
open QuadraticAlgebra
open PreparedDecoderMachine (Input Element)

/-- Original-parameter fuel: fixed positive order, or growing multiplicity at order zero. -/
def decoderFuel (d m q e : ℕ) : ℕ :=
  if d = 0 then SeparateSampleDecoder.sizePolynomial 26 * q ^ (2 * e + 25)
  else SeparateSampleDecoder.sizePolynomial
    (SeparateSampleDecoder.fixedSizeCoefficient d m) * q ^ (e * (d + 2) + 10)

/-- Scalar decoder fuel with independent strict interpolation cutoff `J`. -/
def decoderFuelWithBudget (d m J q e : ℕ) : ℕ :=
  SeparateSampleDecoder.sizePolynomial
    (SeparateSampleDecoder.fixedSizeCoefficientWithBudget d m J) * q ^ (e * (d + 2) + 10)

/-- Materialized center and guard alphabets, with the exponent of their numerical field size. -/
structure Alphabets (q : ℕ) (a : ZMod q) where
  centers : List (Element (ZMod q) a)
  guards : List (Element (ZMod q) a)
  exponent : ℕ

/-- Use the actual base embedding in the restricted branch; otherwise share the setup lists.
The count register, rather than a traversal of the base list, supplies the embedding fuel. -/
def chooseAlphabets {q : ℕ} {a : ZMod q} (data : SetupMachine.Prepared q a)
    (restricted : Bool) : Option (Alphabets q a) × ℕ :=
  if restricted then
    let embedded := BaseEmbeddingMachine.runFuel (2 * data.baseCount + 2)
      (.scan data.base [] : BaseEmbeddingMachine.Configuration (ZMod q) a)
    match embedded.1 with
    | .done bs => (some ⟨bs, bs, 1⟩, embedded.2.total + 32)
    | _ => (none, embedded.2.total + 32)
  else (some ⟨data.alphabet, data.samples, 2⟩, 32)

variable {q : ℕ} [Fact q.Prime]

/-- Run the prepared decoder at a numerical fuel bound, preserving its observed cost on failure.
No mathematical root selector or list witness occurs in this executable definition. -/
def runCore {a : ZMod q} (input : Input (ZMod q) a)
    (guards : List (Element (ZMod q) a)) (ha : ¬IsSquare a)
    (terms : List (PreparedDecoderMachine.Term (ZMod q))) (m e : ℕ) :
    Option (List (List (ZMod q))) × ℕ :=
  let decoded := SeparateSampleDecoder.runFuel input guards ha
    (decoderFuel input.order m q e) (.start terms)
  match decoded.1 with
  | .done out => (out, decoded.2 + 8)
  | _ => (none, decoded.2 + 8)

/-- Prepared root recovery charged at the independent strict interpolation cutoff `J`. -/
def runCoreWithBudget {a : ZMod q} (input : Input (ZMod q) a)
    (guards : List (Element (ZMod q) a)) (ha : ¬IsSquare a)
    (terms : List (PreparedDecoderMachine.Term (ZMod q))) (m J e : ℕ) :
    Option (List (List (ZMod q))) × ℕ :=
  let decoded := SeparateSampleDecoder.runFuel input guards ha
    (decoderFuelWithBudget input.order m J q e) (.start terms)
  match decoded.1 with
  | .done out => (out, decoded.2 + 8)
  | _ => (none, decoded.2 + 8)

/-- Select the center regime from the actual returned degree, then execute the prepared child.
The integrity certificate is erased and only supplies the computable quadratic field dictionary. -/
def runPrepared (k d m A : ℕ) (rows : List (ZMod q × ZMod q))
    (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A)) : Option (List (List (ZMod q))) × ℕ :=
  let selected := chooseAlphabets setup.data (decide (2 * (m * A + d - (found.degree + 1)) ≤ q))
  match selected.1 with
  | none => (none, selected.2 + 32)
  | some alphabets =>
      let input : Input (ZMod q) setup.parameter :=
        ⟨alphabets.centers, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
      let decoded := runCore input alphabets.guards setup.correct.nonsquare
        found.interpolant.terms m alphabets.exponent
      (decoded.1, selected.2 + decoded.2 + 32)

/-- Prepared decoding for an interpolant enumerated at strict jet cutoff `J`. -/
def runPreparedWithBudget (k d m J A : ℕ) (rows : List (ZMod q × ZMod q))
    (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A)) : Option (List (List (ZMod q))) × ℕ :=
  let selected := chooseAlphabets setup.data (decide (2 * (m * A + d - (found.degree + 1)) ≤ q))
  match selected.1 with
  | none => (none, selected.2 + 32)
  | some alphabets =>
      let input : Input (ZMod q) setup.parameter :=
        ⟨alphabets.centers, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
      let decoded := runCoreWithBudget input alphabets.guards setup.correct.nonsquare
        found.interpolant.terms m J alphabets.exponent
      (decoded.1, selected.2 + decoded.2 + 32)

/-- One program executes interpolation, actual setup and decoding in that order.
Prime odd characteristic and sample capacity are proof-only preconditions of this branch;
the small-block and oversized-agreement outer branches do not need quadratic setup. -/
def run (k d m A : ℕ) (rows : List (ZMod q × ZMod q)) (hodd : q ≠ 2)
    (hL : m * A ≤ q ^ 2) : Option (List (List (ZMod q))) × ℕ :=
  let interpolated := InterpolationDispatch.run k d m A rows
  match interpolated.1 with
  | none => (none, interpolated.2 + 32)
  | some found =>
      let setup := SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL
      let decoded := runPrepared k d m A rows found setup
      (decoded.1, interpolated.2 + setup.cost.total + decoded.2 + 32)

/-- Full decoder using independent strict interpolation cutoff `J`. -/
def runWithBudget (k d m J A : ℕ) (rows : List (ZMod q × ZMod q)) (hodd : q ≠ 2)
    (hL : m * A ≤ q ^ 2) : Option (List (List (ZMod q))) × ℕ :=
  let interpolated := InterpolationDispatch.runWithBudget k d m J A rows
  match interpolated.1 with
  | none => (none, interpolated.2 + 32)
  | some found =>
      let setup := SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL
      let decoded := runPreparedWithBudget k d m J A rows found setup
      (decoded.1, interpolated.2 + setup.cost.total + decoded.2 + 32)

/-- A completed concrete trace determines the exact core result at the original-parameter fuel. -/
theorem runCore_of_trace {a : ZMod q} (input : Input (ZMod q) a)
    (guards : List (Element (ZMod q) a)) (ha : ¬IsSquare a)
    (terms : List (PreparedDecoderMachine.Term (ZMod q))) (m e steps cost : ℕ)
    (out : List (List (ZMod q)))
    (ht : SeparateSampleDecoder.Trace input guards ha steps (.start terms) cost (.done (some out)))
    (hb : steps ≤ decoderFuel input.order m q e) :
    runCore input guards ha terms m e = (some out, cost + 8) := by
  have he := ht.runFuel_done (decoderFuel input.order m q e - steps)
  rw [Nat.add_sub_of_le hb] at he
  simp only [runCore, he]

/-- A completed trace determines the budget-aware prepared core result. -/
theorem runCoreWithBudget_of_trace {a : ZMod q} (input : Input (ZMod q) a)
    (guards : List (Element (ZMod q) a)) (ha : ¬IsSquare a)
    (terms : List (PreparedDecoderMachine.Term (ZMod q))) (m J e steps cost : ℕ)
    (out : List (List (ZMod q)))
    (ht : SeparateSampleDecoder.Trace input guards ha steps (.start terms) cost
      (.done (some out)))
    (hb : steps ≤ decoderFuelWithBudget input.order m J q e) :
    runCoreWithBudget input guards ha terms m J e = (some out, cost + 8) := by
  have he := ht.runFuel_done (decoderFuelWithBudget input.order m J q e - steps)
  rw [Nat.add_sub_of_le hb] at he
  simp only [runCoreWithBudget, he]

end ReedSolomon.ListDecoding.QuadraticDecoderMachine

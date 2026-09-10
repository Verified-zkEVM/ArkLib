/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateSeparateSampleRefinement
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderMachine
public import ArkLib.Data.QuadraticAlgebra.CoordinateAlphabetMachine
/-!
# Coordinate root-recovery core with executed alphabet materialization

The original setup's quadratic records are converted by three actual linear controllers, for
the center alphabet, recovery grid, and guard grid. The raw-pair decoder then runs at a bound
computed solely from the original integer parameters. No observed cost, output size, or root
witness is used to choose runtime fuel. The result and primitive-work bound concern this same
executed composition. Bit lowering, scalar fuel arithmetic, and physical serialization remain
separate obligations; this module does not assert the full bit-time theorem.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CoordinateDecoderCore

open QuadraticAlgebra
open PreparedDecoderMachine (Input Element Term)

variable {q : ℕ} [Fact q.Prime]

/-- A fixed-size record assembly after the three coordinate lists have actually been produced. -/
def assemble {a : ZMod q} (input : Input (ZMod q) a)
    (alphabet samples : List (ZMod q × ZMod q)) : QuadraticPreparedDecoderMachine.Input (ZMod q) :=
  ⟨alphabet, samples, input.received, input.order, input.degree, input.residualLength,
    input.dimension, input.agreement⟩

/-- The coordinate simulation factor multiplies the original parameter-only decoder budget. -/
def fuel (d m q e : ℕ) : ℕ := 17179869184 * QuadraticDecoderMachine.decoderFuel d m q e

/-- Execute all input conversions and then raw coordinate recovery and output collection.
All observed conversion costs are retained even if a supplied list exceeds its length bound. -/
def run {a : ZMod q} (input : Input (ZMod q) a) (guards : List (Element (ZMod q) a))
    (terms : List (Term (ZMod q))) (m e : ℕ) : Option (List (List (ZMod q))) × ℕ :=
  let alphabet := CoordinateAlphabetMachine.runFuel (2 * q ^ 2 + 2) (.scan input.alphabet [])
  let samples := CoordinateAlphabetMachine.runFuel (2 * q ^ 2 + 2) (.scan input.samples [])
  let guardGrid := CoordinateAlphabetMachine.runFuel (2 * q ^ 2 + 2) (.scan guards [])
  let preparedCost := alphabet.2 + samples.2 + guardGrid.2 + 32
  match alphabet.1, samples.1, guardGrid.1 with
  | .done bs, .done rs, .done gs =>
      let decoded := QuadraticSeparateSampleDecoder.runFuel a (assemble input bs rs) gs
        (fuel input.order m q e) (.start terms)
      match decoded.1 with
      | .done out => (out, preparedCost + decoded.2 + 8)
      | _ => (none, preparedCost + decoded.2 + 8)
  | _, _, _ => (none, preparedCost)

/-- Successful source execution lowers to this actual fixed-fuel program with exact same output.
The input bounds concern only the three already supplied lists; no backend hypothesis is assumed. -/
theorem run_of_trace {a : ZMod q} (input : Input (ZMod q) a)
    (guards : List (Element (ZMod q) a)) (ha : ¬IsSquare a)
    (terms : List (Term (ZMod q))) (m e steps cost : ℕ) (out : List (List (ZMod q)))
    (ht : SeparateSampleDecoder.Trace input guards ha steps (.start terms) cost (.done (some out)))
    (hb : steps + cost ≤ QuadraticDecoderMachine.decoderFuel input.order m q e)
    (halphabet : input.alphabet.length ≤ q ^ 2) (hsamples : input.samples.length ≤ q ^ 2)
    (hguards : guards.length ≤ q ^ 2) :
    ∃ work, run input guards terms m e = (some out, work) ∧
      work ≤ fuel input.order m q e + 45 * q ^ 2 + 64 := by
  obtain ⟨n, c, hc, hbound⟩ :=
    QuadraticSeparateSampleDecoder.trace_lowering a ha input guards ht
  change QuadraticSeparateSampleDecoder.Trace a
    (QuadraticPreparedDecoderMachine.encodeInput input)
    (guards.map MvPolynomial.QuadraticEvaluationMachine.encode) n (.start terms) c
      (.done (some out)) at hc
  have hbudget : n + c ≤ fuel input.order m q e :=
    hbound.trans (Nat.mul_le_mul_left _ hb)
  have hn : n ≤ fuel input.order m q e := (Nat.le_add_right _ _).trans hbudget
  have he := hc.runFuel_done (fuel input.order m q e - n)
  rw [Nat.add_sub_of_le hn] at he
  have haRun := CoordinateAlphabetMachine.evaluation_runFuel input.alphabet (q ^ 2) halphabet
  have hsRun := CoordinateAlphabetMachine.evaluation_runFuel input.samples (q ^ 2) hsamples
  have hgRun := CoordinateAlphabetMachine.evaluation_runFuel guards (q ^ 2) hguards
  have hi : assemble input (CoordinateAlphabetMachine.coordinates input.alphabet)
      (CoordinateAlphabetMachine.coordinates input.samples) =
        QuadraticPreparedDecoderMachine.encodeInput input := rfl
  have hg : CoordinateAlphabetMachine.coordinates guards =
      guards.map MvPolynomial.QuadraticEvaluationMachine.encode := rfl
  refine ⟨(15 * input.alphabet.length + 8) + (15 * input.samples.length + 8) +
    (15 * guards.length + 8) + 32 + c + 8, ?_, ?_⟩
  · simp only [run, haRun, hsRun, hgRun, hi, hg, he]
  · omega

end ReedSolomon.ListDecoding.CoordinateDecoderCore

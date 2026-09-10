/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Coordinate.CoordinateDecoderCore
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderProof
/-!
# Executed interpolation, setup and coordinate decoding

This composition keeps the actual interpolation and certified setup programs. It replaces the
quadratic root-recovery core with the raw-coordinate program, including executed conversions
of all three supplied alphabets. Both center regimes use the same recovery grid. Exact output
and primitive work concern this literal composition; the global bit-cost refinement is not
assumed and remains a separate theorem.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CoordinateDecoderMachine

open HiddenDerivative QuadraticAlgebra PolynomialDifferential
open PreparedDecoderMachine (Input Element)
open SeparateSampleDecoder (FieldSizes)
open SeparateSampleFieldExecution (AttemptPremises ExactOutput)

variable {q : ℕ} [Fact q.Prime]

/-- Choose the actual center regime, then execute all coordinate materialization and recovery. -/
def runPrepared (k d m A : ℕ) (rows : List (ZMod q × ZMod q))
    (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A)) : Option (List (List (ZMod q))) × ℕ :=
  let selected := QuadraticDecoderMachine.chooseAlphabets setup.data
    (decide (2 * (m * A + d - (found.degree + 1)) ≤ q))
  match selected.1 with
  | none => (none, selected.2 + 32)
  | some alphabets =>
      let input : Input (ZMod q) setup.parameter :=
        ⟨alphabets.centers, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
      let decoded := CoordinateDecoderCore.run input alphabets.guards
        found.interpolant.terms m alphabets.exponent
      (decoded.1, selected.2 + decoded.2 + 32)

/-- Actual interpolation and proof-erased setup supply all runtime values to the coordinate core. -/
def run (k d m A : ℕ) (rows : List (ZMod q × ZMod q)) (hodd : q ≠ 2)
    (hL : m * A ≤ q ^ 2) : Option (List (List (ZMod q))) × ℕ :=
  let interpolated := InterpolationDispatch.run k d m A rows
  match interpolated.1 with
  | none => (none, interpolated.2 + 32)
  | some found =>
      let setup := SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL
      let decoded := runPrepared k d m A rows found setup
      (decoded.1, interpolated.2 + setup.cost.total + decoded.2 + 32)

/-- The observed setup and successful interpolation attempt imply exact coordinate decoding.
The bound includes all alphabet conversion and regime-selection charges in this same run. -/
theorem runPrepared_exact (k d m A : ℕ) {n : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A))
    (hr : (NonzeroInterpolationMachine.run found.degree d m A
      (List.ofFn (fun i ↦ (domain i, received i)))).1 = some found.interpolant)
    (hdepth : d ≤ found.degree) (hk : k ≤ found.degree + 1)
    (hD : found.degree ≤ n) (hnq : n ≤ q) (hA : A ≤ n) (hm : m ≤ n)
    (hchar : IsBelowCharacteristic found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant))
    (hweight : differentialWeightedDegree found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d)
        found.degree m A found.interpolant) < m * A) :
    ∃ out cost, runPrepared k d m A (List.ofFn (fun i ↦ (domain i, received i))) found setup =
      (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ CoordinateDecoderCore.fuel d m q
        (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
          45 * q ^ 2 + 16 * q + 136 := by
  let rows := List.ofFn (fun i ↦ (domain i, received i))
  have hbase : setup.data.base.length = q :=
    setup.correct.base_length.trans setup.correct.base_count
  have hsample : setup.data.samples.length = m * A :=
    setup.correct.sample_length.trans setup.correct.sample_count
  have halphabet : setup.data.alphabet.length = q ^ 2 :=
    setup.correct.extension_length.trans setup.correct.extension_count
  have hL : m * A ≤ q ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hm.trans hnq) (hA.trans hnq)
  obtain ⟨points, hpoints⟩ := setup.correct.samples_embedding
  by_cases hlarge : 2 * (m * A + d - (found.degree + 1)) ≤ q
  · let W := BaseEmbeddingMachine.embedded (a := setup.parameter) setup.data.base
    let input : Input (ZMod q) setup.parameter :=
      ⟨W, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
    have hp : AttemptPremises input found.interpolant m domain received points :=
      ⟨hr, rfl, hpoints, hdepth, hk, hchar, hweight⟩
    have hW : W.length = q := (BaseEmbeddingMachine.embedded_length _).trans hbase
    have hWq : W.length ≤ q ^ 2 := by
      rw [hW]
      have := (Fact.out : q.Prime).pos
      nlinarith
    have hs : FieldSizes input input.alphabet m A n q 1 :=
      ⟨hD, hnq, hA, rfl, hsample, hWq, by simp [input, rows], by simpa using hW⟩
    obtain ⟨ec, he, _hc⟩ := BaseEmbeddingMachine.evaluation_runFuel
      (a := setup.parameter) setup.data.base
    obtain ⟨_hec, steps, c, out, _hs, ht, _hr, _hc, hb, ho⟩ :=
      QuadraticDecoderMachine.restricted_execution
        input setup.correct.nonsquare found.interpolant m domain received points hp hs hm
        setup.data.base setup.correct.base_complete setup.correct.base_nodup ec he
        (by simpa only [input, hbase] using hlarge)
    obtain ⟨work, hrun, hwork⟩ := CoordinateDecoderCore.run_of_trace input W
      setup.correct.nonsquare found.interpolant.terms m 1 steps c out ht hb hWq
      (hsample.le.trans hL) hWq
    obtain ⟨_ec, _he, _hcost, hchoice⟩ :=
      QuadraticDecoderMachine.chooseAlphabets_restricted (m * A) setup.data setup.correct
    refine ⟨out, 16 * q + 40 + work + 32, ?_, ho, ?_⟩
    · simp only [runPrepared, decide_eq_true hlarge, hchoice]
      change ((CoordinateDecoderCore.run input W found.interpolant.terms m 1).1,
        16 * q + 40 + (CoordinateDecoderCore.run input W found.interpolant.terms m 1).2 + 32) = _
      rw [hrun]
    · simp only [if_pos hlarge]
      change work ≤ CoordinateDecoderCore.fuel d m q 1 + 45 * q ^ 2 + 64 at hwork
      omega
  · let input : Input (ZMod q) setup.parameter :=
      ⟨setup.data.alphabet, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
    have hp : AttemptPremises input found.interpolant m domain received points :=
      ⟨hr, rfl, hpoints, hdepth, hk, hchar, hweight⟩
    have hs : FieldSizes input input.samples m A n q 2 :=
      ⟨hD, hnq, hA, rfl, hsample, hsample.le.trans hL, by simp [input, rows], halphabet⟩
    obtain ⟨steps, c, out, _hs, ht, _hr, _hc, hb, ho⟩ :=
      QuadraticDecoderMachine.full_execution
        input setup.correct.nonsquare found.interpolant m domain received points hp hs hm
        setup.correct.extension_complete setup.correct.extension_nodup
    obtain ⟨work, hrun, hwork⟩ := CoordinateDecoderCore.run_of_trace input setup.data.samples
      setup.correct.nonsquare found.interpolant.terms m 2 steps c out ht hb halphabet.le
      (hsample.le.trans hL) (hsample.le.trans hL)
    refine ⟨out, 32 + work + 32, ?_, ho, ?_⟩
    · simp only [runPrepared, decide_eq_false hlarge, QuadraticDecoderMachine.chooseAlphabets,
        Bool.false_eq_true, if_false]
      change ((CoordinateDecoderCore.run input setup.data.samples found.interpolant.terms m 2).1,
        32 + (CoordinateDecoderCore.run input setup.data.samples
          found.interpolant.terms m 2).2 + 32) = _
      rw [hrun]
    · simp only [if_neg hlarge]
      change work ≤ CoordinateDecoderCore.fuel d m q 2 + 45 * q ^ 2 + 64 at hwork
      omega

/-- Successful executed interpolation supplies one complete exact coordinate decoder run.
The remaining hypotheses are mathematical properties of the returned interpolant, not a cost
implementation interface or a chosen decoding list. -/
theorem run_exact_of_interpolation (k d m A : ℕ) {n : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hodd : q ≠ 2) (hL : m * A ≤ q ^ 2)
    (found : AmbientSearchMachine.Output (ZMod q))
    (hi : (InterpolationDispatch.run k d m A
      (List.ofFn (fun i ↦ (domain i, received i)))).1 = some found)
    (hdepth : d ≤ found.degree) (hk : k ≤ found.degree + 1)
    (hD : found.degree ≤ n) (hnq : n ≤ q) (hA : A ≤ n) (hm : m ≤ n)
    (hchar : IsBelowCharacteristic found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d) found.degree m A found.interpolant))
    (hweight : differentialWeightedDegree found.degree
      (NonzeroInterpolationMachine.sourceOutput (d := d)
        found.degree m A found.interpolant) < m * A) :
    ∃ out cost, run k d m A (List.ofFn (fun i ↦ (domain i, received i))) hodd hL =
      (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budget k d m A n + SetupMachine.budget q (m * A) +
        CoordinateDecoderCore.fuel d m q
          (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
            45 * q ^ 2 + 16 * q + 168 := by
  let rows := List.ofFn (fun i ↦ (domain i, received i))
  let setup := SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL
  have hr := InterpolationDispatch.returned_attempt k d m A rows found hi
  obtain ⟨out, cost, hd, ho, hb⟩ := runPrepared_exact k d m A domain received found setup
    hr hdepth hk hD hnq hA hm hchar hweight
  have hi' : InterpolationDispatch.run k d m A rows =
      (some found, (InterpolationDispatch.run k d m A rows).2) := by
    exact Prod.ext hi rfl
  have hir := InterpolationDispatch.cost_le k d m A rows
  have hsize : rows.length = n := by simp [rows]
  rw [hsize] at hir
  refine ⟨out, (InterpolationDispatch.run k d m A rows).2 + setup.cost.total + cost + 32,
    ?_, ho, ?_⟩
  · change run k d m A rows hodd hL = _
    unfold run
    rw [hi']
    change ((runPrepared k d m A rows found setup).1,
      (InterpolationDispatch.run k d m A rows).2 + setup.cost.total +
        (runPrepared k d m A rows found setup).2 + 32) = _
    change runPrepared k d m A rows found setup = (some out, cost) at hd
    rw [hd]
  · have hs := setup.cost_bound
    unfold CoordinateDecoderCore.fuel at hb ⊢
    omega

end ReedSolomon.ListDecoding.CoordinateDecoderMachine

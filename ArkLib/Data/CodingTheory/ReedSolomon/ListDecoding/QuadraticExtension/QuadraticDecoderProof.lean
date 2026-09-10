/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderComposition
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSampleFieldExecution
/-!
# Exact output of the executed quadratic decoder

The actual interpolation attempt and setup values feed the executed alphabet branch and decoder.
The two regimes retain the same extension recovery samples but use different center/guard lists.
The integer-parameter fuel bound applies to that same exact-output execution, including order zero
with multiplicity growing with block length. This theorem accounts for primitive work only;
source-parameter existence and the bit-cost refinement are separate obligations.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticDecoderMachine

open HiddenDerivative QuadraticAlgebra PolynomialDifferential
open PreparedDecoderMachine (Input Element)
open SeparateSampleDecoder (FieldSizes)
open SeparateSampleFieldExecution
  (AttemptPremises AttemptPremisesWithBudget ExactExecution ExactExecutionWithBudget ExactOutput)

variable {q : ℕ} [Fact q.Prime]

/-- The full-alphabet exact run has the same scalar-parameter fuel used by the executable. -/
theorem full_execution {a : ZMod q} (input : Input (ZMod q) a) (ha : ¬IsSquare a)
    (interp : NonzeroInterpolationMachine.Output (ZMod q)) (m : ℕ) {n : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (points : Fin input.residualLength ↪ Element (ZMod q) a)
    (hp : AttemptPremises input interp m domain received points)
    (hs : FieldSizes input input.samples m input.agreement n q 2) (hm : m ≤ n)
    (hall : ∀ x, x ∈ input.alphabet) (hn : input.alphabet.Nodup) :
    ExactExecution input input.samples ha interp m domain received
      (decoderFuel input.order m q 2) := by
  by_cases hd : input.order = 0
  · simpa only [decoderFuel, if_pos hd] using
      SeparateSampleFieldExecution.full_zero input ha interp m q 2
        (Fact.out : q.Prime).pos domain received points hp hs hd hm hall hn
  · simpa only [decoderFuel, if_neg hd] using
      SeparateSampleFieldExecution.full_fixed input ha interp m q 2
        (Fact.out : q.Prime).pos domain received points hp hs hall hn

/-- The restricted exact run uses the same scalar fuel, with the real embedding kept separate. -/
theorem restricted_execution {a : ZMod q} (input : Input (ZMod q) a) (ha : ¬IsSquare a)
    (interp : NonzeroInterpolationMachine.Output (ZMod q)) (m : ℕ) {n : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (points : Fin input.residualLength ↪ Element (ZMod q) a)
    (hp : AttemptPremises input interp m domain received points)
    (hs : FieldSizes input input.alphabet m input.agreement n q 1) (hm : m ≤ n)
    (base : List (ZMod q)) (hall : ∀ x, x ∈ base) (hn : base.Nodup)
    (ec : BaseEmbeddingMachine.Cost)
    (he : BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : BaseEmbeddingMachine.Configuration (ZMod q) a) = (.done input.alphabet, ec))
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length) :
    ec.total = 16 * base.length + 8 ∧
      ExactExecution input input.alphabet ha interp m domain received
        (decoderFuel input.order m q 1) := by
  by_cases hd : input.order = 0
  · simpa only [decoderFuel, if_pos hd] using
      SeparateSampleFieldExecution.restricted_zero input ha interp m q 1
        (Fact.out : q.Prime).pos domain received points hp hs hd hm base hall hn ec he hlarge
  · simpa only [decoderFuel, if_neg hd] using
      SeparateSampleFieldExecution.restricted_fixed input ha interp m q 1
        (Fact.out : q.Prime).pos domain received points hp hs base hall hn ec he hlarge

/-- Full-alphabet exact execution for independent strict interpolation cutoff `J`. -/
theorem fullWithBudget_execution {a : ZMod q} (input : Input (ZMod q) a)
    (ha : ¬IsSquare a) (interp : NonzeroInterpolationMachine.Output (ZMod q)) (m J : ℕ)
    {n : ℕ} (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (points : Fin input.residualLength ↪ Element (ZMod q) a)
    (hp : AttemptPremisesWithBudget input interp m J domain received points)
    (hs : FieldSizes input input.samples m input.agreement n q 2)
    (hall : ∀ x, x ∈ input.alphabet) (hn : input.alphabet.Nodup) :
    ExactExecutionWithBudget input input.samples ha interp m J domain received
      (decoderFuelWithBudget input.order m J q 2) := by
  exact SeparateSampleFieldExecution.fullWithBudget_fixed input ha interp m J q 2
    (Fact.out : q.Prime).pos domain received points hp hs hall hn

/-- Restricted exact execution for independent strict interpolation cutoff `J`. -/
theorem restrictedWithBudget_execution {a : ZMod q} (input : Input (ZMod q) a)
    (ha : ¬IsSquare a) (interp : NonzeroInterpolationMachine.Output (ZMod q)) (m J : ℕ)
    {n : ℕ} (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (points : Fin input.residualLength ↪ Element (ZMod q) a)
    (hp : AttemptPremisesWithBudget input interp m J domain received points)
    (hs : FieldSizes input input.alphabet m input.agreement n q 1)
    (base : List (ZMod q)) (hall : ∀ x, x ∈ base) (hn : base.Nodup)
    (ec : BaseEmbeddingMachine.Cost)
    (he : BaseEmbeddingMachine.runFuel (2 * base.length + 2)
      (.scan base [] : BaseEmbeddingMachine.Configuration (ZMod q) a) = (.done input.alphabet, ec))
    (hlarge : 2 * (input.residualLength + input.order - (input.degree + 1)) ≤ base.length) :
    ec.total = 16 * base.length + 8 ∧
      ExactExecutionWithBudget input input.alphabet ha interp m J domain received
        (decoderFuelWithBudget input.order m J q 1) := by
  exact SeparateSampleFieldExecution.restrictedWithBudget_fixed input ha interp m J q 1
    (Fact.out : q.Prime).pos domain received points hp hs base hall hn ec he hlarge

/-- Actual setup, interpolation and integer size contracts imply successful prepared execution.
The returned list and charged cost belong to `runPrepared` itself. -/
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
      cost ≤ decoderFuel d m q
        (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) + 16 * q + 80 := by
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
    obtain ⟨_hec, steps, c, out, _hs, ht, _hr, _hc, hb, ho⟩ := restricted_execution
      input setup.correct.nonsquare found.interpolant m domain received points hp hs hm
      setup.data.base setup.correct.base_complete setup.correct.base_nodup ec he
      (by simpa only [input, hbase] using hlarge)
    have hrun := runPrepared_restricted_of_trace k d m A rows found setup hlarge steps c out
      ht ((Nat.le_add_right _ _).trans hb)
    refine ⟨out, 16 * q + c + 80, hrun, ho, ?_⟩
    simp only [if_pos hlarge]
    change steps + c ≤ decoderFuel d m q 1 at hb
    omega
  · let input : Input (ZMod q) setup.parameter :=
      ⟨setup.data.alphabet, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
    have hp : AttemptPremises input found.interpolant m domain received points :=
      ⟨hr, rfl, hpoints, hdepth, hk, hchar, hweight⟩
    have hs : FieldSizes input input.samples m A n q 2 :=
      ⟨hD, hnq, hA, rfl, hsample, hsample.le.trans hL, by simp [input, rows], halphabet⟩
    obtain ⟨steps, c, out, _hs, ht, _hr, _hc, hb, ho⟩ := full_execution
      input setup.correct.nonsquare found.interpolant m domain received points hp hs hm
      setup.correct.extension_complete setup.correct.extension_nodup
    have hrun := runPrepared_full_of_trace k d m A rows found setup hlarge steps c out ht
      ((Nat.le_add_right _ _).trans hb)
    refine ⟨out, c + 72, hrun, ho, ?_⟩
    simp only [if_neg hlarge]
    change steps + c ≤ decoderFuel d m q 2 at hb
    omega

/-- Exact prepared execution for interpolation with strict jet cutoff `J`. -/
theorem runPreparedWithBudget_exact (k d m J A : ℕ) {n : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A))
    (hr : (NonzeroInterpolationMachine.runWithBudget found.degree d m J A
      (List.ofFn (fun i ↦ (domain i, received i)))).1 = some found.interpolant)
    (hdepth : d ≤ found.degree) (hk : k ≤ found.degree + 1)
    (hD : found.degree ≤ n) (hnq : n ≤ q) (hA : A ≤ n) (hL : m * A ≤ q ^ 2)
    (hchar : IsBelowCharacteristic found.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d)
        found.degree m J A found.interpolant))
    (hweight : differentialWeightedDegree found.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d)
        found.degree m J A found.interpolant) < m * A) :
    ∃ out cost,
      runPreparedWithBudget k d m J A (List.ofFn (fun i ↦ (domain i, received i))) found setup =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ decoderFuelWithBudget d m J q
        (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) + 16 * q + 80 := by
  let rows := List.ofFn (fun i ↦ (domain i, received i))
  have hbase : setup.data.base.length = q :=
    setup.correct.base_length.trans setup.correct.base_count
  have hsample : setup.data.samples.length = m * A :=
    setup.correct.sample_length.trans setup.correct.sample_count
  have halphabet : setup.data.alphabet.length = q ^ 2 :=
    setup.correct.extension_length.trans setup.correct.extension_count
  obtain ⟨points, hpoints⟩ := setup.correct.samples_embedding
  by_cases hlarge : 2 * (m * A + d - (found.degree + 1)) ≤ q
  · let W := BaseEmbeddingMachine.embedded (a := setup.parameter) setup.data.base
    let input : Input (ZMod q) setup.parameter :=
      ⟨W, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
    have hp : AttemptPremisesWithBudget input found.interpolant m J domain received points :=
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
      restrictedWithBudget_execution input setup.correct.nonsquare found.interpolant m J
        domain received points hp hs setup.data.base setup.correct.base_complete
        setup.correct.base_nodup ec he (by simpa only [input, hbase] using hlarge)
    have hrun := runPreparedWithBudget_restricted_of_trace k d m J A rows found setup hlarge
      steps c out ht ((Nat.le_add_right _ _).trans hb)
    refine ⟨out, 16 * q + c + 80, hrun, ho, ?_⟩
    simp only [if_pos hlarge]
    change steps + c ≤ decoderFuelWithBudget d m J q 1 at hb
    omega
  · let input : Input (ZMod q) setup.parameter :=
      ⟨setup.data.alphabet, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
    have hp : AttemptPremisesWithBudget input found.interpolant m J domain received points :=
      ⟨hr, rfl, hpoints, hdepth, hk, hchar, hweight⟩
    have hs : FieldSizes input input.samples m A n q 2 :=
      ⟨hD, hnq, hA, rfl, hsample, hsample.le.trans hL, by simp [input, rows], halphabet⟩
    obtain ⟨steps, c, out, _hs, ht, _hr, _hc, hb, ho⟩ :=
      fullWithBudget_execution input setup.correct.nonsquare found.interpolant m J
        domain received points hp hs setup.correct.extension_complete setup.correct.extension_nodup
    have hrun := runPreparedWithBudget_full_of_trace k d m J A rows found setup hlarge
      steps c out ht ((Nat.le_add_right _ _).trans hb)
    refine ⟨out, c + 72, hrun, ho, ?_⟩
    simp only [if_neg hlarge]
    change steps + c ≤ decoderFuelWithBudget d m J q 2 at hb
    omega

/-- Successful integer interpolation supplies one complete exact decoder execution.
All costs in the conclusion are for this program's actual children and handoffs. -/
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
        decoderFuel d m q (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
          16 * q + 112 := by
  let rows := List.ofFn (fun i ↦ (domain i, received i))
  let setup := SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL
  have hr := InterpolationDispatch.returned_attempt k d m A rows found hi
  obtain ⟨out, cost, hd, ho, hb⟩ := runPrepared_exact k d m A domain received found setup
    hr hdepth hk hD hnq hA hm hchar hweight
  have hi' : InterpolationDispatch.run k d m A rows =
      (some found, (InterpolationDispatch.run k d m A rows).2) := Prod.ext hi rfl
  have he := run_of_interpolation k d m A rows hodd hL found _ cost out hi' hd
  refine ⟨out, _, he, ho, ?_⟩
  have hc := InterpolationDispatch.cost_le k d m A rows
  have hs := setup.cost_bound
  simp only [rows, List.length_ofFn] at hc
  dsimp only [setup, rows] at hs hb ⊢
  omega

/-- Successful budgeted interpolation supplies one exact decoder execution. -/
theorem runWithBudget_exact_of_interpolation (k d m J A : ℕ) {n : ℕ}
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hodd : q ≠ 2) (hL : m * A ≤ q ^ 2)
    (found : AmbientSearchMachine.Output (ZMod q))
    (hi : (InterpolationDispatch.runWithBudget k d m J A
      (List.ofFn (fun i ↦ (domain i, received i)))).1 = some found)
    (hdepth : d ≤ found.degree) (hk : k ≤ found.degree + 1)
    (hD : found.degree ≤ n) (hnq : n ≤ q) (hA : A ≤ n)
    (hchar : IsBelowCharacteristic found.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d)
        found.degree m J A found.interpolant))
    (hweight : differentialWeightedDegree found.degree
      (NonzeroInterpolationMachine.sourceOutputWithBudget (d := d)
        found.degree m J A found.interpolant) < m * A) :
    ∃ out cost,
      runWithBudget k d m J A (List.ofFn (fun i ↦ (domain i, received i))) hodd hL =
        (some out, cost) ∧ ExactOutput domain received k A out ∧
      cost ≤ InterpolationDispatch.budgetWithBudget k d m J A n +
        SetupMachine.budget q (m * A) +
        decoderFuelWithBudget d m J q
          (if 2 * (m * A + d - (found.degree + 1)) ≤ q then 1 else 2) +
        16 * q + 112 := by
  let rows := List.ofFn (fun i ↦ (domain i, received i))
  let setup := SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL
  have hr := InterpolationDispatch.returned_attemptWithBudget k d m J A rows found hi
  obtain ⟨out, cost, hd, ho, hb⟩ :=
    runPreparedWithBudget_exact k d m J A domain received found setup hr hdepth hk hD hnq hA hL
      hchar hweight
  have hi' : InterpolationDispatch.runWithBudget k d m J A rows =
      (some found, (InterpolationDispatch.runWithBudget k d m J A rows).2) := Prod.ext hi rfl
  have he := runWithBudget_of_interpolation k d m J A rows hodd hL found _ cost out hi' hd
  refine ⟨out, _, he, ho, ?_⟩
  have hc := InterpolationDispatch.costWithBudget_le k d m J A rows
  have hs := setup.cost_bound
  simp only [rows, List.length_ofFn] at hc
  dsimp only [setup, rows] at hs hb ⊢
  omega

end ReedSolomon.ListDecoding.QuadraticDecoderMachine

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderMachine
/-!
# Same-run composition of the quadratic decoder

These equations connect concrete completed child traces to the surrounding executable, including
the actual embedding charge in the restricted branch. Setup integrity supplies the observed
alphabet counts. No independent mathematical decoder output is substituted into the program.
The full interpolation/parameter existence proofs and bit-cost refinement remain separate.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticDecoderMachine

open HiddenDerivative QuadraticAlgebra
open PreparedDecoderMachine (Input Element)

variable {q : ℕ} [Fact q.Prime]

/-- Certified base counts let the actual embedding run finish at its scalar-parameter fuel. -/
theorem chooseAlphabets_restricted {a : ZMod q} (L : ℕ) (data : SetupMachine.Prepared q a)
    (hc : SetupMachine.Correct L a data) :
    ∃ cost : BaseEmbeddingMachine.Cost,
      BaseEmbeddingMachine.runFuel (2 * data.baseCount + 2)
        (.scan data.base [] : BaseEmbeddingMachine.Configuration (ZMod q) a) =
          (.done (BaseEmbeddingMachine.embedded data.base), cost) ∧
      cost.total = 16 * q + 8 ∧
      chooseAlphabets data true =
        (some ⟨BaseEmbeddingMachine.embedded data.base,
          BaseEmbeddingMachine.embedded data.base, 1⟩, 16 * q + 40) := by
  obtain ⟨cost, hr, hcost⟩ := BaseEmbeddingMachine.evaluation_runFuel (a := a) data.base
  rw [hc.base_length] at hr hcost
  refine ⟨cost, hr, ?_, ?_⟩
  · simpa only [hc.base_count] using hcost
  · simp only [chooseAlphabets, if_true, hr]
    rw [hcost, hc.base_count]

/-- A full-alphabet child trace determines the entire prepared execution and all handoff costs. -/
theorem runPrepared_full_of_trace (k d m A : ℕ) (rows : List (ZMod q × ZMod q))
    (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A))
    (hfull : ¬2 * (m * A + d - (found.degree + 1)) ≤ q)
    (steps cost : ℕ) (out : List (List (ZMod q)))
    (ht : let input : Input (ZMod q) setup.parameter :=
        ⟨setup.data.alphabet, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
      SeparateSampleDecoder.Trace input setup.data.samples setup.correct.nonsquare steps
        (.start found.interpolant.terms) cost (.done (some out)))
    (hb : steps ≤ decoderFuel d m q 2) :
    runPrepared k d m A rows found setup = (some out, cost + 72) := by
  have hr := runCore_of_trace _ _ _ _ m 2 steps cost out ht hb
  simp only [runPrepared, decide_eq_false hfull, chooseAlphabets, Bool.false_eq_true,
    if_false, hr]
  congr 1
  omega

/-- Restricted execution uses the actual embedded alphabet for both centers and guards.
The scalar embedding is executed and charged in addition to the prepared child. -/
theorem runPrepared_restricted_of_trace (k d m A : ℕ) (rows : List (ZMod q × ZMod q))
    (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A))
    (hbase : 2 * (m * A + d - (found.degree + 1)) ≤ q)
    (steps cost : ℕ) (out : List (List (ZMod q)))
    (ht : let W := BaseEmbeddingMachine.embedded (a := setup.parameter) setup.data.base
      let input : Input (ZMod q) setup.parameter :=
        ⟨W, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
      SeparateSampleDecoder.Trace input W setup.correct.nonsquare steps
        (.start found.interpolant.terms) cost (.done (some out)))
    (hb : steps ≤ decoderFuel d m q 1) :
    runPrepared k d m A rows found setup = (some out, 16 * q + cost + 80) := by
  obtain ⟨_ec, _hembed, _hecost, hchoice⟩ :=
    chooseAlphabets_restricted (m * A) setup.data setup.correct
  have hr := runCore_of_trace _ _ _ _ m 1 steps cost out ht hb
  simp only [runPrepared, decide_eq_true hbase, hchoice, hr]
  congr 1
  omega

/-- Interpolation, observed setup and prepared decoding compose into one executable result. -/
theorem run_of_interpolation (k d m A : ℕ) (rows : List (ZMod q × ZMod q))
    (hodd : q ≠ 2) (hL : m * A ≤ q ^ 2)
    (found : AmbientSearchMachine.Output (ZMod q)) (interpolationCost decodingCost : ℕ)
    (out : List (List (ZMod q)))
    (hi : InterpolationDispatch.run k d m A rows = (some found, interpolationCost))
    (hd : runPrepared k d m A rows found
      (SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL) =
        (some out, decodingCost)) :
    run k d m A rows hodd hL =
      (some out, interpolationCost +
        (SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL).cost.total +
          decodingCost + 32) := by
  simp only [run, hi, hd]

/-- A full-alphabet trace determines budget-aware prepared execution. -/
theorem runPreparedWithBudget_full_of_trace (k d m J A : ℕ)
    (rows : List (ZMod q × ZMod q)) (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A))
    (hfull : ¬2 * (m * A + d - (found.degree + 1)) ≤ q)
    (steps cost : ℕ) (out : List (List (ZMod q)))
    (ht : let input : Input (ZMod q) setup.parameter :=
        ⟨setup.data.alphabet, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
      SeparateSampleDecoder.Trace input setup.data.samples setup.correct.nonsquare steps
        (.start found.interpolant.terms) cost (.done (some out)))
    (hb : steps ≤ decoderFuelWithBudget d m J q 2) :
    runPreparedWithBudget k d m J A rows found setup = (some out, cost + 72) := by
  have hr := runCoreWithBudget_of_trace _ _ _ _ m J 2 steps cost out ht hb
  simp only [runPreparedWithBudget, decide_eq_false hfull, chooseAlphabets,
    Bool.false_eq_true, if_false, hr]
  congr 1
  omega

/-- Restricted traces determine budget-aware prepared execution, including embedding cost. -/
theorem runPreparedWithBudget_restricted_of_trace (k d m J A : ℕ)
    (rows : List (ZMod q × ZMod q)) (found : AmbientSearchMachine.Output (ZMod q))
    (setup : SetupMachine.CertifiedOutput q (m * A))
    (hbase : 2 * (m * A + d - (found.degree + 1)) ≤ q)
    (steps cost : ℕ) (out : List (List (ZMod q)))
    (ht : let W := BaseEmbeddingMachine.embedded (a := setup.parameter) setup.data.base
      let input : Input (ZMod q) setup.parameter :=
        ⟨W, setup.data.samples, rows, d, found.degree, m * A, k, A⟩
      SeparateSampleDecoder.Trace input W setup.correct.nonsquare steps
        (.start found.interpolant.terms) cost (.done (some out)))
    (hb : steps ≤ decoderFuelWithBudget d m J q 1) :
    runPreparedWithBudget k d m J A rows found setup =
      (some out, 16 * q + cost + 80) := by
  obtain ⟨_ec, _hembed, _hecost, hchoice⟩ :=
    chooseAlphabets_restricted (m * A) setup.data setup.correct
  have hr := runCoreWithBudget_of_trace _ _ _ _ m J 1 steps cost out ht hb
  simp only [runPreparedWithBudget, decide_eq_true hbase, hchoice, hr]
  congr 1
  omega

/-- Budgeted interpolation, setup and prepared decoding compose into one result. -/
theorem runWithBudget_of_interpolation (k d m J A : ℕ)
    (rows : List (ZMod q × ZMod q)) (hodd : q ≠ 2) (hL : m * A ≤ q ^ 2)
    (found : AmbientSearchMachine.Output (ZMod q)) (interpolationCost decodingCost : ℕ)
    (out : List (List (ZMod q)))
    (hi : InterpolationDispatch.runWithBudget k d m J A rows =
      (some found, interpolationCost))
    (hd : runPreparedWithBudget k d m J A rows found
      (SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL) =
        (some out, decodingCost)) :
    runWithBudget k d m J A rows hodd hL =
      (some out, interpolationCost +
        (SetupMachine.certifiedRun (m * A) (Fact.out : q.Prime) hodd hL).cost.total +
          decodingCost + 32) := by
  simp only [runWithBudget, hi, hd]

end ReedSolomon.ListDecoding.QuadraticDecoderMachine

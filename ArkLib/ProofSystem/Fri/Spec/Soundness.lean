/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.Spec.VerifierExecution
public import ArkLib.ProofSystem.Fri.Spec.InputRelation
public import ArkLib.OracleReduction.Security.Acceptance

/-!
# End-to-end soundness of the FRI oracle reduction

The computable `reduction` performs `k + 1` folds and samples `l` independent queries with
replacement. Its initial degree bound is `2 ^ (∑ i, (s i).val) * d.val`. The total error is
the sum of the powers-generator MCA errors, plus `Real.toNNReal (1 - min θ δ) ^ l`.

`soundness_proximity` bounds any acceptance for inputs at relative distance at least `δ`.
`soundness` uses the specification's closed-ball input relation, and `rbr_soundness` gives
the per-challenge guarantee. All bounds concern arbitrary adaptive provers in the actual
execution, including private prover state and shared oracle state.

The real parameters are unrestricted; useful numerical bounds require the hypotheses of
the chosen MCA estimate. At `l = 0`, the query term is one and the total bound is vacuous.
These results assert ordinary and round-by-round soundness, without a knowledge extractor
or an extraction-time bound.

The analysis follows the March 27, 2026 revision of [GMW25]. The correspondence and credit
to the earlier `zksecurity/simple-rbr-fri` development are in `docs/kb/audits/fri-soundness.md`.

## References

* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]
-/

@[expose] public section

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [SampleableType F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- Sum of the per-fold MCA errors and the repeated-query error. -/
noncomputable def soundnessError (θ δ : ℝ) : ℝ≥0 :=
  (∑ i, foldingError (ω := ω) s d θ i) + Real.toNNReal (1 - min θ δ) ^ l

/-- End-to-end ordinary soundness, in the stronger form of bounding any acceptance for
inputs at relative distance at least `δ` from the initial Reed–Solomon code. -/
theorem soundness_proximity (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ δ : ℝ) [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k s d hdom l).verifier.toVerifier.soundness init impl
      ((initialOracle (ω := ω) s) ⁻¹' proximityLanguage s d δ) Set.univ
      (soundnessError (ω := ω) s d l θ δ) := by
  apply Verifier.soundness_of_rejection_event (pSpec := pSpec k (ω := ω) s l) init impl _ _ _
    (fun stmt tr ↦ queryBad s d l (round_bound hdom) (initialOracle s stmt)
      (Transcript.restrict (b := Fin.last _)
        (by simp only [Fin.val_succ, Fin.val_last]; omega) tr))
  · intro stmt _ tr hbad
    rw [reduction_run, ite_eq_right hbad]
  · intro WitIn WitOut wit prover stmt hstmt os
    have h := terminalEvent_prob_le s d l (round_bound hdom) θ δ impl prover stmt hstmt wit
      (fun tr ↦ queryBad s d l (round_bound hdom) (initialOracle s stmt)
        (Transcript.restrict (b := Fin.last _)
          (by simp only [Fin.val_succ, Fin.val_last]; omega) tr))
      (fun _ h ↦ h) os
    simpa only [soundnessError, ENNReal.coe_add, ENNReal.coe_pow,
      ENNReal.ofNNReal_finsetSum, ENNReal.ofReal] using h

/-- Soundness of the specified FRI oracle reduction, with its existing input and output
relations. In fact, `soundness_proximity` bounds any acceptance, not only valid outputs. -/
theorem soundness (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ : ℝ≥0) [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k (ω := ω) s d hdom l).verifier.soundness init impl
      (inputRelation k s d hdom δ).language (outputRelation k s d hdom δ).language
      (soundnessError (ω := ω) s d l θ δ) := by
  intro WitIn WitOut wit prover stmt hstmt
  have hnot : initialOracle s stmt ∉ proximityLanguage s d (δ : ℝ) :=
    fun h ↦ hstmt (mem_inputLanguage_of_proximity s d hdom δ stmt h)
  have h := soundness_proximity s d l hdom θ δ init impl
    WitIn WitOut wit prover stmt hnot
  refine le_trans ?_ h
  apply prEvent_mono _ _ _
  intro _ _
  exact Set.mem_univ _

/-- Round-by-round soundness outside the closed-ball input language. Each folding challenge
incurs its MCA error; the final query vector incurs the repeated-query error. -/
theorem rbr_soundness (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ : ℝ≥0) [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k (ω := ω) s d hdom l).verifier.rbrSoundnessAveraged init impl
      (inputRelation k s d hdom δ).language (outputRelation k s d hdom δ).language
      (challengeError (ω := ω) s d l θ δ) := by
  apply Verifier.rbrSoundness_implies_rbrSoundnessAveraged
  apply Verifier.rbrSoundness_of_badEvents
    (bad := fun j stmt tr ↦ badEvent s d l (round_bound hdom) θ j (initialOracle s stmt) tr)
  · intro stmt tr _ hsafe
    have hbad : ¬ queryBad s d l (round_bound hdom) (initialOracle s stmt)
        (Transcript.restrict (b := Fin.last _)
          (by simp only [Fin.val_succ, Fin.val_last]; omega) tr) := by
      intro hquery
      exact hsafe (queryChallenge s l)
        ((badEvent_query s d l (round_bound hdom) θ (initialOracle s stmt) _).mpr hquery)
    have hrun := reduction_run s l d hdom stmt tr
    rw [ite_eq_right hbad] at hrun
    have hv : (reduction k s d hdom l).verifier.toVerifier.run stmt tr = failure :=
      OptionT.ext hrun
    rw [hv]
    change Pr{let result ← OptionT.mk do
      (simulateQ impl (pure none)).run' (← init)}[
        result ∈ (outputRelation k s d hdom δ).language] = 0
    rw [OptionT.prEvent_mk]
    simp [StateT.run'_eq, StateT.run_pure]
  · intro stmt hstmt j tr hbefore
    apply badEvent_prob_le s d l (round_bound hdom) θ δ (initialOracle s stmt)
    · exact fun h ↦ hstmt (mem_inputLanguage_of_proximity s d hdom δ stmt h)
    · rintro (hclose | hbad)
      · exact hstmt (mem_inputLanguage_of_proximity s d hdom δ stmt hclose)
      · exact hbefore (Or.inr hbad)

end Fri.Spec

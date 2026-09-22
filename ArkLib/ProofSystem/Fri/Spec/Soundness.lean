/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Fri.Spec.VerifierExecution
import ArkLib.ProofSystem.Fri.Spec.InputRelation
import ArkLib.OracleReduction.Security.Acceptance

/-!
# End-to-end soundness of the FRI oracle reduction

The bound applies to the existing composed verifier and every adaptive prover in ArkLib's
ordinary soundness game. Folding errors reuse ArkLib's powers-generator MCA error; the query
term follows the March 27, 2026 revision of [GMW25]. See `docs/kb/audits/fri-soundness.md`
for the source correspondence and credit to the earlier `zksecurity/simple-rbr-fri` development.

## References

* [Garreta, A., Mohnblatt, N., Wagner, B., *A Simplified Round-by-round Soundness Proof
  of FRI*][GMW25]
-/

namespace Fri.Spec

open Domain OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+) (l : ℕ)

/-- The total FRI error: one existing MCA error per fold and one independent-query term. -/
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
    rw [reduction_run, if_neg hbad]
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
  apply probEvent_mono''
  intro _ _
  exact Set.mem_univ _

/-- Round-by-round soundness for the actual composed FRI verifier. Prover moves preserve
the persistent bad-event state; each folding challenge incurs its MCA error and the final
query vector incurs the independent-query error. -/
theorem rbrSoundness (hdom : 2 ^ (∑ j, (s j).val) * d.val ≤ 2 ^ n)
    (θ : ℝ) (δ : ℝ≥0) [∀ j, SampleableType ((pSpec k (ω := ω) s l).Challenge j)]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl (emptySpec.{0, 0}) (StateT σ ProbComp)) :
    (reduction k (ω := ω) s d hdom l).verifier.rbrSoundness init impl
      (inputRelation k s d hdom δ).language (outputRelation k s d hdom δ).language
      (challengeError (ω := ω) s d l θ δ) := by
  apply Verifier.rbrSoundness_of_badEvents
    (bad := fun j stmt tr ↦ badEvent s d l (round_bound hdom) θ j (initialOracle s stmt) tr)
  · intro stmt tr _ hsafe
    have hbad : ¬ queryBad s d l (round_bound hdom) (initialOracle s stmt)
        (Transcript.restrict (b := Fin.last _)
          (by simp only [Fin.val_succ, Fin.val_last]; omega) tr) := by
      simpa only [badEvent_query] using hsafe (queryChallenge s l)
    have hrun := reduction_run s l d hdom stmt tr
    rw [if_neg hbad] at hrun
    have hv : (reduction k s d hdom l).verifier.toVerifier.run stmt tr = failure :=
      OptionT.ext hrun
    rw [hv]
    change Pr[ (· ∈ (outputRelation k s d hdom δ).language) | OptionT.mk do
      (simulateQ impl (pure none)).run' (← init)] = 0
    simp [StateT.run'_eq, StateT.run_pure]
  · intro stmt hstmt j tr hbefore
    apply badEvent_prob_le s d l (round_bound hdom) θ δ (initialOracle s stmt)
    · exact fun h ↦ hstmt (mem_inputLanguage_of_proximity s d hdom δ stmt h)
    · rintro (hclose | hbad)
      · exact hstmt (mem_inputLanguage_of_proximity s d hdom δ stmt hclose)
      · exact hbefore (Or.inr hbad)

end Fri.Spec

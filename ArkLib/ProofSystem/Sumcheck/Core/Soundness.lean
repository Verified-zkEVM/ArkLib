/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.LegacyEquivalence
public import ArkLib.Interaction.Core.Legacy.OracleSecurity

/-!
# Soundness of Sumcheck in the interaction layer

The interaction-layer Sumcheck verifier is sound for the Sumcheck languages, against every prover
and every prover output type, with error the sum over the challenges of `deg / |R|`, the error of
the legacy knowledge soundness.

The legacy Sumcheck states round-by-round knowledge soundness; round-by-round soundness follows by
`Verifier.rbrSoundness_of_rbrKnowledgeSoundness`, and soundness by the guarded implication
`OracleVerifier.soundness_of_rbrSoundness_of_guarded`, all in the legacy layer. The result is
then transferred through the equivalence of `LegacyEquivalence` and `oracleSoundness_iff`, with
no loss. Challenges are sampled uniformly. Since the legacy specification has one challenge per
round, the error is `n * (deg / |R|)`.
-/

@[expose] public section

namespace Sumcheck.Core
open scoped ENNReal NNReal
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Interaction.Core.Legacy

variable (R : Type) [CommSemiring R] [DecidableEq R] [SampleableType R] (deg n : ℕ)
  {d : ℕ} (D : Fin d ↪ R) {ι : Type} (ambient : OracleSpec ι)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Soundness of the interaction-layer Sumcheck verifier: a statement outside the round-`0`
language is accepted into the final language with probability at most `deg / |R|` per challenge,
for every prover. -/
theorem verifier_soundness [Fintype R] [IsDomain R] :
    ∀ Out : PathAlong oracleSig (protocol R deg n) → Type,
      letI : MeasurableSpace (Observation oracleSig (protocol R deg n) Out
        (fun _ => Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i))) :=
          ⊤
      soundness ((verifier R deg n D ambient).classicalModel (Out := Out) init impl
          (challengeQueryImpl oracleSig (protocol R deg n)))
        (langProblem (Spec.relationRound R n deg D 0).language)
        (langProblem (Spec.relationRound R n deg D (Fin.last n)).language)
        (fun obs => projectPathAlong oracleSig _ obs.1) (fun obs => obs.2.2)
        ((∑ _ : (Spec.pSpec R deg n).ChallengeIdx, (deg : ℝ≥0) / Fintype.card R : ℝ≥0) :
          ℝ≥0∞) := by
  let : ∀ t, Inhabited (ambient.Range t) := fun t => ⟨supportedAnswer init impl t⟩
  rw [challengeQueryImpl_eq_legacy]
  intro Out
  refine ((verifier_agrees R deg n D ambient).soundness_iff (mObs := ⊤) init impl _ _ _ _ _).mpr ?_
  revert Out
  refine (OracleVerifier.soundness_cast _ _ _ _ _ _ _ _).mpr ?_
  simpa only [OracleVerifier.langProblem_cast, polyFamily, family] using (oracleSoundness_iff init
    impl (Spec.oracleVerifier R deg D n ambient) _ _ _).mpr
    (OracleVerifier.soundness_of_rbrSoundness_of_guarded
      (Spec.oracleVerifierGuardedForm R deg D n ambient)
      (_root_.Verifier.rbrSoundness_of_rbrKnowledgeSoundness (init := init) (impl := impl)
        (Spec.oracleVerifier_rbrKnowledgeSoundness R deg D n ambient)))

omit [DecidableEq R] [SampleableType R] in
/-- The legacy Sumcheck specification has one challenge per round. -/
theorem card_challengeIdx : Fintype.card (Spec.pSpec R deg n).ChallengeIdx = n := by
  let e : (Spec.pSpec R deg n).ChallengeIdx ≃ Fin n :=
    { toFun := fun k => (Fin.splitSum k.1).1
      invFun := fun i => ⟨Fin.embedSum i 1, by
        change Fin.vflatten _ _ = _
        rw [Fin.vflatten_embedSum]
        rfl⟩
      left_inv := fun k => by
        obtain ⟨k, hk⟩ := k
        apply Subtype.ext
        change Fin.embedSum _ 1 = k
        have hsplit := Fin.embedSum_splitSum k
        change Fin.vflatten (fun _ => (Spec.SingleRound.pSpec R deg).dir) k = _ at hk
        rw [← hsplit, Fin.vflatten_embedSum] at hk
        have h1 : (Fin.splitSum k).2 = 1 := by
          revert hk
          generalize (Fin.splitSum k).2 = j
          fin_cases j
          · simp only [Fin.zero_eta, Fin.isValue]
            exact fun h => absurd h (by decide)
          · simp
        conv_rhs => rw [← hsplit]
        rw [h1]
      right_inv := fun i => by
        change (Fin.splitSum (Fin.embedSum i 1)).1 = i
        rw [Fin.splitSum_embedSum] }
  exact (Fintype.card_congr e).trans (Fintype.card_fin n)

/-- Soundness of the interaction-layer Sumcheck verifier with error `n * (deg / |R|)`. -/
theorem verifier_soundness_rounds [Fintype R] [IsDomain R] :
    ∀ Out : PathAlong oracleSig (protocol R deg n) → Type,
      letI : MeasurableSpace (Observation oracleSig (protocol R deg n) Out
        (fun _ => Spec.StatementRound R n (Fin.last n) × (∀ i, Spec.OracleStatement R n deg i))) :=
          ⊤
      soundness ((verifier R deg n D ambient).classicalModel (Out := Out) init impl
          (challengeQueryImpl oracleSig (protocol R deg n)))
        (langProblem (Spec.relationRound R n deg D 0).language)
        (langProblem (Spec.relationRound R n deg D (Fin.last n)).language)
        (fun obs => projectPathAlong oracleSig _ obs.1) (fun obs => obs.2.2)
        ((n * ((deg : ℝ≥0) / Fintype.card R) : ℝ≥0) : ℝ≥0∞) := by
  have h := verifier_soundness R deg n D ambient init impl
  rwa [Finset.sum_const, Finset.card_univ, card_challengeIdx, nsmul_eq_mul] at h

end Sumcheck.Core

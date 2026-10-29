/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.Completeness

/-!
# Fixed default challenges do not preserve completeness error

One Boolean challenge suffices: the prover always succeeds, and the verifier accepts exactly
when the challenge differs from the default. Interactive acceptance has probability one half;
replaying the default challenge always rejects.
-/

namespace FiatShamirCompletenessTest

open ProtocolSpec OracleSpec OracleComp
open scoped NNReal ENNReal

instance : VCVCompatible Unit where
instance : VCVCompatible Bool where

/-- A single Boolean challenge, with no prover messages. -/
abbrev spec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Bool]⟩

/-- A lossless prover that ignores the challenge. -/
def prover : Prover []ₒ Unit Unit Unit Unit spec where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i _ => by
    have hfalse : False := by
      have hi : i.1 = 0 := Fin.fin_one_eq_zero _
      have h := i.2
      simp [hi, spec] at h
    exact hfalse.elim
  receiveChallenge := fun _ _ => pure (fun _ => ())
  output := fun _ => pure ((), ())

/-- Reject the default challenge. -/
def reduction : Reduction []ₒ Unit Unit Unit Unit spec where
  prover := prover
  verifier := ⟨fun _ tr => if (show Bool from tr 0) = (default : Bool) then failure else pure ()⟩

/-- There are no base queries or state effects. -/
def impl : QueryImpl []ₒ (StateT Unit ProbComp) := fun q => nomatch q

/-- The old initialization always answered with the default Boolean. -/
def defaultTable : QueryImpl (srChallengeOracle Unit spec) Id :=
  fun ⟨⟨⟨0, _⟩, _⟩, _⟩ => (default : Bool)

/-- The transcript of the single challenge round. -/
def transcript (b : Bool) : spec.FullTranscript := fun | ⟨0, _⟩ => b

/-- The original reduction has completeness error one half. -/
theorem interactive_complete :
    reduction.completeness (pure ()) impl Set.univ Set.univ (1 / 2) := by
  intro stmt wit _
  have hr : (simulateQ (impl.addLift challengeQueryImpl :
      QueryImpl _ (StateT Unit ProbComp)) (reduction.run stmt wit).run).run' () =
      (do
        let b ← $ᵗ Bool
        pure ((if b = false then none else some ()).map
          (fun v => ((transcript b, (), ()), v)))) := by
    let : VerifierOnly spec := { verifier_first' := rfl }
    erw [Reduction.run_run_eq_bind, Prover.run_of_verifier_first stmt wit reduction.prover]
    simp only [Verifier.run, reduction, prover, liftComp_eq_liftM, liftM_pure,
      pure_bind, bind_assoc]
    erw [StateT.run'_eq]
    simp only [simulateQ_bind, StateT.run_bind, map_bind]
    erw [simulateQ_addLift_challengeQueryImpl_getChallenge impl
      (⟨0, rfl⟩ : spec.ChallengeIdx), StateT.run_monadLift]
    simp only [monadLift_self, bind_assoc, pure_bind]
    apply bind_congr
    intro b
    cases b <;> rfl
  simp only [pure_bind]
  erw [hr]
  simp only [OptionT.prEvent_mk, map_bind, map_pure, Option.elim_map,
    Set.mem_univ, and_self, Function.comp_def]
  have he : (fun b : Bool => (if b = false then none else some ()).elim False
      (fun _ => True)) = (fun b => b = true) := by
    funext b
    cases b <;> simp
  change (1 - ↑(1 / 2 : ℝ≥0) : ℝ≥0∞) ≤
    Pr{let b ← $ᵗ Bool}[(if b = false then none else some ()).elim False (fun _ => True)]
  rw [he]
  norm_num [SampleableType.prEvent_uniformSample_eq_singleton, Finset.filter_eq']

/-- The conclusion of the old fixed-default completeness claim is false. -/
theorem fixed_default_not_complete :
    ¬ reduction.fiatShamir.completeness (pure ((), defaultTable))
      (impl.addLift fsChallengeQueryImpl') Set.univ Set.univ (1 / 2) := by
  intro h
  have hr : (simulateQ
      ((impl.addLift fsChallengeQueryImpl' :
        QueryImpl ([]ₒ + srChallengeOracle Unit spec)
          (StateT (Unit × QueryImpl (srChallengeOracle Unit spec) Id) ProbComp)).addLift
          challengeQueryImpl :
        QueryImpl _ (StateT (Unit × QueryImpl (srChallengeOracle Unit spec) Id) ProbComp))
      (reduction.fiatShamir.run () ()).run).run' ((), defaultTable) = pure none := by
    rw [Reduction.fiatShamir_run_option]
    simp only [liftComp_eq_liftM]
    rfl
  have h := h () () (Set.mem_univ _)
  simp only [pure_bind] at h
  erw [hr] at h
  norm_num [OptionT.prEvent_mk] at h

/-- Fixed default tables cannot preserve arbitrary completeness errors. -/
theorem old_completeness_claim_false :
    ¬ ∀ R : Reduction []ₒ Unit Unit Unit Unit spec,
      R.completeness (pure ()) impl Set.univ Set.univ (1 / 2) →
      R.fiatShamir.completeness (pure ((), defaultTable))
        (impl.addLift fsChallengeQueryImpl') Set.univ Set.univ (1 / 2) := by
  intro h
  exact fixed_default_not_complete (h reduction interactive_complete)

end FiatShamirCompletenessTest

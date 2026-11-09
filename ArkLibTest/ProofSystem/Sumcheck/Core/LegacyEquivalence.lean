/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.LegacyEquivalence
import ArkLibTest.ProofSystem.Sumcheck.Core.Execution
import Mathlib.Data.ZMod.Basic

/-!
# The interaction-layer Sumcheck is the embedded legacy Sumcheck: tests

The embedded legacy single-round prover generates the expected transcript and output; against a
prover whose first round fails, the embedded legacy verifier draws every challenge and rejects, and
both decisions reject without an ambient query; with zero rounds the embedded legacy verifier
accepts the input claim at once.
-/

namespace Sumcheck.Core.LegacyEquivalenceTest

open Polynomial PFunctor Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec Interaction.Core.Legacy

/-! ## The embedded legacy prover generates the transcript -/

-- Migration rows: Sumcheck Interaction/Legacy #1 and #2.

noncomputable section

/-- The degree-one message `X`. -/
def polynomial : (ZMod 17)⦃≤ 1⦄[X] := ⟨X, Polynomial.mem_degreeLE.mpr Polynomial.degree_X_le⟩

/-- An oracle-capable ambient context, unused by the prover. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Unit

local instance : ∀ i, OracleInterface ((Spec.SingleRound.pSpec (ZMod 17) 1).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

/-- The legacy single-round prover, with its challenge answered by `r`, sends `p`, receives `r`
and outputs the target `p(r)` with history `r` and the unchanged oracle statement. -/
theorem legacy_prover_run (p : (ZMod 17)⦃≤ 1⦄[X]) (target r : ZMod 17) :
    simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec (ZMod 17) 1).Challenge) (roundFullTranscript p r).challenges)
      ((Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient).run (target, fun _ => p) ()) =
      pure (roundFullTranscript p r, ((p.val.eval r, r), fun _ : Unit => p), ()) := by
  have hfirst : (Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient).runToRound (1 : Fin 3)
      (target, fun _ => p) () =
      pure (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
        (pSpec := Spec.SingleRound.pSpec (ZMod 17) 1) p (fun i => Fin.elim0 i), p) := by
    erw [Prover.runToRound_succ (0 : Fin 2)]
    erw [Prover.processRound_of_dir_eq_P_to_V 0 rfl]
    simp [Spec.SingleRound.Simple.prover]
    rfl
  have hsecond : simulateQ
      (OracleInterface.simOracle ambient (T := (Spec.SingleRound.pSpec (ZMod 17) 1).Challenge)
        (roundFullTranscript p r).challenges)
      ((Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient).runToRound (2 : Fin 3)
        (target, fun _ => p) ()) =
      pure (ProtocolSpec.Transcript.concat (m := (1 : Fin 2)) r
        (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
          (pSpec := Spec.SingleRound.pSpec (ZMod 17) 1) p (fun i => Fin.elim0 i)),
        (p, r)) := by
    erw [Prover.runToRound_succ (1 : Fin 2)]
    erw [Prover.processRound_of_dir_eq_V_to_P 1 rfl, hfirst]
    simp [Spec.SingleRound.Simple.prover, ProtocolSpec.getChallenge]
    rfl
  simp only [Prover.run, simulateQ_bind]
  change (simulateQ _ ((Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient).runToRound
    (2 : Fin 3) (target, fun _ => p) ()) >>= _) = _
  rw [hsecond]
  have ht : ProtocolSpec.Transcript.concat (m := (1 : Fin 2)) r
      (ProtocolSpec.Transcript.concat (m := (0 : Fin 2))
        (pSpec := Spec.SingleRound.pSpec (ZMod 17) 1) p (fun i => Fin.elim0 i)) =
      roundFullTranscript p r := by
    funext i
    fin_cases i <;> rfl
  simp only [Spec.SingleRound.Simple.prover, pure_bind, monadLift_pure, simulateQ_pure]
  erw [ht]

/-- The embedded legacy single-round prover, run counterpart-first and decoded, generates the
same transcript and output as the legacy prover. -/
theorem embedded_prover_generates (p : (ZMod 17)⦃≤ 1⦄[X]) (target r : ZMod 17) :
    simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec (ZMod 17) 1).Challenge) (roundFullTranscript p r).challenges)
      ((fun z => (decode _ z.1, z.2.1)) <$>
        runWith .counterpartFirst (Legacy.protocol (Spec.SingleRound.pSpec (ZMod 17) 1))
          ((embedProver (Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient)
            (target, fun _ => p) ()).simulate (liftShared ambient _))
          (legacySampler _ (challengeOracle ambient _))) =
      pure (roundFullTranscript p r, ((p.val.eval r, r), fun _ : Unit => p), ()) := by
  rw [decode_runWith_counterpartFirst, legacy_prover_run]

/-- The legacy single-round prover on `X` with challenge five sends `X`, receives five and
outputs target `X(5) = 5` with history five; the oracle statement stays `X`. -/
example : simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec (ZMod 17) 1).Challenge)
      (roundFullTranscript polynomial 5).challenges)
      ((fun z => (decode _ z.1, z.2.1)) <$>
        runWith .counterpartFirst (Legacy.protocol (Spec.SingleRound.pSpec (ZMod 17) 1))
          ((embedProver (Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient)
            (1, fun _ => polynomial) ()).simulate (liftShared ambient _))
          (legacySampler _ (challengeOracle ambient _))) =
      pure (roundFullTranscript polynomial 5,
        (((5 : ZMod 17), 5), fun _ : Unit => polynomial), ()) := by
  rw [embedded_prover_generates]
  simp [polynomial]

/-- Generation does not read the claim: a wrong target two with challenge three. -/
example : simulateQ (OracleInterface.simOracle ambient
      (T := (Spec.SingleRound.pSpec (ZMod 17) 1).Challenge)
      (roundFullTranscript polynomial 3).challenges)
      ((fun z => (decode _ z.1, z.2.1)) <$>
        runWith .counterpartFirst (Legacy.protocol (Spec.SingleRound.pSpec (ZMod 17) 1))
          ((embedProver (Spec.SingleRound.Simple.prover (ZMod 17) 1 ambient)
            (2, fun _ => polynomial) ()).simulate (liftShared ambient _))
          (legacySampler _ (challengeOracle ambient _))) =
      pure (roundFullTranscript polynomial 3,
        (((3 : ZMod 17), 3), fun _ : Unit => polynomial), ()) := by
  rw [embedded_prover_generates]
  simp [polynomial]

end

/-! ## Rejection agreement -/

section Reject

open ExecutionTest

variable {ι : Type} (amb : OracleSpec ι) [∀ t, Inhabited (amb.Range t)]

/-- Against a prover whose first message misses the target, the embedded legacy verifier still
draws both challenges and rejects: its finalized run is the Sumcheck run's, which is `none` on
every challenge. -/
theorem legacy_run_badFirst {d : ℕ} (D : Fin d ↪ F) (bad : F⦃≤ 1⦄[X])
    (stmt : Spec.StatementRound F 2 0) (oStmt : ∀ i, Spec.OracleStatement F 2 1 i)
    (hbad : ∑ x ∈ Finset.univ.map D, bad.val.eval x ≠ stmt.target) :
    simulateQ (oracleChallengeReindex amb (Spec.pSpec F 1 2))
        (oracleFinalize <$> (embedOracleVerifier (Spec.oracleVerifier F 1 D 2 amb)).run
          stmt oStmt ((protocol_eq F 1 2) ▸ badFirstProver amb D bad stmt oStmt)) =
      simulateQ (challengeReindex F 1 2 amb)
        ((fun _ => none) <$> drawChallenges 2 (drawOf amb 2)) := by
  rw [← run_eq_legacy, run_badFirstProver amb D bad stmt oStmt hbad, Functor.map_map]
  rfl

/-- On the transcript of a bad first round, both decisions are `pure none` in every lawful
monad: they make no ambient query and reject together. -/
example {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl amb m) {d : ℕ}
    (D : Fin d ↪ F) (bad : F⦃≤ 1⦄[X]) (stmt : Spec.StatementRound F 2 0)
    (oStmt : ∀ i, Spec.OracleStatement F 2 1 i)
    (hbad : ∑ x ∈ Finset.univ.map D, bad.val.eval x ≠ stmt.target) (chals : Fin 2 → F) :
    let tr := foldTranscript (badFirst D bad) (nextState (badFirst D bad)) 2
      (initState stmt oStmt) chals
    simulateQ (QueryImpl.addLift impl ((sumFamily (polyFamily F 1 2) (pathFamily (protocol F 1 2)
        (FreeM.projectPathAlong oracleSig _ tr))).behaviorOfRealizations
          (sumData oStmt (payloads _ tr))))
      ((verifier F 1 2 D amb).decide stmt _ (toView _ tr)).run = (pure none : m _) ∧
    simulateQ (QueryImpl.addLift impl ((sumFamily (polyFamily F 1 2) (pathFamily (protocol F 1 2)
        (FreeM.projectPathAlong oracleSig _ tr))).behaviorOfRealizations
          (sumData oStmt (payloads _ tr))))
      ((legacyVerifier F 1 2 D amb).decide stmt _ (toView _ tr)).run = (pure none : m _) := by
  intro tr
  have hv : legacyVerdict F 1 2 D amb stmt (decodeTranscript 2 tr) = none :=
    legacyVerdict_eq_none (k := 1) stmt (roundFullTranscript bad (chals 0))
      (legacyTranscript 1 _ _) hbad
  have h := decide_trace F 1 2 D amb impl stmt oStmt tr
  rw [hv] at h
  exact h

end Reject

/-! ## Zero rounds -/

/-- With zero rounds the embedded legacy verifier accepts the input claim at once against the
Sumcheck honest prover, and the run draws nothing. -/
example {ι : Type} (amb : OracleSpec ι) [∀ t, Inhabited (amb.Range t)] {d : ℕ}
    (D : Fin d ↪ ExecutionTest.F) (stmt : Spec.StatementRound ExecutionTest.F 0 0)
    (oStmt : ∀ i, Spec.OracleStatement ExecutionTest.F 0 1 i) :
    simulateQ (oracleChallengeReindex amb (Spec.pSpec ExecutionTest.F 1 0))
        (oracleFinalize <$>
          (embedOracleVerifier (Spec.oracleVerifier ExecutionTest.F 1 D 0 amb)).run
            stmt oStmt ((protocol_eq ExecutionTest.F 1 0) ▸ honestProver D stmt oStmt)) =
      pure (some ((decodeTranscript 0 ⟨⟩, finishState (initState stmt oStmt)),
        (stmt, oStmt))) := by
  rw [← run_eq_legacy, run_verifier_honestProver]
  rfl

end Sumcheck.Core.LegacyEquivalenceTest

run_cmd do
  for decl in [``Sumcheck.Core.protocol_eq, ``Sumcheck.Core.oracleDecode_eq_decodeTranscript,
      ``Sumcheck.Core.verifier_agrees, ``Sumcheck.Core.challengeQueryImpl_eq_legacy,
      ``Sumcheck.Core.run_eq_legacy, ``Sumcheck.Core.legacyProver_pureChallengeSlots,
      ``Sumcheck.Core.run_legacyProver, ``Sumcheck.Core.decide_trace,
      ``Sumcheck.Core.LegacyEquivalenceTest.legacy_prover_run,
      ``Sumcheck.Core.LegacyEquivalenceTest.embedded_prover_generates,
      ``Sumcheck.Core.LegacyEquivalenceTest.legacy_run_badFirst] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"

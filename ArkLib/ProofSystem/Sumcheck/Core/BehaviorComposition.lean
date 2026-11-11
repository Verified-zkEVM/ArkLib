/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.FoldComposition
public import ArkLib.ProofSystem.Sumcheck.Core.Behavior

/-! # Public interval composition with arbitrary retained behavior -/

@[expose] public section

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec
variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ}
  {ι : Type} (ambient : OracleSpec ι) (D : Fin d → R)

/-- Resource interpretation of the public interval decision gives its transcript verdict. -/
theorem decideWith_behaviorIntervalVerifier (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, (Fin n → R) → R)
    (tr : PathAlong oracleSig (protocol R deg count)) :
    (behaviorIntervalVerifier (n := n) (deg := deg) D ambient start count bound).decideWith
      stmt _ (toView _ tr)
      (data, payloads _ tr) = pure (intervalVerdict D count
        (intervalInitial start count bound stmt) tr) :=
  simulateQ_foldVerifier_decide (QueryImpl.id' ambient) _ _ _ _ _ _

/-- The public one-round interval and its public suffix retain the arbitrary original behavior. -/
noncomputable def behaviorPublicIntervalCompatibility (start count : ℕ)
    (bound : start + (count + 1) ≤ n) :
    OracleVerifier.OutputCompatibility
      (behaviorIntervalVerifier (n := n) (deg := deg) D ambient start 1 (by omega))
      (fun _ => behaviorIntervalVerifier (n := n) (deg := deg) D ambient
        (1 + start) count (by omega)) where
  outputMap _ _ _ := OracleMap.fst _ _
  agrees _ _ _ _ _ _ := rfl

/-- The public suffix receives exactly the input behavior and its own message payloads. -/
theorem suffixRoute_behaviorPublicInterval (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, (Fin n → R) → R)
    (msg : R⦃≤ deg⦄[X]) (r : R) (tail : PathAlong oracleSig (protocol R deg count)) :
    (OracleVerifier.suffixRoute (s₂ := fun _ => protocol R deg count)
      (behaviorIntervalVerifier (n := n) (deg := deg) D ambient start 1 (by omega)) stmt _
      (toView _ (consTranscript msg r tail))).f (data, payloads _ (consTranscript msg r tail)) =
        (data, payloads _ tail) := by
  apply Prod.ext <;> rfl

/-- Appending the public interval interfaces composes their actual decisions. -/
theorem decideWith_append_behaviorPublicInterval (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, (Fin n → R) → R)
    (tr : PathAlong oracleSig (protocol R deg (count + 1))) :
    ((behaviorIntervalVerifier (n := n) (deg := deg) D ambient start 1 (by omega)).append
      (fun _ => behaviorIntervalVerifier (n := n) (deg := deg) D ambient
        (1 + start) count (by omega))
      (behaviorPublicIntervalCompatibility ambient D start count bound)).decideWith
        stmt _ (toView _ tr)
        (data, payloads _ tr) = pure
      ((intervalVerdict D 1 (intervalInitial start 1 (by omega) stmt)
        (roundTranscript (headMessage tr) (headChallenge tr))).bind fun mid =>
          intervalVerdict D count (intervalInitial (1 + start) count (by omega) mid)
            (tailTranscript tr)) := by
  rcases tr with ⟨msg, r, tail⟩
  erw [OracleVerifier.append_decideWith, split_toView_round, prefixRoute_round]
  refine (congrArg (fun z => z >>= _)
    (decideWith_behaviorIntervalVerifier ambient D start 1 (by omega) stmt data
      (roundTranscript msg r))).trans ?_
  refine (FreeM.pure_bind _ _).trans ?_
  erw [suffixRoute_behaviorPublicInterval ambient D start count bound]
  dsimp only [headMessage, headChallenge, tailTranscript]
  cases h : intervalVerdict D 1 (intervalInitial start 1 (by omega) stmt)
      (roundTranscript msg r) with
  | none => rfl
  | some mid =>
    exact decideWith_behaviorIntervalVerifier ambient D (1 + start) count (by omega) mid data tail

/-- The actual appended public interval run is the full interval run, after endpoint transport.
The comparison preserves the entire transcript, private prover output and original oracle. -/
theorem run_append_behaviorIntervalVerifier (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ _ : Unit, (Fin n → R) → R)
    {Out : PathAlong oracleSig (protocol R deg (count + 1)) → Type}
    (prover : Prover oracleSig ambient (protocol R deg (count + 1)) Out) :
    ((behaviorIntervalVerifier (n := n) (deg := deg) D ambient start 1 (by omega)).append
      (fun _ => behaviorIntervalVerifier (n := n) (deg := deg) D ambient
        (1 + start) count (by omega))
      (behaviorPublicIntervalCompatibility ambient D start count bound)).run stmt data prover =
      (fun result => (⟨result.1, result.2.1, result.2.2.map (fun t =>
        (t.1.transport (show (⟨count + 1 + start, by omega⟩ : Fin (n + 1)) =
          ⟨count + (1 + start), by omega⟩ from Fin.ext (by
            change count + 1 + start = count + (1 + start); omega)), t.2))⟩ :
              Observation oracleSig (protocol R deg (count + 1)) Out
                (fun _ => RoundStatement R n ⟨count + (1 + start), by omega⟩ ×
                  (∀ _ : Unit, (Fin n → R) → R)))) <$>
        (behaviorIntervalVerifier (n := n) (deg := deg) D ambient start (count + 1) bound).run
          stmt data prover := by
  have hd : data = fun _ => data () := funext fun u => by cases u; rfl
  rw [hd]
  rw [OracleVerifier.run_eq_decideWith, behaviorIntervalVerifier_run, foldVerifier_run,
    _root_.map_bind]
  refine bind_congr fun result => ?_
  rcases result with ⟨tr, out, u⟩
  dsimp only
  erw [decideWith_append_behaviorPublicInterval ambient D start count bound stmt data tr]
  rw [simulateQ_pure, LawfulMonad.pure_bind,
    LawfulApplicative.map_pure]
  rcases tr with ⟨msg, r, tail⟩
  have hv := intervalVerdict_succ_public D start count bound stmt msg r tail
  have hm := congrArg (Option.map (fun t => (t, data))) hv
  simp only [Option.map_map] at hm
  simpa only [OracleVerifier.append, behaviorPublicIntervalCompatibility, OracleMap.fst,
    headMessage, headChallenge, tailTranscript, Option.map_map, Function.comp_def,
    intervalVerdict, consTranscript, OracleVerifier.Output, splitFamily] using
    congrArg (fun decision => (pure ⟨⟨msg, r, tail⟩, out, decision⟩ :
    OracleComp (ambient + challengeSpec oracleSig (protocol R deg (count + 1)))
      (Observation oracleSig (protocol R deg (count + 1)) Out
        (fun _ => RoundStatement R n ⟨count + (1 + start), by omega⟩ ×
          (∀ _ : Unit, (Fin n → R) → R))))) hm.symm

end Sumcheck.Core

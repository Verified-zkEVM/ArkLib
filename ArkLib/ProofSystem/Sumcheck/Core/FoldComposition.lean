/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Interval

/-! # Composition of native passive round checks

Appending the next round to the remaining checks gives the actual fold run, against every
prover. All interactions run before the decisions, including after a rejected prefix.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {deg : ℕ} {ι : Type} (ambient : OracleSpec ι)
  {I : Type} {A : I → Type} (inputs : OracleFamily I A)
  {State : ℕ → Type} {T : Type} (V : RoundChecks R State) (finish : State 0 → T)

/-- Check just the next round, leaving its successor state for the suffix. -/
def foldHeadVerifier (k : ℕ) :
    OracleVerifier ambient (protocol R deg 1) (State (k + 1)) (fun _ => State k)
      inputs (fun _ => inputs) :=
  foldVerifier R deg ambient inputs (State := fun r => State (k + r))
    (fun r => V (k + r)) id 1

/-- Appending two verifiers that retain the input oracle retains that same oracle. -/
def nativeFoldCompatibility (k : ℕ) :
    OracleVerifier.OutputCompatibility (foldHeadVerifier (deg := deg) ambient inputs V k)
      (fun _ => foldVerifier R deg ambient inputs V finish k) where
  outputMap _ _ _ := OracleMap.fst _ _
  agrees _ _ _ _ _ _ := rfl

/-- The decision with resources answered is the pure transcript verdict. -/
theorem decideWith_foldVerifier (k : ℕ) (stmt : State k) (data : ∀ i, A i)
    (tr : PathAlong oracleSig (protocol R deg k)) :
    (foldVerifier R deg ambient inputs V finish k).decideWith stmt _ (toView _ tr)
      (data, payloads _ tr) = pure (foldVerdict V finish k stmt tr) :=
  Interpreted.simulate_verifier (QueryImpl.id' ambient) V finish k stmt data tr

/-- The next round's decision computes exactly its local verdict. -/
theorem decideWith_foldHeadVerifier (k : ℕ) (stmt : State (k + 1)) (data : ∀ i, A i)
    (msg : R⦃≤ deg⦄[X]) (r : R) :
    (foldHeadVerifier (deg := deg) ambient inputs V k).decideWith stmt _
      (toView _ (roundTranscript msg r)) (data, payloads _ (roundTranscript msg r)) =
        pure (roundVerdict (V k) stmt msg r) := by
  erw [foldHeadVerifier, decideWith_foldVerifier]
  simp only [foldVerdict, Interpreted.verdict, id_eq, Option.bind_fun_some, roundTranscript]
  rfl

/-- The suffix receives the original input and precisely its own message payloads. -/
theorem suffixRoute_foldHead (k : ℕ) (stmt : State (k + 1)) (data : ∀ i, A i)
    (msg : R⦃≤ deg⦄[X]) (r : R) (tail : PathAlong oracleSig (protocol R deg k)) :
    (OracleVerifier.suffixRoute (s₂ := fun _ => protocol R deg k)
      (foldHeadVerifier (deg := deg) ambient inputs V k) stmt _
        (toView _ (consTranscript msg r tail))).f
      (data, payloads _ (consTranscript msg r tail)) = (data, payloads _ tail) := by
  apply Prod.ext
  · rfl
  · rfl

/-- The appended decision agrees with the native fold on every completed transcript. -/
theorem decideWith_append_foldVerifier (k : ℕ) (stmt : State (k + 1)) (data : ∀ i, A i)
    (tr : PathAlong oracleSig (protocol R deg (k + 1))) :
    ((foldHeadVerifier (deg := deg) ambient inputs V k).append
      (fun _ => foldVerifier R deg ambient inputs V finish k)
      (nativeFoldCompatibility (deg := deg) ambient inputs V finish k)).decideWith stmt _
        (toView _ tr)
        (data, payloads _ tr) =
      (foldVerifier R deg ambient inputs V finish (k + 1)).decideWith stmt _ (toView _ tr)
        (data, payloads _ tr) := by
  rcases tr with ⟨msg, r, tail⟩
  erw [OracleVerifier.append_decideWith, split_toView_round, prefixRoute_round]
  refine (congrArg (fun z => z >>= _)
    (decideWith_foldHeadVerifier ambient inputs V k stmt data msg r)).trans ?_
  refine (pure_bind _ _).trans ?_
  erw [suffixRoute_foldHead]
  rw [decideWith_foldVerifier]
  rw [foldVerdict_succ]
  simp only [Interpreted.message, Interpreted.challenge, Interpreted.tail]
  cases h : roundVerdict (V k) stmt msg r with
  | none => rfl
  | some mid =>
    exact decideWith_foldVerifier ambient inputs V finish k mid data tail

/-- Appending a round to the remaining checks gives the actual native fold run. -/
theorem run_append_foldVerifier (k : ℕ) (stmt : State (k + 1)) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (protocol R deg (k + 1)) → Type}
    (prover : Prover oracleSig ambient (protocol R deg (k + 1)) Out) :
    ((foldHeadVerifier (deg := deg) ambient inputs V k).append
      (fun _ => foldVerifier R deg ambient inputs V finish k)
      (nativeFoldCompatibility (deg := deg) ambient inputs V finish k)).run stmt data prover =
      (foldVerifier R deg ambient inputs V finish (k + 1)).run stmt data prover := by
  rw [OracleVerifier.run_eq_decideWith, OracleVerifier.run_eq_decideWith]
  refine bind_congr fun result => ?_
  obtain ⟨tr, out, ⟨⟩⟩ := result
  dsimp only
  exact congrArg (fun decision => simulateQ _ decision >>= _)
    (decideWith_append_foldVerifier ambient inputs V finish k stmt data tr)

/-- Every bounded interval decomposes into its first round and its remaining rounds. This
identity compares actual oracle-verifier runs and retains arbitrary prover effects and outputs. -/
theorem run_append_intervalVerifier [DecidableEq R] {n d : ℕ} (D : Fin d → R)
    (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    {Out : PathAlong oracleSig (protocol R deg (count + 1)) → Type}
    (prover : Prover oracleSig ambient (protocol R deg (count + 1)) Out) :
    let checks := intervalCheck (stop := ⟨count + 1 + start, by omega⟩) D
    ((foldHeadVerifier (deg := deg) ambient (polynomialFamily R n deg) checks count).append
      (fun _ => foldVerifier R deg ambient (polynomialFamily R n deg) checks
        IntervalClaim.finish count)
      (nativeFoldCompatibility (deg := deg) ambient (polynomialFamily R n deg) checks
        IntervalClaim.finish count)).run
        (intervalInitial start (count + 1) bound stmt) data prover =
      (intervalVerifier R deg n D ambient start (count + 1) bound).run stmt data prover :=
  (run_append_foldVerifier ambient (polynomialFamily R n deg) _ IntervalClaim.finish count
    (intervalInitial start (count + 1) bound stmt) data prover).trans
      (intervalVerifier_run D ambient start (count + 1) bound stmt data prover).symm

section PublicIntervals
variable [DecidableEq R] {n d : ℕ} (D : Fin d → R)

/-- Resource interpretation of the public interval decision gives its transcript verdict. -/
theorem decideWith_intervalVerifier (start count : ℕ) (bound : start + count ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    (tr : PathAlong oracleSig (protocol R deg count)) :
    (intervalVerifier R deg n D ambient start count bound).decideWith stmt _ (toView _ tr)
      (data, payloads _ tr) = pure (intervalVerdict D count
        (intervalInitial start count bound stmt) tr) :=
  simulateQ_intervalVerifier_decide D (QueryImpl.id' ambient) start count bound stmt data tr

/-- The public one-round interval and its public suffix retain the original polynomial. -/
noncomputable def publicIntervalCompatibility (start count : ℕ) (bound : start + (count + 1) ≤ n) :
    OracleVerifier.OutputCompatibility
      (intervalVerifier R deg n D ambient start 1 (by omega))
      (fun _ => intervalVerifier R deg n D ambient (1 + start) count (by omega)) where
  outputMap _ _ _ := OracleMap.fst _ _
  agrees _ _ _ _ _ _ := rfl

/-- The public suffix receives exactly the input polynomial and its own message payloads. -/
theorem suffixRoute_publicInterval (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    (msg : R⦃≤ deg⦄[X]) (r : R) (tail : PathAlong oracleSig (protocol R deg count)) :
    (OracleVerifier.suffixRoute (s₂ := fun _ => protocol R deg count)
      (intervalVerifier R deg n D ambient start 1 (by omega)) stmt _
      (toView _ (consTranscript msg r tail))).f (data, payloads _ (consTranscript msg r tail)) =
        (data, payloads _ tail) := by
  apply Prod.ext <;> rfl

/-- Appending the public interval interfaces composes their actual decisions. -/
theorem decideWith_append_publicInterval (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    (tr : PathAlong oracleSig (protocol R deg (count + 1))) :
    ((intervalVerifier R deg n D ambient start 1 (by omega)).append
      (fun _ => intervalVerifier R deg n D ambient (1 + start) count (by omega))
      (publicIntervalCompatibility ambient D start count bound)).decideWith stmt _ (toView _ tr)
        (data, payloads _ tr) = pure
      ((intervalVerdict D 1 (intervalInitial start 1 (by omega) stmt)
        (roundTranscript (Interpreted.message tr) (Interpreted.challenge tr))).bind fun mid =>
          intervalVerdict D count (intervalInitial (1 + start) count (by omega) mid)
            (Interpreted.tail tr)) := by
  rcases tr with ⟨msg, r, tail⟩
  erw [OracleVerifier.append_decideWith, split_toView_round, prefixRoute_round]
  refine (congrArg (fun z => z >>= _)
    (decideWith_intervalVerifier ambient D start 1 (by omega) stmt data
      (roundTranscript msg r))).trans ?_
  refine (pure_bind _ _).trans ?_
  erw [suffixRoute_publicInterval ambient D start count bound]
  dsimp only [Interpreted.message, Interpreted.challenge, Interpreted.tail]
  cases h : intervalVerdict D 1 (intervalInitial start 1 (by omega) stmt)
      (roundTranscript msg r) with
  | none => rfl
  | some mid =>
    exact decideWith_intervalVerifier ambient D (1 + start) count (by omega) mid data tail

/-- The actual appended public interval run is the full interval run, after endpoint transport.
The comparison preserves the entire transcript, private prover output and original oracle. -/
theorem run_append_public_intervalVerifier (start count : ℕ) (bound : start + (count + 1) ≤ n)
    (stmt : RoundStatement R n ⟨start, by omega⟩) (data : ∀ i, PolynomialData R n deg i)
    {Out : PathAlong oracleSig (protocol R deg (count + 1)) → Type}
    (prover : Prover oracleSig ambient (protocol R deg (count + 1)) Out) :
    ((intervalVerifier R deg n D ambient start 1 (by omega)).append
      (fun _ => intervalVerifier R deg n D ambient (1 + start) count (by omega))
      (publicIntervalCompatibility ambient D start count bound)).run stmt data prover =
      (fun result => (⟨result.1, result.2.1, result.2.2.map (fun t =>
        (t.1.transport (show (⟨count + 1 + start, by omega⟩ : Fin (n + 1)) =
          ⟨count + (1 + start), by omega⟩ from Fin.ext (by
            change count + 1 + start = count + (1 + start); omega)), t.2))⟩ :
              Observation oracleSig (protocol R deg (count + 1)) Out
                (fun _ => RoundStatement R n ⟨count + (1 + start), by omega⟩ ×
                  (∀ i, PolynomialData R n deg i)))) <$>
        (intervalVerifier R deg n D ambient start (count + 1) bound).run stmt data prover := by
  rw [OracleVerifier.run_eq_decideWith, intervalVerifier_run, Interpreted.verifier_run,
    _root_.map_bind]
  refine bind_congr fun result => ?_
  rcases result with ⟨tr, out, u⟩
  dsimp only
  erw [decideWith_append_publicInterval ambient D start count bound stmt data tr]
  rw [simulateQ_pure, LawfulMonad.pure_bind,
    LawfulApplicative.map_pure]
  rcases tr with ⟨msg, r, tail⟩
  have hv := intervalVerdict_succ_public D start count bound stmt msg r tail
  have hm := congrArg (Option.map (fun t => (t, data))) hv
  simp only [Option.map_map] at hm
  simpa only [OracleVerifier.append, publicIntervalCompatibility, OracleMap.fst,
    Interpreted.message, Interpreted.challenge, Interpreted.tail, Option.map_map, Function.comp_def,
    intervalVerdict, consTranscript, OracleVerifier.Output, splitFamily] using
    congrArg (fun decision => (pure ⟨⟨msg, r, tail⟩, out, decision⟩ :
    OracleComp (ambient + challengeSpec oracleSig (protocol R deg (count + 1)))
      (Observation oracleSig (protocol R deg (count + 1)) Out
        (fun _ => RoundStatement R n ⟨count + (1 + start), by omega⟩ ×
          (∀ i, PolynomialData R n deg i))))) hm.symm

end PublicIntervals

end Sumcheck.Core

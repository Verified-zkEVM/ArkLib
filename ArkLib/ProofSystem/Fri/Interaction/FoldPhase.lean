/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.Core
import ArkLib.Interaction.Oracle.Chain

open Interaction.TwoParty

/-!
# FRI Interaction: Fold Phase

This module composes the `k` non-final FRI fold rounds over the
terminal-indexed `Interaction.Oracle.Spec.PathChain` layer.
-/

open Interaction CompPoly CPoly OracleComp OracleSpec

namespace Fri

namespace OracleLayer

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

private theorem initialRoundEq :
    0 + k = k := by
  omega

private theorem stateRound_lt {m round : ℕ}
    (h : round + (m + 1) = k) :
    round < k := by
  omega

private theorem nextStateEq {m round : ℕ}
    (h : round + (m + 1) = k) :
    round.succ + m = k := by
  omega

/-- Total challenge vector used internally while the fold phase is running.
Entries beyond the current round are irrelevant until they are filled in. -/
def initialFoldChallenges :
    FoldChallenges (F := F) (k := k) :=
  fun _ => 0

/-- Record the verifier challenge produced at a given non-final fold round. -/
def recordChallenge
    (round : Fin k)
    (challenges : FoldChallenges (F := F) (k := k))
    (α : F) :
    FoldChallenges (F := F) (k := k) :=
  Function.update challenges round α

/-- Terminal-indexed chain of the remaining non-final fold rounds.

The current round and terminal round `k` are both part of the chain type. That
extra endpoint is what lets final result code recover an `IndexedProverState k`
without a result-time cast. -/
def foldPhasePathChainFrom :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.PathChain Nat remaining round k
  | 0, _round, h =>
      match h with
      | rfl => .nil
  | remaining + 1, round, h =>
      let i : Fin k := ⟨round, stateRound_lt (k := k) h⟩
      .cons
        (foldRoundSpec (F := F) (n := n) D x s i)
        (foldRoundRoles (F := F) (n := n) D x s i)
        (foldRoundOD (F := F) (n := n) D x s i)
        (fun _ => round.succ)
        (fun _ =>
          foldPhasePathChainFrom remaining round.succ
            (nextStateEq (k := k) h))

/-- Terminal-indexed chain for all non-final fold rounds. -/
def foldPhasePathChain :
    Interaction.Oracle.Spec.PathChain Nat k 0 k :=
  foldPhasePathChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
    k 0 (initialRoundEq (k := k))

/-- Oracle context for the full terminal-indexed non-final fold phase. -/
abbrev foldPhasePathContext : Interaction.Oracle.Spec :=
  Interaction.Oracle.Spec.PathChain.toSpec k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))

/-- Role decoration for the full terminal-indexed non-final fold phase. -/
abbrev foldPhasePathRoles :
    Interaction.Oracle.Spec.RoleDeco
      (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.PathChain.toRoles k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))

/-- Oracle decoration for the full terminal-indexed non-final fold phase. -/
abbrev foldPhasePathOD :
    Interaction.Oracle.Spec.OracleDeco
      (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  Interaction.Oracle.Spec.PathChain.toOracleDeco k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))

/-- Codeword trace accumulated by the indexed fold-phase prover. -/
private structure IndexedCodewordTrace (round : Nat) where
  initial : Codeword (F := F) s n 0
  messages : MessageTrace (F := F) (n := n) s round 0 round

/-- Honest prover state indexed directly by the absolute fold round. -/
private structure IndexedProverState (round : Nat) where
  challenges : FoldChallenges (F := F) (k := k)
  codewords : IndexedCodewordTrace (F := F) (n := n) (s := s) round
  poly : HonestPoly (F := F) s d round

/-- Initial honest prover state for the indexed fold phase. -/
private def indexedProverInit
    {SharedIn : Type}
    (shared : SharedIn)
    (sWithOracles :
      StatementWithOracles (fun _ : SharedIn => PUnit)
        (fun _ => InputOracleFamily (F := F) (n := n) D x s) shared)
    (witness : HonestPoly (F := F) s d 0) :
    IndexedProverState (F := F) (n := n) (s := s) (d := d) 0 :=
  let initialCodeword :
      Codeword (F := F) s n 0 :=
    sWithOracles.oracleStmt ()
  { challenges := initialFoldChallenges (F := F) (k := k)
    codewords :=
      { initial := initialCodeword
        messages := .nil }
    poly := witness }

/-- Pure cast-free honest prover transition for a non-final fold round. -/
private def indexedProverNext
    (round : Nat) (hround : round < k)
    (state : IndexedProverState (F := F) (n := n) (s := s) (d := d) round)
    (α : F) :
    Codeword (F := F) s n round.succ ×
      IndexedProverState
        (F := F) (n := n) (s := s) (d := d) round.succ :=
  let i : Fin k := ⟨round, hround⟩
  let nextPoly : HonestPoly (F := F) s d round.succ :=
    honestFoldPoly (F := F) (s := s) (d := d) (i := i) state.poly α
  let nextCodeword : Codeword (F := F) s n round.succ :=
    honestCodeword (F := F) (D := D) (x := x) (s := s) (d := d)
      round.succ nextPoly
  let nextChallenges : FoldChallenges (F := F) (k := k) :=
    recordChallenge (F := F) i state.challenges α
  let nextCodewords : IndexedCodewordTrace (F := F) (n := n) (s := s) round.succ :=
    { initial := state.codewords.initial
      messages := MessageTrace.snoc (F := F) (n := n) s state.codewords.messages nextCodeword }
  let nextState :
      IndexedProverState
        (F := F) (n := n) (s := s) (d := d) round.succ :=
    { challenges := nextChallenges
      codewords := nextCodewords
      poly := nextPoly }
  ⟨nextCodeword, nextState⟩

/-- Verifier state indexed directly by the absolute fold round. -/
private structure IndexedVerifierState (round : Nat) where
  challenges : FoldChallenges (F := F) (k := k)

/-- Initial verifier state for the indexed fold phase. -/
private def indexedVerifierInit :
    IndexedVerifierState (F := F) (k := k) 0 :=
  { challenges := initialFoldChallenges (F := F) (k := k) }

/-- Pure cast-free verifier transition for a non-final fold round. -/
private def indexedVerifierNext
    (round : Nat) (hround : round < k)
    (state : IndexedVerifierState (F := F) (k := k) round)
    (α : F) :
    IndexedVerifierState (F := F) (k := k) round.succ :=
  let i : Fin k := ⟨round, hround⟩
  { challenges := recordChallenge (F := F) i state.challenges α }

/-- One indexed honest-prover fold-round handler. -/
private def indexedProverStepAux {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {remaining round : Nat}
    (hround : round + (remaining + 1) = k)
    (state : IndexedProverState (F := F) (n := n) (s := s) (d := d) round) :
    OracleComp oSpec
      (Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
        (foldRoundSpec (F := F) (n := n) D x s
          ⟨round, stateRound_lt (k := k) hround⟩).toInteractionSpec
        ((foldRoundSpec (F := F) (n := n) D x s
          ⟨round, stateRound_lt (k := k) hround⟩).toSpecRoles
            (foldRoundRoles (F := F) (n := n) D x s
              ⟨round, stateRound_lt (k := k) hround⟩))
        (fun _ => IndexedProverState
          (F := F) (n := n) (s := s) (d := d) round.succ)) := do
  let roundIdx : Fin k := ⟨round, stateRound_lt (k := k) hround⟩
  pure <| fun α => do
    let next := indexedProverNext
      (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
      round roundIdx.2 state α
    let roundOutput :
        (_cw : Codeword (F := F) s n round.succ) ×
          IndexedProverState
            (F := F) (n := n) (s := s) (d := d) round.succ :=
      ⟨next.1, next.2⟩
    pure <|
      (show OracleComp oSpec
          ((_cw : Codeword (F := F) s n round.succ) ×
            IndexedProverState
              (F := F) (n := n) (s := s) (d := d) round.succ) from
        pure roundOutput)

/-- One indexed verifier fold-round handler. -/
private def indexedVerifierStepAux {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F)
    {remaining round : Nat}
    (hround : round + (remaining + 1) = k)
    (state : IndexedVerifierState (F := F) (k := k) round) :
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      (foldRoundSpec (F := F) (n := n) D x s
        ⟨round, stateRound_lt (k := k) hround⟩).toInteractionSpec
      (RoleDecoration.withMonads
        ((foldRoundSpec (F := F) (n := n) D x s
          ⟨round, stateRound_lt (k := k) hround⟩).toSpecRoles
            (foldRoundRoles (F := F) (n := n) D x s
              ⟨round, stateRound_lt (k := k) hround⟩))
        ((foldRoundSpec (F := F) (n := n) D x s
          ⟨round, stateRound_lt (k := k) hround⟩).toMonadDecoration oSpec
            (InputOracleFamily (F := F) (n := n) D x s)
            (foldRoundRoles (F := F) (n := n) D x s
              ⟨round, stateRound_lt (k := k) hround⟩)
            (foldRoundOD (F := F) (n := n) D x s
              ⟨round, stateRound_lt (k := k) hround⟩)
            []ₒ))
      (fun _ => IndexedVerifierState (F := F) (k := k) round.succ) := do
  let roundIdx : Fin k := ⟨round, stateRound_lt (k := k) hround⟩
  let α ← sampleChallenge roundIdx
  pure ⟨α, fun _ =>
    indexedVerifierNext (F := F) (k := k)
      round (stateRound_lt (k := k) hround) state α⟩

/-- Terminal-indexed honest-prover handlers for all remaining fold rounds. -/
private def pathProverSteps {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.PathChain.Prover.RoundSteps
        (m := OracleComp oSpec)
        (IndexedProverState (F := F) (n := n) (s := s) (d := d))
        remaining
        (foldPhasePathChainFrom
          (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round h)
  | 0, _, h => by
      cases h
      exact ⟨⟩
  | remaining + 1, round, h =>
      ⟨indexedProverStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
          (k := k) (oSpec := oSpec) h,
        fun _ =>
          pathProverSteps (oSpec := oSpec)
            remaining round.succ (nextStateEq (k := k) h)⟩

/-- Terminal-indexed verifier handlers for all remaining fold rounds. -/
private def pathVerifierSteps {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F) :
    (remaining round : Nat) → (h : round + remaining = k) →
      Interaction.Oracle.Spec.PathChain.Verifier.RoundSteps
        (oSpec := oSpec)
        (OStmtIn := InputOracleFamily (F := F) (n := n) D x s)
        (IndexedVerifierState (F := F) (k := k))
        remaining
        (foldPhasePathChainFrom
          (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round h)
  | 0, _, h => by
      cases h
      exact ⟨⟩
  | remaining + 1, round, h =>
      ⟨indexedVerifierStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
          (oSpec := oSpec) sampleChallenge h,
        fun _ =>
          pathVerifierSteps (oSpec := oSpec) sampleChallenge
            remaining round.succ (nextStateEq (k := k) h)⟩

/-- Terminal prover state selected by a full terminal-indexed fold transcript. -/
private def pathTerminalProverState
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (F := F) (n := n) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    IndexedProverState (F := F) (n := n) (s := s) (d := d) k :=
  Interaction.Oracle.Spec.PathChain.terminalOutput
    (IndexedProverState (F := F) (n := n) (s := s) (d := d))
    k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
    pt state

/-- Terminal verifier state selected by a full terminal-indexed fold transcript. -/
private def pathTerminalVerifierState
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedVerifierState (F := F) (k := k))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    IndexedVerifierState (F := F) (k := k) k :=
  Interaction.Oracle.Spec.PathChain.terminalOutput
    (IndexedVerifierState (F := F) (k := k))
    k
    (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
    pt state

/-- Plain output statement extracted from the terminal prover state. -/
private def pathProverStatementResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (F := F) (n := n) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    FoldChallenges (F := F) (k := k) :=
  (pathTerminalProverState
    (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
    pt state).challenges

/-- Plain output statement extracted from the terminal verifier state. -/
private def pathVerifierStatementResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedVerifierState (F := F) (k := k))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    FoldChallenges (F := F) (k := k) :=
  (pathTerminalVerifierState
    (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
    pt state).challenges

/-- Output oracle statements extracted from the terminal prover state. -/
private def pathOracleStatementResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (F := F) (n := n) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    OracleStatement (FoldCodewordTraceOracleFamily (F := F) (n := n) D x s) :=
  fun _ =>
    { initial :=
        (pathTerminalProverState
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
          pt state).codewords.initial
      messages :=
        (pathTerminalProverState
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
          pt state).codewords.messages }

/-- Honest witness extracted from the terminal prover state. -/
private def pathWitnessResult
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (state :
      Interaction.Oracle.Spec.PathChain.outputFamily
        (IndexedProverState (F := F) (n := n) (s := s) (d := d))
        k
        (foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
        pt) :
    HonestPoly (F := F) s d k :=
  (pathTerminalProverState
    (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
    pt state).poly

/-- Route a query to a carried trace message into the corresponding
oracle message of the terminal-indexed fold path. -/
@[reducible] private def pathMessageTraceQueryHandleFrom :
    (remaining round : Nat) → (h : round + remaining = k) →
      (pt :
        Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.PathChain.toSpec remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round h))) →
      MessageTrace.Query (n := n) s remaining round k →
      Interaction.Oracle.Spec.QueryHandle
        (Interaction.Oracle.Spec.PathChain.toSpec remaining
          (foldPhasePathChainFrom
            (D := D) (n := n) (x := x) (s := s) (k := k)
            remaining round h))
        (Interaction.Oracle.Spec.PathChain.toOracleDeco remaining
          (foldPhasePathChainFrom
            (D := D) (n := n) (x := x) (s := s) (k := k)
            remaining round h))
        pt
  | 0, _, _, _, query => nomatch query
  | remaining + 1, round, h, pt, .here idx =>
      let i : Fin k := ⟨round, stateRound_lt (k := k) h⟩
      let spec := foldRoundSpec (F := F) (n := n) D x s i
      let rest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toSpec remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      let odRest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toOracleDeco remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      Interaction.Oracle.Spec.QueryHandle.routeLeft
        spec rest
        (foldRoundOD (F := F) (n := n) D x s i)
        odRest pt (.inl idx)
  | remaining + 1, round, h, pt, .later query =>
      let i : Fin k := ⟨round, stateRound_lt (k := k) h⟩
      let spec := foldRoundSpec (F := F) (n := n) D x s i
      let rest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toSpec remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      let odRest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toOracleDeco remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      let split := Interaction.Oracle.Spec.PublicTranscript.split spec rest pt
      Interaction.Oracle.Spec.QueryHandle.routeRight
        spec rest
        (foldRoundOD (F := F) (n := n) D x s i)
        odRest pt
        (pathMessageTraceQueryHandleFrom
          remaining round.succ (nextStateEq (k := k) h) split.2 query)

/-- Route a trace-message query directly through a query implementation for the
current path segment. This is the simulator-facing version of
`pathMessageTraceQueryHandleFrom`: the recursion restricts the implementation to
the current round or the remaining suffix, so the result type is `F` at the
branch where the codeword is queried. -/
private def pathMessageTraceQueryImplFrom {ιTarget : Type}
    (targetSpec : OracleSpec.{0, 0} ιTarget) :
    (remaining round : Nat) → (h : round + remaining = k) →
      (pt :
        Interaction.Oracle.Spec.PublicTranscript
          (Interaction.Oracle.Spec.PathChain.toSpec remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round h))) →
      QueryImpl
        (Interaction.Oracle.Spec.toOracleSpec
          (Interaction.Oracle.Spec.PathChain.toSpec remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round h))
          (Interaction.Oracle.Spec.PathChain.toOracleDeco remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round h))
          pt)
        (OracleComp targetSpec) →
      MessageTrace.Query (n := n) s remaining round k →
      OracleComp targetSpec F
  | 0, _, _, _, _, query => nomatch query
  | remaining + 1, round, h, pt, embed, .here idx =>
      let i : Fin k := ⟨round, stateRound_lt (k := k) h⟩
      let spec := foldRoundSpec (F := F) (n := n) D x s i
      let rest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toSpec remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      let odRest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toOracleDeco remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      let currentImpl :=
        Interaction.Oracle.Spec.restrictLeft spec rest
          (foldRoundOD (F := F) (n := n) D x s i)
          odRest pt embed
      currentImpl (.inl idx)
  | remaining + 1, round, h, pt, embed, .later query =>
      let i : Fin k := ⟨round, stateRound_lt (k := k) h⟩
      let spec := foldRoundSpec (F := F) (n := n) D x s i
      let rest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toSpec remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      let odRest :=
        fun _ =>
          Interaction.Oracle.Spec.PathChain.toOracleDeco remaining
            (foldPhasePathChainFrom
              (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) h))
      let split := Interaction.Oracle.Spec.PublicTranscript.split spec rest pt
      let restImpl :=
        Interaction.Oracle.Spec.restrictRight spec rest
          (foldRoundOD (F := F) (n := n) D x s i)
          odRest pt embed
      pathMessageTraceQueryImplFrom targetSpec
        remaining round.succ (nextStateEq (k := k) h) split.2 restImpl query

/-- Simulate fold-codeword trace oracle queries from the initial codeword oracle
and the queryable oracle messages accumulated along the fold path. -/
private def pathSimulateCodewordQuery
    (pt :
      Interaction.Oracle.Spec.PublicTranscript
        (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k))) :
    QueryImpl [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ
      (OracleComp
        ([InputOracleFamily (F := F) (n := n) D x s]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k))
            (foldPhasePathOD (D := D) (n := n) (x := x) (s := s) (k := k))
            pt))
  | ⟨(), .inl idx⟩ =>
      liftM <| ([InputOracleFamily (F := F) (n := n) D x s]ₒ).query ⟨(), idx⟩
  | ⟨(), .inr query⟩ =>
      let pathSpec :=
        Interaction.Oracle.Spec.toOracleSpec
          (foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k))
          (foldPhasePathOD (D := D) (n := n) (x := x) (s := s) (k := k))
          pt
      let fullSpec :=
        ([InputOracleFamily (F := F) (n := n) D x s]ₒ +
          pathSpec)
      let embedPath : QueryImpl pathSpec (OracleComp fullSpec) :=
        fun q => liftM <| fullSpec.query (.inr q)
      pathMessageTraceQueryImplFrom
        (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
        fullSpec k 0 (initialRoundEq (k := k)) pt embedPath query

/-- Continuation for all non-final FRI fold rounds, composed through the
terminal-indexed path-chain layer. -/
def foldPhaseContinuation {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F) :
    Interaction.Oracle.Reduction (ι := ι) oSpec PUnit
      (fun _ => foldPhasePathContext (D := D) (n := n) (x := x) (s := s) (k := k))
      (fun _ => foldPhasePathRoles (D := D) (n := n) (x := x) (s := s) (k := k))
      (fun _ => foldPhasePathOD (D := D) (n := n) (x := x) (s := s) (k := k))
      (fun _ => PUnit)
      (ιₛᵢ := fun _ => Unit)
      (fun _ => InputOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) s d 0)
      (fun _ _ => FoldChallenges (F := F) (k := k))
      (ιₛₒ := fun _ _ => Unit)
      (fun _ _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
      (fun _ _ => HonestPoly (F := F) s d k) :=
  Interaction.Oracle.Reduction.ofPathChain
    (Idx := Nat)
    (ι := ι) (oSpec := oSpec)
    (SharedIn := PUnit)
    (StatementIn := fun _ => PUnit)
    (WitnessIn := fun _ => HonestPoly (F := F) s d 0)
    (ιₛᵢ := fun _ => Unit)
    (OStatementIn := fun _ => InputOracleFamily (F := F) (n := n) D x s)
    (n := k)
    (idx := fun _ => 0)
    (finish := fun _ => k)
    (c := fun _ => foldPhasePathChain (D := D) (n := n) (x := x) (s := s))
    (StatementOut := fun _ _ => FoldChallenges (F := F) (k := k))
    (ιₛₒ := fun _ _ => Unit)
    (OStatementOut := fun _ _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
    (WitnessOut := fun _ _ => HonestPoly (F := F) s d k)
    (ProverState := fun _ round =>
      IndexedProverState (F := F) (n := n) (s := s) (d := d) round)
    (VerifierState := fun _ round =>
      IndexedVerifierState (F := F) (k := k) round)
    (proverInit := fun shared sWithOracles witness =>
      indexedProverInit
        (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
        shared sWithOracles witness)
    (verifierInit := fun _ _ =>
      indexedVerifierInit (F := F) (k := k))
    (proverSteps := fun _ =>
      pathProverSteps
        (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
        (oSpec := oSpec) k 0 (initialRoundEq (k := k)))
    (verifierSteps := fun _ =>
      pathVerifierSteps
        (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
        (oSpec := oSpec) sampleChallenge k 0 (initialRoundEq (k := k)))
    (proverStmtResult := fun _ pt state =>
      pathProverStatementResult
        (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
        pt state)
    (verifierStmtResult := fun _ pt state =>
      pathVerifierStatementResult
        (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
        pt state)
    (oStmtResult := fun _ pt state =>
      pathOracleStatementResult
        (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
        pt state)
    (witResult := fun _ pt state =>
      pathWitnessResult
        (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
        pt state)
    (simulate := fun _ pt =>
      pathSimulateCodewordQuery
        (F := F) (D := D) (n := n) (x := x) (s := s) (k := k) pt)

end

end OracleLayer

end Fri


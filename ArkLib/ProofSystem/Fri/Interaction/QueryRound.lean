/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Fin.Basic
import ArkLib.ProofSystem.Fri.Interaction.FinalFold
import ArkLib.ProofSystem.Fri.RoundConsistency

/-!
# FRI Interaction: Query Round

This module formalizes the executable FRI query checks on the
`Interaction.Oracle.Spec` layer.
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
variable (l : ℕ)

/-- The sampled base-domain query indices used by the public-coin FRI query
round. -/
abbrev QueryBatch : Type :=
  Fin l → EvalIdx (n := n) s 0

/-- The query phase returns an explicit acceptance bit. -/
abbrev QueryResult : Type :=
  Bool

/-- Public-coin query shell: the verifier samples the full batch of base-domain
query indices in one shot. -/
def queryRoundSpec : Interaction.Oracle.Spec :=
  .public (QueryBatch (n := n) s l) fun _ => .done

/-- Role decoration for the query shell. -/
def queryRoundRoles :
    Interaction.Oracle.Spec.RoleDeco (queryRoundSpec (n := n) (s := s) (l := l)) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- No prover message is sent in the query shell, so there is no new oracle
decoration. -/
def queryRoundOD :
    Interaction.Oracle.Spec.OracleDeco (queryRoundSpec (n := n) (s := s) (l := l)) :=
  fun _ => ⟨⟩

/-- The challenge used in the `i`-th FRI round, including the terminal final
fold challenge at index `k`. -/
private def roundChallengeAt
    (stmt : FinalStatement (F := F) (k := k) (d := d)) :
    Fin (k + 1) → F
  | ⟨i, _⟩ =>
      if h : i < k then
        stmt.1 ⟨i, h⟩
      else
        stmt.2.1

/-- The final polynomial sent in the terminal fold round. -/
private abbrev finalPolynomial
    (stmt : FinalStatement (F := F) (k := k) (d := d)) :
    CDegreeLE F d :=
  stmt.2.2

/-- The sampled next-round index induced by a base-domain query at round `i`. -/
private def nextRoundSampleIdx
    (baseIdx : EvalIdx (n := n) s 0) (i : Fin (k + 1)) :
    EvalIdx (n := n) s i.1.succ :=
  nextRoundIdx (n := n) (s := s) i (roundAnchorIdx (n := n) (s := s) baseIdx i)

/-- Direct access to a carried trace codeword query. -/
private def evalTraceCodeword
    (codewords : OracleStatement (FoldCodewordTraceOracleFamily (F := F) (n := n) D x s))
    (query : FoldCodewordTrace.Query (n := n) s) : F :=
  FoldCodewordTrace.answer (n := n) s (codewords ()) query

/-- Oracle-query access to a carried trace codeword query. -/
private def evalTraceCodewordQ
    (query : FoldCodewordTrace.Query (n := n) s) :
    OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ F :=
  ([FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ).query ⟨(), query⟩

/-- The evaluation pairs used in one FRI round consistency check, with the
current-round codeword supplied by the caller. -/
private def roundEvaluationPairsWith
    (h_domain : totalShift s ≤ n)
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0)
    (currentValue : EvalIdx (n := n) s i.1 → F) :
    Fin (roundArity s i) → F × F :=
  let nextIdx := nextRoundSampleIdx (n := n) (s := s) baseIdx i
  fun u =>
    let idx := roundFiberIdx (n := n) (s := s) h_domain i nextIdx u
    (evalPointVal (D := D) (x := x) (s := s) i.1 idx,
      currentValue idx)

/-- The evaluation pairs used in one FRI round consistency check, obtained via
oracle queries against the supplied current-round accessor. -/
private def roundEvaluationPairsWithQ
    (h_domain : totalShift s ≤ n)
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0)
    (currentQuery :
      EvalIdx (n := n) s i.1 →
        OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ F) :
    OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ
      (Fin (roundArity s i) → F × F) := do
  let nextIdx := nextRoundSampleIdx (n := n) (s := s) baseIdx i
  Fin.traverseM fun u => do
    let idx := roundFiberIdx (n := n) (s := s) h_domain i nextIdx u
    let value ← currentQuery idx
    pure (evalPointVal (D := D) (x := x) (s := s) i.1 idx, value)

/-- The `i`-th FRI round consistency check at one sampled base-domain index,
with current- and next-round values supplied by the caller. -/
private noncomputable def roundConsistentAtWith
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0)
    (currentValue : EvalIdx (n := n) s i.1 → F)
    (nextValue : EvalIdx (n := n) s i.1.succ → F) : Bool :=
  let nextIdx := nextRoundSampleIdx (n := n) (s := s) baseIdx i
  RoundConsistency.roundConsistencyCheck
    (roundChallengeAt (F := F) (k := k) (d := d) stmt i)
    (roundEvaluationPairsWith (D := D) (n := n) (x := x) (s := s)
      h_domain i baseIdx currentValue)
    (nextValue nextIdx)

/-- The `i`-th FRI round consistency check at one sampled base-domain index,
performed through oracle queries against supplied current- and next-round
accessors. -/
private noncomputable def roundConsistentAtWithQ
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0)
    (currentQuery :
      EvalIdx (n := n) s i.1 →
        OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ F)
    (nextQuery :
      EvalIdx (n := n) s i.1.succ →
        OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ F) :
    OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ Bool := do
  let pts ← roundEvaluationPairsWithQ (F := F) (D := D) (n := n) (x := x) (s := s)
    h_domain i baseIdx currentQuery
  let β ← nextQuery (nextRoundSampleIdx (n := n) (s := s) baseIdx i)
  pure <|
    RoundConsistency.roundConsistencyCheck
      (roundChallengeAt (F := F) (k := k) (d := d) stmt i)
      pts β

/-- Check all remaining FRI rounds against one sampled base-domain index,
threading structural trace-query routing as the fold trace is traversed. -/
private noncomputable def pointConsistentFrom
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (codewords : OracleStatement (FoldCodewordTraceOracleFamily (F := F) (n := n) D x s))
    (baseIdx : EvalIdx (n := n) s 0) :
    (remaining round : Nat) → (h : round + remaining = k) →
      (EvalIdx (n := n) s round → F) →
      (MessageTrace.Query (n := n) s remaining round k →
        FoldCodewordTrace.Query (n := n) s) →
        Bool
  | 0, round, h, currentValue, _ =>
      let i : Fin (k + 1) := ⟨round, by omega⟩
      let nextValue : EvalIdx (n := n) s i.1.succ → F :=
        fun idx =>
          evalAtIdx (D := D) (x := x) (s := s)
            (finalPolynomial (F := F) (k := k) (d := d) stmt).1 idx
      roundConsistentAtWith (F := F) (D := D) (n := n) (x := x) (s := s)
        (d := d) h_domain stmt i baseIdx currentValue nextValue
  | remaining + 1, round, h, currentValue, liftMessageQuery =>
      let i : Fin (k + 1) := ⟨round, by omega⟩
      let nextValue : EvalIdx (n := n) s i.1.succ → F :=
        fun idx =>
          evalTraceCodeword (F := F) (D := D) (n := n) (x := x) (s := s)
            codewords (liftMessageQuery (.here idx))
      roundConsistentAtWith (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt i baseIdx currentValue nextValue &&
        pointConsistentFrom h_domain stmt codewords baseIdx
          remaining round.succ (by omega) nextValue
          (fun query => liftMessageQuery (.later query))

/-- Check all FRI rounds against one sampled base-domain index through oracle
queries. -/
private noncomputable def pointConsistentFromQ
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (baseIdx : EvalIdx (n := n) s 0) :
    (remaining round : Nat) → (h : round + remaining = k) →
      (EvalIdx (n := n) s round →
        OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ F) →
      (MessageTrace.Query (n := n) s remaining round k →
        FoldCodewordTrace.Query (n := n) s) →
        OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ Bool
  | 0, round, h, currentQuery, _ =>
      let i : Fin (k + 1) := ⟨round, by omega⟩
      let nextQuery :
          EvalIdx (n := n) s i.1.succ →
            OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ F :=
        fun idx =>
          pure <|
            evalAtIdx (D := D) (x := x) (s := s)
              (finalPolynomial (F := F) (k := k) (d := d) stmt).1 idx
      roundConsistentAtWithQ (F := F) (D := D) (n := n) (x := x) (s := s)
        (d := d) h_domain stmt i baseIdx currentQuery nextQuery
  | remaining + 1, round, h, currentQuery, liftMessageQuery => do
      let i : Fin (k + 1) := ⟨round, by omega⟩
      let nextQuery :
          EvalIdx (n := n) s i.1.succ →
            OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ F :=
        fun idx =>
          evalTraceCodewordQ (F := F) (D := D) (n := n) (x := x) (s := s)
            (liftMessageQuery (.here idx))
      let ok ←
        roundConsistentAtWithQ (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt i baseIdx currentQuery nextQuery
      if ok then
        pointConsistentFromQ h_domain stmt baseIdx
          remaining round.succ (by omega) nextQuery
          (fun query => liftMessageQuery (.later query))
      else
        pure false

/-- Run the full FRI query-phase consistency checks on a sampled query batch,
computed directly from the carried codeword trace. -/
noncomputable def queryBatchConsistent
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (codewords : OracleStatement (FoldCodewordTraceOracleFamily (F := F) (n := n) D x s))
    (pts : QueryBatch (n := n) s l) : Bool :=
  ((List.finRange l) : List (Fin l)).foldl
    (fun ok m =>
      ok &&
        pointConsistentFrom (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt codewords (pts m)
          k 0 (by omega)
          (fun idx =>
            evalTraceCodeword (F := F) (D := D) (n := n) (x := x) (s := s)
              codewords (.inl idx))
          (fun query => .inr query))
    true

/-- Run the full FRI query-phase consistency checks on a sampled query batch
through oracle queries. -/
noncomputable def queryBatchConsistentQ
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (pts : QueryBatch (n := n) s l) :
    OracleComp [FoldCodewordTraceOracleFamily (F := F) (n := n) D x s]ₒ Bool :=
  ((List.finRange l) : List (Fin l)).foldlM
    (fun ok m => do
      if ok then
        pointConsistentFromQ (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt (pts m)
          k 0 (by omega)
          (fun idx =>
            evalTraceCodewordQ (F := F) (D := D) (n := n) (x := x) (s := s)
              (.inl idx))
          (fun query => .inr query)
      else
        pure false)
    true

/-- Reduction for the FRI query phase. It samples a batch of base-domain
query indices and returns the Boolean result of all round-consistency checks. -/
noncomputable def queryRoundReduction
    {SharedIn : Type} {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {StatementIn : SharedIn → Type}
    (h_domain : totalShift s ≤ n)
    (toFinalStatement :
      (shared : SharedIn) → StatementIn shared → FinalStatement (F := F) (k := k) (d := d))
    (sampleQueries : SharedIn → OracleComp oSpec (QueryBatch (n := n) s l)) :
    Interaction.Oracle.Reduction (ι := ι) oSpec SharedIn
      (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
      (fun _ => queryRoundRoles (n := n) (s := s) (l := l))
      (fun _ => queryRoundOD (n := n) (s := s) (l := l))
      StatementIn
      (fun _ => FoldCodewordTraceOracleFamily (F := F) (n := n) D x s)
      (fun _ => PUnit)
      (fun _ _ => QueryResult)
      (fun _ _ => EmptyOracleFamily)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    pure <| fun pts => do
      let accepted :=
        queryBatchConsistent (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) (l := l) h_domain
          (toFinalStatement _ sWithOracles.stmt) sWithOracles.oracleStmt pts
      pure ⟨⟨accepted, fun i => nomatch i⟩, PUnit.unit⟩
  verifier := {
    toFun := fun shared stmt => do
      let pts ← sampleQueries shared
      let accepted ←
        liftM <|
          queryBatchConsistentQ (F := F) (D := D) (n := n) (x := x) (s := s)
            (d := d) (l := l) h_domain (toFinalStatement shared stmt) pts
      pure ⟨pts, accepted⟩
    simulate := fun _ _ i => nomatch i
  }

end

end OracleLayer

end Fri

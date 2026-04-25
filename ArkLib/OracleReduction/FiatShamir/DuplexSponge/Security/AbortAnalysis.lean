/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Definition and analysis of aborts

This file contains the definition and analysis of aborts for the analysis of duplex sponge
Fiat-Shamir, following Section 5.7 in the paper.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [HasChallengeSize pSpec]

/-- Forward-permutation projection `tr.p` of a DS trace. -/
def forwardPermTraceOfDS
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (forwardPermutationOracle (CanonicalSpongeState U)) :=
  trace.filterMap fun entry =>
    match entry with
    | ⟨.inr (.inl stateIn), stateOut⟩ => some ⟨stateIn, stateOut⟩
    | _ => none

/-- Paper-facing predicate: `StdTrace` on `trace` does not abort. -/
def StdTraceNoAbort [DecidableEq StmtIn] [DecidableEq U]
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  stdTraceSingle
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap trace ≠
    (failure : OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))

/-- Paper-facing predicate: `StdTrace` on `trace` aborts. -/
def StdTraceAbort [DecidableEq StmtIn] [DecidableEq U]
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ¬ StdTraceNoAbort
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap trace

/-- Paper-facing predicate: `BackTrack` does not hit the `err` branch on `(trace, state)`.

`tr_∇` (the sorted query-answer index of Definition 5.2) is bulk-initialized from `trace`
internally so the predicate keeps a `(trace, state)`-only API. -/
def BackTrackNoAbort [DecidableEq StmtIn] [DecidableEq U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  let trΔ : Section52.DefaultTraceDelta StmtIn U :=
    Section52.DefaultTraceDelta.ofQueryLog trace
  (backTrack (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    trΔ (trace.length + 1) state).run ≠ none

/-- Paper-facing predicate: `LookAhead` does not hit the `err` branch on `(trace, state, i)`.

The paper's `LookAhead(tr_∇.p, s, i)` takes only the permutation sub-table; we pass the
empty `ListTraceTable` here since the predicate is signature-level (not computation-level)
and `lookAhead` does not yet read from the table. -/
def LookAheadNoAbort [DecidableEq U]
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) : Prop :=
  let trΔp : Section52.ListBacked.ListTraceTable
      (CanonicalSpongeState U) (CanonicalSpongeState U) :=
    Section52.TraceTableOps.empty
  let _ := trace
  lookAhead (pSpec := pSpec) (U := U) trΔp state i ≠
    (failure : OptionT (OracleComp (Unit →ₒ U)) (Option (Vector U (challengeSize i))))

section D2SQueryNoAbort

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type}
  {T_P : Type}
  [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]

/-- Paper-facing predicate: `D2SQuery` does not hit the `err` branch when started from `trace`. -/
def D2SQueryNoAbortOnTrace
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ q : (duplexSpongeChallengeOracle StmtIn U).Domain,
    (d2sQueryStep
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params q).run
        ({ trace := trace, cacheP := [] } :
          D2SQueryState (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) ≠
      (failure : OptionT (OracleComp (Unit →ₒ U))
        ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)))

end D2SQueryNoAbort

/-- Paper-facing predicate: `D2SQuery` aborts when started from `trace`. -/
def D2SQueryAbortOnTrace
    [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ¬ D2SQueryNoAbortOnTrace
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params trace

/-- Lemma 5.17: if `E(tr) = 0`, then `StdTrace(tr)` does not abort. -/
theorem lemma_5_17_stdTrace_noAbort [DecidableEq StmtIn] [DecidableEq U]
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hE : ¬ OracleSpec.QueryLog.BadEventDS.E trace) :
    StdTraceNoAbort (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap trace := by
  sorry

/--
Lemma 5.18: if `E(tr_𝒜) = 0`, then `𝒜 ^ D2SQuery` does not abort.

`traceA` is the paper-facing `tr_𝒜` trace.
-/
theorem lemma_5_18_d2sQuery_noAbort
    [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (traceA : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hE : ¬ OracleSpec.QueryLog.BadEventDS.E traceA) :
    D2SQueryNoAbortOnTrace
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params traceA := by
  sorry

/--
Theorem 5.19 (paper direction): if `𝒜 ^ D2SQuery` aborts, then `E(tr_𝒜)` holds.

This is the non-contrapositive statement used in Section 5.7.
-/
theorem theorem_5_19_d2sQuery_abort_implies_badEvent
    [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [Section52.LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (traceA : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAbort : D2SQueryAbortOnTrace
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params traceA) :
    OracleSpec.QueryLog.BadEventDS.E traceA := by
  classical
  by_contra hE
  exact hAbort
    (lemma_5_18_d2sQuery_noAbort
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      params traceA hE)

/--
Theorem 5.20 (paper direction): if `StdTrace(tr)` aborts, then `E(tr)` holds.

This is the non-contrapositive statement used in Section 5.7.
-/
theorem theorem_5_20_stdTrace_abort_implies_badEvent [DecidableEq StmtIn] [DecidableEq U]
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAbort :
      StdTraceAbort (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        remap trace) :
    OracleSpec.QueryLog.BadEventDS.E trace := by
  classical
  by_contra hE
  exact hAbort
    (lemma_5_17_stdTrace_noAbort
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap trace hE)

/--
Claim 5.19: if `E_inv(tr, s) = E_prp(tr) = E_fork(tr, s) = 0`,
then `backTrack(tr, s) ≠ err`.
-/
theorem claim_5_19_backTrack_noAbort [DecidableEq StmtIn] [DecidableEq U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U)
    (hInv : ¬ OracleSpec.QueryLog.BadEventDS.E_inv_paper trace state)
    (hPrp : ¬ OracleSpec.QueryLog.BadEventDS.E_prp trace)
    (hFork : ¬ OracleSpec.QueryLog.BadEventDS.E_fork_paper trace state) :
    BackTrackNoAbort (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) trace state := by
  sorry

/--
Claim 5.20: if `E_prp(tr) = 0`, then `lookAhead(tr.p, s, i) ≠ err` for all `(s, i)`.

Here `tr.p` is `forwardPermTraceOfDS tr`.
-/
theorem claim_5_20_lookAhead_noAbort [DecidableEq U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U)
    (i : pSpec.ChallengeIdx)
    (hPrp : ¬ OracleSpec.QueryLog.BadEventDS.E_prp trace) :
    LookAheadNoAbort (pSpec := pSpec) (U := U)
      (forwardPermTraceOfDS (StmtIn := StmtIn) (U := U) trace) state i := by
  sorry

end DuplexSpongeFS

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
def StdTraceNoAbort
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  stdTraceSingle
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap trace ≠
    (failure : OptionT (OracleComp (Unit →ₒ U))
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))

/-- Paper-facing predicate: `StdTrace` on `trace` aborts. -/
def StdTraceAbort
    (remap : StdTraceToFSRemap (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ¬ StdTraceNoAbort
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      remap trace

/-- Paper-facing predicate: `BackTrack` does not hit the `err` branch on `(trace, state)`. -/
def BackTrackNoAbort
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  (backTrack (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) trace state).run ≠ none

/-- Paper-facing predicate: `LookAhead` does not hit the `err` branch on `(trace, state, i)`. -/
def LookAheadNoAbort
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) : Prop :=
  lookAhead (pSpec := pSpec) (U := U) trace state i ≠
    (failure : OptionT (OracleComp (Unit →ₒ U)) (Option (Vector U (challengeSize i))))

section D2SQueryNoAbort

variable [DecidableEq StmtIn] [DecidableEq U]

/-- Paper-facing predicate: `D2SQuery` does not hit the `err` branch when started from `trace`. -/
def D2SQueryNoAbortOnTrace
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ q : (duplexSpongeChallengeOracle StmtIn U).Domain,
    (d2sQueryStep (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params q).run
        { trace := trace, cacheP := [] } ≠
      (failure : OptionT (OracleComp (Unit →ₒ U))
        ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState (StmtIn := StmtIn) (U := U)))

end D2SQueryNoAbort

/-- Paper-facing predicate: `D2SQuery` aborts when started from `trace`. -/
def D2SQueryAbortOnTrace
    [DecidableEq StmtIn] [DecidableEq U]
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ¬ D2SQueryNoAbortOnTrace
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params trace

/-- Lemma 5.17: if `E(tr) = 0`, then `StdTrace(tr)` does not abort. -/
theorem lemma_5_17_stdTrace_noAbort
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
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (traceA : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hE : ¬ OracleSpec.QueryLog.BadEventDS.E traceA) :
    D2SQueryNoAbortOnTrace
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params traceA := by
  sorry

/--
Theorem 5.19 (paper direction): if `𝒜 ^ D2SQuery` aborts, then `E(tr_𝒜)` holds.

This is the non-contrapositive statement used in Section 5.7.
-/
theorem theorem_5_19_d2sQuery_abort_implies_badEvent
    [DecidableEq StmtIn] [DecidableEq U]
    (params : D2SQueryParams (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (traceA : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAbort : D2SQueryAbortOnTrace
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) params traceA) :
    OracleSpec.QueryLog.BadEventDS.E traceA := by
  classical
  by_contra hE
  exact hAbort
    (lemma_5_18_d2sQuery_noAbort
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      params traceA hE)

/--
Theorem 5.20 (paper direction): if `StdTrace(tr)` aborts, then `E(tr)` holds.

This is the non-contrapositive statement used in Section 5.7.
-/
theorem theorem_5_20_stdTrace_abort_implies_badEvent
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
theorem claim_5_19_backTrack_noAbort
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
theorem claim_5_20_lookAhead_noAbort
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U)
    (i : pSpec.ChallengeIdx)
    (hPrp : ¬ OracleSpec.QueryLog.BadEventDS.E_prp trace) :
    LookAheadNoAbort (pSpec := pSpec) (U := U)
      (forwardPermTraceOfDS (StmtIn := StmtIn) (U := U) trace) state i := by
  sorry

end DuplexSpongeFS

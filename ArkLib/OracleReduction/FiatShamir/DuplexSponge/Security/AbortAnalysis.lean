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

## Declaration order (bottom-up by dependency)

1. **Claim 5.19** (`claim_5_19_backTrack_noAbort`) — `BackTrack(tr, s) ≠ err` under
   `isConsistentTrace(tr) ∧ ¬ E(tr)`.  Used by Lemmas 5.17 and 5.18.
2. **Claim 5.20** (`claim_5_20_lookAhead_noAbort`) — `LookAhead(tr.p, s, i) ≠ err` under
   `¬ E(tr)`.  Used by Lemma 5.17.
3. **Lemma 5.17** (`lemma_5_17_d2sTrace_noAbort`) — `D2STrace(tr)` does not abort under
   `isConsistentTrace(tr) ∧ ¬ E(tr)`.  Used to derive Theorem 5.20.
4. **Lemma 5.18** (`lemma_5_18_d2sQuery_noAbort`) — `A^D2SQuery` does not abort under
   `isConsistentTrace(tr_A) ∧ ¬ E(tr_A)`.  Used to derive Theorem 5.19.
5. **Theorem 5.19** (`theorem_5_19_d2sQuery_abort_implies_badEvent`) — contrapositive of
   Lemma 5.18: if `A^D2SQuery` aborts then `E(tr_A)` holds.  Used in Section 5.8.
6. **Theorem 5.20** (`theorem_5_20_d2sTrace_abort_implies_badEvent`) — contrapositive of
   Lemma 5.17: if `StdTrace(tr)` aborts then `E(tr)` holds.  Used in Section 5.8.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.AbortAnalysis

open ProverTransform Backtrack Lookahead TraceTransform DSTraceStorage

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]
  {δ : ℕ}

/-- Predicate: `D2STrace` on `trace` does not abort.

Blackbox over `T_H T_P` via `[LawfulTraceNablaImpl …]` (matches `d2sTrace`). -/
def D2STraceNoAbort [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  d2sTrace (T_H := T_H) (T_P := T_P) (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      trace ≠
    (failure : UnitSampleM U
      (QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)))

/-- Predicate: `D2STrace` on `trace` aborts. -/
def D2STraceAbort [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ¬ D2STraceNoAbort (T_H := T_H) (T_P := T_P) (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      trace

/-- Predicate: `BackTrack` does not hit the `err` branch on `(trace, state)`.

The caller supplies the generic `tr_∇` alongside its provenance `h_trΔ : trΔ = ofQueryLog trace`;
`backTrack` consumes both. -/
def BackTrackNoAbort [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (depthBound : ℕ)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ = TraceNabla.ofQueryLog trace)
    (state : CanonicalSpongeState U) : Prop :=
  backTrack (δ := δ) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    trace trΔ h_trΔ state depthBound ≠
    (ExperimentOutput.err :
      ExperimentOutput (BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))

/-- Predicate: `LookAhead(tr_∇.p, state, i)` does not hit the `err` branch. -/
def LookAheadNoAbort [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) : Prop :=
  lookAhead (pSpec := pSpec) (U := U) (trΔp := trΔ.p) state i ≠
    (pure ExperimentOutput.err :
      OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (challengeSize i))))

section D2SQueryNoAbort

variable [DecidableEq StmtIn] [DecidableEq U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Predicate: `D2SQuery` does not hit the `err` branch when started from `trace`.

Stepped through `d2sQueryStep` (encoded `gSpec` target). The codec composition
`ψ⁻¹∘f∘φ⁻¹` lives in `d2sCodecBridgeImpl` as a `QueryImpl`, applied post-hoc by `d2sAlgo`. -/
def D2SQueryNoAbortOnTrace
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  -- TODO: fix this to generalize arbitrary D2SQuery procedure.
    -- an `trace`, `cacheP`, and `trΔ` come with some relations between them
  ∀ (cacheP : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain),
    (d2sQueryStep (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run
        ({ trace := trace, cacheP := cacheP, trΔ := TraceNabla.ofQueryLog trace } :
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) ≠
      (failure : AbortComp
        (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
        ((duplexSpongeChallengeOracle StmtIn U).Range q ×
          D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)))

end D2SQueryNoAbort

/-- Predicate: `D2SQuery` aborts when started from `trace`. -/
def D2SQueryAbortOnTrace
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ¬ D2SQueryNoAbortOnTrace (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) trace

/-! ## Claim 5.19 and Claim 5.20 — subroutine no-abort -/

/-- CO25 Claim 5.19 — If `¬ E_inv(tr, s)`, `¬ E_prp(tr)`, and `¬ E_fork(tr, s)`, then
`BackTrack(tr, tr_∇, s) ≠ err`.

Paper-faithful (CO25 §5.7 Claim 5.19). `S_BT` is the backtrack-sequence family for
`(trace, state)`; callers derive `hInv` and `hFork` via `lemma_5_12` / `lemma_5_14` (both
hold for any `S_BT` under `¬ E`), and `hPrp` via `lemma_5_10` (under `isConsistentTrace ∧ ¬ E`).
The proof connects this `S_BT` to the one computed by `BackTrackNoAbort`. -/
lemma claim_5_19_backTrack_noAbort [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ = TraceNabla.ofQueryLog trace)
    (state : CanonicalSpongeState U)
    (S_BT : S_BT trace state)
    (hInv : ¬ BadEventDS.E_inv trace state S_BT)
    (hPrp : ¬ BadEventDS.E_prp trace)
    (hFork : ¬ BadEventDS.E_fork trace state S_BT) :
    BackTrackNoAbort (δ := δ)
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (depthBound := trace.length + 1) (trace := trace) (trΔ := trΔ) (h_trΔ := h_trΔ)
      (state := state) := by
  sorry

/-- CO25 Claim 5.20 — If `¬ E_prp(tr)`, then `LookAhead(tr.p, s, i) ≠ err` for all `(s, i)`.

Paper-faithful (CO25 §5.7 Claim 5.20). Callers derive `hPrp` via `lemma_5_10`
(under `isConsistentTrace ∧ ¬ E`). -/
lemma claim_5_20_lookAhead_noAbort [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (state : CanonicalSpongeState U)
    (i : pSpec.ChallengeIdx)
    (hPrp : ¬ BadEventDS.E_prp trace) :
    LookAheadNoAbort
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      trΔ state i := by
  sorry

/-! ## Lemma 5.17 and Lemma 5.18 — full algorithm no-abort -/

/-- CO25 Lemma 5.17 — For every `(h, p, p⁻¹)`-trace `tr`, if `isConsistentTrace(tr) ∧ ¬ E(tr)`
then `D2STrace(tr)` does not abort.

Paper statement (CO25 §5.7 Lemma 5.17): if `E(tr) = 0` then `D2STrace(tr)` does not abort.
We additionally require `isConsistentTrace(tr)` (implicit in the paper from the `(h, p, p⁻¹)`
sampling context) because our `lemma_5_10` needs it to derive `¬ E_prp(tr)`.

Proof sketch: D2STrace aborts in two sub-calls:
- The `BackTrack` sub-call: derive `¬ E_inv` (via `lemma_5_12`), `¬ E_prp` (via `lemma_5_10`),
  `¬ E_fork` (via `lemma_5_14`), then apply Claim 5.19.
- The `LookAhead` sub-call: derive `¬ E_prp` (via `lemma_5_10`), then apply Claim 5.20. -/
lemma lemma_5_17_d2sTrace_noAbort [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hConsistent : BadEventDS.isConsistentTrace trace)
    (hE : ¬ BadEventDS.E trace) :
    D2STraceNoAbort (T_H := T_H) (T_P := T_P) (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      trace := by
  sorry

-- `[∀ i, DecidableEq (pSpec.Message i)]` is needed in the proof body but not the type.
set_option linter.unusedDecidableInType false in
/-- CO25 Lemma 5.18 — For every `(t_h, t_p, t_{p⁻¹})`-query algorithm `A`, let `tr_A` be the
query-answer trace from `A` with `D2SQuery` oracle access.  If `isConsistentTrace(tr_A) ∧ ¬ E(tr_A)`
then `A^D2SQuery` does not abort.

Paper statement (CO25 §5.7 Lemma 5.18): if `E(tr_A) = 0` then `A^D2SQuery` does not abort.
We additionally require `isConsistentTrace(tr_A)` for the same reason as Lemma 5.17.

Proof sketch: D2SQuery aborts in its `BackTrack` sub-call; derive `¬ E_inv` (via `lemma_5_12`),
`¬ E_prp` (via `lemma_5_10`), `¬ E_fork` (via `lemma_5_14`), then apply Claim 5.19. -/
lemma lemma_5_18_d2sQuery_noAbort
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (traceA : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hConsistent : BadEventDS.isConsistentTrace traceA)
    (hE : ¬ BadEventDS.E traceA) :
    D2SQueryNoAbortOnTrace (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) traceA := by
  sorry

/-! ## Theorem 5.19 and Theorem 5.20 — contrapositives (used in Section 5.8) -/

/-- CO25 Theorem 5.19 — If `A^D2SQuery` aborts then `E(tr_A)` holds.

This is the contrapositive of Lemma 5.18, and is the form used in Section 5.8. -/
theorem theorem_5_19_d2sQuery_abort_implies_badEvent
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (traceA : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hConsistent : BadEventDS.isConsistentTrace traceA)
    (hAbort : D2SQueryAbortOnTrace (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) traceA) :
    BadEventDS.E traceA := by
  classical
  by_contra hE
  exact hAbort
    (lemma_5_18_d2sQuery_noAbort (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      traceA hConsistent hE)

/-- CO25 Theorem 5.20 — If `D2STrace(tr)` aborts then `E(tr)` holds.

This is the contrapositive of Lemma 5.17, and is the form used in Section 5.8. -/
theorem theorem_5_20_d2sTrace_abort_implies_badEvent [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    {T_H T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hConsistent : BadEventDS.isConsistentTrace trace)
    (hAbort :
      D2STraceAbort (T_H := T_H) (T_P := T_P) (δ := δ)
        (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
        trace) :
    BadEventDS.E trace := by
  classical
  by_contra hE
  exact hAbort
    (lemma_5_17_d2sTrace_noAbort (T_H := T_H) (T_P := T_P) (δ := δ)
      (oSpec := oSpec) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      trace hConsistent hE)

end DuplexSpongeFS.AbortAnalysis

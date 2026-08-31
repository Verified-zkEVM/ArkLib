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

1. **Claim 5.19** (`claim_5_19_backTrack_noAbort`) — `BackTrack(tr, s) ≠ err` for a
   duplicate-free sound subindex under `¬ E(tr)`.
2. **Claim 5.20** (`claim_5_20_lookAhead_noAbort`) — `LookAhead(tr.p, s, i) ≠ err` for the same
   normalized index under `¬ E(tr)`. Used by Lemma 5.17.
3. **Lemma 5.17** (`lemma_5_17_d2sTrace_noAbort`) — `D2STrace(tr)` does not abort under
4. **Lemma 5.18** (`lemma_5_18_d2sQuery_noAbort`) — `A^D2SQuery` does not abort under
   The no-abort predicate replays the trace through `d2sQueryStep` from the default
   `D2SQueryState`, so that `cacheP` evolves naturally rather than being universally
   quantified.
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
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  none ∉ support (d2sTraceSalted (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      log).run

/-- Predicate: `D2STrace` on `trace` aborts. -/
def D2STraceAbort [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ¬ D2STraceNoAbort (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      log

/-- Predicate: `BackTrack` does not hit the `err` branch on `(trace, state)`.

The caller supplies the generic `tr_∇` alongside its provenance `h_trΔ : trΔ.IsSubsetOfQueryLog trace`;
`backTrack` consumes both. -/
def BackTrackNoAbort [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (depthBound : ℕ)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
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
  ExperimentOutput.err ∉ support
    (lookAhead (pSpec := pSpec) (U := U) (trΔp := trΔ.p) state i)

section D2SQueryNoAbort

variable [DecidableEq StmtIn] [DecidableEq U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Predicate: `A^{D2SQuery^g}` does not abort for a generic probabilistic adversary `A` -/
def D2SQueryNoAbort
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (A : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) : Prop :=
  none ∉ support (d2fRaw (T_H := T_H) (T_P := T_P) gImpl A initM).run

/-- Predicate: `A^{D2SQuery}` aborts for a generic probabilistic adversary `A` -/
def D2SQueryAbort
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (A : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) : Prop :=
  ¬ D2SQueryNoAbort (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      gImpl A initM

end D2SQueryNoAbort

/-! ## Claim 5.19 and Claim 5.20 — subroutine no-abort -/

/-- Corrected CO25 Claim 5.19 — outside the combined bad event, BackTrack cannot return `err`
when `trΔ` is a duplicate-free sound normalized subindex of `trace`.

This is the interface actually needed by Claim 5.21. It avoids the false refinement step from an
arbitrary `S_BT` family to the executable linear scan. The fully proved theorem
`BadEventDS.backtrack_searchUnambiguous_of_normalizedSubindex_of_not_E` establishes that the two
concrete lookup sites are unambiguous; self-loops and repeated capacities are invalid chains and
return `noResult`. -/
lemma claim_5_19_backTrack_noAbort [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (hIndex : trΔ.IsNormalizedSubindex trace)
    (state : CanonicalSpongeState U)
    (hNoBad : ¬ BadEventDS.E trace) :
    BackTrackNoAbort (δ := δ)
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (depthBound := trace.length + 1) (trace := trace) (trΔ := trΔ)
      (h_trΔ := hIndex.isSubset)
      (state := state) := by
  unfold BackTrackNoAbort
  apply backTrack_ne_err_of_searchUnambiguous
  exact BadEventDS.backtrack_searchUnambiguous_of_normalizedSubindex_of_not_E
    (trace := trace) hIndex hNoBad

/-- Corrected CO25 Claim 5.20 — outside the combined bad event, LookAhead cannot return `err`
when its permutation table is a duplicate-free sound normalized subindex of `trace`.

The `hIndex` hypothesis is the missing trace binding identified in review. The fully proved theorem
`BadEventDS.lookahead_searchUnambiguous_of_normalizedIndex_of_not_E` gives one successor per full
input state; a capacity self-loop returns `noResult`, not `err`. -/
lemma claim_5_20_lookAhead_noAbort [DecidableEq StmtIn] [DecidableEq U]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (state : CanonicalSpongeState U)
    (i : pSpec.ChallengeIdx)
    (hIndex : trΔ.IsNormalizedSubindex trace)
    (hNoBad : ¬ BadEventDS.E trace) :
    LookAheadNoAbort
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      trΔ state i := by
  sorry

/-! ## Lemma 5.17 and Lemma 5.18 — full algorithm no-abort -/

/-- CO25 Lemma 5.17 — For every `(h, p, p⁻¹)`-trace `tr`, if `¬ E(tr)`
then `D2STrace(tr)` does not abort.

Paper statement (CO25 §5.7 Lemma 5.17): if `E(tr) = 0` then `D2STrace(tr)` does not abort.

Proof sketch: maintain that the live two-table view is an `IsNormalizedSubindex` of the relevant raw
trace. The common hypothesis `¬ E(trace)` then feeds Claim 5.19 for `BackTrack` and Claim 5.20 for
`LookAhead`; their fully proved bad-event bridges discharge the concrete lookup ambiguity facts. -/
lemma lemma_5_17_d2sTrace_noAbort [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (hE : ¬ BadEventDS.E (dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
      (TaggedQueryLog.untagged log))) :
    D2STraceNoAbort (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      log := by
  sorry

/-- `duplexSpongeTrace gImpl A initM` — the internal duplex-sponge query log (`tr_A`) produced
by running `A^{D2SQuery^{gImpl}}` from initial inner state `initM`.
This is used for Hyb1, Hyb2, Hyb3, i.e. the middle D2SQuery-simulated hybrid games. -/
noncomputable def duplexSpongeTrace
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (A : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M) :
    AbortComp (oSpec + D2SChallengePlusUnitOracle (U := U) challengeSpec)
      (QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  (do let ⟨⟨_, st⟩, _⟩ ← d2fRaw (T_H := T_H) (T_P := T_P) gImpl A initM
      pure st.trace)

-- `[∀ i, DecidableEq (pSpec.Message i)]` is needed in the proof body but not the type.
set_option linter.unusedDecidableInType false in
/-- CO25 Lemma 5.18 — For every `(t_h, t_p, t_{p⁻¹})`-query algorithm `A`, let
`tr_A := duplexSpongeTrace gImpl A initM` be the query-answer trace from `A` with `D2SQuery`
oracle access. If `¬ E(tr_A)` then `A^D2SQuery` does not abort.

Paper statement (CO25 §5.7 Lemma 5.18): if `E(tr_A) = 0` then `A^D2SQuery` does not abort.

The property holds for all oracle implementations `gImpl`, since the abort
depends only on `BackTrack`'s structural analysis of the trace, not on oracle responses.

Proof sketch: the replay invariant supplies an `IsNormalizedSubindex` for the trace at each
`BackTrack` call. Apply corrected Claim 5.19 with that index and `¬ E(tr_A)`. -/
lemma lemma_5_18_d2sQuery_noAbort
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (A : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M)
    (tr_A : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h_tr_A_mem_support : some tr_A ∈ support (duplexSpongeTrace (δ := δ) (T_H := T_H) (T_P := T_P)
        gImpl A initM).run)
    (hE : ¬ BadEventDS.E tr_A) :
    D2SQueryNoAbort (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n)
      (pSpec := pSpec) (U := U) gImpl A initM
    -- This also means tr_A is the full trace that we can collect from
      -- the non-aborted D2SQuery-simulated computation A
    := by sorry

/-! ## Theorem 5.19 and Theorem 5.20 — contrapositives (used in Section 5.8) -/

/-- CO25 Theorem 5.19 — If `A^{D2SQuery}` aborts then `E(tr_A)` holds.

This is the contrapositive of Lemma 5.18, and is the form used in Section 5.8.
Given a specific trace `tr_A` from a successful execution path, if `D2SQueryAbort` holds, then `E(tr_A)` must hold. -/
theorem theorem_5_19_d2sQuery_abort_implies_badEvent
    [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {T_H : Type}
    {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {α : Type}
    {κ : Type} {challengeSpec : OracleSpec κ}
    {M : Type} [Inhabited M]
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (A : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (initM : M)
    (tr_A : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h_tr_A_mem_support : some tr_A ∈ support (duplexSpongeTrace (δ := δ) (T_H := T_H) (T_P := T_P)
        gImpl A initM).run)
    (hAbort : D2SQueryAbort (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (n := n)
      (pSpec := pSpec) (U := U) gImpl A initM) :
    BadEventDS.E tr_A := by
  by_contra hE
  exact hAbort (lemma_5_18_d2sQuery_noAbort (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
    gImpl A initM tr_A h_tr_A_mem_support hE)

/-- CO25 Theorem 5.20 — If `D2STrace(tr)` aborts then `E(tr)` holds.

This is the contrapositive of Lemma 5.17, and is the form used in Section 5.8. -/
theorem theorem_5_20_d2sTrace_abort_implies_badEvent [DecidableEq StmtIn] [DecidableEq U]
    [∀ i, Fintype (pSpec.Message i)]
    {T_H T_P : Type} {Salt : Type} [SaltCodec U δ Salt]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (log : TaggedQueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U))
    (hAbort :
      D2STraceAbort (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        log) :
    BadEventDS.E (dsTraceOfLog (oSpec := oSpec) (StmtIn := StmtIn) (U := U)
      (TaggedQueryLog.untagged log)) := by
  classical
  by_contra hE
  exact hAbort
    (lemma_5_17_d2sTrace_noAbort (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
      (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      log hE)

end DuplexSpongeFS.AbortAnalysis

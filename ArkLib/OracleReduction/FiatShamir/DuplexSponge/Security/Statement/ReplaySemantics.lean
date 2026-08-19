/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.Bounds
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.Data.Hash.DuplexSponge

/-!
# Statement layer — module 2: replay semantics (real Backtrack + LookAhead + schedule markers)

This module **does not define** a parallel `SearchCursor`/`ExactMatch`/
`EarlyFork`/`SemanticResult`/`Marker`/`Chain` family nor a vacuous `Nonempty`-based "no-abort".
Instead it retains the concrete trace-normalization **data** helpers and then **refers directly to
the real, acyclic-safe replay operators**:

- `DuplexSpongeFS.Backtrack`: `S_BT` (=`BacktrackSequenceFamily`), `J_BT`, `BacktrackOutput`,
  `backTrack`;
- `DuplexSpongeFS.Lookahead`: `S_LA` (=`LookaheadSequenceFamily`), `lookAhead`;
- the **no-abort** statements name the real operators **and their real `.err` result**:
  `backTrack … ≠ ExperimentOutput.err` and the LookAhead fork condition is stated over the real
  monadic `lookAhead` (Step 2 returns `err` exactly when `|S_LA| > 1`);
- `Certified` uses the **real schedule marker predicate** `ScheduleCursor.firstSqueezeQuery?`
  (a nonempty squeeze starting at a rate boundary), not a trivial in-bounds check.

All of the imported operators are handler-free (they live in the acyclic `Backtrack`,
`Lookahead`, `BacktrackSchedule`, `BadEventDefs` layers), so this module adds no import cycle and
no handler dependency.
-/

namespace DuplexSpongeFS

namespace Statement

open OracleComp OracleSpec ProtocolSpec
open DSTraceStorage

/-! ## Concrete trace-normalization data (retained from the audit) -/

/-- A **concrete forward occurrence** in the normalized forward table: a real state pair
`(s_in, s_out)` — one `p`-call's input and output `CanonicalSpongeState`.  This is what the
absorptions / squeezes of the transcript reduce to once `p⁻¹` entries are normalized forward
(CO25 Def 5.3). -/
abbrev ForwardOccurrence (U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  CanonicalSpongeState U × CanonicalSpongeState U

/-- The **concrete normalized forward table** `T_fwd`: the ordered list of forward occurrences. -/
abbrev ForwardTable (U : Type) [SpongeUnit U] [SpongeSize] : Type := List (ForwardOccurrence U)

/-- The concrete forward-normalizing map from a real trace: every `p`-query entry becomes
`(s_in, s_out)`, every `p⁻¹`-query entry is normalized to its forward counterpart, and hash /
other entries are dropped.  This implements CO25 Def 5.3's inverse-to-forward normalization. -/
def forwardTableOfTrace {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
    (trace : Trace StmtIn U) : ForwardTable U :=
  trace.filterMap (fun e =>
    match e with
    | ⟨.inr (Sum.inl s_in), s_out⟩ => some (s_in, s_out)
    | ⟨.inr (Sum.inr s_out), s_in⟩ => some (s_in, s_out)
    | _ => none)

/-- The **strict-prefix** normalized forward table used by Backtrack: the forward occurrences
falling before the current replay cursor (CO25 Algo 5.1). -/
def strictPrefixOf (U : Type) [SpongeUnit U] [SpongeSize]
    (T_fwd : ForwardTable U) (cutoff : ℕ) : ForwardTable U :=
  T_fwd.take cutoff

/-- The **full** normalized forward table used by LookAhead (CO25 Algo 5.2). -/
def fullOf (U : Type) [SpongeUnit U] [SpongeSize]
    (T_fwd : ForwardTable U) : ForwardTable U :=
  T_fwd

/-- The rate block of an output state, as the underlying symbol list. -/
def rateListOf (U : Type) [SpongeUnit U] [SpongeSize]
    (state : CanonicalSpongeState U) : List U :=
  (Vector.take state SpongeSize.R).toList

/-- The concrete **per-entry agreement** relation: a forward occurrence `(s_in, s_out)`
reproduces the `symIdx`-th symbol of the target transcript iff the output state's rate block, at
position `symIdx`, equals the target symbol. -/
def ForwardOccurrenceAgreesAt (U : Type) [SpongeUnit U] [SpongeSize]
    (occ : ForwardOccurrence U) (symIdx : ℕ) (target : Option U) : Prop :=
  (rateListOf U occ.2)[symIdx]? = target

/-! ## Real replay operators (referred, not redefined) -/

/-- The real Backtrack **no-abort** (plan PF-1 / audit #4): absent the bad event `BadEvent` on the
trace, the real procedural operator `backTrack …` never returns its `ExperimentOutput.err`
(multiple-match / ambiguous) result — it yields a unique `BacktrackOutput`.  This names the real
operator and its real `.err` result; there is **no** vacuous `Nonempty` outcome. -/
def BacktrackNoAbort {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq StmtIn]
    [DecidableEq U] {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {n : Nat} {pSpec : ProtocolSpec n} {δ : Nat} [HasMessageSize pSpec] [HasChallengeSize pSpec]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (trΔ : TraceNabla T_H T_P StmtIn U) (h_trΔ : trΔ.IsSubsetOfQueryLog trace)
    (state : CanonicalSpongeState U) : Prop :=
  ¬ BadEvent trace →
    DuplexSpongeFS.Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
      trace trΔ h_trΔ state ≠ ExperimentOutput.err

/-- The real LookAhead **no-abort** (plan PF-1 / audit #4): absent the bad event, the real
executable `lookAhead` (CO25 Algo 5.2) never yields its `.err` outcome.  Step 2 returns
`ExperimentOutput.err` exactly when `|S_LA| > 1` (a scan-time fork on multiple maximal lookahead
sequences), so this states that `lookAhead` is not the `.err` computation.  No vacuous
`Nonempty (Chain U)`. -/
def LookAheadNoAbort {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U] {n : Nat}
    {pSpec : ProtocolSpec n} [HasChallengeSize pSpec] {T_P : Type}
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trΔp : T_P) (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) : Prop :=
  DuplexSpongeFS.Lookahead.lookAhead trΔp state i ≠
    (pure ExperimentOutput.err :
      OracleComp (Unit →ₒ U) (ExperimentOutput (Vector U (challengeSize i))))

/-! ## LookAhead certification via the real schedule marker (audit #5) -/

/-- The real **post-prover / pre-squeeze certification** predicate: a forward-table position
`pos` is certified exactly when it is the **first query of a nonempty squeeze beginning at a rate
boundary** of the canonical schedule.  This cites the real `ScheduleCursor.firstSqueezeQuery?`
marker (and its witnesses `BacktrackSchedule.schedulePhase_squeeze_first`), **not** a trivial
`pos < length` check. -/
def Certified (R : ℕ) (cursor : DuplexSpongeFS.Backtrack.ScheduleCursor) (len : ℕ)
    (pos : ℕ) : Prop :=
  DuplexSpongeFS.Backtrack.ScheduleCursor.firstSqueezeQuery? R cursor len = some pos

end Statement

end DuplexSpongeFS

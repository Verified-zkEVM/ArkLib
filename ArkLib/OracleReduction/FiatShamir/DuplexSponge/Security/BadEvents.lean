/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventDefs

/-!
# Definition and analysis of bad events

This file contains the analysis of bad events for the duplex sponge Fiat-Shamir transformation,
following Section 5.6 in the paper.

The trace-only surface — the redundancy test, the base trace `getBaseTrace` (Defs 5.5/5.6), and
the bad events `E_h` / `E_p` / `E_pinv` / `E_dup` / `E_func` / `E` (Def 5.7) — lives in the lower
module `BadEventDefs` (imported below), so that live algorithms (`D2SQuery`, `StdTrace`) can
invoke `Monitor` against `E` without an import cycle.  This file provides everything above that
boundary: the Lemma 5.8 experiment, the collision-family events, and the BackTrack-family events.

## Predicate organization

The bad-event surface mirrors the paper definitions directly:

- **Trace-only events (Def 5.7):** `E_h` / `E_p` / `E_pinv` / `E_dup` / `E_func` / `E`
  (in [`BadEventDefs`](./BadEventDefs.lean)).
- **Collision family (Def 5.9):** `collisionFwdFwd` / `collisionBwdBwd` / `collisionFwdBwd` /
  `collisionBwdFwd` / `collisionPerm`, with paper aliases `E_col_p` / `E_col_pinv` /
  `E_col_p_pinv` / `E_col_pinv_p` / `E_prp`.
- **BackTrack-family events (Defs 5.11, 5.13, 5.15):** `E_inv`, `E_fork` (with subcases
  `E_fork_h`, `E_fork_p`, `E_fork_h_p`), and `E_time` (with subcases `E_time_h`, `E_time_p`).
  These take `(S_BT : Backtrack.S_BT trace state)` as an explicit parameter and quantify over
  the family `S_BT.seqFamily` and the index-list family `Backtrack.J_BT S_BT` (CO25 Defs 5.3 &
  5.4).

Lemmas `lemma_5_12` / `lemma_5_14` / `lemma_5_16` are the paper-faithful "if `E(tr) = 0` then
the BackTrack-family event vanishes" statements.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

namespace BadEventDS
open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)


/-! ## Lemma 5.8 — closed-form bound
This section is consistency-free: `lemma_5_8` bounds `Pr[E]` directly via birthday-style
counting on freshly-sampled values. -/
section Lemma_5_8

/-- CO25 Lemma 5.8 — Closed-form upper bound on `max{Pr[E | 𝒟_𝔖], Pr[E | 𝒟_Σ]}`.
For a `(tₕ, tₚ, tₚᵢ)`-query prover and verifier making `L` permutation queries (with `tₚ ≥ L`),
the bound is:

```
(7·T² − 3·T) / (2·|Σ|^c)
```

where `T = tₕ + 1 + tₚ + L + tₚᵢ`. -/
noncomputable def lemma5_8Bound (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- CO25 §5.6 — Run a concrete duplex-sponge experiment under an oracle implementation and return
the full DS query-answer trace.  Used as the building block for both the sponge (`𝒟_𝔖`) and
simulator (`𝒟_Σ`) trace distributions in Lemma 5.8. -/
def traceDistOfConcreteExperiment
    {σ α : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (exp : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let outWithLog :
      OracleComp (duplexSpongeChallengeOracle StmtIn U)
        (α × QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
    (simulateQ loggingOracle exp).run
  let ⟨_, trace⟩ ← (simulateQ impl outWithLog).run' (← init)
  pure trace

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Class predicate on the `[]ₒ + DS` query domain: is this a hash (`h`) query point? -/
def isHashQueryPoint : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- Class predicate on the `[]ₒ + DS` query domain: is this a forward-permutation (`p`) point? -/
def isFwdPermQueryPoint : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inr (.inr (.inl _)) => true
  | _ => false

/-- Class predicate on the `[]ₒ + DS` query domain: is this an inverse-permutation (`p⁻¹`)
point? -/
def isBwdPermQueryPoint : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inr (.inr (.inr _)) => true
  | _ => false

/-- CO25 Lemma 5.8 — aggregate DS hash queries in the combined empty-plus-DS surface. -/
def isLemma5_8HashQuery :
    ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Prop :=
  fun t => isHashQueryPoint (StmtIn := StmtIn) (U := U) t = true

/-- CO25 Lemma 5.8 — aggregate DS forward-permutation queries in the combined surface. -/
def isLemma5_8PermQuery :
    ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Prop :=
  fun t => isFwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true

/-- CO25 Lemma 5.8 — aggregate DS inverse-permutation queries in the combined surface. -/
def isLemma5_8PermInvQuery :
    ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Prop :=
  fun t => isBwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true

instance : DecidablePred (isLemma5_8HashQuery (StmtIn := StmtIn) (U := U)) := by
  intro t
  unfold isLemma5_8HashQuery
  infer_instance

instance : DecidablePred (isLemma5_8PermQuery (StmtIn := StmtIn) (U := U)) := by
  intro t
  unfold isLemma5_8PermQuery
  infer_instance

instance : DecidablePred (isLemma5_8PermInvQuery (StmtIn := StmtIn) (U := U)) := by
  intro t
  unfold isLemma5_8PermInvQuery
  infer_instance

/-- CO25 Lemma 5.8 — Semantic `(tₕ, tₚ, tₚᵢ)` query bound for the salted §5.6 prover.
`IsLemma5_8QueryBound maliciousProver tₕ tₚ tₚᵢ` asserts that the prover makes **in total** at
most `tₕ` hash queries, `tₚ` forward permutation queries, and `tₚᵢ` inverse permutation queries
on the combined `[]ₒ + DS` surface that matches the §5.8 hybrid games (LHS=Hyb_0, RHS=Hyb_1).

Formalized as three per-class `IsQueryBoundP` totals.  (A per-point
`IsPerIndexQueryBound` with a constant budget would be strictly weaker — it caps each *specific*
query point separately and admits unboundedly long traces — and cannot support the paper's
`|tr̄| ≤ tₕ + 1 + tₚ + L + tₚᵢ` accounting.) -/
abbrev IsLemma5_8QueryBound
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  OracleComp.IsQueryBoundP maliciousProver isLemma5_8HashQuery tₕ ∧
  OracleComp.IsQueryBoundP maliciousProver isLemma5_8PermQuery tₚ ∧
  OracleComp.IsQueryBoundP maliciousProver isLemma5_8PermInvQuery tₚᵢ

/-- CO25 §5.6 — Project a `[]ₒ + DS` combined trace log down to just the DS component.
The empty-oracle branch is unreachable, so we discard it via `PEmpty.elim`. -/
def lemma5_8ProjectTraceLog
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, _⟩ => PEmpty.elim q
    | ⟨.inr q, r⟩ => some ⟨q, r⟩

/-- The empty-oracle branch of the Section 5.6 experiment is uncallable. -/
private def lemma5_8EmptyQueryImpl {σ : Type} :
    QueryImpl []ₒ (StateT σ ProbComp) :=
  fun q => PEmpty.elim q

/-- Generic-`m` sibling of `lemma5_8EmptyQueryImpl`: the empty-oracle branch is uncallable in any
target monad. Used to build `QueryImpl ([]ₒ + DS) (OptionT (StateT _ ProbComp))` via `QueryImpl.+`
where the right summand is the abortable DS impl. -/
private def lemma5_8EmptyQueryImplGeneric {m : Type → Type} : QueryImpl []ₒ m :=
  fun q => PEmpty.elim q

/-- CO25 §5.6 — Monad-reorder + logging wrapper. Reorders `StateT σ (OptionT ProbComp)`
into `OptionT (StateT (σ × QueryLog) ProbComp)` so the log survives an abort (paper line 1417:
"abort halts execution; trace is partial"), and appends `⟨q, a⟩` on each successful query. -/
private def lemma5_8LoggingWrapper {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp))) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (OptionT
        (StateT (σ × QueryLog (duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
  fun q => OptionT.mk fun st => do
    let r ← (impl q st.1).run
    match r with
    | none => pure (none, st)
    | some (a, s') => pure (some a, (s', st.2 ++ [⟨q, a⟩]))

/-- CO25 §5.6 — the log-appending wrapper of the Lemma-5.8 experiments, standalone so
support/counting lemmas can reason about it: each *successful* DS query appends the wide-tagged
entry `⟨Sum.inr q, a⟩` to the `[]ₒ + DS` log; an abort leaves the log unchanged (paper line 1417:
"abort halts execution; trace is partial"). -/
def lemma5_8WrappedDSImpl {σ : Type}
    (spongeImpl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp))) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (OptionT
        (StateT (σ ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
  fun q => OptionT.mk fun st => do
    let r ← (spongeImpl q st.1).run
    match r with
    | none => pure (none, st)
    | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))

/-- The `[]ₒ + DS` combined implementation of the Lemma-5.8 experiments: the (uncallable) empty
branch paired with the log-appending DS wrapper `lemma5_8WrappedDSImpl`. -/
def lemma5_8CombinedImpl {σ : Type}
    (spongeImpl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp))) :
    QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
      (OptionT
        (StateT (σ ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
  (lemma5_8EmptyQueryImplGeneric
    (m := OptionT
      (StateT (σ ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)))
  + lemma5_8WrappedDSImpl (StmtIn := StmtIn) (U := U) spongeImpl

/-- CO25 §5.6 — Abortable Lemma-5.8 trace experiment, mirroring the §5.8 hybrid skeleton
(`KeyLemma.dsfsGame` / `hybridGame`): the salted `maliciousProver` runs under `impl`, then the
forward-only verifier `𝒱^{h,p} := V.toDSFS δ` (paper Figure 4 line 3) runs on its output, with the
carrier `σ` (e.g. `D_𝔖.Carrier` / `D2SQueryState`) threaded throughout.

Returns `(tr_P̃, tr_V)`; the bad event `E` (Def 5.7) is evaluated on `tr_P̃ ++ tr_V`. -/
noncomputable def lemma5_8ProjectedTraceDistAbortable
    {σ : Type}
    (init : ProbComp σ)
    (spongeImpl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp)))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let s₀ ← init
  -- Log each DS query into the wide `[]ₒ + DS` log (tagged `Sum.inr`); the log is kept on abort.
  -- The `[]ₒ` summand is unreachable (`lemma5_8CombinedImpl` pairs it with the generic empty
  -- impl).
  let combinedImpl := lemma5_8CombinedImpl (StmtIn := StmtIn) (U := U) spongeImpl
  -- Prover phase on a fresh log `[]`; the log accumulates the prover trace `tr_P̃`.
  let proverResult ← ((simulateQ combinedImpl maliciousProver).run) (s₀, [])
  match proverResult with
  | (none, (_, trP)) =>
      -- Abort (paper line 1417): execution halts, `V` never runs, so `tr_V = []`.
      pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP, [])
  | (some ⟨stmtIn, proof⟩, (s₁, trP)) =>
      -- Success: verifier reuses carrier `s₁` but a fresh log, so `tr_V` is verifier-only.
      -- `runForwardVerifierWide` lifts the forward verifier to the wide spec (shared log surface).
      let verifyCompWide :
          OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
        runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof
      let verifierResult ← ((simulateQ combinedImpl verifyCompWide).run) (s₁, [])
      let trV := verifierResult.2.2
      -- Project both `[]ₒ + DS` logs down to bare DS.
      pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP,
            lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trV)

/-- CO25 §5.6 Lemma 5.8 — Shared sequential experiment for the lazy simulator runner.
The salted malicious prover produces `(statement, (salt, messages))`; the verifier consumes that
same salted proof through the forward-only wide lift `runForwardVerifierWide`.  Thus this is
exactly the computation underlying the success branch of
`lemma5_8ProjectedTraceDistAbortable`, except that its wrapper log is not reset between phases.

Type-level CO25 Figure 4 line 3: the honest verifier begins at the narrow forward-only surface
`[]ₒ + duplexSpongeForwardOracle` (`𝒱^{h,p}`, with no `p⁻¹`); `runForwardVerifierWide` then lifts
that computation into the adversary's wide `[]ₒ + duplexSpongeChallengeOracle` surface. -/
def lemma5_8TraceExperiment
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) := do
  let ⟨stmtIn, proof⟩ ← maliciousProver
  runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof

/-- CO25 §5.6 — Trivially lift a total `StateT σ ProbComp` DS implementation to the
abortable shape `StateT σ (OptionT ProbComp)` required by `lemma5_8ProjectedTraceDistAbortable`.
The lifted impl never produces `none`. -/
def lemma5_8TotalAbortLift {σ : Type}
    (spongeImpl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)) :=
  fun q s => OptionT.lift (spongeImpl q s)

/-- CO25 Lemma 5.8 — Left-hand-side trace distribution with explicit abort handling.
Sponge DS execution under the explicit `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` implementation. The eager impl is
total (never aborts), so the `OptionT`-layer is a dummy. Returns the pair `(tr_P̃, tr_V)`. -/
noncomputable def lemma5_8SpongeTraceDist
    {σSponge : Type}
    (initSponge : ProbComp σSponge)
    (implSponge : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σSponge ProbComp))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
    (init := initSponge)
    (spongeImpl := lemma5_8TotalAbortLift (StmtIn := StmtIn) (U := U) implSponge)
    V maliciousProver

/- The revised Lemma 5.8 endpoints are stated in `Lemma58Revised.lean`.  Its ideal-side proof
uses the reusable per-index union-bound infrastructure; its revised-D2S side uses the stateful
first-bad runner.  The obsolete eager max-of-sponge-and-Σ façade has been removed. -/

end Lemma_5_8

/-! ## Definition 5.9 — permutation collisions; paper `E_prp`; well-formed trace predicate -/
section Def5_9_CollisionsAndConsistency

/-! Then we define other bad events that don't hold (`= 0`)
if the combined event doesn't hold (`= 0`)
-/

/-- CO25 Definition 5.9 Item 1 — Event `E_{col,p}(tr)`.
There exist `(p, s_in, s_out)` and `(p, s_in', s_out)` in `tr̄` with `s_in ≠ s_in'`:
two distinct forward-permutation inputs map to the same output. -/
def collisionFwdFwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateIn stateIn' stateOut,
    ⟨.inr <|.inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <|.inl stateIn', stateOut⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

/-- CO25 Definition 5.9 Item 2 — Event `E_{col,p⁻¹}(tr)`.
There exist `(p⁻¹, s_out, s_in)` and `(p⁻¹, s_out', s_in)` in `tr̄` with `s_out ≠ s_out'`:
two distinct inverse-permutation inputs map to the same output. -/
def collisionBwdBwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateOut stateOut' stateIn,
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

/-- CO25 Definition 5.9 Item 3 — Event `E_{col,p,p⁻¹}(tr)` in exact paper shape.
There exist `(p, s_in, s_out)` and `(p⁻¹, s_out, s_in')` in `tr̄` with `s_out = s_out'` and
`s_in ≠ s_in'`: `p` is onto but its inverse is not a function. -/
def collisionFwdBwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateIn stateOut stateIn',
    ⟨.inr <| .inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut, stateIn'⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p_pinv := collisionFwdBwd

/-- CO25 Definition 5.9 Item 4 — Event `E_{col,p⁻¹,p}(tr)` in exact paper shape.
There exist `(p⁻¹, s_out, s_in)` and `(p, s_in, s_out')` in `tr̄` with `s_out ≠ s_out'`:
`p⁻¹` is onto but `p` is not a function. -/
def collisionBwdFwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateOut stateIn stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateIn, stateOut'⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p := collisionBwdFwd

/-- CO25 Definition 5.9 — Event `E_prp(tr)`: the disjunction of the four collision events above
(`E_col_p`, `E_col_pinv`, `E_col_p_pinv`, `E_col_pinv_p`). Informally, Items 1/3 make `p`
non-injective; Items 2/4 make `p⁻¹` non-injective. -/
def collisionPerm : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace
    ∨ collisionFwdBwd trace ∨ collisionBwdFwd trace

alias E_prp := collisionPerm

end Def5_9_CollisionsAndConsistency

/-! ## Lemma 5.10 — trace-level bad-event implication -/
section Lemma5_10

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 1 of Definition 5.9. -/
lemma not_collisionFwdFwd_of_not_combined (h : ¬ E trace) : ¬ collisionFwdFwd trace := by
  intro hff
  apply h; clear h
  obtain ⟨sI, sI', sO, hm1, hm2, hne⟩ := hff
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    exact hne (congrArg (fun x => match x with | ⟨.inr (.inl s), _⟩ => s | _ => sI) hgj)
  left; right; left
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · exact ⟨⟨j, hj⟩, sO.capacitySegment, ⟨sI', sO, hgj, rfl⟩,
      Or.inr (Or.inl ⟨⟨i, hi⟩, h_lt, sI, sO, hgi, rfl⟩)⟩
  · exact ⟨⟨i, hi⟩, sO.capacitySegment, ⟨sI, sO, hgi, rfl⟩,
      Or.inr (Or.inl ⟨⟨j, hj⟩, h_lt, sI', sO, hgj, rfl⟩)⟩

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 2 of Definition 5.9. -/
lemma not_collisionBwdBwd_of_not_combined (h : ¬ E trace) : ¬ collisionBwdBwd trace := by
  intro hbb
  apply h; clear h
  obtain ⟨sO, sO', sI, hm1, hm2, hne⟩ := hbb
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    exact hne (congrArg (fun x => match x with | ⟨.inr (.inr s), _⟩ => s | _ => sO) hgj)
  left; right; right
  unfold capacitySegmentDupPermInv
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · refine ⟨⟨j, hj⟩, sI.capacitySegment, ⟨sO', sI, hgj, rfl⟩, ?_⟩
    right; right; left
    exact ⟨⟨i, hi⟩, h_lt, sO, sI, hgi, rfl⟩
  · refine ⟨⟨i, hi⟩, sI.capacitySegment, ⟨sO, sI, hgi, rfl⟩, ?_⟩
    right; right; left
    exact ⟨⟨j, hj⟩, h_lt, sO', sI, hgj, rfl⟩

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 3 of Definition 5.9. -/
lemma not_collisionFwdBwd_of_not_combined (h : ¬ E trace) : ¬ collisionFwdBwd trace := by
  intro hfb
  apply h; clear h
  obtain ⟨sI, sO, sI', hm1, hm2, hne⟩ := hfb
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    have hq : true = false :=
      congrArg (fun x => match x with | ⟨.inr (.inl _), _⟩ => true | _ => false) hgj
    contradiction
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · right
    refine ⟨⟨j, hj⟩, sI', sO, Or.inr ⟨hgj, ⟨⟨i, hi⟩, h_lt, Or.inr ⟨sI, hgi, hne⟩⟩⟩⟩
  · left; right; left
    unfold capacitySegmentDupPerm
    refine ⟨⟨i, hi⟩, sO.capacitySegment, ⟨sI, sO, hgi, rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨j, hj⟩, h_lt.le, sO, sI', hgj, rfl⟩)))⟩

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 4 of Definition 5.9. -/
lemma not_collisionBwdFwd_of_not_combined (h : ¬ E trace) : ¬ collisionBwdFwd trace := by
  intro hbf
  apply h; clear h
  obtain ⟨sO, sI, sO', hm1, hm2, hne⟩ := hbf
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    have hq : true = false :=
      congrArg (fun x => match x with | ⟨.inr (.inr _), _⟩ => true | _ => false) hgj
    contradiction
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · right
    refine ⟨⟨j, hj⟩, sI, sO', Or.inl ⟨hgj, ⟨⟨i, hi⟩, h_lt, Or.inr ⟨sO, hgi, hne⟩⟩⟩⟩
  · left; right; right
    unfold capacitySegmentDupPermInv
    refine ⟨⟨i, hi⟩, sI.capacitySegment, ⟨sO, sI, hgi, rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨j, hj⟩, h_lt.le, sI, sO', hgj, rfl⟩)))⟩

/-- CO25 Lemma 5.10 — helper.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0`, then the exact paper-form
`E_prp(tr)` does not hold. -/
lemma not_collisionPerm_of_not_combined
    (h : ¬ E trace) : ¬ E_prp trace := by
  intro hprp
  rcases hprp with hff | hbb | hfb | hbf
  · exact not_collisionFwdFwd_of_not_combined (trace := trace) h hff
  · exact not_collisionBwdBwd_of_not_combined (trace := trace) h hbb
  · exact not_collisionFwdBwd_of_not_combined (trace := trace) h hfb
  · exact not_collisionBwdFwd_of_not_combined (trace := trace) h hbf

/-- CO25 Lemma 5.10.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0` then `E_prp(tr) = 0`. -/
theorem lemma_5_10 (h : ¬ E trace) : ¬ E_prp trace :=
  not_collisionPerm_of_not_combined (trace := trace) h

/-- Outside the canonical combined bad event, normalized permutation pairs in the base trace are
output-functional: one output state has at most one input state.  The two inverse-only
representatives are handled by the backward half of the canonical bidirectional `E_func`; the
other three direction combinations are the corresponding Lemma 5.10 collision cases. -/
lemma normalizedPermPair_input_unique_of_not_E
    (hNoBad : ¬ E trace)
    {sIn sIn' sOut : CanonicalSpongeState U}
    (hLeft : (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace ∨ ⟨.inr (.inr sOut), sIn⟩ ∈ getBaseTrace trace)
    (hRight : (⟨.inr (.inl sIn'), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace ∨ ⟨.inr (.inr sOut), sIn'⟩ ∈ getBaseTrace trace) :
    sIn' = sIn := by
  by_contra hne
  rcases hLeft with hFwd | hInv <;> rcases hRight with hFwd' | hInv'
  · exact (not_collisionFwdFwd_of_not_combined (trace := trace) hNoBad)
      ⟨sIn, sIn', sOut, hFwd, hFwd', Ne.symm hne⟩
  · exact (not_collisionFwdBwd_of_not_combined (trace := trace) hNoBad)
      ⟨sIn, sOut, sIn', hFwd, hInv', Ne.symm hne⟩
  · exact (not_collisionFwdBwd_of_not_combined (trace := trace) hNoBad)
      ⟨sIn', sOut, sIn, hFwd', hInv, hne⟩
  · rw [List.mem_iff_get] at hInv hInv'
    obtain ⟨⟨i, hi⟩, hgi⟩ := hInv
    obtain ⟨⟨i', hi'⟩, hgi'⟩ := hInv'
    simp only [List.get_eq_getElem] at hgi hgi'
    have hidx : i ≠ i' := by
      intro heq
      subst heq
      rw [hgi] at hgi'
      exact hne (congrArg
        (fun e => match e with | ⟨.inr (.inr _), s⟩ => s | _ => sIn') hgi').symm
    rcases Nat.lt_or_gt_of_ne hidx with hlt | hlt
    · apply hNoBad
      right
      refine ⟨⟨i', hi'⟩, sIn', sOut, Or.inr ⟨hgi', ⟨⟨i, hi⟩, hlt, ?_⟩⟩⟩
      exact Or.inl ⟨sIn, hgi, Ne.symm hne⟩
    · apply hNoBad
      right
      refine ⟨⟨i, hi⟩, sIn, sOut, Or.inr ⟨hgi, ⟨⟨i', hi'⟩, hlt, ?_⟩⟩⟩
      exact Or.inl ⟨sIn', hgi', hne⟩

/-- Transport the trace-level partial-permutation fact through D2SQuery's exact mirror.  Together
with table nodupness, this is precisely the precondition of the safe `outlu` theorem. -/
lemma table_outputFunctional_of_mirror_of_not_E
    {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) (hNoBad : ¬ E trace) :
    TraceTableOps.OutputFunctional trΔ.p := by
  intro sIn sIn' sOut hLeft hRight
  have hLeftEntries : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p := by
    apply Multiset.mem_coe.mp
    rw [LawfulTraceTable.toMultiSet_ofEntries]
    exact hLeft
  have hRightEntries : (sIn', sOut) ∈ TraceTableOps.entries trΔ.p := by
    apply Multiset.mem_coe.mp
    rw [LawfulTraceTable.toMultiSet_ofEntries]
    exact hRight
  have hLeftRaw :
      (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
        ⟨.inr (.inr sOut), sIn⟩ ∈ trace :=
    (hMirror.2 sIn sOut).mpr hLeftEntries
  have hRightRaw :
      (⟨.inr (.inl sIn'), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
        ⟨.inr (.inr sOut), sIn'⟩ ∈ trace :=
    (hMirror.2 sIn' sOut).mpr hRightEntries
  exact normalizedPermPair_input_unique_of_not_E (trace := trace) hNoBad
    (normalizedPermPair_mem_getBaseTrace_of_mem trace sIn sOut hLeftRaw)
    (normalizedPermPair_mem_getBaseTrace_of_mem trace sIn' sOut hRightRaw)

/-- Outside the canonical combined bad event, normalized permutation pairs in the base trace are
input-functional as well.  This is the forward dual of
`normalizedPermPair_input_unique_of_not_E`. -/
lemma normalizedPermPair_output_unique_of_not_E
    (hNoBad : ¬ E trace)
    {sIn sOut sOut' : CanonicalSpongeState U}
    (hLeft : (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace ∨ ⟨.inr (.inr sOut), sIn⟩ ∈ getBaseTrace trace)
    (hRight : (⟨.inr (.inl sIn), sOut'⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace ∨ ⟨.inr (.inr sOut'), sIn⟩ ∈ getBaseTrace trace) :
    sOut' = sOut := by
  by_contra hne
  rcases hLeft with hFwd | hInv <;> rcases hRight with hFwd' | hInv'
  · rw [List.mem_iff_get] at hFwd hFwd'
    obtain ⟨⟨i, hi⟩, hgi⟩ := hFwd
    obtain ⟨⟨i', hi'⟩, hgi'⟩ := hFwd'
    simp only [List.get_eq_getElem] at hgi hgi'
    have hidx : i ≠ i' := by
      intro heq
      subst heq
      rw [hgi] at hgi'
      exact hne (congrArg
        (fun e => match e with | ⟨.inr (.inl _), s⟩ => s | _ => sOut') hgi').symm
    rcases Nat.lt_or_gt_of_ne hidx with hlt | hlt
    · apply hNoBad
      right
      refine ⟨⟨i', hi'⟩, sIn, sOut', Or.inl ⟨hgi', ⟨⟨i, hi⟩, hlt, ?_⟩⟩⟩
      exact Or.inl ⟨sOut, hgi, Ne.symm hne⟩
    · apply hNoBad
      right
      refine ⟨⟨i, hi⟩, sIn, sOut, Or.inl ⟨hgi, ⟨⟨i', hi'⟩, hlt, ?_⟩⟩⟩
      exact Or.inl ⟨sOut', hgi', hne⟩
  · exact (not_collisionBwdFwd_of_not_combined (trace := trace) hNoBad)
      ⟨sOut', sIn, sOut, hInv', hFwd, hne⟩
  · exact (not_collisionBwdFwd_of_not_combined (trace := trace) hNoBad)
      ⟨sOut, sIn, sOut', hInv, hFwd', Ne.symm hne⟩
  · exact (not_collisionBwdBwd_of_not_combined (trace := trace) hNoBad)
      ⟨sOut, sOut', sIn, hInv, hInv', Ne.symm hne⟩

/-- The mirror also transports input functionality from the no-bad base trace to the D2SQuery
permutation table. -/
lemma table_inputFunctional_of_mirror_of_not_E
    {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) (hNoBad : ¬ E trace) :
    TraceTableOps.InputFunctional trΔ.p := by
  intro sIn sOut sOut' hLeft hRight
  have hLeftEntries : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p := by
    apply Multiset.mem_coe.mp
    rw [LawfulTraceTable.toMultiSet_ofEntries]
    exact hLeft
  have hRightEntries : (sIn, sOut') ∈ TraceTableOps.entries trΔ.p := by
    apply Multiset.mem_coe.mp
    rw [LawfulTraceTable.toMultiSet_ofEntries]
    exact hRight
  have hLeftRaw :
      (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
        ⟨.inr (.inr sOut), sIn⟩ ∈ trace :=
    (hMirror.2 sIn sOut).mpr hLeftEntries
  have hRightRaw :
      (⟨.inr (.inl sIn), sOut'⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
        ⟨.inr (.inr sOut'), sIn⟩ ∈ trace :=
    (hMirror.2 sIn sOut').mpr hRightEntries
  exact normalizedPermPair_output_unique_of_not_E (trace := trace) hNoBad
    (normalizedPermPair_mem_getBaseTrace_of_mem trace sIn sOut hLeftRaw)
    (normalizedPermPair_mem_getBaseTrace_of_mem trace sIn sOut' hRightRaw)

end Lemma5_10

/-! ## Toolbox for Lemmas 5.12 / 5.14 / 5.16

Following the patch `DSFS-archive/(Analysis #1) …`, §4 (Lemma B) and §5.  The proofs of the three
BackTrack-family lemmas reduce to two freshness corollaries of `¬E_dup`:

- **(B1)** distinct base entries have distinct *answer capacities* (`answerCap_inj`);
- **(B2)** a base entry's answer capacity never equals the *query capacity* of an earlier-or-equal
  base entry (`answerCap_ne_queryCap_le`).

`answerCap`/`queryCap` name the paper's `acap`/`qcap`. -/
section BadEventToolbox

/-- The *answer capacity* `acap(e)` of a base trace entry (patch §1, terminology table):
the capacity segment of the value the entry returns. -/
def answerCap (e : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Vector U SpongeSize.C :=
  match e with
  | ⟨.inl _, cap⟩ => cap
  | ⟨.inr (.inl _), sOut⟩ => sOut.capacitySegment
  | ⟨.inr (.inr _), sIn⟩ => sIn.capacitySegment

/-- The *query capacity* `qcap(e)` of a base trace entry: the capacity segment of the value the
entry was queried on.  Defined only for permutation entries (`none` for `h`). -/
def queryCap (e : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Option (Vector U SpongeSize.C) :=
  match e with
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl sIn), _⟩ => some sIn.capacitySegment
  | ⟨.inr (.inr sOut), _⟩ => some sOut.capacitySegment

/-- `¬E` splits into `¬E_dup`. -/
lemma not_E_dup_of_not_E (h : ¬ E trace) : ¬ capacitySegmentDup trace :=
  fun hd => h (Or.inl hd)

/-- `¬E` splits into `¬E_func`. -/
lemma not_E_func_of_not_E (h : ¬ E trace) : ¬ E_func trace :=
  fun hf => h (Or.inr hf)

/-- If an earlier base entry has answer capacity `c`, then index `j` sees a duplicated prior
capacity `c` (the `< j` clauses of `isDuplicatedPriorCapacity`). -/
private lemma isDup_of_earlier_answerCap
    {baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {i j : Fin baseTrace.length} (hij : i < j)
    {e₁ : Sigma (duplexSpongeChallengeOracle StmtIn U)} (h1 : baseTrace[i] = e₁)
    {c : Vector U SpongeSize.C} (hc : answerCap e₁ = c) :
    isDuplicatedPriorCapacity baseTrace j c := by
  obtain ⟨q, r⟩ := e₁
  match q with
  | .inl stmt =>
      simp only [answerCap] at hc
      exact Or.inl ⟨i, hij, stmt, by rw [h1, hc]⟩
  | .inr (.inl sIn) =>
      simp only [answerCap] at hc
      exact Or.inr <| Or.inl ⟨i, hij, sIn, r, by rw [h1], hc⟩
  | .inr (.inr sOut) =>
      simp only [answerCap] at hc
      exact Or.inr <| Or.inr <| Or.inl ⟨i, hij, sOut, r, by rw [h1], hc⟩

/-- If an earlier-or-equal base entry is a permutation entry with query capacity `c`, then index
`j` sees a duplicated prior capacity `c` (the `≤ j` clauses of `isDuplicatedPriorCapacity`). -/
private lemma isDup_of_le_queryCap
    {baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {i j : Fin baseTrace.length} (hij : i ≤ j)
    {e₁ : Sigma (duplexSpongeChallengeOracle StmtIn U)} (h1 : baseTrace[i] = e₁)
    {c : Vector U SpongeSize.C} (hc : queryCap e₁ = some c) :
    isDuplicatedPriorCapacity baseTrace j c := by
  obtain ⟨q, r⟩ := e₁
  match q with
  | .inl stmt =>
      simp only [queryCap, reduceCtorEq] at hc
  | .inr (.inl sIn) =>
      simp only [queryCap, Option.some.injEq] at hc
      exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨i, hij, sIn, r, by rw [h1], hc⟩
  | .inr (.inr sOut) =>
      simp only [queryCap, Option.some.injEq] at hc
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨i, hij, sOut, r, by rw [h1], hc⟩

/-- If the entry at index `j` has a duplicated prior capacity equal to its own answer capacity,
then `E_dup` holds. -/
private lemma capacitySegmentDup_of_isDup_at
    {j : Fin (getBaseTrace trace).length}
    {e₂ : Sigma (duplexSpongeChallengeOracle StmtIn U)} (h2 : (getBaseTrace trace)[j] = e₂)
    (hdupCap : isDuplicatedPriorCapacity (getBaseTrace trace) j (answerCap e₂)) :
    capacitySegmentDup trace := by
  obtain ⟨q, r⟩ := e₂
  match q with
  | .inl stmt =>
      refine Or.inl ⟨j, answerCap ⟨.inl stmt, r⟩, ⟨stmt, ?_⟩, hdupCap⟩
      simp only [answerCap]; exact h2
  | .inr (.inl sIn) =>
      refine Or.inr <| Or.inl ⟨j, answerCap ⟨.inr (.inl sIn), r⟩, ⟨sIn, r, h2, ?_⟩, hdupCap⟩
      simp only [answerCap]
  | .inr (.inr sOut) =>
      refine Or.inr <| Or.inr ⟨j, answerCap ⟨.inr (.inr sOut), r⟩, ⟨sOut, r, h2, ?_⟩, hdupCap⟩
      simp only [answerCap]

/-- **(B1)** If `¬E_dup`, then distinct base entries have distinct answer capacities. -/
lemma answerCap_inj (hdup : ¬ capacitySegmentDup trace)
    {e₁ e₂ : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (h1 : e₁ ∈ getBaseTrace trace) (h2 : e₂ ∈ getBaseTrace trace)
    (hne : e₁ ≠ e₂) : answerCap e₁ ≠ answerCap e₂ := by
  intro hAcap
  apply hdup
  rw [List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  have hij : i ≠ j := by
    intro h; subst h; rw [hgi] at hgj; exact hne hgj
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · -- `e₁` (index i) earlier; collide at `j` with `e₂`.
    refine capacitySegmentDup_of_isDup_at trace (j := ⟨j, hj⟩) hgj ?_
    exact isDup_of_earlier_answerCap (i := ⟨i, hi⟩) hlt hgi (by rw [hAcap])
  · -- `e₂` (index j) earlier; collide at `i` with `e₁`.
    refine capacitySegmentDup_of_isDup_at trace (j := ⟨i, hi⟩) hgi ?_
    exact isDup_of_earlier_answerCap (i := ⟨j, hj⟩) hlt hgj (by rw [hAcap])

/-- Capacity segments at definitionally-equal indices agree (used to discharge index arithmetic
without rewriting inside `getElem`). -/
lemma inputCap_congr {l : List (CanonicalSpongeState U)} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i = j) :
    l[i].capacitySegment = l[j].capacitySegment := by
  subst hij; rfl

omit [SpongeSize] in
/-- `getElem` at equal indices agree. -/
lemma getElem_idx_congr {α : Type*} {l : List α} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i = j) : l[i] = l[j] := by
  subst hij; rfl

omit [SpongeSize] in
/-- `getElem` of equal lists at the same index agree. -/
lemma getElem_listEq {α : Type*} {l l' : List α} (hll : l = l') {i : ℕ}
    (hi : i < l.length) (hi' : i < l'.length) : l[i] = l'[i] := by
  subst hll; rfl

/-- Injectivity of the forward-permutation entry shape. -/
lemma fwdEntry_inj {a a' b b' : CanonicalSpongeState U}
    (heq : (⟨.inr (.inl a), b⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
         = ⟨.inr (.inl a'), b'⟩) : a = a' ∧ b = b' := by
  rw [Sigma.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  rw [Sum.inr.injEq, Sum.inl.injEq] at h1
  subst h1
  exact ⟨rfl, eq_of_heq h2⟩

/-- Contrapositive of (B1): base entries with equal answer capacities are equal. -/
lemma eq_of_answerCap_eq (hdup : ¬ capacitySegmentDup trace)
    {e₁ e₂ : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (h1 : e₁ ∈ getBaseTrace trace) (h2 : e₂ ∈ getBaseTrace trace)
    (heq : answerCap e₁ = answerCap e₂) : e₁ = e₂ := by
  by_contra hne
  exact answerCap_inj trace hdup h1 h2 hne heq

/-- **(B2)** If `¬E_dup`, then a base entry's answer capacity never equals the query capacity of
an earlier-or-equal base entry. -/
lemma answerCap_ne_queryCap_le (hdup : ¬ capacitySegmentDup trace)
    {i j : Fin (getBaseTrace trace).length} (hij : i ≤ j)
    {c : Vector U SpongeSize.C} (hq : queryCap (getBaseTrace trace)[i] = some c) :
    answerCap (getBaseTrace trace)[j] ≠ c := by
  intro hAcap
  apply hdup
  refine capacitySegmentDup_of_isDup_at trace (j := j) rfl ?_
  rw [hAcap]
  exact isDup_of_le_queryCap (i := i) (j := j) hij rfl hq

end BadEventToolbox

/-! ## Definition 5.11 and Lemma 5.12 — inverse-step event -/
section Def511_Lemma512

/-- CO25 Definition 5.11 — event `E_inv(tr, s)`.

Paper-faithful (CO25 Eq. 35): `E_inv(tr, s) = 1` iff there exists an index list
`J^(k) = (j_h^(k), j_0^(k), …, j_{m_k}^(k)) ∈ 𝒥_BT(tr, s)` and an index `ι ∈ [0, m_k - 1]` such
that `tr_{j_ι^(k)} = ('p⁻¹', ·, ·)`, i.e., the `ι`-th step of the corresponding BackTrack
sequence is constructed using `p⁻¹` rather than `p`.

`𝒥_BT(tr, s)` is computed deterministically from `S_BT(tr, s)` via
`Backtrack.BacktrackSequence.Index` (cf. CO25 Def 5.4), so this definition takes `S_BT` as input
but quantifies directly over `Backtrack.J_BT S_BT` in the body. -/
def E_inv (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
  ∃ ι : Fin p.1.outputState.length,
  ∃ s_out s_in : CanonicalSpongeState U,
    (trace)[(p.2.2 ⟨ι.val, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val]? = some ⟨.inr (.inr s_out), s_in⟩
    -- (Eq. 36): ι = 0
    -- (Eq. 37): 0 < ι ≤ m_k - 1

/-- CO25 Lemma 5.12 — If `E(tr) = 0` then `E_inv(tr, s) = 0`.

Patch §5.2: by **minimal inversion**.  Suppose some step's representative is a `p⁻¹` entry; take the
minimal such step `ι*` (strong induction).  If `ι* = 0`, the hash anchor and the inverted step are
two distinct base entries with equal answer capacity (`acap = s_{C,in,0}`), contradicting (B1).  If
`ι* ≥ 1`, minimality makes step `ι*-1` forward, and the chain condition forces its answer capacity
to equal the inverted step's — again two distinct base entries colliding, contradicting (B1). -/
lemma lemma_5_12 (h : ¬ E trace)
    (seq_BT : Backtrack.S_BT trace state) :
    ¬ E_inv trace state seq_BT := by
  classical
  have hdup : ¬ capacitySegmentDup trace := not_E_dup_of_not_E trace h
  intro he_inv
  obtain ⟨p, hp, ι, s_out, s_in, hentry⟩ := he_inv
  obtain ⟨seq, hseq, rfl⟩ := Finset.mem_image.mp hp
  have hlen : seq.inputState.length = seq.outputState.length + 1 :=
    seq.inputState_length_eq_outputState_length_succ
  -- No step's representative is a `p⁻¹` entry (proved by strong induction = minimal inversion).
  have key : ∀ k, ∀ (hk : k < seq.outputState.length) (hki : k < seq.inputState.length),
      (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val]?
        ≠ some ⟨.inr (.inr seq.outputState[k]), seq.inputState[k]⟩ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      rcases k with _ | j
      · -- ι* = 0: collide with the hash anchor.
        intro hk hki hQ
        have hpos : 0 < seq.inputState.length := by omega
        -- The inverted step-0 entry is in the base trace.
        have hnotmem := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨0, hk⟩ hki
        have hmemB : (⟨.inr (.inr seq.outputState[0]), seq.inputState[0]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          permInv_mem_getBaseTrace trace hQ hnotmem.2 hnotmem.1
        -- The hash anchor is in the base trace.
        have hgetH : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).1).val]?
            = some ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
          rw [List.getElem?_eq_getElem (Backtrack.BacktrackSequence.Index trace state seq).1.isLt,
            ← List.get_eq_getElem]
          exact congrArg some (Backtrack.BacktrackSequence.Index_fst_get seq hpos)
        have hmemH : (⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          hash_mem_getBaseTrace trace hgetH
            (Backtrack.BacktrackSequence.Index_fst_not_mem_take seq hpos)
        -- Equal answer capacities, distinct entries: contradicts (B1).
        refine answerCap_inj trace hdup hmemH hmemB (by simp) ?_
        simp only [answerCap, CanonicalSpongeState.capacitySegment]
      · -- ι* = j+1: minimality makes step j forward; collide via the chain condition.
        intro hk hki hQ
        have hkj : j < seq.outputState.length := by omega
        have hkij : j < seq.inputState.length := by omega
        -- Step j is not inverted (induction hypothesis), hence forward.
        have hjnot := ih j (Nat.lt_succ_self j) hkj hkij
        have hjspec := Backtrack.BacktrackSequence.Index_snd_getElem? seq ⟨j, hkj⟩ hkij
        have hjfwd : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2
            ⟨j, hkij⟩).val]? = some ⟨.inr (.inl seq.inputState[j]), seq.outputState[j]⟩ := by
          rcases hjspec with hA | hB
          · exact hA
          · exact absurd hB hjnot
        -- The forward step-j entry and the inverted step-(j+1) entry are in the base trace.
        have hnotmemJ := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨j, hkj⟩ hkij
        have hmemA : (⟨.inr (.inl seq.inputState[j]), seq.outputState[j]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          permFwd_mem_getBaseTrace trace hjfwd hnotmemJ.1 hnotmemJ.2
        have hnotmemB := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨j + 1, hk⟩ hki
        have hmemB : (⟨.inr (.inr seq.outputState[j + 1]), seq.inputState[j + 1]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          permInv_mem_getBaseTrace trace hQ hnotmemB.2 hnotmemB.1
        -- Chain condition `(d)`: `s_{C,out,j} = s_{C,in,j+1}`, so equal answer capacities.
        refine answerCap_inj trace hdup hmemA hmemB (by simp) ?_
        simp only [answerCap]
        exact seq.capacitySegment_output_eq_input ⟨j, hkj⟩
  -- Apply `key` to the witnessing inverted step `ι`.
  have hιlt : ι.val < seq.outputState.length := ι.isLt
  have hki : ι.val < seq.inputState.length := by omega
  have hentry' : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨ι.val, hki⟩).val]?
      = some ⟨.inr (.inr s_out), s_in⟩ := hentry
  have hspec := Backtrack.BacktrackSequence.Index_snd_getElem? seq ι hki
  rw [hentry'] at hspec
  rcases hspec with hA | hB
  · simp at hA
  · rw [Option.some_inj] at hB
    exact key ι.val hιlt hki (hB ▸ hentry')

/-- Corollary of Lemma 5.12: under `¬E`, every backtrack step's representative is the *forward*
(`p`) query form. -/
lemma step_forward (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {seq : Backtrack.BacktrackSequence trace state} (hseq : seq ∈ S_BT.seqFamily)
    (k : ℕ) (hk : k < seq.outputState.length) (hki : k < seq.inputState.length) :
    (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val]?
      = some ⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ := by
  classical
  rcases Backtrack.BacktrackSequence.Index_snd_getElem? seq ⟨k, hk⟩ hki with hA | hB
  · exact hA
  · exfalso
    apply lemma_5_12 (trace := trace) (state := state) h S_BT
    exact ⟨⟨seq, Backtrack.BacktrackSequence.Index trace state seq⟩,
      Finset.mem_image_of_mem _ hseq, ⟨k, hk⟩, seq.outputState[k], seq.inputState[k], hB⟩

/-- Base-trace index of a forward step's representative (`|getBaseTrace (trace.take j_k)|`). -/
lemma fwdStep_base (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {seq : Backtrack.BacktrackSequence trace state} (hseq : seq ∈ S_BT.seqFamily)
    (k : ℕ) (hk : k < seq.outputState.length) (hki : k < seq.inputState.length) :
    ∃ idx : Fin (getBaseTrace trace).length,
      idx.val = (getBaseTrace (trace.take
        ((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val)).length ∧
      (getBaseTrace trace)[idx] = ⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ := by
  have hget := step_forward (trace := trace) (state := state) h S_BT hseq k hk hki
  have hnotmem := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨k, hk⟩ hki
  have hnr : ¬ isRedundantEntryOfPrefix
      (trace.take ((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val)
      ⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ := by
    intro hred; simp only [isRedundantEntryOfPrefix] at hred
    rcases hred with hh | hh
    · exact hnotmem.1 hh
    · exact hnotmem.2 hh
  obtain ⟨hb, heq⟩ := baseIdx_of_getElem?_not_redundant trace hget hnr
  exact ⟨⟨_, hb⟩, rfl, heq⟩

/-- A forward step's representative entry is a member of the base trace. -/
lemma fwdStep_mem (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {seq : Backtrack.BacktrackSequence trace state} (hseq : seq ∈ S_BT.seqFamily)
    (k : ℕ) (hk : k < seq.outputState.length) (hki : k < seq.inputState.length) :
    (⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace := by
  obtain ⟨idx, _, heq⟩ := fwdStep_base (trace := trace) (state := state) h S_BT hseq k hk hki
  exact heq ▸ List.getElem_mem idx.isLt

/-- Base-trace index of the hash anchor (`|getBaseTrace (trace.take j_h)|`). -/
lemma hashAnchor_base (seq : Backtrack.BacktrackSequence trace state)
    (hpos : 0 < seq.inputState.length) :
    ∃ idx : Fin (getBaseTrace trace).length,
      idx.val = (getBaseTrace (trace.take
        ((Backtrack.BacktrackSequence.Index trace state seq).1).val)).length ∧
      (getBaseTrace trace)[idx]
        = ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
  have hget : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).1).val]?
      = some ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
    rw [List.getElem?_eq_getElem (Backtrack.BacktrackSequence.Index trace state seq).1.isLt,
      ← List.get_eq_getElem]
    exact congrArg some (Backtrack.BacktrackSequence.Index_fst_get seq hpos)
  have hnr : ¬ isRedundantEntryOfPrefix
      (trace.take ((Backtrack.BacktrackSequence.Index trace state seq).1).val)
      ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
    intro hred; simp only [isRedundantEntryOfPrefix] at hred
    exact (Backtrack.BacktrackSequence.Index_fst_not_mem_take seq hpos) hred
  obtain ⟨hb, heq⟩ := baseIdx_of_getElem?_not_redundant trace hget hnr
  exact ⟨⟨_, hb⟩, rfl, heq⟩

/-- The hash anchor entry is a member of the base trace. -/
lemma hashAnchor_mem (seq : Backtrack.BacktrackSequence trace state)
    (hpos : 0 < seq.inputState.length) :
    (⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace := by
  obtain ⟨idx, _, heq⟩ := hashAnchor_base (trace := trace) (state := state) seq hpos
  exact heq ▸ List.getElem_mem idx.isLt

end Def511_Lemma512

/-! ## Lemma 5.14 -/
section Def513_Lemma514

/-- CO25 Definition 5.13 / Eq. 38 — `E_{fork,h}(tr, s)`: collision of two outputs of `h`.
Two backtrack sequences in `𝒮_BT(tr, s)` have distinct input statements `𝕩^{(1)} ≠ 𝕩^{(2)}` but
their first input states share the same capacity segment `s_{C,in,0}^{(1)} = s_{C,in,0}^{(2)}`. -/
def E_fork_h (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ S₁ ∈ S_BT.seqFamily, ∃ S₂ ∈ S_BT.seqFamily,
    S₁.stmt ≠ S₂.stmt ∧
    (S₁.inputState[0]'(by
      have := S₁.inputState_length_eq_outputState_length_succ; omega)).capacitySegment =
    (S₂.inputState[0]'(by
      have := S₂.inputState_length_eq_outputState_length_succ; omega)).capacitySegment

/-- CO25 Definition 5.13 / Eq. 39 — `E_{fork,p}(tr, s)`: capacity-segment collision of two
outputs of `p`.  There exist `S^{(1)}, S^{(2)} ∈ 𝒮_BT(tr, s)` and indices
`ι_1 ∈ [0, m_1 - 1]`, `ι_2 ∈ [0, m_2 - 1]` with `s_{in,ι_1}^{(1)} ≠ s_{in,ι_2}^{(2)}` (full input
states differ) and `s_{C,out,ι_1}^{(1)} = s_{C,out,ι_2}^{(2)}` (output capacity segments
coincide). -/
def E_fork_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ S₁ ∈ S_BT.seqFamily, ∃ S₂ ∈ S_BT.seqFamily,
  ∃ ι₁ : Fin S₁.outputState.length, ∃ ι₂ : Fin S₂.outputState.length,
    S₁.inputState[ι₁.val]'(by have := S₁.inputState_length_eq_outputState_length_succ; omega) ≠
    S₂.inputState[ι₂.val]'(by have := S₂.inputState_length_eq_outputState_length_succ; omega) ∧
    S₁.outputState[ι₁].capacitySegment = S₂.outputState[ι₂].capacitySegment

/-- CO25 Definition 5.13 / Eq. 40 — `E_{fork,h,p}(tr, s)`: collision of `h` with the output
capacity segment of a query to `p`.  There exist `S^{(1)}, S^{(2)} ∈ 𝒮_BT(tr, s)` and
`ι ∈ [m_2 - 1]` (paper notation: `{1, …, m₂ - 1}`) with
`s_{C,in,0}^{(1)} = s_{C,out,ι}^{(2)}`.

Note: `ι ≥ 1` is required by the paper — the `ι = 0` case cannot arise in the
exhaustiveness proof (Claim 5.19) because it would be handled by `E_fork_h` instead. -/
def E_fork_h_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ S₁ ∈ S_BT.seqFamily, ∃ S₂ ∈ S_BT.seqFamily,
  ∃ ι : Fin S₂.outputState.length,
    0 < ι.val ∧ (S₁.inputState[0]'(by
      have := S₁.inputState_length_eq_outputState_length_succ; omega)).capacitySegment =
    S₂.outputState[ι].capacitySegment

def E_fork (S_BT : Backtrack.S_BT trace state) : Prop :=
  S_BT.seqFamily.card > 1

/-- Backward determinism (Lemma 5.14, Step 1): two backtrack sequences ending at the same state
agree on their input states counting from the end, as long as `E_dup = 0`.  All steps are forward
(Lemma 5.12), so equal next-input forces equal output capacities (chain), hence equal base
representatives (B1), hence equal full predecessor states. -/
private lemma bt_seq_eq_of_le (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {A B : Backtrack.BacktrackSequence trace state}
    (hA : A ∈ S_BT.seqFamily) (hB : B ∈ S_BT.seqFamily)
    (hmle : A.outputState.length ≤ B.outputState.length) : A = B := by
  classical
  have hdup : ¬ capacitySegmentDup trace := not_E_dup_of_not_E trace h
  have hAlen : A.inputState.length = A.outputState.length + 1 :=
    A.inputState_length_eq_outputState_length_succ
  have hBlen : B.inputState.length = B.outputState.length + 1 :=
    B.inputState_length_eq_outputState_length_succ
  -- Step 1: backward determinism on input states.
  have bdet : ∀ d, d ≤ A.outputState.length →
      A.inputState.get ⟨A.outputState.length - d, by omega⟩
        = B.inputState.get ⟨B.outputState.length - d, by omega⟩ := by
    intro d
    induction d with
    | zero =>
      intro _
      have hA0 : A.inputState.get ⟨A.outputState.length - 0, by omega⟩ = state := by
        have e1 : (⟨A.outputState.length - 0, by omega⟩ : Fin A.inputState.length)
                = ⟨A.inputState.length - 1, by omega⟩ := by rw [Fin.mk.injEq]; omega
        rw [e1, List.get_eq_getElem]
        exact A.last_inputState_eq_state
      have hB0 : B.inputState.get ⟨B.outputState.length - 0, by omega⟩ = state := by
        have e1 : (⟨B.outputState.length - 0, by omega⟩ : Fin B.inputState.length)
                = ⟨B.inputState.length - 1, by omega⟩ := by rw [Fin.mk.injEq]; omega
        rw [e1, List.get_eq_getElem]
        exact B.last_inputState_eq_state
      rw [hA0, hB0]
    | succ d ih =>
      intro hd
      have hIH := ih (by omega)
      rw [List.get_eq_getElem, List.get_eq_getElem] at hIH
      have hkA : A.outputState.length - (d + 1) < A.outputState.length := by omega
      have hkAi : A.outputState.length - (d + 1) < A.inputState.length := by omega
      have hkB : B.outputState.length - (d + 1) < B.outputState.length := by omega
      have hkBi : B.outputState.length - (d + 1) < B.inputState.length := by omega
      have hmemA := fwdStep_mem (trace := trace) (state := state) h S_BT hA
        (A.outputState.length - (d + 1)) hkA hkAi
      have hmemB := fwdStep_mem (trace := trace) (state := state) h S_BT hB
        (B.outputState.length - (d + 1)) hkB hkBi
      have chA : A.outputState[A.outputState.length - (d + 1)].capacitySegment
          = A.inputState[A.outputState.length - (d + 1) + 1].capacitySegment :=
        A.capacitySegment_output_eq_input ⟨A.outputState.length - (d + 1), hkA⟩
      have chB : B.outputState[B.outputState.length - (d + 1)].capacitySegment
          = B.inputState[B.outputState.length - (d + 1) + 1].capacitySegment :=
        B.capacitySegment_output_eq_input ⟨B.outputState.length - (d + 1), hkB⟩
      have hidxA : A.inputState[A.outputState.length - (d + 1) + 1].capacitySegment
          = A.inputState[A.outputState.length - d].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hidxB : B.inputState[B.outputState.length - (d + 1) + 1].capacitySegment
          = B.inputState[B.outputState.length - d].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hcapeq : answerCap (⟨.inr (.inl A.inputState[A.outputState.length - (d + 1)]),
            A.outputState[A.outputState.length - (d + 1)]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U))
          = answerCap (⟨.inr (.inl B.inputState[B.outputState.length - (d + 1)]),
            B.outputState[B.outputState.length - (d + 1)]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        change A.outputState[A.outputState.length - (d + 1)].capacitySegment
          = B.outputState[B.outputState.length - (d + 1)].capacitySegment
        rw [chA, chB, hidxA, hidxB]
        exact congrArg _ hIH
      have he := eq_of_answerCap_eq trace hdup hmemA hmemB hcapeq
      rw [List.get_eq_getElem, List.get_eq_getElem]
      exact (fwdEntry_inj he).1
  -- Step 2: equal lengths.
  have hmeq : A.outputState.length = B.outputState.length := by
    rcases eq_or_lt_of_le hmle with heq | hlt
    · exact heq
    · exfalso
      have hb := bdet A.outputState.length (le_refl _)
      rw [List.get_eq_getElem, List.get_eq_getElem] at hb
      have hposA : 0 < A.inputState.length := by omega
      have hmemH := hashAnchor_mem (trace := trace) (state := state) A hposA
      have hkB' : B.outputState.length - A.outputState.length - 1 < B.outputState.length := by omega
      have hkB'i : B.outputState.length - A.outputState.length - 1 < B.inputState.length := by omega
      have hmemS := fwdStep_mem (trace := trace) (state := state) h S_BT hB
        (B.outputState.length - A.outputState.length - 1) hkB' hkB'i
      have chB : B.outputState[B.outputState.length - A.outputState.length - 1].capacitySegment
          = B.inputState[B.outputState.length - A.outputState.length - 1 + 1].capacitySegment :=
        B.capacitySegment_output_eq_input ⟨_, hkB'⟩
      have hidxB : B.inputState[B.outputState.length - A.outputState.length - 1 + 1].capacitySegment
          = B.inputState[B.outputState.length - A.outputState.length].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hidxA : A.inputState[0].capacitySegment
          = A.inputState[A.outputState.length - A.outputState.length].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hcapeq : answerCap (⟨.inl A.stmt, Vector.drop (A.inputState[0]'hposA) SpongeSize.R⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U))
          = answerCap (⟨.inr (.inl B.inputState[B.outputState.length - A.outputState.length - 1]),
            B.outputState[B.outputState.length - A.outputState.length - 1]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        change Vector.drop (A.inputState[0]'hposA) SpongeSize.R
          = B.outputState[B.outputState.length - A.outputState.length - 1].capacitySegment
        calc Vector.drop (A.inputState[0]'hposA) SpongeSize.R
            = A.inputState[0].capacitySegment := rfl
          _ = A.inputState[A.outputState.length - A.outputState.length].capacitySegment := hidxA
          _ = B.inputState[B.outputState.length - A.outputState.length].capacitySegment :=
              congrArg _ hb
          _ = B.inputState[B.outputState.length - A.outputState.length - 1 + 1].capacitySegment :=
              hidxB.symm
          _ = B.outputState[B.outputState.length - A.outputState.length - 1].capacitySegment :=
              chB.symm
      have he := eq_of_answerCap_eq trace hdup hmemH hmemS hcapeq
      simp at he
  -- Step 3: input states coincide.
  have hin : A.inputState = B.inputState := by
    apply List.ext_getElem
    · rw [hAlen, hBlen, hmeq]
    · intro i h1 h2
      have hbd := bdet (A.outputState.length - i) (by omega)
      rw [List.get_eq_getElem, List.get_eq_getElem] at hbd
      calc A.inputState[i]
          = A.inputState[A.outputState.length - (A.outputState.length - i)] :=
            getElem_idx_congr h1 (by omega) (by omega)
        _ = B.inputState[B.outputState.length - (A.outputState.length - i)] := hbd
        _ = B.inputState[i] := getElem_idx_congr (by omega) h2 (by omega)
  -- Step 4: statements coincide.
  have hstmt : A.stmt = B.stmt := by
    by_contra hne
    have hposA : 0 < A.inputState.length := by omega
    have hposB : 0 < B.inputState.length := by omega
    have hmemA := hashAnchor_mem (trace := trace) (state := state) A hposA
    have hmemB := hashAnchor_mem (trace := trace) (state := state) B hposB
    have hin0 : A.inputState[0]'hposA = B.inputState[0]'hposB :=
      getElem_listEq hin hposA hposB
    have hcapeq : answerCap (⟨.inl A.stmt, Vector.drop (A.inputState[0]'hposA) SpongeSize.R⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U))
        = answerCap ⟨.inl B.stmt, Vector.drop (B.inputState[0]'hposB) SpongeSize.R⟩ := by
      change Vector.drop (A.inputState[0]'hposA) SpongeSize.R
        = Vector.drop (B.inputState[0]'hposB) SpongeSize.R
      exact congrArg (fun x => Vector.drop x SpongeSize.R) hin0
    have he := eq_of_answerCap_eq trace hdup hmemA hmemB hcapeq
    simp only [Sigma.mk.injEq, Sum.inl.injEq] at he
    exact hne he.1
  -- Step 5: output states coincide.
  have hout : A.outputState = B.outputState := by
    apply List.ext_getElem
    · rw [hmeq]
    · intro i h1 h2
      have hiAi : i < A.inputState.length := by omega
      have hiB : i < B.outputState.length := by omega
      have hiBi : i < B.inputState.length := by omega
      have hmemA := fwdStep_mem (trace := trace) (state := state) h S_BT hA i h1 hiAi
      have hmemB := fwdStep_mem (trace := trace) (state := state) h S_BT hB i hiB hiBi
      have chA : A.outputState[i].capacitySegment = A.inputState[i + 1].capacitySegment :=
        A.capacitySegment_output_eq_input ⟨i, h1⟩
      have chB : B.outputState[i].capacitySegment = B.inputState[i + 1].capacitySegment :=
        B.capacitySegment_output_eq_input ⟨i, hiB⟩
      have hcapeq : answerCap (⟨.inr (.inl A.inputState[i]), A.outputState[i]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U))
          = answerCap (⟨.inr (.inl B.inputState[i]), B.outputState[i]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        change A.outputState[i].capacitySegment = B.outputState[i].capacitySegment
        rw [chA, chB]
        exact congrArg (fun x => x.capacitySegment)
          (getElem_listEq hin (i := i + 1) (by omega) (by omega))
      have he := eq_of_answerCap_eq trace hdup hmemA hmemB hcapeq
      exact (fwdEntry_inj he).2
  exact Backtrack.BacktrackSequence.ext hstmt hin hout

/-- CO25 Lemma 5.14 — If `E(tr) = 0` then `E_fork(tr, s) = 0`. -/
lemma lemma_5_14 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_fork trace state S_BT := by
  rw [E_fork, not_lt, Finset.card_le_one]
  intro A hA B hB
  rcases le_total A.outputState.length B.outputState.length with hle | hle
  · exact bt_seq_eq_of_le (trace := trace) (state := state) h S_BT hA hB hle
  · exact (bt_seq_eq_of_le (trace := trace) (state := state) h S_BT hB hA hle).symm

end Def513_Lemma514

/-! ## Lemma 5.16 -/
section Def515_Lemma516

/-- CO25 Definition 5.15 / Eq. 41 — `E_{time,h}(tr, s)`: the query to `h` is out of order.
There exists `J^{(k)} = (j_h^{(k)}, j_0^{(k)}, …, j_{m_k}^{(k)}) ∈ 𝒥_BT(tr, s)` with
`j_h^{(k)} > j_0^{(k)}`. -/
def E_time_h (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
    p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ; omega⟩).val

/-- CO25 Definition 5.15 / Eq. 42 — `E_{time,p}(tr, s)`: a query to `p` is out of order.
There exists `J^{(k)} ∈ 𝒥_BT(tr, s)` and `ι ∈ [m_k - 1]` (paper notation: `{1, …, m_k - 1}`)
with `j_{ι-1}^{(k)} > j_ι^{(k)}`, i.e. some consecutive pair of permutation-step `j`-indices is
out of order.  In 0-based indexing this checks `j_ι > j_{ι+1}` for `ι ∈ {0, …, m_k - 2}`. -/
def E_time_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
  ∃ ι : Fin p.1.outputState.length,
    ι.val + 1 < p.1.outputState.length ∧
    (p.2.2 ⟨ι.val, by
      have := p.1.inputState_length_eq_outputState_length_succ
      have := ι.isLt; omega⟩).val >
    (p.2.2 ⟨ι.val + 1, by
      have := p.1.inputState_length_eq_outputState_length_succ
      have := ι.isLt; omega⟩).val

/-- CO25 Definition 5.15 — `E_time(tr, s)` -/
def E_time (S_BT : Backtrack.S_BT trace state) : Prop :=
  E_time_h trace state S_BT ∨ E_time_p trace state S_BT

/-- CO25 Lemma 5.16 — If `E(tr) = 0` then `E_time(tr, s) = 0`.

Patch §5.4: by Lemma 5.12 every step is forward (`p`), so each index points at a base `p` entry and
the hash index at a base `h` entry, in trace order = base order.  An out-of-order pair would make a
*later* base entry's answer capacity equal an *earlier* base entry's query capacity (via the chain
condition / hash anchor), contradicting (B2). -/
lemma lemma_5_16 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_time trace state S_BT := by
  classical
  have hdup : ¬ capacitySegmentDup trace := not_E_dup_of_not_E trace h
  rintro (htime | htime)
  · -- `E_time_h`: the hash query `j_h` is later than the step-0 query `j_0`.
    obtain ⟨p, hp, hgt⟩ := htime
    obtain ⟨seq, hseq, rfl⟩ := Finset.mem_image.mp hp
    have hpos : 0 < seq.inputState.length := by
      have := seq.inputState_length_eq_outputState_length_succ; omega
    by_cases h0 : 0 < seq.outputState.length
    · -- Step 0 exists; collide its query capacity with the hash anchor's answer capacity.
      obtain ⟨i0, hi0val, hi0eq⟩ :=
        fwdStep_base (trace := trace) (state := state) h S_BT hseq 0 h0 hpos
      obtain ⟨iH, hiHval, hiHeq⟩ := hashAnchor_base (trace := trace) (state := state) seq hpos
      have hij : i0 ≤ iH := by
        have h1 : i0.val ≤ iH.val := by
          rw [hi0val, hiHval]; exact getBaseTrace_take_length_mono trace (le_of_lt hgt)
        exact h1
      refine answerCap_ne_queryCap_le trace hdup hij
        (c := seq.inputState[0].capacitySegment) ?_ ?_
      · rw [hi0eq]; rfl
      · rw [hiHeq]; simp only [answerCap, CanonicalSpongeState.capacitySegment]
    · -- No steps: `j_0 = |trace|`, but `j_h < |trace|`, so `j_h > j_0` is impossible.
      exfalso
      rw [Backtrack.BacktrackSequence.Index_snd_eq_length seq (by omega) hpos] at hgt
      exact absurd hgt (by
        have := (Backtrack.BacktrackSequence.Index trace state seq).1.isLt
        omega)
  · -- `E_time_p`: step `ι` query is later than step `ι+1` query.
    obtain ⟨p, hp, ι, hι1, hgt⟩ := htime
    obtain ⟨seq, hseq, rfl⟩ := Finset.mem_image.mp hp
    have hlen : seq.inputState.length = seq.outputState.length + 1 :=
      seq.inputState_length_eq_outputState_length_succ
    have hιlt : ι.val < seq.outputState.length := ι.isLt
    have hι1' : ι.val + 1 < seq.outputState.length := hι1
    have hkiι : ι.val < seq.inputState.length := by omega
    have hkiι1 : ι.val + 1 < seq.inputState.length := by omega
    obtain ⟨iIdx, hival, hieq⟩ :=
      fwdStep_base (trace := trace) (state := state) h S_BT hseq (ι.val + 1) hι1' hkiι1
    obtain ⟨jIdx, hjval, hjeq⟩ :=
      fwdStep_base (trace := trace) (state := state) h S_BT hseq ι.val hιlt hkiι
    have hij : iIdx ≤ jIdx := by
      have h1 : iIdx.val ≤ jIdx.val := by
        rw [hival, hjval]; exact getBaseTrace_take_length_mono trace (le_of_lt hgt)
      exact h1
    refine answerCap_ne_queryCap_le trace hdup hij
      (c := seq.inputState[ι.val + 1].capacitySegment) ?_ ?_
    · rw [hieq]; rfl
    · rw [hjeq]; simp only [answerCap]
      exact seq.capacitySegment_output_eq_input ⟨ι.val, hιlt⟩

end Def515_Lemma516

end BadEventDS

end DuplexSpongeFS

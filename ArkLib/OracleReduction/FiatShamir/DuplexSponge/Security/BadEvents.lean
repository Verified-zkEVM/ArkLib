/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform

/-!
# Definition and analysis of bad events

This file contains the definition and analysis of bad events for the analysis of duplex sponge
Fiat-Shamir, following Section 5.6 in the paper.

## Predicate organization

The bad-event surface mirrors the paper definitions directly:

- **Trace-only events (Def 5.7):** `E_h` / `E_p` / `E_pinv` / `E_dup` / `E_func` / `E`.
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

/-! ## Definition 5.5 and Definition 5.6 - Redundant entries in a trace -/
section Def_5_5_6_RedundantEntryDSHelpers

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- **Definition 5.5**: Redundancy test for a new entry against a prefix of the trace -/
def isRedundantEntryOfPrefix
    (pref : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ =>
      ⟨.inl stmt, capSeg⟩ ∈ pref
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
      ⟨.inr (.inl stateIn), stateOut⟩ ∈ pref
      ∨ ⟨.inr (.inr stateOut), stateIn⟩ ∈ pref
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
      ⟨.inr (.inr stateOut), stateIn⟩ ∈ pref
      ∨ ⟨.inr (.inl stateIn), stateOut⟩ ∈ pref

/-- CO25 Definition 5.6 — Base trace `tr̄` side condition.
`hasNoRedundantEntries log` holds iff no entry of `log` is redundant in the sense of
Definition 5.5.  The base trace `tr̄` is the unique sub-log satisfying this predicate
(see `getBaseTrace`). -/
def hasNoRedundantEntries (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ i : ℕ, ∀ hi : i < log.length,
    ¬ isRedundantEntryOfPrefix (log.take i) log[i]

private lemma noRedundantEntryDS_nil : hasNoRedundantEntries (StmtIn := StmtIn) (U := U) [] := by
  intro i hi _
  exact (Nat.not_lt_zero i) hi

private lemma noRedundantEntryDS_append_singleton
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : hasNoRedundantEntries acc)
    (hEntry : ¬ isRedundantEntryOfPrefix acc entry) :
    hasNoRedundantEntries (acc ++ [entry]) := by
  intro i hi
  have hi' : i < acc.length + 1 := by
    rw [List.length_append, List.length_singleton] at hi
    exact hi
  by_cases hlt : i < acc.length
  · have hOld :
      ¬ isRedundantEntryOfPrefix (acc.take i) acc[i] := hAcc i hlt
    simp only [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
    exact hOld
  · have hEq : i = acc.length := Nat.eq_of_lt_succ_of_not_lt hi' hlt
    subst hEq
    revert hEntry
    simp [isRedundantEntryOfPrefix]

noncomputable def getBaseTraceAux
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) := by
  classical
  exact match remaining with
  | [] => acc
  | entry :: rest =>
      if hRed : isRedundantEntryOfPrefix acc entry then
        getBaseTraceAux rest acc
      else
        getBaseTraceAux rest (acc ++ [entry])

private lemma getBaseTraceAux_noRedundant
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : hasNoRedundantEntries acc) :
    hasNoRedundantEntries (getBaseTraceAux remaining acc) := by
  classical
  induction remaining generalizing acc with
  | nil => exact hAcc
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc hAcc
      · let hAcc' := noRedundantEntryDS_append_singleton acc entry hAcc hRed
        simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih (acc ++ [entry]) hAcc'

/-- CO25 Definition 5.6 — Compute the base trace `tr̄` of a duplex-sponge query-answer trace by
removing all redundant entries (in the sense of Definition 5.5). -/
noncomputable def getBaseTrace
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  getBaseTraceAux log []

lemma getBaseTrace_noRedundant
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    hasNoRedundantEntries (getBaseTrace log) :=
  getBaseTraceAux_noRedundant log [] (noRedundantEntryDS_nil (StmtIn := StmtIn) (U := U))

end Def_5_5_6_RedundantEntryDSHelpers

/-! ## Bad-event-related predicates and lemmas (Definition 5.7 -> Lemma 5.16) -/
namespace BadEventDS
open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)

/-! ## Definition 5.7 — trace-only bad events (`E_h`, `E_p`, `E_{p⁻¹}`, `E_dup`, `E_func`, `E`) -/

section Def57_TraceOnlyBadEvents

/-! The main bad event `E` (Def 5.7) is the disjunction of two conditions: a capacity-segment
duplication on the base trace (`E_dup`), or `p` behaving non-functionally (`E_func`). -/

/- NOTE: the paper write `∃ j > 0`, which can be confusing since we don't know whether the intended
indexing is from 0 or from 1. We assume they mean from 1, and since indexing here is from 0, we just
write `∃ j`. -/

/-- A unified check for whether a capacity segment `capSeg` has appeared previously as an
output capacity (strictly before `j`) or as an input capacity (up to and including `j`).
This exactly captures the redundancy conditions in `E_h`, `E_p`, and `E_{p⁻¹}`. -/
def isDuplicatedPriorCapacity (baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j : Fin baseTrace.length) (capSeg : Vector U SpongeSize.C) : Prop :=
  (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
  (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
    stateOut1.capacitySegment = capSeg) ∨
  (∃ j' < j, ∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
    stateIn2.capacitySegment = capSeg) ∨
  (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
    stateIn3.capacitySegment = capSeg) ∨
  (∃ j' ≤ j, ∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
    stateOut4.capacitySegment = capSeg)

/-- CO25 Definition 5.7 — Event `E_h(tr)` (Eq. 23).
An output capacity segment `s_C` of an `h`-entry in the base trace `tr̄` previously appears
as an output or input capacity segment of `h`, `p`, or `p⁻¹`:

```
E_h(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (h, ·, s_C)  and  ∃ j' < j :
  tr̄_{j'} = (h, ·, s_C)  ∨  tr̄_{j'} = (p, ·, (·, s_C))  ∨  tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  tr̄_{j'} = (p, (·, s_C), ·)  ∨  tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

All five prior-entry branches are unified via `isDuplicatedPriorCapacity`. -/
def capacitySegmentDupHash : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_h := capacitySegmentDupHash

/-- CO25 Definition 5.7 — Event `E_p(tr)` (Eq. 24).
An output capacity segment `s_C` of a `p`-entry in the base trace `tr̄` previously (or
simultaneously for some branches) appears as an output or input capacity segment of `h`, `p`,
or `p⁻¹`:

```
E_p(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (p, ·, (·, s_C))  and
  ∃ j' < j : tr̄_{j'} = (h, ·, s_C)  ∨  ∃ j' < j : tr̄_{j'} = (p, ·, (·, s_C))
  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  ∃ j' ≤ j : tr̄_{j'} = (p, (·, s_C), ·)  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

Branches realized by `isDuplicatedPriorCapacity`'s uniform `≤ j`; extensionally equal to the
paper's asymmetric `< j`/`≤ j` (the extra `j' = j` cases are vacuous). -/
def capacitySegmentDupPerm : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_p := capacitySegmentDupPerm

/-- CO25 Definition 5.7 — Event `E_{p⁻¹}(tr)` (Eq. 25).
An output capacity segment `s_C` (i.e. the output of `p⁻¹`, which is the input side `s_in`) of a
`p⁻¹`-entry in the base trace `tr̄` previously (or simultaneously for some branches) appears as
an output or input capacity segment of `h`, `p`, or `p⁻¹`:

```
E_{p⁻¹}(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (p⁻¹, ·, (·, s_C))  and
  ∃ j' < j : tr̄_{j'} = (h, ·, s_C)  ∨  ∃ j' < j : tr̄_{j'} = (p, ·, (·, s_C))
  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  ∃ j' ≤ j : tr̄_{j'} = (p, (·, s_C), ·)  ∨  ∃ j' ≤ j : tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

Same uniform-`≤ j` caveat as `E_p` (via `isDuplicatedPriorCapacity`); extensionally equal to
Eq. 25's asymmetric quantifiers. -/
def capacitySegmentDupPermInv : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_pinv := capacitySegmentDupPermInv

/-- CO25 Definition 5.7 — Combined capacity-segment duplication event `E_dup(tr)`.
Holds iff at least one of `E_h(tr)`, `E_p(tr)`, or `E_{p⁻¹}(tr)` holds: there exists an output
capacity segment in the base trace `tr̄` that previously appeared as an output or input capacity
segment. -/
def capacitySegmentDup : Prop :=
  capacitySegmentDupHash trace ∨ capacitySegmentDupPerm trace ∨ capacitySegmentDupPermInv trace

alias E_dup := capacitySegmentDup

/-- CO25 Definition 5.7 — Event `E_func(tr)` (Eq. 26).
**The same query to `p` leads to different answers**, or there are inconsistent queries across `p`
and `p⁻¹`:

```
E_func(tr) := ∃ j > 0, s_in ∈ Σ^{r+c} :  tr̄_j = (p, s_in, ·)  and  ∃ j' < j :
  tr̄_{j'} = (p, s_in, ·)  ∨  tr̄_{j'} = (p⁻¹, ·, s_in)
```

Note: `E_func(tr)` never holds for a true permutation `p` and its inverse `p⁻¹`, but may hold
(with small probability) for the D2SQuery simulator.

**Strengthening:** bidirectional. Case 1 (`j`-th entry `p`-forward) is Eq. 26; Case 2 (`j`-th entry
`p⁻¹`) has no paper counterpart but is *required* by `not_collisionFwdBwd_of_not_combined`
(Lemma 5.10, Item 3). The `≠`-output conditions are forced by base-trace non-redundancy.
See `DSFS-archive/BadEvents_deep_analysis.md` §7. -/
def E_func : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    (baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      ∃ j' < j,
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)) ∨
    (baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      ∃ j' < j,
        (∃ stateIn1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut, stateIn1⟩ ∧ stateIn1 ≠ stateIn) ∨
        (∃ stateIn2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn2, stateOut⟩ ∧ stateIn2 ≠ stateIn))

/-- CO25 Definition 5.7 — Combined bad event `E(tr)`.
`E(tr)` is the disjunction `E_dup(tr) ∨ E_func(tr)`, i.e., either a capacity-segment
duplication occurs or `p` behaves non-functionally.  Lemma 5.8 bounds `Pr[E(tr_P̃ ‖ tr_V)]`
in both the real `𝒟_𝔖` and simulator `𝒟_Σ` experiments. -/
def E : Prop :=
  capacitySegmentDup trace ∨ E_func trace

end Def57_TraceOnlyBadEvents

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
the full DS query-answer trace.  Used as the building block for both the real (`𝒟_𝔖`) and
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
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- CO25 §5.6 Lemma 5.8 — Per-oracle query budget map for a salted malicious prover on
`[]ₒ + duplexSpongeChallengeOracle`. `tₕ` bounds `h` queries, `tₚ` forward `p` queries,
`tₚᵢ` backward `p⁻¹` queries; the `[]ₒ` branch is uncallable so its share is `0`.
Aligns with the §5.8 hybrid bookkeeping (`duplexSpongeQueryBudgetWithShared` in `Defs.lean`)
so Lemma 5.8 plugs into `claim_5_21` / `claim_5_22` / `claim_5_24` without re-keying. -/
def lemma5_8QueryBudget (tₕ tₚ tₚᵢ : ℕ) :
    ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → ℕ :=
  duplexSpongeQueryBudgetWithShared (oSpec := []ₒ) PEmpty.elim tₕ tₚ tₚᵢ

/-- CO25 Lemma 5.8 — Semantic `(tₕ, tₚ, tₚᵢ)` query bound for the salted §5.6 prover.
`IsLemma5_8QueryBound maliciousProver tₕ tₚ tₚᵢ` asserts that the prover makes at most `tₕ`
hash queries, `tₚ` forward permutation queries, and `tₚᵢ` inverse permutation queries on the
combined `[]ₒ + DS` surface that matches the §5.8 hybrid games (LHS=Hyb_0, RHS=Hyb_1). -/
abbrev IsLemma5_8QueryBound
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  OracleComp.IsPerIndexQueryBound maliciousProver
    (lemma5_8QueryBudget (StmtIn := StmtIn) (U := U) tₕ tₚ tₚᵢ)

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

/-- CO25 §5.6 (Option G) — Monad-reorder + logging wrapper. Reorders `StateT σ (OptionT ProbComp)`
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

/-- CO25 §5.6 (Option G) — Abortable Lemma-5.8 trace experiment, mirroring the §5.8 hybrid skeleton
(`KeyLemma.dsfsGame` / `hybridGame`): the salted `maliciousProver` runs under `impl`, then the
forward-only verifier `𝒱^{h,p} := V.toDSFS δ` (paper Figure 4 line 3) runs on its output, with the
carrier `σ` (e.g. `D_𝔖.Carrier` / `D2SQueryState`) threaded throughout.

Returns `(tr_P̃, tr_V)`; the bad event `E` (Def 5.7) is evaluated on `tr_P̃ ++ tr_V`. -/
noncomputable def lemma5_8ProjectedTraceDistAbortable
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp)))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let s₀ ← init
  -- Log each DS query into the wide `[]ₒ + DS` log (tagged `Sum.inr`); the log is kept on abort.
  let wrappedDSImpl :
      QueryImpl (duplexSpongeChallengeOracle StmtIn U)
        (OptionT
          (StateT (σ ×
            QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
    fun q => OptionT.mk fun st => do
      let r ← (impl q st.1).run
      match r with
      | none => pure (none, st)
      | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))
  -- The `[]ₒ` summand is unreachable, so compose it via the generic empty impl.
  let combinedImpl :
      QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
        (OptionT
          (StateT (σ ×
            QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
    (lemma5_8EmptyQueryImplGeneric
      (m := OptionT
        (StateT (σ ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)))
    + wrappedDSImpl
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

/-- CO25 §5.6 — Run a concrete Lemma 5.8 experiment over `[]ₒ + DS` and keep only the DS trace.
Combines the logging oracle with the given DS implementation, runs the experiment, and projects
the combined trace down to the DS component. -/
def lemma5_8ProjectedTraceDistOfConcreteExperiment
    {σ α : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (exp : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let combinedImpl :
      QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp) :=
    (lemma5_8EmptyQueryImpl (σ := σ)) + impl
  let outWithLog :
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
        (α × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :=
    (simulateQ loggingOracle exp).run
  let ⟨_, trace⟩ ←
    (simulateQ combinedImpl outWithLog).run' (← init)
  pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trace)

/-- CO25 §5.6 Lemma 5.8 — Shared experiment shape for both sides of Lemma 5.8.
Runs the malicious prover under the DS oracle, then runs the DSFS verifier on the resulting
`(statement, proof)` pair.  Returns the optional verifier output.

Type-level CO25 Figure 4 line 3: the honest verifier is invoked at the narrow forward-only spec
`[]ₒ + duplexSpongeForwardOracle StmtIn U` (`𝒱^{h,p}` — no `p⁻¹`); its computation is then
`liftComp`-ed into the wide spec used by the (adversarial) prover for trace concatenation. -/
def lemma5_8TraceExperiment
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) := do
  let _ : Codec pSpec U := codec
  let ⟨stmtIn, messages⟩ ← maliciousProver
  let verifyCompNarrow :
      OracleComp ([]ₒ + duplexSpongeForwardOracle StmtIn U) (Option StmtOut) :=
    ((Verifier.duplexSpongeFiatShamirForward
        (oSpec := []ₒ) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) V).run
      stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run
  liftComp verifyCompNarrow ([]ₒ + duplexSpongeChallengeOracle StmtIn U)

/-- CO25 §5.6 (Option G) — Trivially lift a total `StateT σ ProbComp` DS implementation to the
abortable shape `StateT σ (OptionT ProbComp)` required by `lemma5_8ProjectedTraceDistAbortable`.
The lifted impl never produces `none`. -/
private def lemma5_8TotalAbortLift {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)) :=
  fun q s => OptionT.lift (impl q s)

/-- CO25 Lemma 5.8 — Left-hand-side trace distribution (Option G — paper-faithful abort).
Real DS execution under the explicit `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` implementation. The eager impl is
total (never aborts), so the `OptionT`-layer is a dummy. Returns the pair `(tr_P̃, tr_V)`. -/
noncomputable def lemma5_8RealTraceDist
    {σReal : Type}
    (initReal : ProbComp σReal)
    (implReal : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σReal ProbComp))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
    initReal
    (lemma5_8TotalAbortLift (StmtIn := StmtIn) (U := U) implReal)
    V maliciousProver

/-- CO25 Lemma 5.8 — Right-hand-side trace distribution (Option G — paper-faithful abort).
Simulator execution under eager `g ← 𝒟_Σ(λ, n)` with `D2SQuery` as the oracle implementation.
The `d2sQueryImpl` runs in `StateT D2SQueryState (OptionT ProbComp)`: an `OptionT`-abort halts the
experiment (paper line 1417). Returns the pair `(tr_P̃, tr_V)`.

The `g` carrier is sampled **once** at experiment start from `𝒟_Σ`, captured by closure,
and consulted deterministically by every `gᵢ` query. This mirrors `lemma5_8RealTraceDist`'s
eager `(h, p, p⁻¹) ← 𝒟_𝔖` sampling — CO25 Def. 4.2 + Lemma 5.8 statement. -/
noncomputable def lemma5_8SigmaTraceDist
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let k_g ←
    (D_Sigma (U := U) StmtIn pSpec δ).sample
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
    (init := pure default)
    (impl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := fun q => OptionT.lift
        ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
      (auxImpl := fun aux => OptionT.lift
        ((ProverTransform.d2sUnitSampleImpl (U := U) +
          QueryImpl.id' unifSpec) aux)))
    V maliciousProver


set_option linter.unusedDecidableInType false in
/-- CO25 Lemma 5.8 — Bad-event probability bound (paper-faithful eager statement).
For every salted `(tₕ, tₚ, tₚᵢ)`-query malicious prover P̃ with `tₚ ≥ L` (where
`L = pSpec.totalNumPermQueries = Lₚ + Lᵥ` is the verifier's total message/challenge
permutation-query count, matching the §5.8 hybrid bookkeeping in `claim_5_21` / `_22` / `_24`),

```
max{ Pr[E(tr_P̃ ‖ tr_V) | 𝒟_𝔖], Pr[E(tr_P̃ ‖ tr_V) | 𝒟_Σ] }
  ≤ (7·T² − 3·T) / (2·|Σ|^c)
```

where `T = tₕ + 1 + tₚ + L + tₚᵢ`. Both sides match CO25 Lemma 5.8 verbatim:
the left-hand side samples `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` once at the start of the experiment
(eager sampling, CO25 Def. 4.2) and corresponds to `KeyLemma.dsfsGame` (`Hyb_0`); the
right-hand side runs `g ← 𝒟_Σ(λ, n)` via the `D2SQuery` simulator and corresponds to
`KeyLemma.hybridGame` instantiated as `Hyb_1`. -/
theorem lemma_5_8
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hMaliciousBound : -- `(tₕ, tₚ, tₚᵢ)`-query bound prover
      IsLemma5_8QueryBound
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        maliciousProver tₕ tₚ tₚᵢ)
    (hTp : tₚ ≥ pSpec.totalNumPermQueries) :
    max
        (Pr[fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              BadEventDS.E (tr.1 ++ tr.2) |
          lemma5_8RealTraceDist
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) (δ := δ)
            (D_𝔖 StmtIn U).sample
            ((D_𝔖 StmtIn U).eagerImpl)
            V maliciousProver])
        (Pr[fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              BadEventDS.E (tr.1 ++ tr.2) |
          lemma5_8SigmaTraceDist
            (T_H := T_H) (T_P := T_P) (δ := δ)
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U)
            V maliciousProver])
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries) := by
  let _ := hMaliciousBound
  let _ := hTp
  sorry

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

end Lemma5_10

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

/-- CO25 Lemma 5.12 — If `E(tr) = 0` then `E_inv(tr, s) = 0`. -/
lemma lemma_5_12 (h : ¬ E trace)
    (seq_BT : Backtrack.S_BT trace state) :
    ¬ E_inv trace state seq_BT := by
  sorry

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

/-- CO25 Lemma 5.14 — If `E(tr) = 0` then `E_fork(tr, s) = 0`. -/
lemma lemma_5_14 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_fork trace state S_BT := by
  sorry

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

/-- CO25 Lemma 5.16 — If `E(tr) = 0` then `E_time(tr, s) = 0`. -/
lemma lemma_5_16 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_time trace state S_BT := by
  sorry

end Def515_Lemma516

end BadEventDS

end DuplexSpongeFS

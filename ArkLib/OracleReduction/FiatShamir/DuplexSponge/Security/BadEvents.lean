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

(TODO: may have to split this into multiple files given the number of lemmas)
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleSpec

namespace QueryLog

section
-- WIP defining more general properties for query log

variable {ι : Type*} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

/-- A query tuple `(i, q, r)` is redundant in a query log if it appears more than once -/
def redundantQuery (log : QueryLog spec) (q : spec.Domain) (r : spec.Range q) : Prop :=
  (log.count ⟨q, r⟩) > 1

/-- Check whether a query-answer entry at position `idx` has an identical prior entry in `log`. -/
def existPriorSameQuery (log : QueryLog spec) (idx : Fin log.length) : Prop :=
  ∃ j' < idx, log[j'] = log[idx]

end
end QueryLog

end OracleSpec

namespace DuplexSpongeFS

/-! ## Definition 5.5 and Definition 5.6 - Redundant entries in a trace -/
section Def_5_5_6_RedundantEntryDSHelpers

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- Redundancy test for a new entry against a prefix of the trace (Definition 5.5). -/
private def redundantEntryDSPrefix
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

/-- CO25 Definition 5.5 — Redundant entry in a duplex-sponge trace.
An entry `tr_j` is redundant if a prior entry `tr_{j'} (j' < j)` makes it superfluous:
- `(h, x, s_C)` is redundant if the same pair already appears earlier (Eq. 20).
- `(p, s_in, s_out)` is redundant if `(p, s_in, s_out)` or `(p⁻¹, s_out, s_in)` appears earlier
  (Eq. 21).
- `(p⁻¹, s_out, s_in)` is redundant if `(p⁻¹, s_out, s_in)` or `(p, s_in, s_out)` appears
  earlier (Eq. 22).

TODO: refactor this into a combination of simpler properties? -/
def redundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  redundantEntryDSPrefix (log.take idx.1) log[idx]

/-- CO25 Definition 5.6 — Base trace `tr̄` side condition.
`NoRedundantEntryDS log` holds iff no entry of `log` is redundant in the sense of
Definition 5.5.  The base trace `tr̄` is the unique sub-log satisfying this predicate
(see `getBaseTrace`). -/
def NoRedundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ i : ℕ, ∀ hi : i < log.length,
    ¬ redundantEntryDSPrefix (log.take i) log[i]

private lemma noRedundantEntryDS_nil : NoRedundantEntryDS (StmtIn := StmtIn) (U := U) [] := by
  intro i hi _
  exact (Nat.not_lt_zero i) hi

private lemma noRedundantEntryDS_append_singleton
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : NoRedundantEntryDS acc)
    (hEntry : ¬ redundantEntryDSPrefix acc entry) :
    NoRedundantEntryDS (acc ++ [entry]) := by
  intro i hi
  have hi' : i < acc.length + 1 := by simpa using hi
  by_cases hlt : i < acc.length
  · have hOld :
      ¬ redundantEntryDSPrefix (acc.take i) acc[i] := hAcc i hlt
    simpa [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
      using hOld
  · have hEq : i = acc.length := Nat.eq_of_lt_succ_of_not_lt hi' hlt
    subst hEq
    simpa [List.take_left, redundantEntryDSPrefix] using hEntry

private noncomputable def getBaseTraceAux
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) := by
  classical
  exact match remaining with
  | [] => acc
  | entry :: rest =>
      if hRed : redundantEntryDSPrefix acc entry then
        getBaseTraceAux rest acc
      else
        getBaseTraceAux rest (acc ++ [entry])

private lemma getBaseTraceAux_noRedundant
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : NoRedundantEntryDS acc) :
    NoRedundantEntryDS (getBaseTraceAux remaining acc) := by
  classical
  induction remaining generalizing acc with
  | nil =>
      simpa [getBaseTraceAux] using hAcc
  | cons entry rest ih =>
      by_cases hRed : redundantEntryDSPrefix acc entry
      · simpa [getBaseTraceAux, hRed] using ih acc hAcc
      · let hAcc' := noRedundantEntryDS_append_singleton acc entry hAcc hRed
        simpa [getBaseTraceAux, hRed] using ih (acc ++ [entry]) hAcc'

/-- CO25 Definition 5.6 — Compute the base trace `tr̄` of a duplex-sponge query-answer trace by
removing all redundant entries (in the sense of Definition 5.5).  The result carries a proof that
no entry in the returned list is redundant. -/
noncomputable def getBaseTrace
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U) |
      NoRedundantEntryDS baseTrace} := by
  refine ⟨getBaseTraceAux log [], ?_⟩
  simpa using getBaseTraceAux_noRedundant
    log [] (noRedundantEntryDS_nil (StmtIn := StmtIn) (U := U))

end Def_5_5_6_RedundantEntryDSHelpers

/-! ## Bad-event-related predicates and lemmas (Definition 5.7 -> Lemma 5.16) -/
namespace BadEventDS
open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)

/-! ## Definition 5.7 — trace-only bad events (`E_h`, `E_p`, `E_{p⁻¹}`, `E_dup`, `E_func`, `E`) -/

section Def57_TraceOnlyBadEvents

/-! Fist, we define the main bad event, which consists of two main conditions:
1. No duplicate in the capacity segment (for the base trace that removed redundant entries)
2. The same query to `p` leads to different answers, or there are inconsistent queries across `p`
and `p⁻¹` -/

/- NOTE: the paper write `∃ j > 0`, which can be confusing since we don't know whether the intended
indexing is from 0 or from 1. We assume they mean from 1, and since indexing here is from 0, we just
write `∃ j`. -/

/-- CO25 Definition 5.7 — Event `E_h(tr)` (Eq. 23).
An output capacity segment `s_C` of an `h`-entry in the base trace `tr̄` previously appears
as an output or input capacity segment of `h`, `p`, or `p⁻¹`:

```
E_h(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (h, ·, s_C)  and  ∃ j' < j :
  tr̄_{j'} = (h, ·, s_C)  ∨  tr̄_{j'} = (p, ·, (·, s_C))  ∨  tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  tr̄_{j'} = (p, (·, s_C), ·)  ∨  tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

All five prior-entry branches are explicit in the Lean definition. -/
def capacitySegmentDupHash : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    ∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩ ∧
      ∃ j' < j,
        ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩ ∨
        (∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩
          ∧ stateOut1.capacitySegment = capSeg) ∨
        (∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩
          ∧ stateIn2.capacitySegment = capSeg) ∨
        (∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩
          ∧ stateIn3.capacitySegment = capSeg) ∨
        (∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩
          ∧ stateOut4.capacitySegment = capSeg)

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
``` -/
def capacitySegmentDupPerm : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
          stateIn2.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
          stateOut4.capacitySegment = capSeg)
      )

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
``` -/
def capacitySegmentDupPermInv : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' < j, ∃ stateIn2 stateOut2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
          CanonicalSpongeState.capacitySegment stateIn2 = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn4 stateOut4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
          stateOut4.capacitySegment = capSeg)
      )

alias E_pinv := capacitySegmentDupPermInv

/-- CO25 Definition 5.7 — Combined capacity-segment duplication event `E_dup(tr)`.
Holds iff at least one of `E_h(tr)`, `E_p(tr)`, or `E_{p⁻¹}(tr)` holds: there exists an output
capacity segment in the base trace `tr̄` that previously appeared as an output or input capacity
segment. -/
def capacitySegmentDup : Prop :=
  capacitySegmentDupHash trace ∨ capacitySegmentDupPerm trace ∨ capacitySegmentDupPermInv trace

alias E_dup := capacitySegmentDup

/-- CO25 Definition 5.7 — Event `E_func(tr)` (Eq. 26).
The same query to `p` leads to different answers, or there are inconsistent queries across `p`
and `p⁻¹`:

```
E_func(tr) := ∃ j > 0, s_in ∈ Σ^{r+c} :  tr̄_j = (p, s_in, ·)  and  ∃ j' < j :
  tr̄_{j'} = (p, s_in, ·)  ∨  tr̄_{j'} = (p⁻¹, ·, s_in)
```

Note: `E_func(tr)` never holds for a true permutation `p` and its inverse `p⁻¹`, but may hold
(with small probability) for the D2SQuery simulator. -/
def E_func : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      ∃ j' < j,
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)

/-- CO25 Definition 5.7 — Combined bad event `E(tr)`.
`E(tr)` is the disjunction `E_dup(tr) ∨ E_func(tr)`, i.e., either a capacity-segment
duplication occurs or `p` behaves non-functionally.  Lemma 5.8 bounds `Pr[E(tr_P̃ ‖ tr_V)]`
in both the real `𝒟_𝔖` and simulator `𝒟_Σ` experiments. -/
def E : Prop :=
  capacitySegmentDup trace ∨ E_func trace

end Def57_TraceOnlyBadEvents

/-! ## Lemma 5.8 — closed-form bound
This section is consistency-free: `lemma_5_8` bounds `Pr[E]` directly via birthday-style
counting on freshly-sampled values, so its statement does not take `isConsistentTrace`. -/
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

/-- CO25 §5.6 Lemma 5.8 — Per-oracle query budget map for a malicious prover.
`tₕ` bounds `h` queries, `tₚ` forward `p` queries, `tₚᵢ` backward `p⁻¹` queries.
Alias for `duplexSpongeQueryBudget`. -/
def lemma5_8QueryBudget (tₕ tₚ tₚᵢ : ℕ) :
    (duplexSpongeChallengeOracle StmtIn U).Domain → ℕ :=
  duplexSpongeQueryBudget tₕ tₚ tₚᵢ

/-- CO25 Lemma 5.8 — Semantic `(tₕ, tₚ, tₚᵢ)` query bound for a malicious prover.
`IsLemma5_8QueryBound maliciousProver tₕ tₚ tₚᵢ` asserts that the prover makes at most `tₕ`
hash queries, `tₚ` forward permutation queries, and `tₚᵢ` inverse permutation queries. -/
abbrev IsLemma5_8QueryBound
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
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

/-- CO25 §5.6 (Option G — paper-faithful abort) — Monad-reorder + logging wrapper.

Lifts a partially-defined DS implementation
  `QueryImpl DS (StateT σ (OptionT ProbComp))`
into a partially-defined, logging DS implementation
  `QueryImpl DS (OptionT (StateT (σ × QueryLog DS) ProbComp))`.

Two operations happen here:
- **Monad reorder**: in `StateT σ (OptionT ProbComp)` an `OptionT`-abort drops the state; in
  `OptionT (StateT (σ × QueryLog) ProbComp)` the state (including the log) is preserved at the
  moment of abort. This is precisely the paper-1417 abort semantics: "abort halts execution;
  trace is partial".
- **Logging**: every successful query `q ↦ a` extends the log with `⟨q, a⟩`; on abort the log is
  frozen. -/
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

/-- CO25 §5.6 (Option G — paper-faithful abort) — Abortable Lemma-5.8 trace experiment with
separate prover and verifier query-log slots.

Runs the malicious prover under `impl` (wrapped via `lemma5_8LoggingWrapper`) with a fresh log
`[]`, yielding either an abort or the prover output `(stmtIn, messages)`. The carrier state `σ`
(e.g., `D𝔖.Carrier` or `D2SQueryState`) is threaded; the log accumulates the prover-phase trace
`tr_P̃`. If the prover aborts mid-execution, the returned pair is `(tr_P̃, [])` (paper line 1417:
abort halts the experiment; `V` never runs; `tr_V` is empty).

On `some`, the verifier `𝒱^{h,p} := Verifier.duplexSpongeFiatShamirForward V` runs over the
narrow forward-only spec `[]ₒ + duplexSpongeForwardOracle`, then is `liftComp`-ed up to the wide
spec `[]ₒ + duplexSpongeChallengeOracle` shared with the prover. The verifier simulation reuses
the post-prover carrier state `s₁` but starts with a fresh log `[]` so the returned `tr_V`
contains only verifier-phase queries.

Returns the pair `(tr_P̃, tr_V)`. The bad-event predicate of CO25 Def 5.7 is evaluated on the
concatenation `tr_P̃ ++ tr_V`. -/
noncomputable def lemma5_8ProjectedTraceDistAbortable
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp)))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let s₀ ← init
  let wrappedImpl :
      QueryImpl (duplexSpongeChallengeOracle StmtIn U)
        (OptionT
          (StateT (σ × QueryLog (duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
    lemma5_8LoggingWrapper (StmtIn := StmtIn) (U := U) impl
  let proverResult ← ((simulateQ wrappedImpl maliciousProver).run) (s₀, [])
  match proverResult with
  | (none, (_, trP)) => pure (trP, [])
  | (some ⟨stmtIn, messages⟩, (s₁, trP)) =>
      let verifyCompNarrow :
          OracleComp ([]ₒ + duplexSpongeForwardOracle StmtIn U) (Option StmtOut) :=
        ((Verifier.duplexSpongeFiatShamirForward
            (oSpec := []ₒ) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
            (U := U) V).run
          stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run
      let verifyCompWide :
          OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
        liftComp verifyCompNarrow ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
      let combinedImpl :
          QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
            (OptionT
              (StateT (σ × QueryLog (duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
        (lemma5_8EmptyQueryImplGeneric
          (m := OptionT
            (StateT (σ × QueryLog (duplexSpongeChallengeOracle StmtIn U)) ProbComp)))
        + wrappedImpl
      let verifierResult ← ((simulateQ combinedImpl verifyCompWide).run) (s₁, [])
      let trV := verifierResult.2.2
      pure (trP, trV)

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
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    initReal
    (lemma5_8TotalAbortLift (StmtIn := StmtIn) (U := U) implReal)
    V maliciousProver

/-- CO25 Lemma 5.8 — Right-hand-side trace distribution (Option G — paper-faithful abort).
Simulator execution under eager `g ← 𝒟_Σ(λ, n)` with `D2SQuery` as the oracle implementation.
The `d2sQueryImpl` runs in `StateT D2SQueryState (OptionT ProbComp)`: an `OptionT`-abort halts the
experiment (paper line 1417). Returns the pair `(tr_P̃, tr_V)`.

The `g` carrier is sampled **once** at experiment start from
`TraceTransform.section58EncodedChallengeOracleDistribution` (the canonical `𝒟_Σ`), captured by closure,
and consulted deterministically by every `gᵢ` query. This mirrors `lemma5_8RealTraceDist`'s
eager `(h, p, p⁻¹) ← 𝒟_𝔖` sampling — CO25 Def. 4.2 + Lemma 5.8 statement. -/
noncomputable def lemma5_8SigmaTraceDist
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let k_g ←
    (TraceTransform.section58EncodedChallengeOracleDistribution (U := U) StmtIn pSpec δ).sample
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U)
    (init := pure default)
    (impl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := fun q => OptionT.lift
        ((TraceTransform.section58EncodedChallengeOracleDistribution
          (U := U) StmtIn pSpec δ).toImpl k_g q))
      (auxImpl := fun aux => OptionT.lift
        ((ProverTransform.d2sUnitSampleImpl (U := U) +
          QueryImpl.id' unifSpec) aux)))
    V maliciousProver

/-- CO25 Lemma 5.8 — eager carrier impl wrapper.
Wraps `D𝔖.toImpl` (a stateless `QueryImpl _ ProbComp` per carrier sample) into the
`StateT D𝔖.Carrier ProbComp` shape required by `lemma5_8RealTraceDist`. The carrier is
sampled once at game start (CO25 Def. 4.2) and then read-only — `get` reads, never
mutates. -/
noncomputable def lemma5_8EagerImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (D𝔖 StmtIn U).Carrier ProbComp) :=
  fun q => do
    let k ← StateT.get
    StateT.lift ((D𝔖 StmtIn U).toImpl k q)

set_option linter.unusedDecidableInType false in
/-- CO25 Lemma 5.8 — Bad-event probability bound (paper-faithful eager statement).
For every `(tₕ, tₚ, tₚᵢ)`-query malicious prover P̃ with `tₚ ≥ L` (where `L` is the total number
of verifier permutation queries),

```
max{ Pr[E(tr_P̃ ‖ tr_V) | 𝒟_𝔖], Pr[E(tr_P̃ ‖ tr_V) | 𝒟_Σ] }
  ≤ (7·T² − 3·T) / (2·|Σ|^c)
```

where `T = tₕ + 1 + tₚ + L + tₚᵢ`. Both sides match CO25 Lemma 5.8 verbatim:
the left-hand side samples `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` once at the start of the experiment
(eager sampling, CO25 Def. 4.2), the right-hand side runs `g ← 𝒟_Σ(λ, n)` via the `D2SQuery`
simulator. -/
theorem lemma_5_8
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ)
    (hMaliciousBound : -- `(tₕ, tₚ, tₚᵢ)`-query bound prover
      IsLemma5_8QueryBound
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        maliciousProver tₕ tₚ tₚᵢ)
    (hTp : tₚ ≥ pSpec.totalNumPermQueries) :
    max
        (Pr[fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              BadEventDS.E (tr.1 ++ tr.2) |
          lemma5_8RealTraceDist
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U)
            (D𝔖 StmtIn U).sample
            (lemma5_8EagerImpl (StmtIn := StmtIn) (U := U))
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
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ stateIn stateIn' stateOut,
    ⟨.inr <|.inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <|.inl stateIn', stateOut⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

/-- CO25 Definition 5.9 Item 2 — Event `E_{col,p⁻¹}(tr)`.
There exist `(p⁻¹, s_out, s_in)` and `(p⁻¹, s_out', s_in)` in `tr̄` with `s_out ≠ s_out'`:
two distinct inverse-permutation inputs map to the same output. -/
def collisionBwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ stateOut stateOut' stateIn,
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

/-- CO25 Definition 5.9 Item 3 — Event `E_{col,p,p⁻¹}(tr)` in exact paper shape.
There exist `(p, s_in, s_out)` and `(p⁻¹, s_out, s_in')` in `tr̄` with `s_out = s_out'` and
`s_in ≠ s_in'`: `p` is onto but its inverse is not a function. -/
def collisionFwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ stateIn stateOut stateIn',
    ⟨.inr <| .inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut, stateIn'⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p_pinv := collisionFwdBwd

/-- CO25 Definition 5.9 Item 4 — Event `E_{col,p⁻¹,p}(tr)` in exact paper shape.
There exist `(p⁻¹, s_out, s_in)` and `(p, s_in, s_out')` in `tr̄` with `s_out ≠ s_out'`:
`p⁻¹` is onto but `p` is not a function. -/
def collisionBwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  ∃ stateOut stateIn stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateIn, stateOut'⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p := collisionBwdFwd

/-- CO25 Definition 5.9 — Event `E_prp(tr)` in exact paper form.
`E_prp(tr)` is the disjunction of:
1. `E_{col,p}(tr)` — two `p`-entries share the same output.
2. `E_{col,p⁻¹}(tr)` — two `p⁻¹`-entries share the same output.
3. `E_{col,p,p⁻¹}(tr)` — a `p`-entry and a `p⁻¹`-entry share the same middle state with
   distinct endpoints.
4. `E_{col,p⁻¹,p}(tr)` — same as above with roles swapped.

Informally: Items 1 or 3 make `p` non-injective; Items 2 or 4 make `p⁻¹` non-injective. -/
def collisionPerm : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace
    ∨ collisionFwdBwd trace ∨ collisionBwdFwd trace


alias E_prp := collisionPerm

/-- `(h, p, p⁻¹)`-trace consistency predicate for a trace, which guarantees both the following:
- `¬ E_{col,p,p⁻¹}(tr): (p, s_in, s_out) ∈ tr̄ ∧ (p⁻¹, s_out, s_in') ∈ tr̄ → s_in = s_in'`
  (this is item #3 of Definition 5.9)
- `¬E_{col,p⁻¹,p}(tr): (p⁻¹, s_out, s_in) ∈ tr̄ ∧ (p, s_in, s_out') ∈ tr̄ → s_out = s_out'`
  (this is item #4 of Definition 5.9 - `E_prp`) -/
def isConsistentTrace : Prop :=
  let ⟨baseTrace, _⟩ := getBaseTrace trace
  -- `¬ E_{col,p,p⁻¹}(tr)`
  (∀ stateIn stateOut stateIn',
      ⟨.inr <| .inl stateIn, stateOut⟩ ∈ baseTrace →
      ⟨.inr <| .inr stateOut, stateIn'⟩ ∈ baseTrace →
      stateIn = stateIn') ∧
  -- `¬ E_{col,p⁻¹,p}(tr)`
  (∀ stateOut stateIn stateOut',
      ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace →
      ⟨.inr <| .inl stateIn, stateOut'⟩ ∈ baseTrace →
      stateOut = stateOut')

-- TODO: investigate when & how we need to prove implications of the form
-- `tr ∈ support experimentTraceDist → isConsistentTrace tr` in hybrid experiments

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
    exact ⟨⟨i, hi⟩, h_lt, sI, sO, hgi, rfl⟩
  · refine ⟨⟨i, hi⟩, sI.capacitySegment, ⟨sO, sI, hgi, rfl⟩, ?_⟩
    right; right; left
    exact ⟨⟨j, hj⟩, h_lt, sI, sO', hgj, rfl⟩

/-- CO25 Lemma 5.10 — helper.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0`, then the exact paper-form
`E_prp(tr)` does not hold. -/
lemma not_collisionPerm_of_not_combined
    (hTrace : isConsistentTrace trace)
    (h : ¬ E trace) : ¬ E_prp trace := by
  intro hprp
  rcases hprp with hff | hbb | hfb | hbf
  · exact not_collisionFwdFwd_of_not_combined (trace := trace) h hff
  · exact not_collisionBwdBwd_of_not_combined (trace := trace) h hbb
  · rcases hTrace with ⟨hFwdBwd, _⟩
    rcases hfb with ⟨stateIn, stateOut, stateIn', hm1, hm2, hne⟩
    exact hne (hFwdBwd stateIn stateOut stateIn' hm1 hm2)
  · rcases hTrace with ⟨_, hBwdFwd⟩
    rcases hbf with ⟨stateOut, stateIn, stateOut', hm1, hm2, hne⟩
    exact hne (hBwdFwd stateOut stateIn stateOut' hm1 hm2)

/-- CO25 Lemma 5.10.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0` then `E_prp(tr) = 0`. -/
theorem lemma_5_10 (hTrace : isConsistentTrace trace) (h : ¬ E trace) : ¬ E_prp trace :=
  not_collisionPerm_of_not_combined (trace := trace) hTrace h

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

/-- CO25 Lemma 5.12 — If `E(tr) = 0` then `E_inv(tr, s) = 0`.

Paper-direct statement (CO25 Def 5.11 / Eq. 35): no BackTrack sequence in `S_BT(tr, s)` uses a
`p⁻¹` step. -/
lemma lemma_5_12 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_inv trace state S_BT := by
  sorry

end Def511_Lemma512

/-! ## Definition 5.13 and Lemma 5.14 — BackTrack fork event -/
section Def513_Lemma514

/-- CO25 Definition 5.13 — Event `E_fork(tr, s)`: there is a (capacity-segment) collision for
`h` or `p`, formalized directly as `|𝒮_BT(tr, s)| > 1`. -/
def E_fork (S_BT : Backtrack.S_BT trace state) : Prop :=
  S_BT.seqFamily.card > 1

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
    (S₁.inputState[ι₁.val]'(by
      have := S₁.inputState_length_eq_outputState_length_succ
      have := ι₁.isLt; omega)) ≠
    (S₂.inputState[ι₂.val]'(by
      have := S₂.inputState_length_eq_outputState_length_succ
      have := ι₂.isLt; omega)) ∧
    S₁.outputState[ι₁].capacitySegment = S₂.outputState[ι₂].capacitySegment

/-- CO25 Definition 5.13 / Eq. 40 — `E_{fork,h,p}(tr, s)`: collision of `h` with the output
capacity segment of a query to `p`.  There exist `S^{(1)}, S^{(2)} ∈ 𝒮_BT(tr, s)` and
`ι ∈ [m_2 - 1]` with `s_{C,in,0}^{(1)} = s_{C,out,ι}^{(2)}`. -/
def E_fork_h_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ S₁ ∈ S_BT.seqFamily, ∃ S₂ ∈ S_BT.seqFamily,
  ∃ ι : Fin S₂.outputState.length,
    (S₁.inputState[0]'(by
      have := S₁.inputState_length_eq_outputState_length_succ; omega)).capacitySegment =
    S₂.outputState[ι].capacitySegment

/-- CO25 Definition 5.13 — Collective exhaustiveness (CE, **not** ME) of the three special cases.
If `E_fork(tr, s) = 1`, i.e. `|𝒮_BT(tr, s)| > 1`, then at least one of `E_{fork,h}`, `E_{fork,p}`,
`E_{fork,h,p}` holds.  The cases are not mutually exclusive — multiple may hold simultaneously. -/
lemma E_fork_implies_subcases
    (S_BT : Backtrack.S_BT trace state) (h : E_fork trace state S_BT) (h_not_E : ¬ E trace) :
    E_fork_h trace state S_BT ∨ E_fork_p trace state S_BT ∨ E_fork_h_p trace state S_BT := by
  sorry

/-- CO25 Lemma 5.14 — If `E(tr) = 0` then `E_fork(tr, s) = 0`, i.e. `|𝒮_BT(tr, s)| ≤ 1`. -/
lemma lemma_5_14 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_fork trace state S_BT := by
  sorry

end Def513_Lemma514

/-! ## Definition 5.15 and Lemma 5.16 — ordering event -/
section Def515_Lemma516

/-- CO25 Definition 5.15 / Eq. 41 — `E_{time,h}(tr, s)`: the query to `h` is out of order.
There exists `J^{(k)} = (j_h^{(k)}, j_0^{(k)}, …, j_{m_k}^{(k)}) ∈ 𝒥_BT(tr, s)` with
`j_h^{(k)} > j_0^{(k)}`. -/
def E_time_h (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
    p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ; omega⟩).val

/-- CO25 Definition 5.15 / Eq. 42 — `E_{time,p}(tr, s)`: a query to `p` is out of order.
There exists `J^{(k)} ∈ 𝒥_BT(tr, s)` and `ι ∈ [m_k - 1]` (paper indexing) with
`j_{ι-1}^{(k)} > j_ι^{(k)}`, i.e. some consecutive pair of `j`-indices is out of order. -/
def E_time_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
  ∃ ι : Fin p.1.outputState.length,
    (p.2.2 ⟨ι.val, by
      have := p.1.inputState_length_eq_outputState_length_succ
      have := ι.isLt; omega⟩).val >
    (p.2.2 ⟨ι.val + 1, by
      have := p.1.inputState_length_eq_outputState_length_succ
      have := ι.isLt; omega⟩).val

/-- CO25 Definition 5.15 — `E_time(tr, s) := E_{time,h}(tr, s) ∨ E_{time,p}(tr, s)`. -/
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

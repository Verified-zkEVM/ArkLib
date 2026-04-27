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

section DuplexSpongeFS

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
(see `removeRedundantEntryDS`). -/
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

private noncomputable def removeRedundantEntryDSAux
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) := by
  classical
  exact match remaining with
  | [] => acc
  | entry :: rest =>
      if hRed : redundantEntryDSPrefix acc entry then
        removeRedundantEntryDSAux rest acc
      else
        removeRedundantEntryDSAux rest (acc ++ [entry])

private lemma removeRedundantEntryDSAux_noRedundant
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : NoRedundantEntryDS acc) :
    NoRedundantEntryDS (removeRedundantEntryDSAux remaining acc) := by
  classical
  induction remaining generalizing acc with
  | nil =>
      simpa [removeRedundantEntryDSAux] using hAcc
  | cons entry rest ih =>
      by_cases hRed : redundantEntryDSPrefix acc entry
      · simpa [removeRedundantEntryDSAux, hRed] using ih acc hAcc
      · let hAcc' := noRedundantEntryDS_append_singleton acc entry hAcc hRed
        simpa [removeRedundantEntryDSAux, hRed] using ih (acc ++ [entry]) hAcc'

/-- CO25 Definition 5.6 — Compute the base trace `tr̄` of a duplex-sponge query-answer trace by
removing all redundant entries (in the sense of Definition 5.5).  The result carries a proof that
no entry in the returned list is redundant. -/
noncomputable def removeRedundantEntryDS
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U) |
      NoRedundantEntryDS baseTrace} := by
  refine ⟨removeRedundantEntryDSAux log [], ?_⟩
  simpa using removeRedundantEntryDSAux_noRedundant
    log [] (noRedundantEntryDS_nil (StmtIn := StmtIn) (U := U))

namespace BadEventDS

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)

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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
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
def notFunction : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ j : Fin baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      ∃ j' < j,
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)

alias E_func := notFunction

/-- CO25 Definition 5.7 — Combined bad event `E(tr)`.
`E(tr)` is the disjunction `E_dup(tr) ∨ E_func(tr)`, i.e., either a capacity-segment
duplication occurs or `p` behaves non-functionally.  Lemma 5.8 bounds `Pr[E(tr_P̃ ‖ tr_V)]`
in both the real `𝒟_𝔖` and simulator `𝒟_Σ` experiments. -/
def combined : Prop :=
  capacitySegmentDup trace ∨ notFunction trace

alias E := combined

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

/-! Then we define other bad events that don't hold (`= 0`)
if the combined event doesn't hold (`= 0`)
-/

/-- CO25 Definition 5.9 Item 1 — Event `E_{col,p}(tr)`.
There exist `(p, s_in, s_out)` and `(p, s_in', s_out)` in `tr̄` with `s_in ≠ s_in'`:
two distinct forward-permutation inputs map to the same output. -/
def collisionFwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateIn' stateOut,
    ⟨.inr <|.inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <|.inl stateIn', stateOut⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

/-- CO25 Definition 5.9 Item 2 — Event `E_{col,p⁻¹}(tr)`.
There exist `(p⁻¹, s_out, s_in)` and `(p⁻¹, s_out', s_in)` in `tr̄` with `s_out ≠ s_out'`:
two distinct inverse-permutation inputs map to the same output. -/
def collisionBwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateOut stateOut' stateIn,
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

/-- CO25 §5.6 — Staged mixed-collision predicate (forward × backward, same output).
Used internally by the `lemma_5_10` proof chain.  Two entries `(p, s_out, s_in)` and
`(p⁻¹, s_out', s_in)` share the same intermediate state `s_in` but differ on the outer state
(`s_out ≠ s_out'`). -/
def collisionFwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateOut',
    ⟨.inr <| .inl stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_p_pinv := collisionFwdBwd

/-- CO25 §5.6 — Staged mixed-collision predicate (backward × forward, same output).
Used internally by the `lemma_5_10` proof chain.  Two entries `(p⁻¹, s_out, s_in)` and
`(p, s_out', s_in)` share the same intermediate state `s_in` but differ on the outer state
(`s_out ≠ s_out'`). -/
def collisionBwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p := collisionBwdFwd

/-- CO25 §5.6 — Staged `E_prp` predicate (four-way disjunction).
Combines `E_{col,p}`, `E_{col,p⁻¹}`, and the two mixed-collision staged variants.
Kept for compatibility with proved helper chains; see `collisionPermPaper` for the
exact paper-form. -/
def collisionPerm : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace ∨ collisionFwdBwd trace ∨ collisionBwdFwd trace

/-- Staged `E_prp` surface kept for compatibility with existing proved helper chains. -/
alias E_prp_staged := collisionPerm

/-- CO25 Definition 5.9 Item 3 — Event `E_{col,p,p⁻¹}(tr)` in exact paper shape.
There exist `(p, s_in, s_out)` and `(p⁻¹, s_out, s_in')` in `tr̄` with `s_out = s_out'` and
`s_in ≠ s_in'`: `p` is onto but its inverse is not a function. -/
def collisionFwdBwdPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateIn',
    ⟨.inr <| .inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut, stateIn'⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p_pinv_paper := collisionFwdBwdPaper

/-- CO25 Definition 5.9 Item 4 — Event `E_{col,p⁻¹,p}(tr)` in exact paper shape.
There exist `(p⁻¹, s_out, s_in)` and `(p, s_in, s_out')` in `tr̄` with `s_out ≠ s_out'`:
`p⁻¹` is onto but `p` is not a function. -/
def collisionBwdFwdPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateOut stateIn stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateIn, stateOut'⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p_paper := collisionBwdFwdPaper

/-- CO25 Definition 5.9 — Event `E_prp(tr)` in exact paper form.
`E_prp(tr)` is the disjunction of:
1. `E_{col,p}(tr)` — two `p`-entries share the same output.
2. `E_{col,p⁻¹}(tr)` — two `p⁻¹`-entries share the same output.
3. `E_{col,p,p⁻¹}(tr)` — a `p`-entry and a `p⁻¹`-entry share the same middle state with
   distinct endpoints.
4. `E_{col,p⁻¹,p}(tr)` — same as above with roles swapped.

Informally: Items 1 or 3 make `p` non-injective; Items 2 or 4 make `p⁻¹` non-injective. -/
def collisionPermPaper : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace
    ∨ collisionFwdBwdPaper trace ∨ collisionBwdFwdPaper trace

alias E_prp := collisionPermPaper

alias E_prp_paper := collisionPermPaper

/-- CO25 §5.6 — Paper-level `(h, p, p⁻¹)` trace consistency on the base trace `tr̄`.
If both `p` and `p⁻¹` entries appear on the same middle state, they must agree on the opposite
endpoint:
- `(p, s_in, s_out) ∈ tr̄` and `(p⁻¹, s_out, s_in') ∈ tr̄` implies `s_in = s_in'`.
- `(p⁻¹, s_out, s_in) ∈ tr̄` and `(p, s_in, s_out') ∈ tr̄` implies `s_out = s_out'`.

This is the explicit well-formedness side condition needed for the §5.6 → Definition 5.9 bridge
over arbitrary Lean traces (which don't syntactically enforce permutation consistency). -/
def PaperTraceConsistent : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  (∀ stateIn stateOut stateIn',
      ⟨.inr <| .inl stateIn, stateOut⟩ ∈ baseTrace →
      ⟨.inr <| .inr stateOut, stateIn'⟩ ∈ baseTrace →
      stateIn = stateIn') ∧
  (∀ stateOut stateIn stateOut',
      ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace →
      ⟨.inr <| .inl stateIn, stateOut'⟩ ∈ baseTrace →
      stateOut = stateOut')

/-- Staged helper used by the current concrete proof script in this file. -/
lemma not_collisionPermStaged_of_not_combined (h : ¬ E trace) : ¬ E_prp_staged trace := by
  intro hprp
  apply h; clear h
  rcases hprp with hff | hbb | hfb | hbf
  · -- collisionFwdFwd → E
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
  · -- collisionBwdBwd → E
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
  · -- collisionFwdBwd → E
    obtain ⟨sI, sO, sO', hm1, hm2, hne⟩ := hfb
    rw [List.mem_iff_get] at hm1 hm2
    obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
    obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
    simp only [List.get_eq_getElem] at hgi hgj
    have hij : i ≠ j := by
      intro heq; subst heq; rw [hgi] at hgj
      exact absurd (congrArg Sigma.fst hgj) (by simp)
    rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
    · -- forward at i, backward at j, i < j: use capacitySegmentDupPermInv at j
      left; right; right
      unfold capacitySegmentDupPermInv
      refine ⟨⟨j, hj⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO', sI, hgj, rfl⟩, ?_⟩
      right; left
      exact ⟨⟨i, hi⟩, h_lt, sO, sI, hgi, rfl⟩
    · -- forward at i, backward at j, j < i: use capacitySegmentDupPerm at i
      left; right; left
      unfold capacitySegmentDupPerm
      refine ⟨⟨i, hi⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO, sI, hgi, rfl⟩, ?_⟩
      right; right; left
      exact ⟨⟨j, hj⟩, Nat.le_of_lt h_lt, sO', sI, hgj, rfl⟩
  · -- collisionBwdFwd → E
    obtain ⟨sI, sO, sO', hm1, hm2, hne⟩ := hbf
    rw [List.mem_iff_get] at hm1 hm2
    obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
    obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
    simp only [List.get_eq_getElem] at hgi hgj
    have hij : i ≠ j := by
      intro heq; subst heq; rw [hgi] at hgj
      exact absurd (congrArg Sigma.fst hgj) (by simp)
    rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
    · -- backward at i, forward at j, i < j: use capacitySegmentDupPerm at j
      left; right; left
      unfold capacitySegmentDupPerm
      refine ⟨⟨j, hj⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO', sI, hgj, rfl⟩, ?_⟩
      right; right; left
      exact ⟨⟨i, hi⟩, Nat.le_of_lt h_lt, sO, sI, hgi, rfl⟩
    · -- backward at i, forward at j, j < i: use capacitySegmentDupPermInv at i
      left; right; right
      unfold capacitySegmentDupPermInv
      refine ⟨⟨i, hi⟩, CanonicalSpongeState.capacitySegment sI, ⟨sO, sI, hgi, rfl⟩, ?_⟩
      right; left
      exact ⟨⟨j, hj⟩, h_lt, sO', sI, hgj, rfl⟩

/-- CO25 Lemma 5.10 — Paper-facing helper.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0`, then the exact paper-form
`E_prp(tr)` does not hold. -/
lemma not_collisionPerm_of_not_combined
    (hTrace : PaperTraceConsistent trace)
    (h : ¬ E trace) : ¬ E_prp trace := by
  intro hprp
  rcases hprp with hff | hbb | hfb | hbf
  · exact (not_collisionPermStaged_of_not_combined (trace := trace) h) (Or.inl hff)
  · exact (not_collisionPermStaged_of_not_combined (trace := trace) h) (Or.inr (Or.inl hbb))
  · rcases hTrace with ⟨hFwdBwd, _⟩
    rcases hfb with ⟨stateIn, stateOut, stateIn', hm1, hm2, hne⟩
    exact hne (hFwdBwd stateIn stateOut stateIn' hm1 hm2)
  · rcases hTrace with ⟨_, hBwdFwd⟩
    rcases hbf with ⟨stateOut, stateIn, stateOut', hm1, hm2, hne⟩
    exact hne (hBwdFwd stateOut stateIn stateOut' hm1 hm2)

/- Core Section 5.6 predicates, written in a paper-facing style. -/

/-- CO25 Definition 5.11 — Core of event `E_inv(tr, s)`.
Checks whether the trace `trace` contains a `p⁻¹`-entry whose output capacity segment equals
that of `state`.  Used to detect that a sponge state `s` was reached by an inversion query
(Eq. 35–37). -/
def invCore (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  ∃ stateOut stateIn : CanonicalSpongeState U,
    ⟨.inr (.inr stateOut), stateIn⟩ ∈ trace ∧
      stateIn.capacitySegment = state.capacitySegment

/-- CO25 Definition 5.11 — Event `E_inv(tr, s)`.
`E_inv(tr, s)` holds if the query-answer trace `tr` contains a `p⁻¹`-entry that produces a
state whose capacity segment matches that of `s`.  In the BackTrack construction, this means
some index list `J^{(k)} ∈ 𝒥_BT(tr, s)` was constructed using `p⁻¹` (Eq. 35).
Lemma 5.12 shows `E(tr) = 0 → E_inv(tr, s) = 0`. -/
abbrev E_inv
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  invCore trace state

/-- CO25 Definition 5.13 — Core of event `E_fork(tr, s)`.
Checks whether `|𝒮_BT(tr, s)| > 1`, i.e., there is a collision for `h` or `p`:
- Two `p`-entries with the same input but different outputs (capacity-segment collision of two
  `p`-outputs, Eq. 39).
- Two `p⁻¹`-entries with the same input but different outputs (similar collision for `p⁻¹`).
The `_state` argument is present for uniformity with the other `*Core` predicates but is
currently unused. -/
def forkCore (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (_state : CanonicalSpongeState U) : Prop :=
  (∃ stateIn stateOut1 stateOut2 : CanonicalSpongeState U,
    stateOut1 ≠ stateOut2 ∧
      ⟨.inr (.inl stateIn), stateOut1⟩ ∈ trace ∧
      ⟨.inr (.inl stateIn), stateOut2⟩ ∈ trace)
  ∨
  (∃ stateOut stateIn1 stateIn2 : CanonicalSpongeState U,
    stateIn1 ≠ stateIn2 ∧
      ⟨.inr (.inr stateOut), stateIn1⟩ ∈ trace ∧
      ⟨.inr (.inr stateOut), stateIn2⟩ ∈ trace)

/-- CO25 Definition 5.13 — Event `E_fork(tr, s)`.
`E_fork(tr, s)` holds if there is a capacity-segment collision for `h` or `p` in the trace,
i.e., `|𝒮_BT(tr, s)| > 1` (Eqs. 38–40).  Lemma 5.14 shows `E(tr) = 0 → E_fork(tr, s) = 0`. -/
abbrev E_fork
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  forkCore trace state

/-- CO25 Definition 5.15 — Core of event `E_time_h(tr, s)`.
The query to `h` is out of order: there exists an index list `J^{(k)}` in `𝒥_BT(tr, s)` with
`j_h^{(k)} > j_0^{(k)}`, i.e., the `h`-query comes after the first `p`-query (Eq. 41). -/
def outOfOrderHashCore (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (_state : CanonicalSpongeState U) : Prop :=
  ∃ jh : Fin trace.length, ∃ jp : Fin trace.length,
    jp < jh ∧
      ∃ stmt : StmtIn, ∃ capSeg : Vector U SpongeSize.C,
        List.get trace jh = ⟨.inl stmt, capSeg⟩ ∧
        ∃ stateIn stateOut : CanonicalSpongeState U,
          List.get trace jp = ⟨.inr (.inl stateIn), stateOut⟩ ∧
            stateIn.capacitySegment = capSeg

/-- CO25 Definition 5.15 — Event `E_time_h(tr, s)`.
The query to `h` is out of order (Eq. 41):
∃ J^{(k)} ∈ 𝒥_BT(tr, s) with `j_h^{(k)} > j_0^{(k)}`. -/
abbrev E_time_h
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  outOfOrderHashCore trace state

/-- CO25 Definition 5.15 — Core of event `E_time_p(tr, s)`.
A query to `p` is out of order: there exist indices `j' < j` in the trace such that
`tr_j = (p, s_mid, s_out)` and `tr_{j'} = (p, s_in, s_mid)`, i.e., a later `p`-query feeds
the output of an earlier one out of the expected sponge order (Eq. 42). -/
def outOfOrderPermCore (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (_state : CanonicalSpongeState U) : Prop :=
  ∃ j : Fin trace.length, ∃ j' : Fin trace.length,
    j' < j ∧
      ∃ sIn sMid sOut : CanonicalSpongeState U,
        List.get trace j = ⟨.inr (.inl sMid), sOut⟩ ∧
          List.get trace j' = ⟨.inr (.inl sIn), sMid⟩

/-- CO25 Definition 5.15 — Event `E_time_p(tr, s)`.
A query to `p` is out of order (Eq. 42):
∃ J^{(k)} ∈ 𝒥_BT(tr, s), ι ∈ [m_k − 1] with `j_{ι−1}^{(k)} > j_ι^{(k)}`. -/
abbrev E_time_p
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  outOfOrderPermCore trace state

/-- CO25 Definition 5.15 — Event `E_time(tr, s)`.
`E_time(tr, s) := E_time_h(tr, s) ∨ E_time_p(tr, s)`: checks if any index list
`J^{(k)} ∈ 𝒥_BT(tr, s)` is out of order (either the `h`-query or some `p`-query).
Lemma 5.16 shows `E(tr) = 0 → E_time(tr, s) = 0`. -/
abbrev E_time
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time_h (StmtIn := StmtIn) (U := U) trace state
    ∨ E_time_p (StmtIn := StmtIn) (U := U) trace state

/-- CO25 Definition 5.11 — Alias `E_inv_paper(tr, s)`.
Paper-facing alias for `E_inv`; no staging conjunction. -/
abbrev E_inv_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_inv (StmtIn := StmtIn) (U := U) trace state

/-- CO25 Definition 5.13 — Alias `E_fork_paper(tr, s)`.
Paper-facing alias for `E_fork`; no staging conjunction. -/
abbrev E_fork_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_fork (StmtIn := StmtIn) (U := U) trace state

/-- CO25 Definition 5.15 — Alias `E_time_h_paper(tr, s)`.
Paper-facing alias for `E_time_h`; no staging conjunction. -/
abbrev E_time_h_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time_h (StmtIn := StmtIn) (U := U) trace state

/-- CO25 Definition 5.15 — Alias `E_time_p_paper(tr, s)`.
Paper-facing alias for `E_time_p`; no staging conjunction. -/
abbrev E_time_p_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time_p (StmtIn := StmtIn) (U := U) trace state

/-- CO25 Definition 5.15 — Alias `E_time_paper(tr, s)`.
Paper-facing alias for `E_time`; no staging conjunction. -/
abbrev E_time_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time (StmtIn := StmtIn) (U := U) trace state

/-- CO25 Lemma 5.10 — Paper-facing.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0` then `E_prp(tr) = 0`. -/
lemma lemma_5_10 (hTrace : PaperTraceConsistent trace) (h : ¬ E trace) : ¬ E_prp trace :=
  not_collisionPerm_of_not_combined (trace := trace) hTrace h

/-- CO25 §5.6 — Support-level paper trace consistency.
All traces in the support of `traceDist` satisfy `PaperTraceConsistent`, i.e., the well-formedness
side condition of Definition 5.9 holds almost-surely. -/
def paperTraceConsistentOnSupport
    (traceDist : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U))) : Prop :=
  ∀ tr ∈ support traceDist, PaperTraceConsistent (StmtIn := StmtIn) (U := U) tr

/-- CO25 §5.6 — No backward `p⁻¹` entries in the base trace.
`NoBackwardInBaseTrace trace` holds if the base trace `tr̄` contains no `p⁻¹`-entries at all.
This is a sufficient condition for `PaperTraceConsistent` (see
`paperTraceConsistent_of_noBackwardInBaseTrace`). -/
def NoBackwardInBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∀ stateOut stateIn, ⟨.inr (.inr stateOut), stateIn⟩ ∉ baseTrace

/-- CO25 §5.6 — No-backward implies paper trace consistency.
If the base trace contains no `p⁻¹`-entries, then `PaperTraceConsistent` holds vacuously. -/
lemma paperTraceConsistent_of_noBackwardInBaseTrace
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hNoBwd : NoBackwardInBaseTrace (StmtIn := StmtIn) (U := U) trace) :
    PaperTraceConsistent (StmtIn := StmtIn) (U := U) trace := by
  dsimp [PaperTraceConsistent, NoBackwardInBaseTrace] at *
  constructor
  · intro stateIn stateOut stateIn' _ hmBwd
    exact False.elim (hNoBwd stateOut stateIn' hmBwd)
  · intro stateOut stateIn stateOut' hmBwd _
    exact False.elim (hNoBwd stateOut stateIn hmBwd)

/-- CO25 §5.6 — Support-level no-backward condition.
All traces in the support of `traceDist` have no `p⁻¹`-entries in the base trace. -/
def noBackwardInBaseTraceOnSupport
    (traceDist : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U))) : Prop :=
  ∀ tr ∈ support traceDist, NoBackwardInBaseTrace (StmtIn := StmtIn) (U := U) tr

/-- CO25 §5.6 — Support-level no-backward implies support-level paper consistency.
If all traces in the support have no `p⁻¹`-entries in the base trace, then all traces in the
support satisfy `PaperTraceConsistent`. -/
lemma paperTraceConsistentOnSupport_of_noBackwardInBaseTraceOnSupport
    {traceDist : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U))}
    (hNoBwd :
      noBackwardInBaseTraceOnSupport (StmtIn := StmtIn) (U := U) traceDist) :
    paperTraceConsistentOnSupport (StmtIn := StmtIn) (U := U) traceDist := by
  intro tr hMem
  exact paperTraceConsistent_of_noBackwardInBaseTrace
    (StmtIn := StmtIn) (U := U) (hNoBwd tr hMem)

section ConcreteSection58Instantiations

variable {StmtOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {codec : Codec pSpec U} [DecidableEq StmtIn] [DecidableEq U]
  [SampleableType U]
  {T_H : Type}
  {T_P : Type}
  [DuplexSpongeFS.Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [DuplexSpongeFS.Section52.LawfulTraceTable T_P
    (CanonicalSpongeState U) (CanonicalSpongeState U)]

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
`(statement, proof)` pair.  Returns the optional verifier output. -/
def lemma5_8TraceExperiment
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) := do
  let _ : Codec pSpec U := codec
  let ⟨stmtIn, messages⟩ ← maliciousProver
  ((Verifier.duplexSpongeFiatShamir
      (oSpec := []ₒ) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) V).run
    stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run

/-- CO25 Lemma 5.8 — Left-hand-side trace distribution.
Real DS execution under the explicit `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` implementation.
Returns the DS query-answer trace of the combined `(P̃ ‖ V)` execution. -/
noncomputable def lemma5_8RealTraceDist
    {σReal : Type}
    (initReal : ProbComp σReal)
    (implReal : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σReal ProbComp))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  lemma5_8ProjectedTraceDistOfConcreteExperiment (StmtIn := StmtIn) (U := U)
    initReal implReal
    (lemma5_8TraceExperiment
      (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)

/-- CO25 Lemma 5.8 — Right-hand-side trace distribution.
Simulator execution under `g ← 𝒟_Σ(λ, n)` with `D2SQuery` as the oracle implementation.
Returns the DS query-answer trace of the combined `(P̃ ‖ V)` execution. -/
noncomputable def lemma5_8SigmaTraceDist
    (simParams : DuplexSpongeFS.D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (onSimAbort :
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain) →
        DuplexSpongeFS.D2SQueryState (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) →
          (duplexSpongeChallengeOracle StmtIn U).Range q ×
            DuplexSpongeFS.D2SQueryState
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
      DuplexSpongeFS.d2sQueryAbortFallback
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  lemma5_8ProjectedTraceDistOfConcreteExperiment (StmtIn := StmtIn) (U := U)
    (pure default)
    (DuplexSpongeFS.d2sQueryImplCoreProb
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec)
      (unitImpl := DuplexSpongeFS.d2sUnitSampleImpl (U := U))
      (params := simParams)
      (onAbort := onSimAbort))
    (lemma5_8TraceExperiment
      (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (codec := codec) V maliciousProver)

/-- CO25 §5.6 Lemma 5.8 — Support-level paper trace consistency for the real experiment.
All traces in the support of the real `𝒟_𝔖` trace distribution satisfy `PaperTraceConsistent`. -/
def lemma5_8RealTraceConsistentOnSupport
    {σReal : Type}
    (initReal : ProbComp σReal)
    (implReal : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σReal ProbComp))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) : Prop :=
  paperTraceConsistentOnSupport (StmtIn := StmtIn) (U := U)
    (lemma5_8RealTraceDist
      (StmtIn := StmtIn) (StmtOut := StmtOut)
      (n := n) (pSpec := pSpec) (U := U) (codec := codec)
      initReal implReal V maliciousProver)

/-- CO25 §5.6 Lemma 5.8 — Support-level paper trace consistency for the simulator experiment.
All traces in the support of the `𝒟_Σ` trace distribution satisfy `PaperTraceConsistent`. -/
def lemma5_8SigmaTraceConsistentOnSupport
    (simParams : DuplexSpongeFS.D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (onSimAbort :
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain) →
        DuplexSpongeFS.D2SQueryState (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) →
          (duplexSpongeChallengeOracle StmtIn U).Range q ×
            DuplexSpongeFS.D2SQueryState
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
      DuplexSpongeFS.d2sQueryAbortFallback
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)) : Prop :=
  paperTraceConsistentOnSupport (StmtIn := StmtIn) (U := U)
    (lemma5_8SigmaTraceDist
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (StmtOut := StmtOut)
      (n := n) (pSpec := pSpec) (U := U) (codec := codec)
      simParams V maliciousProver onSimAbort)

/-- CO25 Lemma 5.8 — Bad-event probability bound.
For every `(tₕ, tₚ, tₚᵢ)`-query malicious prover P̃ with `tₚ ≥ L` (where `L` is the total number
of verifier permutation queries),

```
max{ Pr[E(tr_P̃ ‖ tr_V) | 𝒟_𝔖], Pr[E(tr_P̃ ‖ tr_V) | 𝒟_Σ] }
  ≤ (7·T² − 3·T) / (2·|Σ|^c)
```

where `T = tₕ + 1 + tₚ + L + tₚᵢ`.  Bounds both the real `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` and the
simulator `g ← 𝒟_Σ(λ, n)` with `D2SQuery` experiments. -/
theorem lemma_5_8
    [Fintype U]
    {σReal : Type}
    (initReal : ProbComp σReal)
    (implReal : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σReal ProbComp))
    (simParams : DuplexSpongeFS.D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) (codec := codec))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (onSimAbort :
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain) →
        DuplexSpongeFS.D2SQueryState (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) →
          (duplexSpongeChallengeOracle StmtIn U).Range q ×
            DuplexSpongeFS.D2SQueryState
              (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U) :=
      DuplexSpongeFS.d2sQueryAbortFallback
        (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
    (tₕ tₚ tₚᵢ : ℕ)
    (hMaliciousBound : -- `(tₕ, tₚ, tₚᵢ)`-query bound prover
      IsLemma5_8QueryBound
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        maliciousProver tₕ tₚ tₚᵢ)
    (hTp : tₚ ≥ pSpec.totalNumPermQueries) :
    max
        (Pr[fun tr => BadEventDS.E tr |
          lemma5_8RealTraceDist
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) (codec := codec)
            initReal implReal V maliciousProver])
        (Pr[fun tr => BadEventDS.E tr |
          lemma5_8SigmaTraceDist
            (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) (codec := codec)
            simParams V maliciousProver onSimAbort])
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries) := by
  let _ := hMaliciousBound
  let _ := hTp
  sorry

end ConcreteSection58Instantiations

/-- CO25 Lemma 5.10 — Instantiated from support-level experiment invariant.
If all traces in the support satisfy `PaperTraceConsistent` and a specific trace `tr` is in the
support, then `¬ E(tr) → ¬ E_prp(tr)`. -/
lemma lemma_5_10_of_mem_support
    {traceDist : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U))}
    (hCons : paperTraceConsistentOnSupport (StmtIn := StmtIn) (U := U) traceDist)
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hMem : tr ∈ support traceDist)
    (h : ¬ E (trace := tr)) :
    ¬ E_prp (trace := tr) := by
  exact lemma_5_10 (trace := tr) (hTrace := hCons tr hMem) h

/-- CO25 Lemma 5.12 — If `E(tr) = 0` then `E_inv(tr, s) = 0`. -/
lemma lemma_5_12 (h : ¬ E trace) : ¬ E_inv_paper trace state := by
  sorry

/-- CO25 Lemma 5.14 — If `E(tr) = 0` then `E_fork(tr, s) = 0`. -/
lemma lemma_5_14 (h : ¬ E trace) : ¬ E_fork_paper trace state := by
  sorry

/-- CO25 Lemma 5.16 — If `E(tr) = 0` then `E_time(tr, s) = 0`. -/
lemma lemma_5_16 (h : ¬ E trace) : ¬ E_time_paper trace state := by
  sorry

end BadEventDS

end DuplexSpongeFS

end QueryLog

end OracleSpec

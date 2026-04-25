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

/-- The definition of a redundant entry in a duplex sponge challenge oracle trace (Definition 5.5),
  used in the analysis of bad events

TODO: refactor this into a combination of simpler properties? -/
def redundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  redundantEntryDSPrefix (log.take idx.1) log[idx]

/-- A duplex sponge challenge oracle trace has no redundant entries if no entry is redundant -/
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

/-- Procedure to remove all redundant queries from the duplex sponge query-answer trace -/
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

/-- Definition 5.7 Eq. (23), with all five prior-entry branches explicit:
`h` output, `p` output, `p⁻¹` output, `p` input, `p⁻¹` input. -/
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

/-- There exists an output capacity segment in the base trace tr¯ that appears as a prior
input/output capacity segment. This breaks down into one of the predicates above -/
def capacitySegmentDup : Prop :=
  capacitySegmentDupHash trace ∨ capacitySegmentDupPerm trace ∨ capacitySegmentDupPermInv trace

alias E_dup := capacitySegmentDup

/- The same query to `p` leads to different answers, or there are inconsistent queries across `p`
and `p⁻¹` -/
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

def combined : Prop :=
  capacitySegmentDup trace ∨ notFunction trace

alias E := combined

/-- Lemma 5.8 bound on the bad-event probability in either experiment. -/
noncomputable def lemma5_8Bound (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- Run a concrete DS experiment under an oracle implementation and return its full DS trace. -/
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

def collisionFwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateIn' stateOut,
    ⟨.inr <|.inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <|.inl stateIn', stateOut⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

def collisionBwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateOut stateOut' stateIn,
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

/-- Staged mixed-collision predicate used by the current `lemma_5_10` proof chain. -/
def collisionFwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateOut',
    ⟨.inr <| .inl stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_p_pinv := collisionFwdBwd

/-- Staged mixed-collision predicate used by the current `lemma_5_10` proof chain. -/
def collisionBwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p := collisionBwdFwd

def collisionPerm : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace ∨ collisionFwdBwd trace ∨ collisionBwdFwd trace

/-- Staged `E_prp` surface kept for compatibility with existing proved helper chains. -/
alias E_prp_staged := collisionPerm

/-- Definition 5.9 Item 3 in exact paper shape (`E_{col,p,p^{-1}}`). -/
def collisionFwdBwdPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateIn',
    ⟨.inr <| .inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut, stateIn'⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p_pinv_paper := collisionFwdBwdPaper

/-- Definition 5.9 Item 4 in exact paper shape (`E_{col,p^{-1},p}`). -/
def collisionBwdFwdPaper : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateOut stateIn stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateIn, stateOut'⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p_paper := collisionBwdFwdPaper

/-- Definition 5.9 in exact paper form, preserving `p,p⁻¹` and `p⁻¹,p` mixed collisions. -/
def collisionPermPaper : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace
    ∨ collisionFwdBwdPaper trace ∨ collisionBwdFwdPaper trace

alias E_prp := collisionPermPaper

alias E_prp_paper := collisionPermPaper

/--
Paper-level `(h,p,p⁻¹)` trace consistency on the base trace `tr̄`:
if both `p` and `p⁻¹` entries appear on the same middle state, they must agree on the opposite
endpoint.

This is the explicit well-formedness side condition needed for the Section 5.6 → Definition 5.9
bridge over arbitrary Lean traces.
-/
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

/--
Paper-facing helper for Lemma 5.10:
for a well-formed `(h,p,p⁻¹)` trace, if `E(tr) = 0`,
then the exact paper-form `E_prp(tr)` does not hold.
-/
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

def invCore (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  ∃ stateOut stateIn : CanonicalSpongeState U,
    ⟨.inr (.inr stateOut), stateIn⟩ ∈ trace ∧
      stateIn.capacitySegment = state.capacitySegment

/-- Definition 5.11 paper-form event `E_inv(tr,s)`. -/
abbrev E_inv
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  invCore trace state

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

/-- Definition 5.13 paper-form event `E_fork(tr,s)`. -/
abbrev E_fork
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  forkCore trace state

def outOfOrderHashCore (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (_state : CanonicalSpongeState U) : Prop :=
  ∃ jh : Fin trace.length, ∃ jp : Fin trace.length,
    jp < jh ∧
      ∃ stmt : StmtIn, ∃ capSeg : Vector U SpongeSize.C,
        List.get trace jh = ⟨.inl stmt, capSeg⟩ ∧
        ∃ stateIn stateOut : CanonicalSpongeState U,
          List.get trace jp = ⟨.inr (.inl stateIn), stateOut⟩ ∧
            stateIn.capacitySegment = capSeg

/-- Definition 5.15 paper-form event `E_time_h(tr,s)`. -/
abbrev E_time_h
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  outOfOrderHashCore trace state

def outOfOrderPermCore (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (_state : CanonicalSpongeState U) : Prop :=
  ∃ j : Fin trace.length, ∃ j' : Fin trace.length,
    j' < j ∧
      ∃ sIn sMid sOut : CanonicalSpongeState U,
        List.get trace j = ⟨.inr (.inl sMid), sOut⟩ ∧
          List.get trace j' = ⟨.inr (.inl sIn), sMid⟩

/-- Definition 5.15 paper-form event `E_time_p(tr,s)`. -/
abbrev E_time_p
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  outOfOrderPermCore trace state

/-- Definition 5.15 paper-form event `E_time(tr,s)`. -/
abbrev E_time
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time_h (StmtIn := StmtIn) (U := U) trace state
    ∨ E_time_p (StmtIn := StmtIn) (U := U) trace state

/-- Definition 5.11 paper-form event `E_inv(tr,s)` (without staging conjunction). -/
abbrev E_inv_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_inv (StmtIn := StmtIn) (U := U) trace state

/-- Definition 5.13 paper-form event `E_fork(tr,s)` (without staging conjunction). -/
abbrev E_fork_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_fork (StmtIn := StmtIn) (U := U) trace state

/-- Definition 5.15 paper-form event `E_time_h(tr,s)` (without staging conjunction). -/
abbrev E_time_h_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time_h (StmtIn := StmtIn) (U := U) trace state

/-- Definition 5.15 paper-form event `E_time_p(tr,s)` (without staging conjunction). -/
abbrev E_time_p_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time_p (StmtIn := StmtIn) (U := U) trace state

/-- Definition 5.15 paper-form event `E_time(tr,s)` (without staging conjunction). -/
abbrev E_time_paper
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) : Prop :=
  E_time (StmtIn := StmtIn) (U := U) trace state

/--
Lemma 5.10 (paper-facing):
for a well-formed `(h,p,p⁻¹)` trace, if `E(tr) = 0` then `E_prp(tr) = 0`.
-/
lemma lemma_5_10 (hTrace : PaperTraceConsistent trace) (h : ¬ E trace) : ¬ E_prp trace :=
  not_collisionPerm_of_not_combined (trace := trace) hTrace h

/--
Support-level packaging for the paper trace consistency side condition:
all traces in the support satisfy `PaperTraceConsistent`.
-/
def paperTraceConsistentOnSupport
    (traceDist : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U))) : Prop :=
  ∀ tr ∈ support traceDist, PaperTraceConsistent (StmtIn := StmtIn) (U := U) tr

/--
No backward `p⁻¹` entries occur in the base trace.

This is a sufficient condition for `PaperTraceConsistent`.
-/
def NoBackwardInBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∀ stateOut stateIn, ⟨.inr (.inr stateOut), stateIn⟩ ∉ baseTrace

/--
If the base trace has no backward entries, then the paper trace-consistency predicate holds
trivially.
-/
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

/--
Support-level packaging of `NoBackwardInBaseTrace`.
-/
def noBackwardInBaseTraceOnSupport
    (traceDist : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U))) : Prop :=
  ∀ tr ∈ support traceDist, NoBackwardInBaseTrace (StmtIn := StmtIn) (U := U) tr

/--
Support-level no-backward condition implies support-level paper consistency.
-/
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
  [HasMessageSize pSpec] [HasChallengeSize pSpec] [DecidableEq StmtIn] [DecidableEq U]
  [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]
  [SampleableType U]
  {T_H : Type}
  {T_P : Type}
  [DuplexSpongeFS.Section52.LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
  [DuplexSpongeFS.Section52.LawfulTraceTable T_P
    (CanonicalSpongeState U) (CanonicalSpongeState U)]

/-- Per-oracle query budget map for a Section 5.6 malicious prover:
- `tₕ` bounds `h` queries,
- `tₚ` bounds forward `p` queries,
- `tₚᵢ` bounds backward `p⁻¹` queries. -/
def lemma5_8QueryBudget (tₕ tₚ tₚᵢ : ℕ) :
    (duplexSpongeChallengeOracle StmtIn U).Domain → ℕ
  | .inl _ => tₕ
  | .inr (.inl _) => tₚ
  | .inr (.inr _) => tₚᵢ

/-- Semantic `(tₕ, tₚ, tₚᵢ)` query bound for a malicious prover in Lemma 5.8. -/
abbrev IsLemma5_8QueryBound
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages))
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  OracleComp.IsPerIndexQueryBound maliciousProver
    (lemma5_8QueryBudget (StmtIn := StmtIn) (U := U) tₕ tₚ tₚᵢ)

/-- Project away the impossible empty-oracle side from a `[]ₒ + DS` trace log. -/
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

/-- Run a concrete Section 5.6 experiment over `[]ₒ + DS` and keep only the DS trace. -/
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

/-- The Section 5.6 experiment shape used in both sides of Lemma 5.8:
run the malicious prover, then run the DSFS verifier on the resulting statement/proof. -/
def lemma5_8TraceExperiment
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) := do
  let ⟨stmtIn, messages⟩ ← maliciousProver
  ((Verifier.duplexSpongeFiatShamir
      (oSpec := []ₒ) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) V).run
    stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run

/-- Left-hand-side Section 5.6 trace distribution:
real DS execution under the explicit `(h, p, p⁻¹)` implementation. -/
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
      (pSpec := pSpec) (U := U) V maliciousProver)

/-- Right-hand-side Section 5.6 trace distribution:
simulator execution under `g <- 𝒟_Σ(λ, n)` with `D2SQuery`. -/
noncomputable def lemma5_8SigmaTraceDist
    (simParams : DuplexSpongeFS.D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
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
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U)
      (unitImpl := DuplexSpongeFS.d2sUnitSampleImpl (U := U))
      (params := simParams)
      (onAbort := onSimAbort))
    (lemma5_8TraceExperiment
      (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) V maliciousProver)

/-- Support-level paper trace consistency for the real Section 5.6 experiment. -/
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
      (n := n) (pSpec := pSpec) (U := U)
      initReal implReal V maliciousProver)

/-- Support-level paper trace consistency for the `Σ` Section 5.6 experiment. -/
def lemma5_8SigmaTraceConsistentOnSupport
    (simParams : DuplexSpongeFS.D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
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
      (n := n) (pSpec := pSpec) (U := U)
      simParams V maliciousProver onSimAbort)

/--
Lemma 5.8 (paper-facing): for every malicious prover with explicit
`(tₕ, tₚ, tₚᵢ)` query budget, compare the two concrete Section 5.6 experiments:
- the real duplex-sponge execution under `(h, p, p⁻¹) <- 𝒟_𝔖(λ, n)`;
- the simulator execution under `g <- 𝒟_Σ(λ, n)` with `D2SQuery`.
-/
theorem lemma_5_8
    [Fintype U]
    {σReal : Type}
    (initReal : ProbComp σReal)
    (implReal : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σReal ProbComp))
    (simParams : DuplexSpongeFS.D2SQueryParams
      (StmtIn := StmtIn) (n := n) (pSpec := pSpec) (U := U))
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
            (n := n) (pSpec := pSpec) (U := U)
            initReal implReal V maliciousProver])
        (Pr[fun tr => BadEventDS.E tr |
          lemma5_8SigmaTraceDist
            (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U)
            simParams V maliciousProver onSimAbort])
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries) := by
  let _ := hMaliciousBound
  let _ := hTp
  sorry

end ConcreteSection58Instantiations

/--
Lemma 5.10 instantiated from a support-level experiment invariant.
-/
lemma lemma_5_10_of_mem_support
    {traceDist : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U))}
    (hCons : paperTraceConsistentOnSupport (StmtIn := StmtIn) (U := U) traceDist)
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hMem : tr ∈ support traceDist)
    (h : ¬ E (trace := tr)) :
    ¬ E_prp (trace := tr) := by
  exact lemma_5_10 (trace := tr) (hTrace := hCons tr hMem) h

/-- Lemma 5.12 (paper-facing): if `E(tr) = 0` then `E_inv(tr, s) = 0`. -/
lemma lemma_5_12 (h : ¬ E trace) : ¬ E_inv_paper trace state := by
  sorry

/-- Lemma 5.14 (paper-facing): if `E(tr) = 0` then `E_fork(tr, s) = 0`. -/
lemma lemma_5_14 (h : ¬ E trace) : ¬ E_fork_paper trace state := by
  sorry

/-- Lemma 5.16 (paper-facing): if `E(tr) = 0` then `E_time(tr, s) = 0`. -/
lemma lemma_5_16 (h : ¬ E trace) : ¬ E_time_paper trace state := by
  sorry

end BadEventDS

end DuplexSpongeFS

end QueryLog

end OracleSpec

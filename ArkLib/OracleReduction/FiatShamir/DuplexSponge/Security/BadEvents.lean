/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
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

#check QueryLog

namespace OracleSpec

namespace QueryLog

section
-- WIP defining more general properties for query log

variable {ι : Type*} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

/-- A query tuple `(i, q, r)` is redundant in a query log if it appears more than once -/
def redundantQuery (log : QueryLog spec) (i : ι) (q : spec.domain i) (r : spec.range i) : Prop :=
  (log.getQ i).count (q, r) > 1

def existPriorSameQuery (log : QueryLog spec) (idx : Fin log.length) : Prop :=
  ∃ j' < idx, log[j'] = log[idx]

end

section DuplexSpongeFS

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- The definition of a redundant entry in a duplex sponge challenge oracle trace (Definition 5.5),
  used in the analysis of bad events

TODO: refactor this into a combination of simpler properties? -/
def redundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  match log[idx] with
  /- If it's a hash query, it's redundant if there is a prior hash query with the same query-answer
     pair -/
  | ⟨.inl _, ⟨stmt, state⟩⟩ => ∃ j' < idx, log[j'] = ⟨.inl _, ⟨stmt, state⟩⟩
  /- If it's a permutation query (`dir ∈ {Fwd, Bwd}`), it's redundant if there is a prior
    permutation query with either:
    - the same direction and input-output pair, or
    - the opposite direction and output-input pair -/
  | ⟨.inr .Fwd, stateIn, stateOut⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr .Fwd, stateIn, stateOut⟩ ∨ log[j'] = ⟨.inr .Bwd, stateOut, stateIn⟩
  | ⟨.inr .Bwd, stateOut, stateIn⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr .Bwd, stateOut, stateIn⟩ ∨ log[j'] = ⟨.inr .Fwd, stateIn, stateOut⟩

/-- A duplex sponge challenge oracle trace has no redundant entries if no entry is redundant -/
def NoRedundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ idx : Fin log.length, ¬ log.redundantEntryDS idx

/-- Procedure to remove all redundant queries from the duplex sponge query-answer trace -/
def removeRedundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) | log.NoRedundantEntryDS} :=
  sorry

namespace BadEventDS

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)

/-! Fist, we define the main bad event, which consists of two main conditions:
1. No duplicate in the capacity segment (for the base trace that removed redundant entries)
2. The same query to `p` leads to different answers, or there are inconsistent queries across `p`
and `p⁻¹` -/

/- NOTE: the paper write `∃ j > 0`, which can be confusing since we don't know whether the intended
indexing is from 0 or from 1. We assume they mean from 1, and since indexing here is from 0, we just
write `∃ j`. -/

def capacitySegmentDupHash : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    ∃ stmt : StmtIn, baseTrace[j] = ⟨.inl (), stmt, capSeg⟩ ∧
      ∃ j' < j,
        ∃ stmt', baseTrace[j'] = ⟨.inl (), stmt', capSeg⟩ ∨
        (∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr .Fwd, stateIn1, stateOut1⟩
          ∧ stateOut1.capacitySegment = capSeg) ∨
        (∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr .Bwd, stateOut2, stateIn2⟩
          ∧ stateIn2.capacitySegment = capSeg) ∨
        (∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr .Fwd, stateIn3, stateOut3⟩
          ∧ stateIn3.capacitySegment = capSeg) ∨
        (∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr .Bwd, stateOut4, stateIn4⟩
          ∧ stateOut4.capacitySegment = capSeg)

alias E_h := capacitySegmentDupHash

def capacitySegmentDupPerm : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr .Fwd, stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl (), stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr .Fwd, stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr .Bwd, stateOut2, stateIn2⟩ ∧
          stateIn2.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr .Fwd, stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr .Bwd, stateOut4, stateIn4⟩ ∧
          stateOut4.capacitySegment = capSeg)
      )

alias E_p := capacitySegmentDupPerm

def capacitySegmentDupPermInv : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr .Bwd, stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
      (
        (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl (), stmt', capSeg⟩) ∨
        (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr .Fwd, stateIn1, stateOut1⟩ ∧
          stateOut1.capacitySegment = capSeg) ∨
        (∃ j' < j, ∃ stateIn2 stateOut2, baseTrace[j'] = ⟨.inr .Bwd, stateOut2, stateIn2⟩ ∧
          stateIn2.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr .Fwd, stateIn3, stateOut3⟩ ∧
          stateIn3.capacitySegment = capSeg) ∨
        (∃ j' ≤ j, ∃ stateIn4 stateOut4, baseTrace[j'] = ⟨.inr .Bwd, stateOut4, stateIn4⟩ ∧
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
  ∃ j : Fin baseTrace.length, ∃ stateIn _stateOut : CanonicalSpongeState U,
    baseTrace[j] = ⟨.inr .Fwd, stateIn, _stateOut⟩ ∧
      ∃ j' < j,
        ∃ stateOut1 : CanonicalSpongeState U, baseTrace[j'] = ⟨.inr .Fwd, stateIn, stateOut1⟩ ∨
        ∃ stateOut2 : CanonicalSpongeState U, baseTrace[j'] = ⟨.inr .Bwd, stateOut2, stateIn⟩

alias E_func := notFunction

def combined : Prop :=
  capacitySegmentDup trace ∨ notFunction trace

alias E := combined

/-! Then we define other bad events that don't hold (`= 0`)
if the combined event doesn't hold (`= 0`)
-/

def collisionFwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateIn' stateOut,
    (stateIn, stateOut) ∈ baseTrace.getQ (.inr .Fwd) ∧
    (stateIn', stateOut) ∈ baseTrace.getQ (.inr .Fwd) ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

def collisionBwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateOut stateOut' stateIn,
    (stateOut, stateIn) ∈ baseTrace.getQ (.inr .Bwd) ∧
    (stateOut', stateIn) ∈ baseTrace.getQ (.inr .Bwd) ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

def collisionFwdBwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateOut',
    (stateIn, stateOut) ∈ baseTrace.getQ (.inr .Fwd) ∧
    (stateOut', stateIn) ∈ baseTrace.getQ (.inr .Bwd) ∧
    stateOut ≠ stateOut'

alias E_col_p_pinv := collisionFwdBwd

def collisionBwdFwd : Prop :=
  let ⟨baseTrace, _⟩ := removeRedundantEntryDS trace
  ∃ stateIn stateOut stateOut',
    (stateIn, stateOut) ∈ baseTrace.getQ (.inr .Bwd) ∧
    (stateOut', stateIn) ∈ baseTrace.getQ (.inr .Fwd) ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p := collisionBwdFwd

def collisionPerm : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace ∨ collisionFwdBwd trace ∨ collisionBwdFwd trace

alias E_prp := collisionPerm

lemma not_collisionPerm_of_not_combined (h : ¬ E trace) : ¬ E_prp trace :=
  sorry

/- TODO: these events / predicates depend on the definition of backtracking sequence family and
indices -/

def inv : Prop :=
  -- NOTE: placeholder for now
  trace = [] ∧ state = 0

alias E_inv := inv

lemma not_inv_of_not_combined (h : ¬ E trace) : ¬ E_inv trace state :=
  sorry

def fork : Prop :=
  -- NOTE: placeholder for now
  trace = [] ∧ state = 0

alias E_fork := fork

lemma not_fork_of_not_combined (h : ¬ E trace) : ¬ E_fork trace state :=
  sorry


def outOfOrderHash : Prop :=
  -- NOTE: placeholder for now
  trace = [] ∧ state = 0

alias E_time_h := outOfOrderHash

def outOfOrderPerm : Prop :=
  -- NOTE: placeholder for now
  trace = [] ∧ state = 0

alias E_time_p := outOfOrderPerm

def outOfOrder : Prop :=
  outOfOrderHash trace state ∨ outOfOrderPerm trace state

alias E_time := outOfOrder

lemma not_outOfOrder_of_not_combined (h : ¬ E trace) : ¬ E_time trace state :=
  sorry

end BadEventDS

end DuplexSpongeFS

end QueryLog

end OracleSpec

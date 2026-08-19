/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Core

/-!
# Capacity Targets for Lemma 5.8 Fresh-Hit Bounds

This module provides the target readout lists that capture the "finitely many prior capacity slots"
that a fresh answer side could hit, simplifying the bad event probability proofs to match the paper.
-/

open OracleComp OracleSpec ProtocolSpec
open DuplexSpongeFS.DSTraceStorage

namespace DuplexSpongeFS
namespace BadEventDS

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-! ## Shared per-entry readouts -/

/-- The output capacity of base position `j` if it is a hash entry, else `none`. -/
def hashOutCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with | ⟨.inl _, out⟩ => some out | ⟨.inr _, _⟩ => none

/-- The queried statement at base position `j` if it is a hash entry, else `none`. -/
def hashQueryAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option StmtIn :=
  (bt[j]?).bind fun e => match e with | ⟨.inl stmt, _⟩ => some stmt | ⟨.inr _, _⟩ => none

/-- Output capacity of base position `j` if it is a forward-permutation entry. -/
def permOutCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inl _), sOut⟩ => some sOut.capacitySegment
    | _ => none

/-- Input capacity of base position `j` if it is a forward-permutation entry. -/
def permInCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inl sIn), _⟩ => some sIn.capacitySegment
    | _ => none

/-- Input state of base position `j` if it is a forward-permutation entry. -/
def permFwdInputAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (CanonicalSpongeState U) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inl sIn), _⟩ => some sIn
    | _ => none

/-- Range/preimage capacity of base position `j` if it is a backward-permutation entry. -/
def permInvRangeCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inr _), sIn⟩ => some sIn.capacitySegment
    | _ => none

/-- Domain/queried-output capacity of base position `j` if it is a backward-permutation entry. -/
def permInvDomainCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inr sOut), _⟩ => some sOut.capacitySegment
    | _ => none

/-- Queried output state of base position `j` if it is a backward-permutation entry. -/
def permBwdOutputAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (CanonicalSpongeState U) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inr sOut), _⟩ => some sOut
    | _ => none

/-- A forward input readout determines the capacity readout of that same domain, independently
of the entry's response. -/
lemma permInCapAt_eq_of_permFwdInputAt
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {sIn : CanonicalSpongeState U}
    (h : permFwdInputAt bt j = some sIn) :
    permInCapAt bt j = some sIn.capacitySegment := by
  unfold permFwdInputAt at h
  unfold permInCapAt
  cases hentry : bt[j]? with
  | none =>
      rw [hentry] at h
      simp only [Option.bind_none, reduceCtorEq] at h
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hentry] at h
          simp only [Option.bind_some, reduceCtorEq] at h
      | inr permDom =>
          cases permDom with
          | inl sIn' =>
              rw [hentry] at h
              simp only [Option.bind_some, Option.some.injEq] at h
              subst sIn'
              rfl
          | inr sOut =>
              rw [hentry] at h
              simp only [Option.bind_some, reduceCtorEq] at h

/-- A backward output readout determines the capacity readout of that same domain, independently
of the entry's response. -/
lemma permInvDomainCapAt_eq_of_permBwdOutputAt
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {sOut : CanonicalSpongeState U}
    (h : permBwdOutputAt bt j = some sOut) :
    permInvDomainCapAt bt j = some sOut.capacitySegment := by
  unfold permBwdOutputAt at h
  unfold permInvDomainCapAt
  cases hentry : bt[j]? with
  | none =>
      rw [hentry] at h
      simp only [Option.bind_none, reduceCtorEq] at h
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hentry] at h
          simp only [Option.bind_some, reduceCtorEq] at h
      | inr permDom =>
          cases permDom with
          | inl sIn =>
              rw [hentry] at h
              simp only [Option.bind_some, reduceCtorEq] at h
          | inr sOut' =>
              rw [hentry] at h
              simp only [Option.bind_some, Option.some.injEq] at h
              subst sOut'
              rfl

/-- A defined forward output-capacity readout comes from a forward query at that position. -/
lemma exists_permFwdInputAt_of_permOutCapAt_target
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {c : Vector U SpongeSize.C}
    (hout : permOutCapAt bt j = some c) :
    ∃ x : CanonicalSpongeState U, permFwdInputAt bt j = some x := by
  unfold permOutCapAt at hout
  unfold permFwdInputAt
  cases hbt : bt[j]? with
  | none =>
      rw [hbt] at hout
      simp only [Option.bind_none, reduceCtorEq] at hout
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hbt] at hout
          simp only [Option.bind_some, reduceCtorEq] at hout
      | inr permDom =>
          cases permDom with
          | inl sIn =>
              rw [hbt] at hout
              simp only [Option.bind_some, Option.some.injEq] at hout
              exact ⟨sIn, rfl⟩
          | inr sOut =>
              rw [hbt] at hout
              simp only [Option.bind_some, reduceCtorEq] at hout

/-- A defined inverse range-capacity readout comes from an inverse query at that position. -/
lemma exists_permBwdOutputAt_of_permInvRangeCapAt_target
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {c : Vector U SpongeSize.C}
    (hout : permInvRangeCapAt bt j = some c) :
    ∃ y : CanonicalSpongeState U, permBwdOutputAt bt j = some y := by
  unfold permInvRangeCapAt at hout
  unfold permBwdOutputAt
  cases hbt : bt[j]? with
  | none =>
      rw [hbt] at hout
      simp only [Option.bind_none, reduceCtorEq] at hout
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hbt] at hout
          simp only [Option.bind_some, reduceCtorEq] at hout
      | inr permDom =>
          cases permDom with
          | inl sIn =>
              rw [hbt] at hout
              simp only [Option.bind_some, reduceCtorEq] at hout
          | inr sOut =>
              rw [hbt] at hout
              simp only [Option.bind_some, Option.some.injEq] at hout
              exact ⟨sOut, rfl⟩

/-- A successful forward-input readout identifies the exact forward permutation entry at that
base position. -/
lemma exists_getElem?_permFwd_of_permFwdInputAt
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {sIn : CanonicalSpongeState U}
    (h : permFwdInputAt bt j = some sIn) :
    ∃ sOut : CanonicalSpongeState U, bt[j]? = some ⟨.inr (.inl sIn), sOut⟩ := by
  unfold permFwdInputAt at h
  cases hbt : bt[j]? with
  | none =>
      rw [hbt] at h
      simp only [Option.bind_none, reduceCtorEq] at h
  | some entry =>
      cases entry with
      | mk dom rng =>
          cases dom with
          | inl _stmt =>
              rw [hbt] at h
              simp only [Option.bind_some, reduceCtorEq] at h
          | inr q =>
              cases q with
              | inl sIn' =>
                  rw [hbt] at h
                  simp only [Option.bind_some, Option.some.injEq] at h
                  subst sIn'
                  exact ⟨rng, rfl⟩
              | inr _sOut =>
                  rw [hbt] at h
                  simp only [Option.bind_some, reduceCtorEq] at h

/-- A successful inverse-query-output readout identifies the exact inverse permutation entry at
that base position. -/
lemma exists_getElem?_permBwd_of_permBwdOutputAt
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {sOut : CanonicalSpongeState U}
    (h : permBwdOutputAt bt j = some sOut) :
    ∃ sIn : CanonicalSpongeState U, bt[j]? = some ⟨.inr (.inr sOut), sIn⟩ := by
  unfold permBwdOutputAt at h
  cases hbt : bt[j]? with
  | none =>
      rw [hbt] at h
      simp only [Option.bind_none, reduceCtorEq] at h
  | some entry =>
      cases entry with
      | mk dom rng =>
          cases dom with
          | inl _stmt =>
              rw [hbt] at h
              simp only [Option.bind_some, reduceCtorEq] at h
          | inr q =>
              cases q with
              | inl _sIn =>
                  rw [hbt] at h
                  simp only [Option.bind_some, reduceCtorEq] at h
              | inr sOut' =>
                  rw [hbt] at h
                  simp only [Option.bind_some, Option.some.injEq] at h
                  subst sOut'
                  exact ⟨rng, rfl⟩

/-- In a no-redundant base trace, a normalized permutation pair cannot occur at a strict earlier
position in either direction. -/
lemma noRedundant_perm_pair_not_prior
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hNoRedundant : hasNoRedundantEntries bt)
    {j j' : ℕ} (hj' : j' < j)
    {sIn sOut : CanonicalSpongeState U}
    (hj : bt[j]? = some ⟨.inr (.inl sIn), sOut⟩)
    (hjPrior : bt[j']? = some ⟨.inr (.inl sIn), sOut⟩ ∨
      bt[j']? = some ⟨.inr (.inr sOut), sIn⟩) :
    False := by
  rw [List.getElem?_eq_some_iff] at hj
  obtain ⟨hjLen, hjEq⟩ := hj
  have hPriorMem :
      (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          bt.take j ∨
        (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          bt.take j := by
    rcases hjPrior with hFwd | hBwd
    · rw [List.getElem?_eq_some_iff] at hFwd
      obtain ⟨hj'Len, hj'Eq⟩ := hFwd
      exact Or.inl (by
        rw [List.mem_take_iff_getElem]
        exact ⟨j', lt_min hj' hj'Len, hj'Eq⟩)
    · rw [List.getElem?_eq_some_iff] at hBwd
      obtain ⟨hj'Len, hj'Eq⟩ := hBwd
      exact Or.inr (by
        rw [List.mem_take_iff_getElem]
        exact ⟨j', lt_min hj' hj'Len, hj'Eq⟩)
  have hRed : isRedundantEntryOfPrefix (bt.take j) bt[j] := by
    rw [hjEq]
    exact hPriorMem
  exact hNoRedundant j hjLen hRed

/-- In a no-redundant base trace, a normalized inverse-permutation pair cannot occur at a strict
earlier position in either direction. -/
lemma noRedundant_perm_inv_pair_not_prior
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hNoRedundant : hasNoRedundantEntries bt)
    {j j' : ℕ} (hj' : j' < j)
    {sIn sOut : CanonicalSpongeState U}
    (hj : bt[j]? = some ⟨.inr (.inr sOut), sIn⟩)
    (hjPrior : bt[j']? = some ⟨.inr (.inr sOut), sIn⟩ ∨
      bt[j']? = some ⟨.inr (.inl sIn), sOut⟩) :
    False := by
  rw [List.getElem?_eq_some_iff] at hj
  obtain ⟨hjLen, hjEq⟩ := hj
  have hPriorMem :
      (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          bt.take j ∨
        (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          bt.take j := by
    rcases hjPrior with hBwd | hFwd
    · rw [List.getElem?_eq_some_iff] at hBwd
      obtain ⟨hj'Len, hj'Eq⟩ := hBwd
      exact Or.inl (by
        rw [List.mem_take_iff_getElem]
        exact ⟨j', lt_min hj' hj'Len, hj'Eq⟩)
    · rw [List.getElem?_eq_some_iff] at hFwd
      obtain ⟨hj'Len, hj'Eq⟩ := hFwd
      exact Or.inr (by
        rw [List.mem_take_iff_getElem]
        exact ⟨j', lt_min hj' hj'Len, hj'Eq⟩)
  have hRed : isRedundantEntryOfPrefix (bt.take j) bt[j] := by
    rw [hjEq]
    exact hPriorMem
  exact hNoRedundant j hjLen hRed

/-- Reading exactly at the freshly appended singleton position returns that singleton. -/
lemma getElem?_append_singleton_length {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  rw [List.getElem?_append_right (by omega)]
  rw [Nat.sub_self]
  rfl

/-- Hash output-capacity readout at a freshly appended hash representative. -/
lemma hashOutCapAt_append_hash_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    hashOutCapAt (bt ++ [⟨.inl stmt, cap⟩]) bt.length = some cap := by
  unfold hashOutCapAt
  rw [getElem?_append_singleton_length]
  rfl

/-- Inverse-permutation range/preimage-capacity readout at a freshly appended inverse
representative. -/
lemma permInvRangeCapAt_append_bwd_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sOut sIn : CanonicalSpongeState U) :
    permInvRangeCapAt (bt ++ [⟨.inr (.inr sOut), sIn⟩]) bt.length =
      some sIn.capacitySegment := by
  unfold permInvRangeCapAt
  rw [getElem?_append_singleton_length]
  rfl

/-- Inverse-permutation queried-output/domain-capacity readout at a freshly appended inverse
representative. -/
lemma permInvDomainCapAt_append_bwd_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sOut sIn : CanonicalSpongeState U) :
    permInvDomainCapAt (bt ++ [⟨.inr (.inr sOut), sIn⟩]) bt.length =
      some sOut.capacitySegment := by
  unfold permInvDomainCapAt
  rw [getElem?_append_singleton_length]
  rfl

/-- The capacity targets that appear strictly before index `j`.
There are at most `2j` such targets (2 per entry). -/
def priorCapacityTargets
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    List (Option (Vector U SpongeSize.C)) :=
  (List.range j).map (fun j' => bt[j']?.bind (fun e => entryCapAt e 0)) ++
    (List.range j).map (fun j' => bt[j']?.bind (fun e => entryCapAt e 1))

lemma priorCapacityTargets_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    (priorCapacityTargets bt j).length = 2 * j := by
  simp only [priorCapacityTargets, List.length_append, List.length_map, List.length_range]
  omega

/-- `Fin`-indexed view of the `2*j` prior capacity targets.  This is the Lean-friendly shape for
generic finite-family union bounds. -/
def priorCapacityTargetAt
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ)
    (i : Fin (2 * j)) : Option (Vector U SpongeSize.C) :=
  (priorCapacityTargets bt j)[i.1]'(by
    rw [priorCapacityTargets_length]
    exact i.2)

lemma exists_priorCapacityTargetAt_of_mem
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {c : Vector U SpongeSize.C}
    (hmem : some c ∈ priorCapacityTargets bt j) :
    ∃ i : Fin (2 * j), priorCapacityTargetAt bt j i = some c := by
  obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hmem
  have hidx' : idx < 2 * j := by
    rw [← priorCapacityTargets_length bt j]
    exact hidx
  refine ⟨⟨idx, hidx'⟩, ?_⟩
  unfold priorCapacityTargetAt
  exact hget

/-! ### Finite target sets for paper-shaped fresh-hit bounds -/

/-- Convert an optional target value to a singleton-or-empty finset. -/
def optionToFinset {α : Type} [DecidableEq α] : Option α → Finset α
  | none => ∅
  | some a => {a}

lemma optionToFinset_card_le_one {α : Type} [DecidableEq α] (x : Option α) :
    (optionToFinset x).card ≤ 1 := by
  cases x <;> simp [optionToFinset]

lemma mem_optionToFinset_of_eq_some {α : Type} [DecidableEq α]
    {x : Option α} {a : α} (h : x = some a) :
    a ∈ optionToFinset x := by
  cases x with
  | none =>
      cases h
  | some a' =>
      simp only [Option.some.injEq] at h
      subst a'
      simp [optionToFinset]

/-- Convert a list of optional target capacities to the finset of exposed target capacities. -/
def optionListToFinset {α : Type} [DecidableEq α] (xs : List (Option α)) : Finset α :=
  (xs.filterMap id).toFinset

lemma optionListToFinset_card_le_length {α : Type} [DecidableEq α] (xs : List (Option α)) :
    (optionListToFinset xs).card ≤ xs.length := by
  unfold optionListToFinset
  exact le_trans (List.toFinset_card_le (xs.filterMap id)) (List.length_filterMap_le id xs)

/-- Finset of the `2*j` prior capacity targets. -/
def priorCapacityTargetFinset
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Finset (Vector U SpongeSize.C) :=
  optionListToFinset (priorCapacityTargets bt j)

lemma priorCapacityTargetFinset_card_le
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    (priorCapacityTargetFinset bt j).card ≤ 2 * j := by
  unfold priorCapacityTargetFinset
  rw [← priorCapacityTargets_length bt j]
  exact optionListToFinset_card_le_length (priorCapacityTargets bt j)

lemma mem_optionListToFinset_of_mem_some {α : Type} [DecidableEq α]
    {xs : List (Option α)} {a : α} (h : some a ∈ xs) :
    a ∈ optionListToFinset xs := by
  unfold optionListToFinset
  rw [List.mem_toFinset]
  exact List.mem_filterMap.mpr ⟨some a, h, rfl⟩

lemma mem_some_of_mem_optionListToFinset {α : Type} [DecidableEq α]
    {xs : List (Option α)} {a : α} (h : a ∈ optionListToFinset xs) :
    some a ∈ xs := by
  unfold optionListToFinset at h
  rw [List.mem_toFinset] at h
  obtain ⟨oa, hoa, hfilter⟩ := List.mem_filterMap.mp h
  change oa = some a at hfilter
  rw [hfilter] at hoa
  exact hoa

lemma mem_priorCapacityTargets_of_mem_priorCapacityTargetFinset
    [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {c : Vector U SpongeSize.C}
    (hmem : c ∈ priorCapacityTargetFinset bt j) :
    some c ∈ priorCapacityTargets bt j := by
  exact mem_some_of_mem_optionListToFinset hmem

/-- The `2*j + 1` target family for an inverse permutation representative: all prior capacity
slots plus the same entry's queried-output/domain capacity. -/
def permBwdCapacityTargetAt
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ)
    (i : Fin (2 * j + 1)) : Option (Vector U SpongeSize.C) :=
  if h : i.1 < 2 * j then
    priorCapacityTargetAt bt j ⟨i.1, h⟩
  else
    permInvDomainCapAt bt j

/-- Finset of the `2*j + 1` forward-permutation capacity targets:
all prior capacity slots plus the same entry's input capacity. -/
def permFwdCapacityTargetFinset
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Finset (Vector U SpongeSize.C) :=
  priorCapacityTargetFinset bt j ∪ optionToFinset (permInCapAt bt j)

lemma permFwdCapacityTargetFinset_card_le
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    (permFwdCapacityTargetFinset bt j).card ≤ 2 * j + 1 := by
  unfold permFwdCapacityTargetFinset
  calc
    (priorCapacityTargetFinset bt j ∪ optionToFinset (permInCapAt bt j)).card
        ≤ (priorCapacityTargetFinset bt j).card +
            (optionToFinset (permInCapAt bt j)).card :=
          Finset.card_union_le _ _
    _ ≤ 2 * j + 1 := by
        exact Nat.add_le_add (priorCapacityTargetFinset_card_le bt j)
          (optionToFinset_card_le_one (permInCapAt bt j))

/-- At the newly appended forward representative, the input and output capacity readouts are
exactly the queried state and returned state. -/
lemma permOutCapAt_append_fwd_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateIn stateOut : CanonicalSpongeState U) :
    permOutCapAt (bt ++ [⟨dsPermQuery stateIn, stateOut⟩]) bt.length =
      some stateOut.capacitySegment := by
  unfold permOutCapAt
  rw [getElem?_append_singleton_length]
  rfl

lemma permInCapAt_append_fwd_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateIn stateOut : CanonicalSpongeState U) :
    permInCapAt (bt ++ [⟨dsPermQuery stateIn, stateOut⟩]) bt.length =
      some stateIn.capacitySegment := by
  unfold permInCapAt
  rw [getElem?_append_singleton_length]
  rfl

/-- Finset of the `2*j + 1` inverse-permutation capacity targets:
all prior capacity slots plus the same entry's queried-output/domain capacity. -/
def permBwdCapacityTargetFinset
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Finset (Vector U SpongeSize.C) :=
  priorCapacityTargetFinset bt j ∪ optionToFinset (permInvDomainCapAt bt j)

lemma permBwdCapacityTargetFinset_card_le
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    (permBwdCapacityTargetFinset bt j).card ≤ 2 * j + 1 := by
  unfold permBwdCapacityTargetFinset
  calc
    (priorCapacityTargetFinset bt j ∪ optionToFinset (permInvDomainCapAt bt j)).card
        ≤ (priorCapacityTargetFinset bt j).card +
            (optionToFinset (permInvDomainCapAt bt j)).card :=
          Finset.card_union_le _ _
    _ ≤ 2 * j + 1 := by
        exact Nat.add_le_add (priorCapacityTargetFinset_card_le bt j)
          (optionToFinset_card_le_one (permInvDomainCapAt bt j))

/-! ### Prefix stability for target readouts -/

lemma getElem?_eq_of_take_eq
    {α : Type} {l₁ l₂ : List α} {j idx : ℕ}
    (h : l₁.take j = l₂.take j) (hidx : idx < j) :
    l₁[idx]? = l₂[idx]? := by
  have hget := congrArg (fun l : List α => l[idx]?) h
  change (List.take j l₁)[idx]? = (List.take j l₂)[idx]? at hget
  rw [List.getElem?_take, List.getElem?_take, if_pos hidx, if_pos hidx] at hget
  exact hget

lemma priorCapacityTargets_eq_of_take_eq
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} (h : bt₁.take j = bt₂.take j) :
    priorCapacityTargets bt₁ j = priorCapacityTargets bt₂ j := by
  unfold priorCapacityTargets
  congr 1
  · apply List.map_congr_left
    intro j' hj'
    have hj'lt : j' < j := List.mem_range.mp hj'
    rw [getElem?_eq_of_take_eq h hj'lt]
  · apply List.map_congr_left
    intro j' hj'
    have hj'lt : j' < j := List.mem_range.mp hj'
    rw [getElem?_eq_of_take_eq h hj'lt]

lemma priorCapacityTargetFinset_eq_of_take_eq
    [DecidableEq U]
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} (h : bt₁.take j = bt₂.take j) :
    priorCapacityTargetFinset bt₁ j = priorCapacityTargetFinset bt₂ j := by
  unfold priorCapacityTargetFinset
  rw [priorCapacityTargets_eq_of_take_eq h]

lemma priorCapacityTargetAt_eq_of_take_eq
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} (h : bt₁.take j = bt₂.take j) (i : Fin (2 * j)) :
    priorCapacityTargetAt bt₁ j i = priorCapacityTargetAt bt₂ j i := by
  unfold priorCapacityTargetAt
  have hlist := priorCapacityTargets_eq_of_take_eq h
  have hget := congrArg
    (fun l : List (Option (Vector U SpongeSize.C)) => l[i.1]?) hlist
  change (priorCapacityTargets bt₁ j)[i.1]? = (priorCapacityTargets bt₂ j)[i.1]? at hget
  rw [List.getElem?_eq_getElem (by
      rw [priorCapacityTargets_length]
      exact i.2),
    List.getElem?_eq_getElem (by
      rw [priorCapacityTargets_length]
      exact i.2)] at hget
  exact Option.some.inj hget

/-- The target family at a newly appended forward representative is already fixed before its
output capacity is sampled: the old prior capacities plus the known input capacity. -/
lemma permFwdCapacityTargetFinset_append_fwd_length
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateIn stateOut : CanonicalSpongeState U) :
    permFwdCapacityTargetFinset (bt ++ [⟨dsPermQuery stateIn, stateOut⟩]) bt.length =
      priorCapacityTargetFinset bt bt.length ∪ {stateIn.capacitySegment} := by
  unfold permFwdCapacityTargetFinset
  have htake :
      (bt ++ [(⟨dsPermQuery stateIn, stateOut⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U))]).take bt.length =
        bt.take bt.length := by
    exact List.take_append_of_le_length (Nat.le_refl bt.length)
  rw [priorCapacityTargetFinset_eq_of_take_eq htake]
  rw [permInCapAt_append_fwd_length]
  rfl

/-- Forward permutation freshness hit event: the output capacity at `j` matches a prior capacity
target or its own input capacity. -/
def permFwdFreshHitAt
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) : Prop :=
  ∃ c, permOutCapAt bt j = some c ∧
    (some c ∈ priorCapacityTargets bt j ∨ permInCapAt bt j = some c)

/-- Inverse permutation freshness hit event: the input capacity at `j` matches a prior capacity
target or its own output capacity. -/
def permBwdFreshHitAt
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) : Prop :=
  ∃ c, permInvRangeCapAt bt j = some c ∧
    (some c ∈ priorCapacityTargets bt j ∨ permInvDomainCapAt bt j = some c)

/-- Hash freshness hit event: the output capacity at `j` matches a prior capacity target.
Note: the paper counts `h` query input capacities as well, but our `E_h` checks only against
prior output/input capacities, so `priorCapacityTargets` is sufficient. -/
def hashFreshHitAt
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) : Prop :=
  ∃ c, hashOutCapAt bt j = some c ∧
    (some c ∈ priorCapacityTargets bt j)

lemma hashFreshHitAt_imp_exists_target
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (h : hashFreshHitAt bt j) :
    ∃ i : Fin (2 * j), ∃ c : Vector U SpongeSize.C,
      hashOutCapAt bt j = some c ∧ priorCapacityTargetAt bt j i = some c := by
  obtain ⟨c, hout, hmem⟩ := h
  obtain ⟨i, hi⟩ := exists_priorCapacityTargetAt_of_mem hmem
  exact ⟨i, c, hout, hi⟩

/-- A forward freshness hit exposes its sampled output capacity in the finite target set used by
the no-replacement permutation bound. -/
lemma permFwdFreshHitAt_imp_mem_targetFinset
    [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (h : permFwdFreshHitAt bt j) :
    ∃ c : Vector U SpongeSize.C,
      permOutCapAt bt j = some c ∧ c ∈ permFwdCapacityTargetFinset bt j := by
  obtain ⟨c, hout, htarget | hself⟩ := h
  · exact ⟨c, hout, Finset.mem_union.mpr
      (Or.inl (mem_optionListToFinset_of_mem_some htarget))⟩
  · exact ⟨c, hout, Finset.mem_union.mpr
      (Or.inr (mem_optionToFinset_of_eq_some hself))⟩

/-- The finite `2j+1` target set is an exact presentation of the forward fresh-hit predicate.
This is the local bridge used by the rate-only forward sampler: once its newly sampled output
capacity is in the pre-step target set, it is precisely the paper's forward collision event. -/
lemma permFwdFreshHitAt_of_mem_targetFinset
    [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {c : Vector U SpongeSize.C}
    (hout : permOutCapAt bt j = some c)
    (hmem : c ∈ permFwdCapacityTargetFinset bt j) :
    permFwdFreshHitAt bt j := by
  unfold permFwdCapacityTargetFinset at hmem
  rw [Finset.mem_union] at hmem
  refine ⟨c, hout, ?_⟩
  rcases hmem with hprior | hself
  · exact Or.inl (mem_priorCapacityTargets_of_mem_priorCapacityTargetFinset hprior)
  · cases hcap : permInCapAt bt j with
    | none =>
        unfold optionToFinset at hself
        rw [hcap] at hself
        exact False.elim (Finset.notMem_empty c hself)
    | some c' =>
        unfold optionToFinset at hself
        rw [hcap] at hself
        simp only [Finset.mem_singleton] at hself
        subst c'
        exact Or.inr rfl

lemma permFwdFreshHitAt_iff_mem_targetFinset
    [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ} :
    permFwdFreshHitAt bt j ↔
      ∃ c : Vector U SpongeSize.C,
        permOutCapAt bt j = some c ∧ c ∈ permFwdCapacityTargetFinset bt j := by
  constructor
  · exact permFwdFreshHitAt_imp_mem_targetFinset
  · intro h
    obtain ⟨c, hout, hmem⟩ := h
    exact permFwdFreshHitAt_of_mem_targetFinset hout hmem

/-- For a just-materialized forward entry, the fresh-hit predicate is precisely membership of
the newly sampled output capacity in the pre-step target set.  This is the shape required for
the local rate-only cache and ordinary-sampling bounds. -/
lemma permFwdFreshHitAt_append_fwd_length_iff
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateIn stateOut : CanonicalSpongeState U) :
    permFwdFreshHitAt (bt ++ [⟨dsPermQuery stateIn, stateOut⟩]) bt.length ↔
      stateOut.capacitySegment ∈
        priorCapacityTargetFinset bt bt.length ∪ {stateIn.capacitySegment} := by
  constructor
  · intro h
    obtain ⟨c, hout, hmem⟩ :=
      (permFwdFreshHitAt_iff_mem_targetFinset
        (StmtIn := StmtIn) (U := U)).mp h
    rw [permOutCapAt_append_fwd_length] at hout
    rw [permFwdCapacityTargetFinset_append_fwd_length] at hmem
    injection hout with hc
    subst c
    exact hmem
  · intro h
    apply (permFwdFreshHitAt_iff_mem_targetFinset
      (StmtIn := StmtIn) (U := U)).mpr
    refine ⟨stateOut.capacitySegment, ?_, ?_⟩
    · exact permOutCapAt_append_fwd_length bt stateIn stateOut
    · rw [permFwdCapacityTargetFinset_append_fwd_length]
      exact h

lemma permBwdFreshHitAt_imp_mem_targetFinset
    [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (h : permBwdFreshHitAt bt j) :
    ∃ c : Vector U SpongeSize.C,
      permInvRangeCapAt bt j = some c ∧ c ∈ permBwdCapacityTargetFinset bt j := by
  obtain ⟨c, hout, htarget | hself⟩ := h
  · exact ⟨c, hout, Finset.mem_union.mpr
      (Or.inl (mem_optionListToFinset_of_mem_some htarget))⟩
  · exact ⟨c, hout, Finset.mem_union.mpr
      (Or.inr (mem_optionToFinset_of_eq_some hself))⟩

lemma permBwdFreshHitAt_of_mem_targetFinset
    [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {c : Vector U SpongeSize.C}
    (hout : permInvRangeCapAt bt j = some c)
    (hmem : c ∈ permBwdCapacityTargetFinset bt j) :
    permBwdFreshHitAt bt j := by
  unfold permBwdCapacityTargetFinset at hmem
  rw [Finset.mem_union] at hmem
  refine ⟨c, hout, ?_⟩
  rcases hmem with hprior | hself
  · exact Or.inl (mem_priorCapacityTargets_of_mem_priorCapacityTargetFinset hprior)
  · cases hcap : permInvDomainCapAt bt j with
    | none =>
        unfold optionToFinset at hself
        rw [hcap] at hself
        exact False.elim (Finset.notMem_empty c hself)
    | some c' =>
        unfold optionToFinset at hself
        rw [hcap] at hself
        simp only [Finset.mem_singleton] at hself
        subst c'
        exact Or.inr rfl

lemma permBwdFreshHitAt_iff_mem_targetFinset
    [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ} :
    permBwdFreshHitAt bt j ↔
      ∃ c : Vector U SpongeSize.C,
        permInvRangeCapAt bt j = some c ∧ c ∈ permBwdCapacityTargetFinset bt j := by
  constructor
  · exact permBwdFreshHitAt_imp_mem_targetFinset
  · intro h
    obtain ⟨c, hout, hmem⟩ := h
    exact permBwdFreshHitAt_of_mem_targetFinset hout hmem

/-- For a just-materialized inverse entry, the fresh-hit predicate is precisely membership of the
newly sampled preimage capacity in the pre-step target set.  This is the inverse counterpart of
`permFwdFreshHitAt_append_fwd_length_iff`, used by the direct inverse-query kernel. -/
lemma permBwdFreshHitAt_append_bwd_length_iff
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateOut stateIn : CanonicalSpongeState U) :
    permBwdFreshHitAt (bt ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) bt.length ↔
      stateIn.capacitySegment ∈
        priorCapacityTargetFinset bt bt.length ∪ {stateOut.capacitySegment} := by
  have htarget :
      permBwdCapacityTargetFinset (bt ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) bt.length =
        priorCapacityTargetFinset bt bt.length ∪ {stateOut.capacitySegment} := by
    unfold permBwdCapacityTargetFinset
    have htake :
        (bt ++ [(⟨dsPermInvQuery stateOut, stateIn⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U))]).take bt.length =
          bt.take bt.length := by
      exact List.take_append_of_le_length (Nat.le_refl bt.length)
    rw [priorCapacityTargetFinset_eq_of_take_eq htake]
    rw [permInvDomainCapAt_append_bwd_length]
    rfl
  constructor
  · intro h
    obtain ⟨c, hout, hmem⟩ :=
      (permBwdFreshHitAt_iff_mem_targetFinset
        (StmtIn := StmtIn) (U := U)).mp h
    rw [permInvRangeCapAt_append_bwd_length] at hout
    rw [htarget] at hmem
    injection hout with hc
    subst c
    exact hmem
  · intro h
    apply (permBwdFreshHitAt_iff_mem_targetFinset
      (StmtIn := StmtIn) (U := U)).mpr
    refine ⟨stateIn.capacitySegment, ?_, ?_⟩
    · exact permInvRangeCapAt_append_bwd_length bt stateOut stateIn
    · rw [htarget]
      exact h

lemma mem_priorCapacityTargets_of_entryCapAt
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j j' : ℕ} (hj' : j' < j) (k : Fin 2) {c : Vector U SpongeSize.C}
    (hc : (bt[j']?).bind (fun e => entryCapAt e k) = some c) :
    some c ∈ priorCapacityTargets bt j := by
  unfold priorCapacityTargets
  fin_cases k
  · exact List.mem_append_left _
      (List.mem_map.mpr ⟨j', List.mem_range.mpr hj', hc⟩)
  · exact List.mem_append_right _
      (List.mem_map.mpr ⟨j', List.mem_range.mpr hj', hc⟩)

/-- Forward trace-only implication: `E_p_at` implies a hit in the target sets. -/
lemma E_p_at_imp_permFwdFreshHitAt
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ)
    (h : E_p_at trace j) :
    permFwdFreshHitAt (getBaseTrace trace) j := by
  let bt := getBaseTrace trace
  obtain ⟨hj, capSeg, ⟨sInj, sOutj, hbtj, hcapj⟩, hdup⟩ := h
  have hout : permOutCapAt bt j = some capSeg := by
    simp only [bt, permOutCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
    exact congrArg some hcapj
  have mkPrior :
      ∀ (j' : Fin bt.length) (k : Fin 2), (j' : ℕ) < j →
        entryCapAt bt[j'] k = some capSeg →
        some capSeg ∈ priorCapacityTargets bt j := by
    intro j' k hlt hcap
    apply mem_priorCapacityTargets_of_entryCapAt (bt := bt) (j := j) (j' := j') hlt k
    rw [List.getElem?_eq_getElem j'.2]
    exact hcap
  refine ⟨capSeg, hout, ?_⟩
  rcases hdup with ⟨j', hlt, stmt', he⟩ | ⟨j', hlt, sIn1, sOut1, he, hc⟩ |
      ⟨j', hlt, sOut2, sIn2, he, hc⟩ | ⟨j', hle, sIn3, sOut3, he, hc⟩ |
      ⟨j', hle, sOut4, sIn4, he, hc⟩
  · exact Or.inl (mkPrior j' 0 (Fin.lt_def.mp hlt) (by rw [he]; rfl))
  · exact Or.inl (mkPrior j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc))
  · exact Or.inl (mkPrior j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc))
  · rcases lt_or_eq_of_le (Fin.le_def.mp hle) with hlt' | heq
    · exact Or.inl (mkPrior j' 0 hlt' (by rw [he]; exact congrArg some hc))
    · have hjj' : j' = (⟨j, hj⟩ : Fin bt.length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      obtain ⟨heDom, _heOut⟩ := Sigma.mk.inj_iff.mp he
      have hs : sInj = sIn3 := Sum.inl.inj (Sum.inr.inj heDom)
      exact Or.inr (by
        simp only [bt, permInCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
        rw [hs]
        exact congrArg some hc)
  · have hlt' : (j' : ℕ) < j := by
      refine lt_of_le_of_ne (Fin.le_def.mp hle) (fun heq => ?_)
      have hjj' : j' = (⟨j, hj⟩ : Fin bt.length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      exact absurd he (by simp)
    exact Or.inl (mkPrior j' 0 hlt' (by rw [he]; exact congrArg some hc))

/-- Inverse trace-only implication: `E_pinv_at` implies a hit in the target sets. -/
lemma E_pinv_at_imp_permBwdFreshHitAt
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ)
    (h : E_pinv_at trace j) :
    permBwdFreshHitAt (getBaseTrace trace) j := by
  let bt := getBaseTrace trace
  obtain ⟨hj, capSeg, ⟨sOutj, sInj, hbtj, hcapj⟩, hdup⟩ := h
  have hout : permInvRangeCapAt bt j = some capSeg := by
    simp only [bt, permInvRangeCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
    exact congrArg some hcapj
  have mkPrior :
      ∀ (j' : Fin bt.length) (k : Fin 2), (j' : ℕ) < j →
        entryCapAt bt[j'] k = some capSeg →
        some capSeg ∈ priorCapacityTargets bt j := by
    intro j' k hlt hcap
    apply mem_priorCapacityTargets_of_entryCapAt (bt := bt) (j := j) (j' := j') hlt k
    rw [List.getElem?_eq_getElem j'.2]
    exact hcap
  refine ⟨capSeg, hout, ?_⟩
  rcases hdup with ⟨j', hlt, stmt', he⟩ | ⟨j', hlt, sIn1, sOut1, he, hc⟩ |
      ⟨j', hlt, sOut2, sIn2, he, hc⟩ | ⟨j', hle, sIn3, sOut3, he, hc⟩ |
      ⟨j', hle, sOut4, sIn4, he, hc⟩
  · exact Or.inl (mkPrior j' 0 (Fin.lt_def.mp hlt) (by rw [he]; rfl))
  · exact Or.inl (mkPrior j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc))
  · exact Or.inl (mkPrior j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc))
  · have hlt' : (j' : ℕ) < j := by
      refine lt_of_le_of_ne (Fin.le_def.mp hle) (fun heq => ?_)
      have hjj' : j' = (⟨j, hj⟩ : Fin bt.length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      exact absurd he (by simp)
    exact Or.inl (mkPrior j' 0 hlt' (by rw [he]; exact congrArg some hc))
  · rcases lt_or_eq_of_le (Fin.le_def.mp hle) with hlt' | heq
    · exact Or.inl (mkPrior j' 0 hlt' (by rw [he]; exact congrArg some hc))
    · have hjj' : j' = (⟨j, hj⟩ : Fin bt.length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      obtain ⟨heDom, _heOut⟩ := Sigma.mk.inj_iff.mp he
      have hs : sOutj = sOut4 := Sum.inr.inj (Sum.inr.inj heDom)
      exact Or.inr (by
        simp only [bt, permInvDomainCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
        rw [hs]
        exact congrArg some hc)

/-- Hash trace-only implication: `E_h_at` implies a hit in the target sets. -/
lemma E_h_at_imp_hashFreshHitAt
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ)
    (h : E_h_at trace j) :
    hashFreshHitAt (getBaseTrace trace) j := by
  let bt := getBaseTrace trace
  obtain ⟨hj, capSeg, ⟨stmt, hbtj⟩, hdup⟩ := h
  have hout : hashOutCapAt bt j = some capSeg := by
    simp only [bt, hashOutCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
  have mkPrior :
      ∀ (j' : Fin bt.length) (k : Fin 2), (j' : ℕ) < j →
        entryCapAt bt[j'] k = some capSeg →
        some capSeg ∈ priorCapacityTargets bt j := by
    intro j' k hlt hcap
    apply mem_priorCapacityTargets_of_entryCapAt (bt := bt) (j := j) (j' := j') hlt k
    rw [List.getElem?_eq_getElem j'.2]
    exact hcap
  refine ⟨capSeg, hout, ?_⟩
  have hlt_of_le : ∀ (j' : Fin bt.length),
      j' ≤ (⟨j, hj⟩ : Fin bt.length) →
      (∀ stmt', bt[j'] ≠ (⟨.inl stmt', capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)) → (j' : ℕ) < j := by
    intro j' hle hnot
    refine lt_of_le_of_ne (Fin.le_def.mp hle) (fun heq => ?_)
    have hjj' : j' = (⟨j, hj⟩ : Fin bt.length) := Fin.ext heq
    exact hnot stmt (by rw [hjj', Fin.getElem_fin]; exact hbtj)
  rcases hdup with ⟨j', hlt, stmt', he⟩ | ⟨j', hlt, sIn1, sOut1, he, hc⟩ |
      ⟨j', hlt, sOut2, sIn2, he, hc⟩ | ⟨j', hle, sIn3, sOut3, he, hc⟩ |
      ⟨j', hle, sOut4, sIn4, he, hc⟩
  · exact mkPrior j' 0 (Fin.lt_def.mp hlt) (by rw [he]; rfl)
  · exact mkPrior j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · exact mkPrior j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · exact mkPrior j' 0 (hlt_of_le j' hle (fun stmt' hsame => by
        have hsame' : bt[j'] = ⟨Sum.inl stmt', capSeg⟩ := hsame
        rw [he] at hsame'
        cases (Sigma.mk.inj_iff.mp hsame').1))
      (by rw [he]; exact congrArg some hc)
  · exact mkPrior j' 0 (hlt_of_le j' hle (fun stmt' hsame => by
        have hsame' : bt[j'] = ⟨Sum.inl stmt', capSeg⟩ := hsame
        rw [he] at hsame'
        cases (Sigma.mk.inj_iff.mp hsame').1))
      (by rw [he]; exact congrArg some hc)

/-- At the newly appended hash position, a hash fresh hit is exactly membership of the sampled
capacity in the capacity targets exposed by the preceding base trace.  This is the hash-direction
counterpart to the forward and inverse append normal forms. -/
lemma hashFreshHitAt_append_hash_length_iff
    [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C) :
    hashFreshHitAt (bt ++ [⟨dsHashQuery stmt, capacity⟩]) bt.length ↔
      capacity ∈ priorCapacityTargetFinset bt bt.length := by
  have htake :
      (bt ++ [(⟨dsHashQuery stmt, capacity⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U))]).take bt.length =
        bt.take bt.length := by
    exact List.take_append_of_le_length (Nat.le_refl bt.length)
  constructor
  · rintro ⟨observed, hout, htargets⟩
    rw [hashOutCapAt_append_hash_length] at hout
    injection hout with hcapacity
    subst observed
    rw [priorCapacityTargets_eq_of_take_eq htake] at htargets
    exact mem_optionListToFinset_of_mem_some htargets
  · intro htargets
    refine ⟨capacity, hashOutCapAt_append_hash_length bt stmt capacity, ?_⟩
    rw [priorCapacityTargets_eq_of_take_eq htake]
    exact mem_priorCapacityTargets_of_mem_priorCapacityTargetFinset htargets

end BadEventDS
end DuplexSpongeFS

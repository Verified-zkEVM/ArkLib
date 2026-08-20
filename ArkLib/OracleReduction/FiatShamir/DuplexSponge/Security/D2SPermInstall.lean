/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Table-only permutation installation for revised D2SQuery

`Install` is deliberately below the simulator implementation.  It classifies an attempted
normalized permutation mapping as fresh, present, or conflicting; only a fresh mapping changes
the table.  The caller owns trace insertion and the subsequent monitor check.
-/

namespace DuplexSpongeFS.ProverTransform

open OracleSpec ProtocolSpec
open DSTraceStorage

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- The table-only outcome for a hash-table `PrefixUpdate`.  This is the hash-side analogue of
`PermInstallStatus`: an identical repeat is present, a new statement is fresh, and a different
capacity at an already-used statement is a conflict.  The caller still owns raw-trace insertion
and the subsequent `Monitor` check. -/
inductive HashInstallStatus where
  | fresh
  | present
  | conflict
deriving DecidableEq, Repr

/-- Classify one proposed hash mapping without modifying its table.  In particular, this does
not collapse a conflicting second capacity into a harmless cache hit: the caller can retain the
raw occurrence and stop at `Monitor`, exactly as for a conflicting permutation installation. -/
def hashInstallStatus
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [TraceTableOps T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C) : HashInstallStatus :=
  match TraceTableOps.inlu t stmt with
  | none => .fresh
  | some stored => if stored = capacity then .present else .conflict

/-- Table-only hash installation.  A fresh mapping is added; an identical repeat or a conflict
leaves the lookup table unchanged.  This is deliberately parallel to `installPerm`, so a single
offline PrefixUpdate can maintain the revised deduplicated `tr_∇` while retaining every raw trace
occurrence for multiplicity. -/
def installHash
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [TraceTableOps T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C) : HashInstallStatus × T :=
  match hashInstallStatus t stmt capacity with
  | .fresh => (.fresh, TraceTableOps.add t stmt capacity)
  | .present => (.present, t)
  | .conflict => (.conflict, t)

omit [SpongeUnit U] in
@[simp] lemma installHash_fst
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [TraceTableOps T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C) :
    (installHash t stmt capacity).1 = hashInstallStatus t stmt capacity := by
  unfold installHash
  cases hashInstallStatus t stmt capacity <;> rfl

omit [SpongeUnit U] in
@[simp] lemma installHash_snd_of_fresh
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [TraceTableOps T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hStatus : hashInstallStatus t stmt capacity = .fresh) :
    (installHash t stmt capacity).2 = TraceTableOps.add t stmt capacity := by
  simp [installHash, hStatus]

omit [SpongeUnit U] in
@[simp] lemma installHash_snd_of_present
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [TraceTableOps T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hStatus : hashInstallStatus t stmt capacity = .present) :
    (installHash t stmt capacity).2 = t := by
  simp [installHash, hStatus]

omit [SpongeUnit U] in
@[simp] lemma installHash_snd_of_conflict
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [TraceTableOps T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hStatus : hashInstallStatus t stmt capacity = .conflict) :
    (installHash t stmt capacity).2 = t := by
  simp [installHash, hStatus]

omit [SpongeUnit U] in
/-- A `present` hash installation is an exact pair already represented in its table.  The
normalization pass needs this small lookup fact to retain repeated raw hash occurrences without
adding a second table entry. -/
lemma hashInstallStatus_present_mem
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [LawfulTraceTable T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hStatus : hashInstallStatus t stmt capacity = .present) :
    (stmt, capacity) ∈ TraceTableOps.entries t := by
  unfold hashInstallStatus at hStatus
  split at hStatus
  · simp at hStatus
  · rename_i stored hLookup
    split at hStatus
    · rename_i hStored
      simp at hStatus
      simpa [hStored] using TraceTableOps.mem_entries_of_inlu_eq_some hLookup
    · simp at hStatus

omit [SpongeUnit U] in
/-- A fresh hash installation is exactly a genuine input-table miss. -/
lemma hashInstallStatus_fresh_inlu_none
    {StmtIn : Type} {T : Type} [DecidableEq StmtIn] [DecidableEq (Vector U SpongeSize.C)]
    [TraceTableOps T StmtIn (Vector U SpongeSize.C)]
    (t : T) (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hStatus : hashInstallStatus t stmt capacity = .fresh) :
    TraceTableOps.inlu t stmt = none := by
  by_contra hNone
  cases hLookup : TraceTableOps.inlu t stmt with
  | none => exact hNone hLookup
  | some stored =>
      simp only [hashInstallStatus, hLookup] at hStatus
      split at hStatus <;> simp_all

/-- The three outcomes of a table-only permutation installation. -/
inductive PermInstallStatus where
  | fresh
  | present
  | conflict
deriving DecidableEq, Repr

/-- A candidate pair conflicts if it reuses an input with another output or an output with
another input. -/
def permPairConflicts
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U) : Bool :=
  (TraceTableOps.entries t).any fun entry => decide
    ((entry.1 = stateIn ∧ entry.2 ≠ stateOut) ∨ (entry.2 = stateOut ∧ entry.1 ≠ stateIn))

lemma permPairConflicts_eq_true_iff
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U) :
    permPairConflicts t stateIn stateOut = true ↔
      ∃ entry ∈ TraceTableOps.entries t,
        (entry.1 = stateIn ∧ entry.2 ≠ stateOut) ∨ (entry.2 = stateOut ∧ entry.1 ≠ stateIn) := by
  simp [permPairConflicts]

/-- Classify an attempted insertion without modifying the table. -/
def permInstallStatus
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U) : PermInstallStatus :=
  if permPairConflicts t stateIn stateOut then .conflict
  else if (stateIn, stateOut) ∈ TraceTableOps.entries t then .present
  else .fresh

lemma permInstallStatus_conflict_iff
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U) :
    permInstallStatus t stateIn stateOut = .conflict ↔
      permPairConflicts t stateIn stateOut = true := by
  cases hConflicts : permPairConflicts t stateIn stateOut with
  | false =>
      by_cases hEntry : (stateIn, stateOut) ∈ TraceTableOps.entries t <;>
        simp [permInstallStatus, hConflicts, hEntry]
  | true => simp [permInstallStatus, hConflicts]

lemma permInstallStatus_present_mem
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus t stateIn stateOut = .present) :
    (stateIn, stateOut) ∈ TraceTableOps.entries t := by
  unfold permInstallStatus at hStatus
  split at hStatus <;> simp_all

/-- A `fresh` installation candidate is absent from the current table.  Combined with
`TraceTableOps.nodup_add`, this is the one-line preservation rule for the permutation-table
nodup invariant of a reusable D2SQuery state. -/
lemma permInstallStatus_fresh_not_mem
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus t stateIn stateOut = .fresh) :
    (stateIn, stateOut) ∉ TraceTableOps.entries t := by
  unfold permInstallStatus at hStatus
  split at hStatus <;> simp_all

/-- A fresh table-only installation preserves duplicate-freedom of the normalized permutation
table.  This is deliberately table-level: the caller still owns the subsequent trace append and
Monitor check. -/
lemma permInstallStatus_fresh_nodup_add
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [LawfulTraceTable T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U)
    (hNodup : (LawfulTraceTable.toMultiSet t).Nodup)
    (hStatus : permInstallStatus t stateIn stateOut = .fresh) :
    (LawfulTraceTable.toMultiSet (TraceTableOps.add t stateIn stateOut)).Nodup := by
  apply TraceTableOps.nodup_add hNodup
  intro hMem
  apply permInstallStatus_fresh_not_mem t stateIn stateOut hStatus
  rw [← LawfulTraceTable.toMultiSet_ofEntries] at hMem
  exact hMem

/-- Table-only `Install`: a fresh pair is added, while a present or conflicting pair preserves
the old normalized table. -/
def installPerm
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U) : PermInstallStatus × T :=
  match permInstallStatus t stateIn stateOut with
  | .fresh => (.fresh, TraceTableOps.add t stateIn stateOut)
  | .present => (.present, t)
  | .conflict => (.conflict, t)

@[simp] lemma installPerm_fst
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U) :
    (installPerm t stateIn stateOut).1 = permInstallStatus t stateIn stateOut := by
  unfold installPerm
  cases permInstallStatus t stateIn stateOut <;> rfl

@[simp] lemma installPerm_snd_of_conflict
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus t stateIn stateOut = .conflict) :
    (installPerm t stateIn stateOut).2 = t := by
  simp [installPerm, hStatus]

@[simp] lemma installPerm_snd_of_present
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus t stateIn stateOut = .present) :
    (installPerm t stateIn stateOut).2 = t := by
  simp [installPerm, hStatus]

@[simp] lemma installPerm_snd_of_fresh
    {T : Type} [DecidableEq (CanonicalSpongeState U)]
    [TraceTableOps T (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (t : T) (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus t stateIn stateOut = .fresh) :
    (installPerm t stateIn stateOut).2 = TraceTableOps.add t stateIn stateOut := by
  simp [installPerm, hStatus]

/-! ## Offline PrefixUpdate table fold -/

/-- Table-only update for one raw duplex occurrence.  It is the executable core of the revised
offline `PrefixUpdate`: exact repeats leave the normalized table unchanged, fresh mappings are
installed, and the first input/output conflict returns `none`.  The raw occurrence is deliberately
*not* removed or rewritten here; callers retain it in their insertion-ordered trace and run
`Monitor` after the occurrence. -/
def prefixUpdateEntry
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trDelta : TraceNabla T_H T_P StmtIn U)
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) :
    Option (TraceNabla T_H T_P StmtIn U) :=
  match entry with
  | ⟨.inl stmt, capacity⟩ =>
      match installHash trDelta.h stmt capacity with
      | (.conflict, _) => none
      | (_, h) => some { trDelta with h }
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
      match installPerm trDelta.p stateIn stateOut with
      | (.conflict, _) => none
      | (_, p) => some { trDelta with p }
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
      match installPerm trDelta.p stateIn stateOut with
      | (.conflict, _) => none
      | (_, p) => some { trDelta with p }

/-- The revised offline lookup-table pass over an insertion-ordered duplex trace.  It starts from
empty hash/permutation tables and processes each raw occurrence exactly once.  `none` marks the
first `Install` conflict; a successful result is the deduplicated `tr_∇` used by strict-prefix
Backtrack and full-table LookAhead. -/
def prefixUpdateTrace
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    Option (TraceNabla T_H T_P StmtIn U) :=
  trace.foldl
    (fun current entry => current.bind (fun trDelta => prefixUpdateEntry trDelta entry))
    (some ⟨TraceTableOps.empty, TraceTableOps.empty⟩)

/-- The reusable table invariant of a successful offline PrefixUpdate.  It deliberately says
nothing about the order or multiplicity of the raw trace: those remain in the caller's log.  It
does retain exactly the facts that turn a successful lookup table into a legal D2S normal-state
table once the caller supplies the separate `Monitor`-passed fact. -/
structure PrefixUpdateInvariant
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (trDelta : TraceNabla T_H T_P StmtIn U)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop where
  mirrors : trDelta.MirrorsQueryLog trace
  permutationNodup : (LawfulTraceTable.toMultiSet trDelta.p).Nodup
  hashNodup : (LawfulTraceTable.toMultiSet trDelta.h).Nodup
  hashInputFunctional : TraceTableOps.InputFunctional trDelta.h

/-- A successful `PrefixUpdate` step preserves the exact set-semantic relationship between the
deduplicated table and the raw trace.  In particular, a repeated occurrence extends the raw log
but leaves the table unchanged, as required by revised StdTrace and D2SQuery. -/
theorem prefixUpdateEntry_mirrors
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trDelta trDelta' : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hMirror : trDelta.MirrorsQueryLog trace)
    (hUpdate : prefixUpdateEntry trDelta entry = some trDelta') :
    trDelta'.MirrorsQueryLog (trace ++ [entry]) := by
  rcases entry with ⟨query, answer⟩
  cases query with
  | inl stmt =>
      cases hStatus : hashInstallStatus trDelta.h stmt answer with
      | fresh =>
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          exact TraceNabla.MirrorsQueryLog_append_hash_add hMirror stmt answer
      | present =>
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          exact TraceNabla.MirrorsQueryLog_append_hash_existing hMirror stmt answer
            (hashInstallStatus_present_mem trDelta.h stmt answer hStatus)
      | conflict => simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
  | inr query =>
      cases query with
      | inl stateIn =>
          cases hStatus : permInstallStatus trDelta.p stateIn answer with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.MirrorsQueryLog_append_perm_add hMirror stateIn answer
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.MirrorsQueryLog_append_perm_existing hMirror stateIn answer
                (permInstallStatus_present_mem trDelta.p stateIn answer hStatus)
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
      | inr stateOut =>
          cases hStatus : permInstallStatus trDelta.p answer stateOut with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.MirrorsQueryLog_append_perm_inv_add hMirror answer stateOut
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.MirrorsQueryLog_append_perm_inv_existing hMirror answer stateOut
                (permInstallStatus_present_mem trDelta.p answer stateOut hStatus)
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate

/-- One successful table-only `PrefixUpdate` preserves every reusable normalized-table
invariant.  The conflict branch has no successor by construction, so it never needs a fake
normal-state proof. -/
theorem prefixUpdateEntry_invariant
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trDelta trDelta' : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hInv : PrefixUpdateInvariant trDelta trace)
    (hUpdate : prefixUpdateEntry trDelta entry = some trDelta') :
    PrefixUpdateInvariant trDelta' (trace ++ [entry]) := by
  have hMirror := prefixUpdateEntry_mirrors hInv.mirrors hUpdate
  rcases entry with ⟨query, answer⟩
  cases query with
  | inl stmt =>
      cases hStatus : hashInstallStatus trDelta.h stmt answer with
      | fresh =>
          have hLookup := hashInstallStatus_fresh_inlu_none trDelta.h stmt answer hStatus
          have hFresh : ∀ capacity : Vector U SpongeSize.C,
              (stmt, capacity) ∉ LawfulTraceTable.toMultiSet trDelta.h :=
            TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
              hInv.hashNodup hInv.hashInputFunctional hLookup
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          exact ⟨hMirror, hInv.permutationNodup,
            TraceTableOps.nodup_add hInv.hashNodup (hFresh answer),
            TraceTableOps.inputFunctional_add hInv.hashInputFunctional hFresh⟩
      | present =>
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          exact ⟨hMirror, hInv.permutationNodup, hInv.hashNodup, hInv.hashInputFunctional⟩
      | conflict => simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
  | inr query =>
      cases query with
      | inl stateIn =>
          cases hStatus : permInstallStatus trDelta.p stateIn answer with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact ⟨hMirror,
                permInstallStatus_fresh_nodup_add trDelta.p stateIn answer
                  hInv.permutationNodup hStatus,
                hInv.hashNodup, hInv.hashInputFunctional⟩
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact ⟨hMirror, hInv.permutationNodup, hInv.hashNodup, hInv.hashInputFunctional⟩
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
      | inr stateOut =>
          cases hStatus : permInstallStatus trDelta.p answer stateOut with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact ⟨hMirror,
                permInstallStatus_fresh_nodup_add trDelta.p answer stateOut
                  hInv.permutationNodup hStatus,
                hInv.hashNodup, hInv.hashInputFunctional⟩
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact ⟨hMirror, hInv.permutationNodup, hInv.hashNodup, hInv.hashInputFunctional⟩
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
/-- A successful `PrefixUpdate` step never invents a lookup-table entry: its normalized table is
still witnessed by the raw trace extended with the occurrence just processed.  This is the local
table-realization invariant needed before the H₀ replay can invoke Backtrack on the strict prefix
and LookAhead on the full prefix. -/
theorem prefixUpdateEntry_isSubset
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trDelta trDelta' : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hInv : trDelta.IsSubsetOfQueryLog trace)
    (hUpdate : prefixUpdateEntry trDelta entry = some trDelta') :
    trDelta'.IsSubsetOfQueryLog (trace ++ [entry]) := by
  rcases entry with ⟨query, answer⟩
  cases query with
  | inl stmt =>
      cases hStatus : hashInstallStatus trDelta.h stmt answer with
      | fresh =>
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          exact TraceNabla.IsSubsetOfQueryLog_append_hash hInv stmt answer
      | present =>
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          exact TraceNabla.IsSubsetOfQueryLog_append_any hInv _
      | conflict => simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
  | inr query =>
      cases query with
      | inl stateIn =>
          cases hStatus : permInstallStatus trDelta.p stateIn answer with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.IsSubsetOfQueryLog_append_perm hInv stateIn answer
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.IsSubsetOfQueryLog_append_any hInv _
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
      | inr stateOut =>
          cases hStatus : permInstallStatus trDelta.p answer stateOut with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.IsSubsetOfQueryLog_append_perm_inv hInv answer stateOut
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact TraceNabla.IsSubsetOfQueryLog_append_any hInv _
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate

/-- Generalized table-realization invariant for the `PrefixUpdate` fold.  The accumulator starts
as a table witnessed by `priorTrace`; if every requested installation succeeds, the returned table is
witnessed by the concatenated raw trace. -/
private lemma prefixUpdateFold_none
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (entries : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    entries.foldl
      (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
      none = (none : Option (TraceNabla T_H T_P StmtIn U)) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih => simpa [List.foldl] using ih

theorem prefixUpdateEntries_isSubset
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trDelta trDelta' : TraceNabla T_H T_P StmtIn U}
    {priorTrace entries : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hInv : trDelta.IsSubsetOfQueryLog priorTrace)
    (hUpdate : entries.foldl
      (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
      (some trDelta) = some trDelta') :
    trDelta'.IsSubsetOfQueryLog (priorTrace ++ entries) := by
  induction entries generalizing trDelta priorTrace with
  | nil =>
      simp at hUpdate
      subst trDelta'
      simpa using hInv
  | cons entry entries ih =>
      cases hEntry : prefixUpdateEntry trDelta entry with
      | none =>
          simp [hEntry] at hUpdate
          have hNone : entries.foldl
              (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
              none = (none : Option (TraceNabla T_H T_P StmtIn U)) :=
            prefixUpdateFold_none (U := U) (T_H := T_H) (T_P := T_P) entries
          rw [hNone] at hUpdate
          cases hUpdate
      | some next =>
          have hTail : entries.foldl
              (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
              (some next) = some trDelta' := by
            simpa [hEntry] using hUpdate
          have hResult := ih (trDelta := next) (priorTrace := priorTrace ++ [entry])
            (prefixUpdateEntry_isSubset hInv hEntry) hTail
          simpa [List.append_assoc] using hResult

/-- Generalized exact-mirror invariant for the successful `PrefixUpdate` fold.  This is the
formal separation of lookup-table normalization from raw trace multiplicity: the latter is never
deduplicated, while the former records exactly the distinct normalized pairs. -/
theorem prefixUpdateEntries_mirrors
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trDelta trDelta' : TraceNabla T_H T_P StmtIn U}
    {priorTrace entries : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hMirror : trDelta.MirrorsQueryLog priorTrace)
    (hUpdate : entries.foldl
      (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
      (some trDelta) = some trDelta') :
    trDelta'.MirrorsQueryLog (priorTrace ++ entries) := by
  induction entries generalizing trDelta priorTrace with
  | nil =>
      simp at hUpdate
      subst trDelta'
      simpa using hMirror
  | cons entry entries ih =>
      cases hEntry : prefixUpdateEntry trDelta entry with
      | none =>
          simp [hEntry] at hUpdate
          have hNone : entries.foldl
              (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
              none = (none : Option (TraceNabla T_H T_P StmtIn U)) :=
            prefixUpdateFold_none (U := U) (T_H := T_H) (T_P := T_P) entries
          rw [hNone] at hUpdate
          cases hUpdate
      | some next =>
          have hTail : entries.foldl
              (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
              (some next) = some trDelta' := by
            simpa [hEntry] using hUpdate
          have hResult := ih (trDelta := next) (priorTrace := priorTrace ++ [entry])
            (prefixUpdateEntry_mirrors hMirror hEntry) hTail
          simpa [List.append_assoc] using hResult

/-- Generalized reusable-table invariant for a successful `PrefixUpdate` fold. -/
theorem prefixUpdateEntries_invariant
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trDelta trDelta' : TraceNabla T_H T_P StmtIn U}
    {priorTrace entries : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hInv : PrefixUpdateInvariant trDelta priorTrace)
    (hUpdate : entries.foldl
      (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
      (some trDelta) = some trDelta') :
    PrefixUpdateInvariant trDelta' (priorTrace ++ entries) := by
  induction entries generalizing trDelta priorTrace with
  | nil =>
      simp at hUpdate
      subst trDelta'
      simpa using hInv
  | cons entry entries ih =>
      cases hEntry : prefixUpdateEntry trDelta entry with
      | none =>
          simp [hEntry] at hUpdate
          have hNone : entries.foldl
              (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
              none = (none : Option (TraceNabla T_H T_P StmtIn U)) :=
            prefixUpdateFold_none (U := U) (T_H := T_H) (T_P := T_P) entries
          rw [hNone] at hUpdate
          cases hUpdate
      | some next =>
          have hTail : entries.foldl
              (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
              (some next) = some trDelta' := by
            simpa [hEntry] using hUpdate
          have hResult := ih (trDelta := next) (priorTrace := priorTrace ++ [entry])
            (prefixUpdateEntry_invariant hInv hEntry) hTail
          simpa [List.append_assoc] using hResult

private theorem prefixUpdateInvariant_empty
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U] :
    PrefixUpdateInvariant
      (⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ : TraceNabla T_H T_P StmtIn U)
      [] := by
  refine ⟨TraceNabla.MirrorsQueryLog_empty_nil, ?_, ?_, ?_⟩
  · rw [LawfulTraceTable.toMultiSet_empty]
    exact Multiset.nodup_zero
  · rw [LawfulTraceTable.toMultiSet_empty]
    exact Multiset.nodup_zero
  · intro stmt capacity₁ capacity₂ h₁ _
    simp [LawfulTraceTable.toMultiSet_empty] at h₁

/-- A successful full `PrefixUpdate` table is realized by its input raw trace.  This is the
deduplication fact that the legacy `TraceNabla.ofQueryLog` fold lacked: repeated raw pairs remain
in the query log but contribute at most once to the normalized table. -/
theorem prefixUpdateTrace_isSubset
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {trDelta : TraceNabla T_H T_P StmtIn U}
    (hUpdate : prefixUpdateTrace trace = some trDelta) :
    trDelta.IsSubsetOfQueryLog trace := by
  apply prefixUpdateEntries_isSubset
    (trDelta := ⟨TraceTableOps.empty, TraceTableOps.empty⟩) (priorTrace := [])
  · exact TraceNabla.IsSubsetOfQueryLog_empty_nil
  · simpa [prefixUpdateTrace] using hUpdate

/-- A successful complete `PrefixUpdate` exactly mirrors the input raw trace at the level of
normalized hash and permutation pairs.  This is the `tr_∇` invariant used by the live H₀
Backtrack/LookAhead replay; equal raw occurrences remain in `trace` but appear only once in the
lookup table. -/
theorem prefixUpdateTrace_mirrors
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {trDelta : TraceNabla T_H T_P StmtIn U}
    (hUpdate : prefixUpdateTrace trace = some trDelta) :
    trDelta.MirrorsQueryLog trace := by
  apply prefixUpdateEntries_mirrors
    (trDelta := ⟨TraceTableOps.empty, TraceTableOps.empty⟩) (priorTrace := [])
  · exact TraceNabla.MirrorsQueryLog_empty_nil
  · simpa [prefixUpdateTrace] using hUpdate

/-- A successful complete `PrefixUpdate` has all reusable normalized-table invariants.  Together
with a caller's `¬ E trace` monitor fact, this is exactly the data needed to construct a
`D2SNormalState`; no raw trace occurrence is dropped. -/
theorem prefixUpdateTrace_invariant
    {StmtIn : Type} {T_H T_P : Type} [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {trDelta : TraceNabla T_H T_P StmtIn U}
    (hUpdate : prefixUpdateTrace trace = some trDelta) :
    PrefixUpdateInvariant trDelta trace := by
  apply prefixUpdateEntries_invariant
    (trDelta := ⟨TraceTableOps.empty, TraceTableOps.empty⟩) (priorTrace := [])
  · exact prefixUpdateInvariant_empty
  · simpa [prefixUpdateTrace] using hUpdate

end DuplexSpongeFS.ProverTransform

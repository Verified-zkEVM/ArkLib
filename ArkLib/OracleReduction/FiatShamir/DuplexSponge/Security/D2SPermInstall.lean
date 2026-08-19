/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceDataStructures

/-!
# Table-only permutation installation for revised D2SQuery

`Install` is deliberately below the simulator implementation.  It classifies an attempted
normalized permutation mapping as fresh, present, or conflicting; only a fresh mapping changes
the table.  The caller owns trace insertion and the subsequent monitor check.
-/

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {U : Type} [SpongeUnit U] [SpongeSize]

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

end DuplexSpongeFS.ProverTransform

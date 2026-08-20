/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SPermInstall

/-!
# No-conflict prefix normalization for a genuine duplex oracle

The offline `PrefixUpdate` table fold is intentionally stricter than the paper bad event: it
returns `none` on a repeated hash input with a different capacity, while such a later occurrence
is redundant for `getBaseTrace` and hence is not, by itself, an `E` witness.  Consequently the
Hyb0 replay proof must use the actual functional/bijective oracle semantics, not falsely derive
success of this fold from `¬ E` alone.

This module proves exactly that deterministic bridge.  It is generic in the hash function and
the forward/inverse permutation pair; the eager sponge instance supplies them from one sampled
`(h,p)` family.
-/

namespace DuplexSpongeFS.ProverTransform

open OracleSpec DSTraceStorage

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- A raw duplex occurrence agrees with one deterministic hash / permutation / inverse family. -/
def PrefixUpdateEntryAgrees {StmtIn : Type} [DecidableEq StmtIn] [DecidableEq U]
    (hashAnswer : StmtIn → Vector U SpongeSize.C)
    (permAnswer permInvAnswer : CanonicalSpongeState U → CanonicalSpongeState U)
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  match entry with
  | ⟨.inl stmt, capacity⟩ => capacity = hashAnswer stmt
  | ⟨.inr (.inl stateIn), stateOut⟩ => stateOut = permAnswer stateIn
  | ⟨.inr (.inr stateOut), stateIn⟩ => stateIn = permInvAnswer stateOut

/-- The normalized tables agree with the same deterministic oracle family. -/
def PrefixUpdateTableAgrees {StmtIn : Type} [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hashAnswer : StmtIn → Vector U SpongeSize.C)
    (permAnswer : CanonicalSpongeState U → CanonicalSpongeState U)
    (trDelta : TraceNabla T_H T_P StmtIn U) : Prop :=
  (∀ stmt capacity, (stmt, capacity) ∈ TraceTableOps.entries trDelta.h →
    capacity = hashAnswer stmt) ∧
  (∀ stateIn stateOut, (stateIn, stateOut) ∈ TraceTableOps.entries trDelta.p →
    stateOut = permAnswer stateIn)

private lemma prefixUpdateTableAgrees_empty {StmtIn : Type} [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hashAnswer : StmtIn → Vector U SpongeSize.C)
    (permAnswer : CanonicalSpongeState U → CanonicalSpongeState U) :
    PrefixUpdateTableAgrees hashAnswer permAnswer
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ : TraceNabla T_H T_P StmtIn U) := by
  constructor
  · intro stmt capacity hMem
    change (stmt, capacity) ∈ TraceTableOps.entries (TraceTableOps.empty : T_H) at hMem
    have hEmpty : (stmt, capacity) ∈ LawfulTraceTable.toMultiSet (TraceTableOps.empty : T_H) := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact hMem
    rw [LawfulTraceTable.toMultiSet_empty] at hEmpty
    simpa using hEmpty
  · intro stateIn stateOut hMem
    change (stateIn, stateOut) ∈ TraceTableOps.entries (TraceTableOps.empty : T_P) at hMem
    have hEmpty : (stateIn, stateOut) ∈ LawfulTraceTable.toMultiSet
        (TraceTableOps.empty : T_P) := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact hMem
    rw [LawfulTraceTable.toMultiSet_empty] at hEmpty
    simpa using hEmpty

/-- A table agreeing with a deterministic oracle family cannot conflict on a matching next raw
occurrence.  The inverse branch uses only `p (p⁻¹ y) = y`; no global decoder-surjectivity or
bad-event assumption is involved. -/
lemma prefixUpdateEntry_some_of_agrees {StmtIn : Type} [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hashAnswer : StmtIn → Vector U SpongeSize.C)
    (permAnswer permInvAnswer : CanonicalSpongeState U → CanonicalSpongeState U)
    (hPermInjective : Function.Injective permAnswer)
    (hPermInv : ∀ stateOut, permAnswer (permInvAnswer stateOut) = stateOut)
    (trDelta : TraceNabla T_H T_P StmtIn U)
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hTable : PrefixUpdateTableAgrees hashAnswer permAnswer trDelta)
    (hEntry : PrefixUpdateEntryAgrees hashAnswer permAnswer permInvAnswer entry) :
    ∃ trDelta', prefixUpdateEntry trDelta entry = some trDelta' := by
  rcases entry with ⟨query, answer⟩
  cases query with
  | inl stmt =>
      cases hStatus : hashInstallStatus trDelta.h stmt answer with
      | fresh =>
          exact ⟨{ trDelta with h := TraceTableOps.add trDelta.h stmt answer }, by
            simp [prefixUpdateEntry, installHash, hStatus]⟩
      | present =>
          exact ⟨trDelta, by simp [prefixUpdateEntry, installHash, hStatus]⟩
      | conflict =>
          exfalso
          unfold hashInstallStatus at hStatus
          cases hLookup : TraceTableOps.inlu trDelta.h stmt with
          | none => simp [hLookup] at hStatus
          | some stored =>
              simp only [hLookup] at hStatus
              split at hStatus
              · simp at hStatus
              · rename_i hNe
                have hMem := TraceTableOps.mem_entries_of_inlu_eq_some hLookup
                have hStored : stored = hashAnswer stmt := hTable.1 stmt stored hMem
                have hAnswer : answer = hashAnswer stmt := hEntry
                exact hNe (hStored.trans hAnswer.symm)
  | inr permutationQuery =>
      cases permutationQuery with
      | inl stateIn =>
          cases hStatus : permInstallStatus trDelta.p stateIn answer with
          | fresh =>
              exact ⟨{ trDelta with p := TraceTableOps.add trDelta.p stateIn answer }, by
                simp [prefixUpdateEntry, installPerm, hStatus]⟩
          | present =>
              exact ⟨trDelta, by simp [prefixUpdateEntry, installPerm, hStatus]⟩
          | conflict =>
              exfalso
              have hConflict : permPairConflicts trDelta.p stateIn answer = true :=
                (permInstallStatus_conflict_iff trDelta.p stateIn answer).mp hStatus
              obtain ⟨prior, hPriorMem, hPrior⟩ :=
                (permPairConflicts_eq_true_iff trDelta.p stateIn answer).mp hConflict
              have hPriorAnswer : prior.2 = permAnswer prior.1 :=
                hTable.2 prior.1 prior.2 hPriorMem
              have hAnswer : answer = permAnswer stateIn := hEntry
              rcases hPrior with (⟨hInput, hOutput⟩ | ⟨hOutput, hInput⟩)
              · apply hOutput
                calc
                  prior.2 = permAnswer prior.1 := hPriorAnswer
                  _ = permAnswer stateIn := by rw [hInput]
                  _ = answer := hAnswer.symm
              · apply hInput
                apply hPermInjective
                rw [← hPriorAnswer, hOutput, hAnswer]
      | inr stateOut =>
          cases hStatus : permInstallStatus trDelta.p answer stateOut with
          | fresh =>
              exact ⟨{ trDelta with p := TraceTableOps.add trDelta.p answer stateOut }, by
                simp [prefixUpdateEntry, installPerm, hStatus]⟩
          | present =>
              exact ⟨trDelta, by simp [prefixUpdateEntry, installPerm, hStatus]⟩
          | conflict =>
              exfalso
              have hConflict : permPairConflicts trDelta.p answer stateOut = true :=
                (permInstallStatus_conflict_iff trDelta.p answer stateOut).mp hStatus
              obtain ⟨prior, hPriorMem, hPrior⟩ :=
                (permPairConflicts_eq_true_iff trDelta.p answer stateOut).mp hConflict
              have hPriorAnswer : prior.2 = permAnswer prior.1 :=
                hTable.2 prior.1 prior.2 hPriorMem
              have hAnswer : answer = permInvAnswer stateOut := hEntry
              have hForward : stateOut = permAnswer answer := by
                rw [hAnswer]
                exact (hPermInv stateOut).symm
              rcases hPrior with (⟨hInput, hOutput⟩ | ⟨hOutput, hInput⟩)
              · apply hOutput
                calc
                  prior.2 = permAnswer prior.1 := hPriorAnswer
                  _ = permAnswer answer := by rw [hInput]
                  _ = stateOut := hForward.symm
              · apply hInput
                apply hPermInjective
                calc
                  permAnswer prior.1 = prior.2 := hPriorAnswer.symm
                  _ = stateOut := hOutput
                  _ = permAnswer answer := hForward

private lemma prefixUpdateEntry_tableAgrees {StmtIn : Type} [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hashAnswer : StmtIn → Vector U SpongeSize.C)
    (permAnswer permInvAnswer : CanonicalSpongeState U → CanonicalSpongeState U)
    (hPermInv : ∀ stateOut, permAnswer (permInvAnswer stateOut) = stateOut)
    {trDelta trDelta' : TraceNabla T_H T_P StmtIn U}
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hTable : PrefixUpdateTableAgrees hashAnswer permAnswer trDelta)
    (hEntry : PrefixUpdateEntryAgrees hashAnswer permAnswer permInvAnswer entry)
    (hUpdate : prefixUpdateEntry trDelta entry = some trDelta') :
    PrefixUpdateTableAgrees hashAnswer permAnswer trDelta' := by
  rcases entry with ⟨query, answer⟩
  cases query with
  | inl stmt =>
      cases hStatus : hashInstallStatus trDelta.h stmt answer with
      | fresh =>
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          constructor
          · intro stmt' capacity hMem
            rw [TraceTableOps.mem_entries_add_iff] at hMem
            rcases hMem with hNew | hOld
            · have hPair : (stmt', capacity) = (stmt, answer) := hNew
              injection hPair with hStmt hCapacity
              subst hStmt
              subst hCapacity
              exact hEntry
            · exact hTable.1 _ _ hOld
          · exact hTable.2
      | present =>
          simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
          subst trDelta'
          exact hTable
      | conflict => simp [prefixUpdateEntry, installHash, hStatus] at hUpdate
  | inr permutationQuery =>
      cases permutationQuery with
      | inl stateIn =>
          cases hStatus : permInstallStatus trDelta.p stateIn answer with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              constructor
              · exact hTable.1
              · intro stateIn' stateOut hMem
                rw [TraceTableOps.mem_entries_add_iff] at hMem
                rcases hMem with hNew | hOld
                · have hPair : (stateIn', stateOut) = (stateIn, answer) := hNew
                  injection hPair with hIn hOut
                  subst hIn
                  subst hOut
                  exact hEntry
                · exact hTable.2 _ _ hOld
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact hTable
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
      | inr stateOut =>
          cases hStatus : permInstallStatus trDelta.p answer stateOut with
          | fresh =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              constructor
              · exact hTable.1
              · intro stateIn' stateOut' hMem
                rw [TraceTableOps.mem_entries_add_iff] at hMem
                rcases hMem with hNew | hOld
                · have hPair : (stateIn', stateOut') = (answer, stateOut) := hNew
                  injection hPair with hIn hOut
                  have hAnswer : answer = permInvAnswer stateOut := hEntry
                  calc
                    stateOut' = stateOut := hOut
                    _ = permAnswer answer := by
                      rw [hAnswer]
                      exact (hPermInv stateOut).symm
                    _ = permAnswer stateIn' := by rw [hIn]
                · exact hTable.2 _ _ hOld
          | present =>
              simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate
              subst trDelta'
              exact hTable
          | conflict => simp [prefixUpdateEntry, installPerm, hStatus] at hUpdate

private lemma prefixUpdateEntries_some_of_agrees {StmtIn : Type} [DecidableEq StmtIn]
    [DecidableEq U] {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hashAnswer : StmtIn → Vector U SpongeSize.C)
    (permAnswer permInvAnswer : CanonicalSpongeState U → CanonicalSpongeState U)
    (hPermInjective : Function.Injective permAnswer)
    (hPermInv : ∀ stateOut, permAnswer (permInvAnswer stateOut) = stateOut)
    (entries : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hEntries : ∀ entry ∈ entries,
      PrefixUpdateEntryAgrees hashAnswer permAnswer permInvAnswer entry)
    (trDelta : TraceNabla T_H T_P StmtIn U)
    (hTable : PrefixUpdateTableAgrees hashAnswer permAnswer trDelta) :
    ∃ trDelta', entries.foldl
      (fun current entry => current.bind (fun tr => prefixUpdateEntry tr entry))
      (some trDelta) = some trDelta' ∧
      PrefixUpdateTableAgrees hashAnswer permAnswer trDelta' := by
  induction entries generalizing trDelta with
  | nil => exact ⟨trDelta, rfl, hTable⟩
  | cons entry entries ih =>
      have hEntry : PrefixUpdateEntryAgrees hashAnswer permAnswer permInvAnswer entry :=
        hEntries entry (by simp)
      obtain ⟨next, hStep⟩ := prefixUpdateEntry_some_of_agrees
        hashAnswer permAnswer permInvAnswer hPermInjective hPermInv trDelta entry hTable hEntry
      have hNext := prefixUpdateEntry_tableAgrees hashAnswer permAnswer permInvAnswer hPermInv
        entry hTable hEntry hStep
      have hTail : ∀ entry' ∈ entries,
          PrefixUpdateEntryAgrees hashAnswer permAnswer permInvAnswer entry' := by
        intro entry' hMem
        exact hEntries entry' (by simp [hMem])
      obtain ⟨final, hFold, hFinal⟩ := ih hTail next hNext
      refine ⟨final, ?_, hFinal⟩
      simpa [List.foldl, hStep] using hFold

/-- A raw trace answered by one deterministic hash function and one bijection/inverse pair cannot
make the revised offline `PrefixUpdate` fail.  This is the H₀-specific replay bridge: it covers
hash functionality, forward permutation functionality, and forward/inverse consistency, which
are genuine oracle semantics rather than consequences of the trace-only event `E`. -/
theorem prefixUpdateTrace_some_of_agrees {StmtIn : Type} [DecidableEq StmtIn] [DecidableEq U]
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (hashAnswer : StmtIn → Vector U SpongeSize.C)
    (permAnswer permInvAnswer : CanonicalSpongeState U → CanonicalSpongeState U)
    (hPermInjective : Function.Injective permAnswer)
    (hPermInv : ∀ stateOut, permAnswer (permInvAnswer stateOut) = stateOut)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hTrace : ∀ entry ∈ trace,
      PrefixUpdateEntryAgrees hashAnswer permAnswer permInvAnswer entry) :
    ∃ trDelta : TraceNabla T_H T_P StmtIn U, prefixUpdateTrace trace = some trDelta := by
  obtain ⟨trDelta, hFold, _⟩ := prefixUpdateEntries_some_of_agrees
    (T_H := T_H) (T_P := T_P) hashAnswer permAnswer
    permInvAnswer hPermInjective hPermInv trace hTrace
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ : TraceNabla T_H T_P StmtIn U)
      (prefixUpdateTableAgrees_empty (T_H := T_H) (T_P := T_P) hashAnswer permAnswer)
  exact ⟨trDelta, by simpa [prefixUpdateTrace] using hFold⟩

end DuplexSpongeFS.ProverTransform

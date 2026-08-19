/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedTransition
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform

/-!
# Restated permutation-install transitions for the revised D2SQuery boundary

These are the Phase&nbsp;2c restatements of `d2sInstallPermForwardState` /
`d2sInstallPermInverseState`: each now takes a `D2SNormalState` and returns a
`D2SRevisedStepResult`, preserving the exact revised order

    table-only Install → add one actual raw trace occurrence → Monitor.

The **conflict** branch does not modify the reusable table/cache, appends the attempted occurrence
to the terminal trace, and returns a `D2SPostOccurrenceStopRecord` (`stopped`), *never*
`Option.none`, via `install_conflict_fwd_imp_E` / `install_conflict_inv_imp_E`.

On **fresh** or **present** the occurrence is added and the **generic** Monitor is still run:
`continue` with a new normal state only when `E` of the extended trace fails; otherwise the same
post-occurrence `stopped` record is produced.  So a conflict is not the only possible stopping path.

The raw `d2sInstallPermForwardState` / `d2sInstallPermInverseState` (and their `_some_trace_append`
lemmas) are left untouched; the restated transitions reuse their successor construction directly
(the table/cache mutation is replayed through the same `TraceNabla` lemmas), and the
correspondence lemma below recovers the raw successor exactly.

**Elaboration note.**  Each restated transition is a single *dependent* `match hStatus : … with`
whose branch terms reference only the match binding `hStatus`.  Because `simp`/`rw`/`cases` cannot
retype a used-binder `match`, every contract below reduces the definition with the `split` tactic
(which case-splits the discriminant in place, keeping the branch binders type-correct); the branch
binders are exposed via `rename_i` and the carrier facts are finished by `by_cases hE` + `injection`
and, where a status hypothesis pins a different branch, by a derived constructor contradiction.

Each status also carries a precise trace/table/cache contract (fresh adds the pair, present and
conflict leave the reusable table and the rate-only cache untouched; every continue appends exactly
one occurrence), recovered by `d2sInstallPermForwardStateRevised_*` /
`d2sInstallPermInverseStateRevised_*` below.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-! ## Restated forward `Install` -/

/-- **Forward `Install` on a normal state, returning a `D2SRevisedStepResult`.**  Preserves the
revised order `Install → append occurrence → Monitor`.  A conflict immediately yields the
post-occurrence `stopped` record (crux) with the reusable table/cache untouched; a fresh or present
install appends its occurrence and runs the generic Monitor, continuing to a new normal state only
when `E` still fails. -/
noncomputable def d2sInstallPermForwardStateRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U) :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (CanonicalSpongeState U) := by
  classical
  match hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut with
  | .conflict =>
      exact .stopped normal
        ⟨dsPermQuery stateIn, stateOut, install_conflict_fwd_imp_E normal hStatus⟩
  | .fresh =>
      if hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) then
        exact .stopped normal ⟨dsPermQuery stateIn, stateOut, hE⟩
      else
        let trace' := normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]
        let trΔ' : TraceNabla T_H T_P StmtIn U :=
          { normal.state.trΔ with p := TraceTableOps.add normal.state.trΔ.p stateIn stateOut }
        let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_perm normal.state.h_inv stateIn stateOut
        let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_add normal.state.h_mirror stateIn stateOut
        let st' : D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
          { normal.state with
            trace := trace'
            trΔ := trΔ'
            h_inv := h_inv'
            h_mirror := h_mirror' }
        exact .continue stateOut ⟨st', hE,
          permInstallStatus_fresh_nodup_add normal.state.trΔ.p stateIn stateOut
            normal.permutationNodup hStatus, normal.hashNodup, normal.hashInputFunctional⟩
  | .present =>
      if hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) then
        exact .stopped normal ⟨dsPermQuery stateIn, stateOut, hE⟩
      else
        have h_mem : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
          permInstallStatus_present_mem normal.state.trΔ.p stateIn stateOut hStatus
        let trace' := normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]
        let h_inv' : normal.state.trΔ.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_any normal.state.h_inv
            ⟨dsPermQuery stateIn, stateOut⟩
        let h_mirror' : normal.state.trΔ.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_existing
            normal.state.h_mirror stateIn stateOut h_mem
        let st' : D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
          { normal.state with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }
        exact .continue stateOut ⟨st', hE, normal.permutationNodup,
          normal.hashNodup, normal.hashInputFunctional⟩

/-- **Forward `Install = conflict` contract.**  The reusable table/cache is untouched (the stopped
record's `normalState` is definitionally the input normal state), the attempted occurrence is
appended to the terminal trace, and the result is a `stopped` record — not `Option.none`. -/
lemma d2sInstallPermForwardStateRevised_conflict
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict) :
    d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .stopped normal
        ⟨dsPermQuery stateIn, stateOut, install_conflict_fwd_imp_E normal hStatus⟩ := by
  classical
  unfold d2sInstallPermForwardStateRevised
  split
  · simp
  · rename_i hfresh
    exact (nomatch (hfresh.symm.trans hStatus))
  · rename_i hpresent
    exact (nomatch (hpresent.symm.trans hStatus))

/-- **Forward correspondence.**  Whenever the restated transition continues, the raw table-only
install produced exactly the successor D2SQueryState. -/
lemma d2sInstallPermForwardStateRevised_correspondence
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermForwardStateRevised normal stateIn stateOut = .continue stateOut normal') :
    d2sInstallPermForwardState normal.state stateIn stateOut = some normal'.state := by
  classical
  unfold d2sInstallPermForwardStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      unfold d2sInstallPermForwardState
      split
      · rename_i hcon
        exact (nomatch (hcon.symm.trans hfresh))
      · rfl
      · rename_i hpre
        exact (nomatch (hpre.symm.trans hfresh))
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      unfold d2sInstallPermForwardState
      split
      · rename_i hcon
        exact (nomatch (hcon.symm.trans hpresent))
      · rename_i hfre
        exact (nomatch (hfre.symm.trans hpresent))
      · rfl

/-- A successful forward `Install` returns exactly the state supplied as its selected output.
This dependent-result fact lets lazy-tail and Program proofs recover the exact synthesized output
without re-unfolding the three `Install` status branches. -/
lemma d2sInstallPermForwardStateRevised_continue_answer_eq
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (h : d2sInstallPermForwardStateRevised normal stateIn stateOut = .continue answer normal') :
    answer = stateOut := by
  unfold d2sInstallPermForwardStateRevised at h
  split at h
  · simp_all
  · split at h
    · simp_all
    · injection h with hAnswer _
      exact hAnswer.symm
  · split at h
    · simp_all
    · injection h with hAnswer _
      exact hAnswer.symm

/-- **Forward `continue` trace contract.**  A continuing install appends exactly the forward
occurrence. -/
lemma d2sInstallPermForwardStateRevised_continue_trace
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermForwardStateRevised normal stateIn stateOut = .continue stateOut normal') :
    normal'.state.trace = normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩] := by
  classical
  unfold d2sInstallPermForwardStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp

/-- **Forward `continue` table (fresh) contract.**  A fresh install extends the reusable table by
the pair. -/
lemma d2sInstallPermForwardStateRevised_continue_table_fresh
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermForwardStateRevised normal stateIn stateOut = .continue stateOut normal') :
    normal'.state.trΔ.p = TraceTableOps.add normal.state.trΔ.p stateIn stateOut := by
  classical
  unfold d2sInstallPermForwardStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp
  · rename_i hpresent
    exact (nomatch (hpresent.symm.trans hStatus))

/-- **Forward `continue` table (present) contract.**  A present install leaves the table
unchanged. -/
lemma d2sInstallPermForwardStateRevised_continue_table_present
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermForwardStateRevised normal stateIn stateOut = .continue stateOut normal') :
    normal'.state.trΔ.p = normal.state.trΔ.p := by
  classical
  unfold d2sInstallPermForwardStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    exact (nomatch (hfresh.symm.trans hStatus))
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp

/-- **Forward `continue` cache contract.**  A continuing install leaves the rate-only cache
untouched. -/
lemma d2sInstallPermForwardStateRevised_continue_cache
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermForwardStateRevised normal stateIn stateOut = .continue stateOut normal') :
    normal'.state.rateCacheP = normal.state.rateCacheP := by
  classical
  unfold d2sInstallPermForwardStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp

/-- A `present` forward `Install` cannot stop: its occurrence is already redundant in the
`E`-good normal prefix, so `Monitor` remains false after the re-recording.  In particular this
deterministic table-hit branch has no fresh-capacity event to charge in Lemma 5.8. -/
lemma d2sInstallPermForwardStateRevised_present_not_stopped
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
    d2sInstallPermForwardStateRevised normal stateIn stateOut ≠ .stopped state record := by
  classical
  intro hStop
  unfold d2sInstallPermForwardStateRevised at hStop
  split at hStop
  · rename_i hConflict
    exact nomatch (hConflict.symm.trans hStatus)
  · rename_i hFresh
    exact nomatch (hFresh.symm.trans hStatus)
  · rename_i _hPresent
    simp [not_E_append_forward_of_present normal stateIn stateOut hStatus] at hStop

/-- Every stopped forward `Install` comes from a fresh or conflicting pair, never from a
deterministic table hit.  This is the exact status split used by the first-event probability
kernel: the sole capacity-bearing candidate is the one selected before this transition. -/
lemma d2sInstallPermForwardStateRevised_stopped_status
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state)
    (hStop : d2sInstallPermForwardStateRevised normal stateIn stateOut = .stopped state record) :
    permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh ∨
      permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict := by
  cases hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut with
  | fresh => exact Or.inl rfl
  | conflict => exact Or.inr rfl
  | present =>
      exact False.elim
        (d2sInstallPermForwardStateRevised_present_not_stopped normal stateIn stateOut hStatus
          state record hStop)

/-! ## Restated inverse `Install` -/

/-- **Inverse `Install` on a normal state, returning a `D2SRevisedStepResult`.**  Same contract as
the forward restatement, with the inverse occurrence and `install_conflict_inv_imp_E`. -/
noncomputable def d2sInstallPermInverseStateRevised
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U) :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (CanonicalSpongeState U) := by
  classical
  match hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut with
  | .conflict =>
      exact .stopped normal
        ⟨dsPermInvQuery stateOut, stateIn, install_conflict_inv_imp_E normal hStatus⟩
  | .fresh =>
      if hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) then
        exact .stopped normal ⟨dsPermInvQuery stateOut, stateIn, hE⟩
      else
        let trace' := normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]
        let trΔ' : TraceNabla T_H T_P StmtIn U :=
          { normal.state.trΔ with p := TraceTableOps.add normal.state.trΔ.p stateIn stateOut }
        let h_inv' : trΔ'.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_perm_inv normal.state.h_inv stateIn stateOut
        let h_mirror' : trΔ'.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_inv_add normal.state.h_mirror stateIn stateOut
        let st' : D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
          { normal.state with
            trace := trace'
            trΔ := trΔ'
            h_inv := h_inv'
            h_mirror := h_mirror' }
        exact .continue stateIn ⟨st', hE,
          permInstallStatus_fresh_nodup_add normal.state.trΔ.p stateIn stateOut
            normal.permutationNodup hStatus, normal.hashNodup, normal.hashInputFunctional⟩
  | .present =>
      if hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) then
        exact .stopped normal ⟨dsPermInvQuery stateOut, stateIn, hE⟩
      else
        have h_mem : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
          permInstallStatus_present_mem normal.state.trΔ.p stateIn stateOut hStatus
        let trace' := normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]
        let h_inv' : normal.state.trΔ.IsSubsetOfQueryLog trace' :=
          TraceNabla.IsSubsetOfQueryLog_append_any normal.state.h_inv
            ⟨dsPermInvQuery stateOut, stateIn⟩
        let h_mirror' : normal.state.trΔ.MirrorsQueryLog trace' :=
          TraceNabla.MirrorsQueryLog_append_perm_inv_existing
            normal.state.h_mirror stateIn stateOut h_mem
        let st' : D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
          { normal.state with trace := trace', h_inv := h_inv', h_mirror := h_mirror' }
        exact .continue stateIn ⟨st', hE, normal.permutationNodup,
          normal.hashNodup, normal.hashInputFunctional⟩

/-- **Inverse `Install = conflict` contract.**  Same as the forward conflict contract, with the
inverse occurrence and `install_conflict_inv_imp_E`. -/
lemma d2sInstallPermInverseStateRevised_conflict
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict) :
    d2sInstallPermInverseStateRevised normal stateOut stateIn =
      .stopped normal
        ⟨dsPermInvQuery stateOut, stateIn, install_conflict_inv_imp_E normal hStatus⟩ := by
  classical
  unfold d2sInstallPermInverseStateRevised
  split
  · simp
  · rename_i hfresh
    exact (nomatch (hfresh.symm.trans hStatus))
  · rename_i hpresent
    exact (nomatch (hpresent.symm.trans hStatus))

/-- **Inverse correspondence.**  Whenever the restated inverse transition continues, the raw
table-only inverse install produced exactly the successor D2SQueryState. -/
lemma d2sInstallPermInverseStateRevised_correspondence
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermInverseStateRevised normal stateOut stateIn = .continue stateIn normal') :
    d2sInstallPermInverseState normal.state stateOut stateIn = some normal'.state := by
  classical
  unfold d2sInstallPermInverseStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      unfold d2sInstallPermInverseState
      split
      · rename_i hcon
        exact (nomatch (hcon.symm.trans hfresh))
      · rfl
      · rename_i hpre
        exact (nomatch (hpre.symm.trans hfresh))
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      unfold d2sInstallPermInverseState
      split
      · rename_i hcon
        exact (nomatch (hcon.symm.trans hpresent))
      · rename_i hfre
        exact (nomatch (hfre.symm.trans hpresent))
      · rfl

/-- **Inverse `continue` trace contract.**  A continuing inverse install appends exactly the
inverse occurrence. -/
lemma d2sInstallPermInverseStateRevised_continue_trace
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermInverseStateRevised normal stateOut stateIn = .continue stateIn normal') :
    normal'.state.trace = normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩] := by
  classical
  unfold d2sInstallPermInverseStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp

/-- **Inverse `continue` table (fresh) contract.**  A fresh inverse install extends the table by
the pair. -/
lemma d2sInstallPermInverseStateRevised_continue_table_fresh
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermInverseStateRevised normal stateOut stateIn = .continue stateIn normal') :
    normal'.state.trΔ.p = TraceTableOps.add normal.state.trΔ.p stateIn stateOut := by
  classical
  unfold d2sInstallPermInverseStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp
  · rename_i hpresent
    exact (nomatch (hpresent.symm.trans hStatus))

/-- **Inverse `continue` table (present) contract.**  A present inverse install leaves the table
unchanged. -/
lemma d2sInstallPermInverseStateRevised_continue_table_present
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermInverseStateRevised normal stateOut stateIn = .continue stateIn normal') :
    normal'.state.trΔ.p = normal.state.trΔ.p := by
  classical
  unfold d2sInstallPermInverseStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    exact (nomatch (hfresh.symm.trans hStatus))
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp

/-- **Inverse `continue` cache contract.**  A continuing inverse install leaves the rate-only cache
untouched. -/
lemma d2sInstallPermInverseStateRevised_continue_cache
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (h : d2sInstallPermInverseStateRevised normal stateOut stateIn = .continue stateIn normal') :
    normal'.state.rateCacheP = normal.state.rateCacheP := by
  classical
  unfold d2sInstallPermInverseStateRevised at h
  split at h
  · simp_all
  · rename_i hfresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp
  · rename_i hpresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp [hE] at h
    · simp [hE] at h
      subst normal'
      simp

/-- The inverse table-hit counterpart of
`d2sInstallPermForwardStateRevised_present_not_stopped`. -/
lemma d2sInstallPermInverseStateRevised_present_not_stopped
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state) :
    d2sInstallPermInverseStateRevised normal stateOut stateIn ≠ .stopped state record := by
  classical
  intro hStop
  unfold d2sInstallPermInverseStateRevised at hStop
  split at hStop
  · rename_i hConflict
    exact nomatch (hConflict.symm.trans hStatus)
  · rename_i hFresh
    exact nomatch (hFresh.symm.trans hStatus)
  · rename_i _hPresent
    simp [not_E_append_inverse_of_present normal stateIn stateOut hStatus] at hStop

/-- Inverse counterpart of `d2sInstallPermForwardStateRevised_stopped_status`. -/
lemma d2sInstallPermInverseStateRevised_stopped_status
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (state : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) state)
    (hStop : d2sInstallPermInverseStateRevised normal stateOut stateIn = .stopped state record) :
    permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh ∨
      permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict := by
  cases hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut with
  | fresh => exact Or.inl rfl
  | conflict => exact Or.inr rfl
  | present =>
      exact False.elim
        (d2sInstallPermInverseStateRevised_present_not_stopped normal stateOut stateIn hStatus
          state record hStop)

end DuplexSpongeFS.ProverTransform

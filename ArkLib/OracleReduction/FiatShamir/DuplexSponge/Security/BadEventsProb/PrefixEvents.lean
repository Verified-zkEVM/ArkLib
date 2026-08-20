/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CapacityTargets

/-!
# Prefix stability for per-index bad events

This file contains pure trace/list lemmas used by the Lemma 5.8 state-invariant arguments.
The main statement is `E_at_of_getBaseTrace_append_eq`: once a later trace has a base trace
extending an earlier base trace, every earlier per-index bad-event witness remains a witness at
the same base index.

The lemmas here deliberately do not mention the simulator state machine or probability monad.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- If a later trace has base trace `getBaseTrace trace ++ extra`, then old base-trace entries
at old indices are unchanged. -/
lemma getBaseTrace_getElem_eq_of_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (hj' : j < (getBaseTrace trace').length) :
    (getBaseTrace trace')[j]'hj' = (getBaseTrace trace)[j]'hj := by
  let hjApp : j < (getBaseTrace trace ++ extra).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  have hleft : (getBaseTrace trace')[j]'hj' =
      (getBaseTrace trace ++ extra)[j]'hjApp :=
    getElem_congr hbt rfl hj'
  have hright : (getBaseTrace trace ++ extra)[j]'hjApp = (getBaseTrace trace)[j]'hj := by
    rw [List.getElem_append_left (bs := extra) hj]
  exact hleft.trans hright

/-- An entry of an appended list whose natural index lies in the left prefix is literally the
corresponding entry of that prefix.  This `Fin`-indexed form avoids proof-irrelevance casts in
the backward (first-bad) transport lemmas below. -/
lemma getElem_append_left_of_fin
    {α : Type} {xs ys : List α}
    (i : Fin (xs ++ ys).length) (hi : i.1 < xs.length) :
    (xs ++ ys)[i.1]'i.2 = xs[i.1]'hi := by
  rw [List.getElem_append_left (bs := ys) hi]

/-- Transport a duplicate-capacity witness across definitional equality of base traces. -/
lemma isDuplicatedPriorCapacity_of_baseTrace_eq
    {baseTrace baseTrace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} {hj : j < baseTrace.length} {hj' : j < baseTrace'.length}
    {capSeg : Vector U SpongeSize.C}
    (hbt : baseTrace = baseTrace')
    (h : isDuplicatedPriorCapacity baseTrace' ⟨j, hj'⟩ capSeg) :
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg := by
  cases hbt
  exact h

/-- A duplicate-capacity witness at an old index remains valid after appending any suffix to the
base trace. -/
lemma isDuplicatedPriorCapacity_append_of_lt
    {baseTrace extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} (hj : j < baseTrace.length)
    {capSeg : Vector U SpongeSize.C}
    (hdup : isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg) :
    isDuplicatedPriorCapacity (baseTrace ++ extra)
      ⟨j, by
        rw [List.length_append]
        exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
      ⟩ capSeg := by
  unfold isDuplicatedPriorCapacity at hdup ⊢
  rcases hdup with hH | hPout | hPinIn | hPin | hPoutInv
  · rcases hH with ⟨j', hlt, stmt', hidx⟩
    refine Or.inl ⟨⟨j'.1, ?_⟩, ?_, stmt', ?_⟩
    · rw [List.length_append]
      exact Nat.lt_of_lt_of_le j'.2 (Nat.le_add_right _ _)
    · exact hlt
    · have hidx' : (baseTrace ++ extra)[j'.1] = ⟨Sum.inl stmt', capSeg⟩ := by
        rw [List.getElem_append_left (bs := extra) j'.2]
        exact hidx
      exact hidx'
  · rcases hPout with ⟨j', hlt, stateIn1, stateOut1, hidx, hcap⟩
    refine Or.inr (Or.inl ⟨⟨j'.1, ?_⟩, ?_, stateIn1, stateOut1, ?_, hcap⟩)
    · rw [List.length_append]
      exact Nat.lt_of_lt_of_le j'.2 (Nat.le_add_right _ _)
    · exact hlt
    · have hidx' :
          (baseTrace ++ extra)[j'.1] = ⟨Sum.inr (Sum.inl stateIn1), stateOut1⟩ := by
        rw [List.getElem_append_left (bs := extra) j'.2]
        exact hidx
      exact hidx'
  · rcases hPinIn with ⟨j', hlt, stateOut2, stateIn2, hidx, hcap⟩
    refine Or.inr (Or.inr (Or.inl ⟨⟨j'.1, ?_⟩, ?_, stateOut2, stateIn2, ?_, hcap⟩))
    · rw [List.length_append]
      exact Nat.lt_of_lt_of_le j'.2 (Nat.le_add_right _ _)
    · exact hlt
    · have hidx' :
          (baseTrace ++ extra)[j'.1] = ⟨Sum.inr (Sum.inr stateOut2), stateIn2⟩ := by
        rw [List.getElem_append_left (bs := extra) j'.2]
        exact hidx
      exact hidx'
  · rcases hPin with ⟨j', hle, stateIn3, stateOut3, hidx, hcap⟩
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨j'.1, ?_⟩, ?_, stateIn3, stateOut3, ?_, hcap⟩)))
    · rw [List.length_append]
      exact Nat.lt_of_lt_of_le j'.2 (Nat.le_add_right _ _)
    · exact hle
    · have hidx' :
          (baseTrace ++ extra)[j'.1] = ⟨Sum.inr (Sum.inl stateIn3), stateOut3⟩ := by
        rw [List.getElem_append_left (bs := extra) j'.2]
        exact hidx
      exact hidx'
  · rcases hPoutInv with ⟨j', hle, stateOut4, stateIn4, hidx, hcap⟩
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨j'.1, ?_⟩, ?_, stateOut4, stateIn4, ?_, hcap⟩)))
    · rw [List.length_append]
      exact Nat.lt_of_lt_of_le j'.2 (Nat.le_add_right _ _)
    · exact hle
    · have hidx' :
          (baseTrace ++ extra)[j'.1] = ⟨Sum.inr (Sum.inr stateOut4), stateIn4⟩ := by
        rw [List.getElem_append_left (bs := extra) j'.2]
        exact hidx
      exact hidx'

/-- A duplicate-capacity witness at an old position of an appended base trace was already a
witness in the prefix.  The capacity predicate therefore depends only on entries through its
designated index. -/
lemma isDuplicatedPriorCapacity_of_append_of_lt
    {baseTrace extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {j : ℕ} (hj : j < baseTrace.length)
    {capSeg : Vector U SpongeSize.C}
    (hdup : isDuplicatedPriorCapacity (baseTrace ++ extra)
      ⟨j, by
        rw [List.length_append]
        exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
      ⟩ capSeg) :
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg := by
  unfold isDuplicatedPriorCapacity at hdup ⊢
  rcases hdup with hH | hPout | hPinIn | hPin | hPoutInv
  · rcases hH with ⟨j', hlt, stmt', hidx⟩
    have hjlt : j'.1 < j := by simpa only [Fin.mk_lt_mk] using hlt
    have hjOld : j'.1 < baseTrace.length := Nat.lt_trans hjlt hj
    refine Or.inl ⟨⟨j'.1, hjOld⟩, hjlt, stmt', ?_⟩
    calc
      baseTrace[j'.1]'hjOld = (baseTrace ++ extra)[j'.1]'j'.2 :=
        (getElem_append_left_of_fin j' hjOld).symm
      _ = ⟨Sum.inl stmt', capSeg⟩ := hidx
  · rcases hPout with ⟨j', hlt, stateIn, stateOut, hidx, hcap⟩
    have hjlt : j'.1 < j := by simpa only [Fin.mk_lt_mk] using hlt
    have hjOld : j'.1 < baseTrace.length := Nat.lt_trans hjlt hj
    refine Or.inr (Or.inl ⟨⟨j'.1, hjOld⟩, hjlt, stateIn, stateOut, ?_, hcap⟩)
    calc
      baseTrace[j'.1]'hjOld = (baseTrace ++ extra)[j'.1]'j'.2 :=
        (getElem_append_left_of_fin j' hjOld).symm
      _ = ⟨Sum.inr (Sum.inl stateIn), stateOut⟩ := hidx
  · rcases hPinIn with ⟨j', hlt, stateOut, stateIn, hidx, hcap⟩
    have hjlt : j'.1 < j := by simpa only [Fin.mk_lt_mk] using hlt
    have hjOld : j'.1 < baseTrace.length := Nat.lt_trans hjlt hj
    refine Or.inr (Or.inr (Or.inl
      ⟨⟨j'.1, hjOld⟩, hjlt, stateOut, stateIn, ?_, hcap⟩))
    calc
      baseTrace[j'.1]'hjOld = (baseTrace ++ extra)[j'.1]'j'.2 :=
        (getElem_append_left_of_fin j' hjOld).symm
      _ = ⟨Sum.inr (Sum.inr stateOut), stateIn⟩ := hidx
  · rcases hPin with ⟨j', hle, stateIn, stateOut, hidx, hcap⟩
    have hjOld : j'.1 < baseTrace.length := Nat.lt_of_le_of_lt hle hj
    refine Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨j'.1, hjOld⟩, hle, stateIn, stateOut, ?_, hcap⟩)))
    calc
      baseTrace[j'.1]'hjOld = (baseTrace ++ extra)[j'.1]'j'.2 :=
        (getElem_append_left_of_fin j' hjOld).symm
      _ = ⟨Sum.inr (Sum.inl stateIn), stateOut⟩ := hidx
  · rcases hPoutInv with ⟨j', hle, stateOut, stateIn, hidx, hcap⟩
    have hjOld : j'.1 < baseTrace.length := Nat.lt_of_le_of_lt hle hj
    refine Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨j'.1, hjOld⟩, hle, stateOut, stateIn, ?_, hcap⟩)))
    calc
      baseTrace[j'.1]'hjOld = (baseTrace ++ extra)[j'.1]'j'.2 :=
        (getElem_append_left_of_fin j' hjOld).symm
      _ = ⟨Sum.inr (Sum.inr stateOut), stateIn⟩ := hidx

/-- Helper combining append stability with transport along `getBaseTrace trace' = ...`. -/
lemma duplicated_event_lift_append
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    {capSeg : Vector U SpongeSize.C}
    (hdup : isDuplicatedPriorCapacity (getBaseTrace trace) ⟨j, hj⟩ capSeg)
    (hjNew : j < (getBaseTrace trace').length) :
    isDuplicatedPriorCapacity (getBaseTrace trace') ⟨j, hjNew⟩ capSeg := by
  let hjApp : j < (getBaseTrace trace ++ extra).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  exact isDuplicatedPriorCapacity_of_baseTrace_eq (baseTrace := getBaseTrace trace')
    (baseTrace' := getBaseTrace trace ++ extra) (j := j) (hj := hjNew) (hj' := hjApp)
    hbt (isDuplicatedPriorCapacity_append_of_lt (extra := extra) hj hdup)

/-- Reflect a duplicate-capacity witness from an appended base trace to its left prefix. -/
lemma duplicated_event_reflect_append
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    {capSeg : Vector U SpongeSize.C}
    (hdup : isDuplicatedPriorCapacity (getBaseTrace trace')
      ⟨j, by
        rw [hbt, List.length_append]
        exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
      ⟩ capSeg) :
    isDuplicatedPriorCapacity (getBaseTrace trace) ⟨j, hj⟩ capSeg := by
  let hjApp : j < (getBaseTrace trace ++ extra).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  have hdupApp : isDuplicatedPriorCapacity (getBaseTrace trace ++ extra)
      ⟨j, hjApp⟩ capSeg :=
    isDuplicatedPriorCapacity_of_baseTrace_eq
      (baseTrace := getBaseTrace trace ++ extra) (baseTrace' := getBaseTrace trace')
      (j := j) (hj := hjApp) hbt.symm hdup
  exact isDuplicatedPriorCapacity_of_append_of_lt hj hdupApp

lemma E_h_at_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_h_at trace j) :
    E_h_at trace' j := by
  unfold E_h_at at h ⊢
  rcases h with ⟨_, capSeg, hentry, hdup⟩
  let hjNew : j < (getBaseTrace trace').length := by
    rw [hbt, List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  refine ⟨hjNew, capSeg, ?_, duplicated_event_lift_append hbt hj hdup hjNew⟩
  rcases hentry with ⟨stmt, hidx⟩
  exact ⟨stmt, (getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).trans hidx⟩

/-- A hash duplicate event at an old base index is equivalent in a trace and any of its base
trace extensions.  This is the reverse half of the first-bad prefix transport. -/
lemma E_h_at_of_getBaseTrace_append_eq_of_lt
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_h_at trace' j) :
    E_h_at trace j := by
  unfold E_h_at at h ⊢
  rcases h with ⟨hjNew, capSeg, hentry, hdup⟩
  refine ⟨hj, capSeg, ?_, duplicated_event_reflect_append hbt hj hdup⟩
  rcases hentry with ⟨stmt, hidx⟩
  exact ⟨stmt, (getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).symm.trans hidx⟩

lemma E_p_at_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_p_at trace j) :
    E_p_at trace' j := by
  unfold E_p_at at h ⊢
  rcases h with ⟨_, capSeg, hentry, hdup⟩
  let hjNew : j < (getBaseTrace trace').length := by
    rw [hbt, List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  refine ⟨hjNew, capSeg, ?_, duplicated_event_lift_append hbt hj hdup hjNew⟩
  rcases hentry with ⟨stateIn, stateOut, hidx, hcap⟩
  exact ⟨stateIn, stateOut,
    (getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).trans hidx, hcap⟩

/-- Reflect a forward-permutation duplicate event from an extension to an old base index. -/
lemma E_p_at_of_getBaseTrace_append_eq_of_lt
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_p_at trace' j) :
    E_p_at trace j := by
  unfold E_p_at at h ⊢
  rcases h with ⟨hjNew, capSeg, hentry, hdup⟩
  refine ⟨hj, capSeg, ?_, duplicated_event_reflect_append hbt hj hdup⟩
  rcases hentry with ⟨stateIn, stateOut, hidx, hcap⟩
  exact ⟨stateIn, stateOut,
    (getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).symm.trans hidx, hcap⟩

lemma E_pinv_at_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_pinv_at trace j) :
    E_pinv_at trace' j := by
  unfold E_pinv_at at h ⊢
  rcases h with ⟨_, capSeg, hentry, hdup⟩
  let hjNew : j < (getBaseTrace trace').length := by
    rw [hbt, List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  refine ⟨hjNew, capSeg, ?_, duplicated_event_lift_append hbt hj hdup hjNew⟩
  rcases hentry with ⟨stateOut, stateIn, hidx, hcap⟩
  exact ⟨stateOut, stateIn,
    (getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).trans hidx, hcap⟩

/-- Reflect an inverse-permutation duplicate event from an extension to an old base index. -/
lemma E_pinv_at_of_getBaseTrace_append_eq_of_lt
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_pinv_at trace' j) :
    E_pinv_at trace j := by
  unfold E_pinv_at at h ⊢
  rcases h with ⟨hjNew, capSeg, hentry, hdup⟩
  refine ⟨hj, capSeg, ?_, duplicated_event_reflect_append hbt hj hdup⟩
  rcases hentry with ⟨stateOut, stateIn, hidx, hcap⟩
  exact ⟨stateOut, stateIn,
    (getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).symm.trans hidx, hcap⟩

lemma E_func_at_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_func_at trace j) :
    E_func_at trace' j := by
  unfold E_func_at at h ⊢
  rcases h with ⟨_, stateIn, stateOut, hF | hB⟩
  · let hjNew : j < (getBaseTrace trace').length := by
      rw [hbt, List.length_append]
      exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
    refine ⟨hjNew, stateIn, stateOut, Or.inl ?_⟩
    rcases hF with ⟨hNow, hPrior⟩
    refine ⟨(getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).trans hNow, ?_⟩
    rcases hPrior with ⟨j', hlt, hprior⟩
    let hjpNew : j'.1 < (getBaseTrace trace').length := by
      rw [hbt, List.length_append]
      exact Nat.lt_of_lt_of_le j'.2 (Nat.le_add_right _ _)
    refine ⟨⟨j'.1, hjpNew⟩, ?_, ?_⟩
    · exact hlt
    · rcases hprior with hprior | hprior
      · rcases hprior with ⟨stateOut1, hidx, hne⟩
        exact Or.inl ⟨stateOut1,
          (getBaseTrace_getElem_eq_of_append_eq hbt j'.2 hjpNew).trans hidx, hne⟩
      · rcases hprior with ⟨stateOut2, hidx, hne⟩
        exact Or.inr ⟨stateOut2,
          (getBaseTrace_getElem_eq_of_append_eq hbt j'.2 hjpNew).trans hidx, hne⟩
  · let hjNew : j < (getBaseTrace trace').length := by
      rw [hbt, List.length_append]
      exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
    refine ⟨hjNew, stateIn, stateOut, Or.inr ?_⟩
    rcases hB with ⟨hNow, hPrior⟩
    refine ⟨(getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).trans hNow, ?_⟩
    rcases hPrior with ⟨j', hlt, hprior⟩
    let hjpNew : j'.1 < (getBaseTrace trace').length := by
      rw [hbt, List.length_append]
      exact Nat.lt_of_lt_of_le j'.2 (Nat.le_add_right _ _)
    refine ⟨⟨j'.1, hjpNew⟩, ?_, ?_⟩
    · exact hlt
    · rcases hprior with hprior | hprior
      · rcases hprior with ⟨stateIn1, hidx, hne⟩
        exact Or.inl ⟨stateIn1,
          (getBaseTrace_getElem_eq_of_append_eq hbt j'.2 hjpNew).trans hidx, hne⟩
      · rcases hprior with ⟨stateIn2, hidx, hne⟩
        exact Or.inr ⟨stateIn2,
          (getBaseTrace_getElem_eq_of_append_eq hbt j'.2 hjpNew).trans hidx, hne⟩

/-- Reflect a functionality event from an extension to an old base index.  Both entries in its
witness lie at indices at most `j`, so neither can be introduced by the appended suffix. -/
lemma E_func_at_of_getBaseTrace_append_eq_of_lt
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_func_at trace' j) :
    E_func_at trace j := by
  unfold E_func_at at h ⊢
  rcases h with ⟨hjNew, stateIn, stateOut, hF | hB⟩
  · refine ⟨hj, stateIn, stateOut, Or.inl ?_⟩
    rcases hF with ⟨hNow, hPrior⟩
    refine ⟨(getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).symm.trans hNow, ?_⟩
    rcases hPrior with ⟨j', hlt, hprior⟩
    have hjpLt : j'.1 < j := by simpa only [Fin.mk_lt_mk] using hlt
    have hjp : j'.1 < (getBaseTrace trace).length := Nat.lt_trans hjpLt hj
    refine ⟨⟨j'.1, hjp⟩, hjpLt, ?_⟩
    rcases hprior with hprior | hprior
    · rcases hprior with ⟨stateOut1, hidx, hne⟩
      exact Or.inl ⟨stateOut1,
        (getBaseTrace_getElem_eq_of_append_eq hbt hjp j'.2).symm.trans hidx, hne⟩
    · rcases hprior with ⟨stateOut2, hidx, hne⟩
      exact Or.inr ⟨stateOut2,
        (getBaseTrace_getElem_eq_of_append_eq hbt hjp j'.2).symm.trans hidx, hne⟩
  · refine ⟨hj, stateIn, stateOut, Or.inr ?_⟩
    rcases hB with ⟨hNow, hPrior⟩
    refine ⟨(getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).symm.trans hNow, ?_⟩
    rcases hPrior with ⟨j', hlt, hprior⟩
    have hjpLt : j'.1 < j := by simpa only [Fin.mk_lt_mk] using hlt
    have hjp : j'.1 < (getBaseTrace trace).length := Nat.lt_trans hjpLt hj
    refine ⟨⟨j'.1, hjp⟩, hjpLt, ?_⟩
    rcases hprior with hprior | hprior
    · rcases hprior with ⟨stateIn1, hidx, hne⟩
      exact Or.inl ⟨stateIn1,
        (getBaseTrace_getElem_eq_of_append_eq hbt hjp j'.2).symm.trans hidx, hne⟩
    · rcases hprior with ⟨stateIn2, hidx, hne⟩
      exact Or.inr ⟨stateIn2,
        (getBaseTrace_getElem_eq_of_append_eq hbt hjp j'.2).symm.trans hidx, hne⟩

/-- Any old per-index bad event remains true after extending the base trace by an arbitrary
suffix. -/
lemma E_at_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (h : E_at trace j) :
    E_at trace' j := by
  have hj : j < (getBaseTrace trace).length := E_at_lt_length trace h
  rcases h with hH | hP | hPinv | hFunc
  · exact Or.inl (E_h_at_of_getBaseTrace_append_eq hbt hj hH)
  · exact Or.inr (Or.inl (E_p_at_of_getBaseTrace_append_eq hbt hj hP))
  · exact Or.inr (Or.inr (Or.inl (E_pinv_at_of_getBaseTrace_append_eq hbt hj hPinv)))
  · exact Or.inr (Or.inr (Or.inr (E_func_at_of_getBaseTrace_append_eq hbt hj hFunc)))

/-- Every per-index event whose index lies in a base-trace prefix reflects from an arbitrary
suffix extension to that prefix. -/
lemma E_at_of_getBaseTrace_append_eq_of_lt
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_at trace' j) :
    E_at trace j := by
  rcases h with hH | hP | hPinv | hFunc
  · exact Or.inl (E_h_at_of_getBaseTrace_append_eq_of_lt hbt hj hH)
  · exact Or.inr (Or.inl (E_p_at_of_getBaseTrace_append_eq_of_lt hbt hj hP))
  · exact Or.inr (Or.inr (Or.inl (E_pinv_at_of_getBaseTrace_append_eq_of_lt hbt hj hPinv)))
  · exact Or.inr (Or.inr (Or.inr (E_func_at_of_getBaseTrace_append_eq_of_lt hbt hj hFunc)))

/-- First-bad status at an index already present in a prefix is invariant under any later base
trace suffix.  This is the precise trace fact used to identify a raw final first-bad witness with
the state retained by `monitorStop`. -/
lemma E_first_at_iff_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length) :
    E_first_at trace' j ↔ E_first_at trace j := by
  constructor
  · rintro ⟨hAt, hNoPrior⟩
    refine ⟨E_at_of_getBaseTrace_append_eq_of_lt hbt hj hAt, ?_⟩
    intro j' hj' hBad
    exact hNoPrior j' hj' (E_at_of_getBaseTrace_append_eq hbt hBad)
  · rintro ⟨hAt, hNoPrior⟩
    refine ⟨E_at_of_getBaseTrace_append_eq hbt hAt, ?_⟩
    intro j' hj' hBad
    have hjOld : j' < (getBaseTrace trace).length := Nat.lt_trans hj' hj
    exact hNoPrior j' hj'
      (E_at_of_getBaseTrace_append_eq_of_lt hbt hjOld hBad)

/-- Global bad-event monotonicity under a base-trace suffix extension. -/
lemma E_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (h : E trace) :
    E trace' := by
  obtain ⟨j, hj⟩ := (E_iff_exists_E_at trace).mp h
  exact (E_iff_exists_E_at trace').mpr ⟨j, E_at_of_getBaseTrace_append_eq hbt hj⟩

/-- The combined bad event is monotone under extension of the *raw* insertion trace.  Normalizing
the longer trace may discard later redundant entries, but it never changes the already processed
base prefix (`getBaseTrace_prefix_of_prefix`); hence a witness already present in the prefix is
still a witness in the extension.  This is the form consumed by the revised `StdTrace` and
stateful-run abort arguments. -/
lemma E_mono_of_raw_prefix
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
  (hprefix : trace <+: trace')
    (h : E trace) :
    E trace' := by
  have hbase : getBaseTrace trace ++ (getBaseTrace trace').drop (getBaseTrace trace).length =
      getBaseTrace trace' :=
    List.prefix_iff_eq_append.mp
      (getBaseTrace_prefix_of_prefix (StmtIn := StmtIn) (U := U) hprefix)
  exact E_of_getBaseTrace_append_eq hbase.symm h

/-- The global bad event depends only on the normalized base trace.  This is the equality form
of the preceding prefix transport lemmas and is the canonical eliminator for a redundant raw
occurrence: no client must rewrite through dependent `Fin baseTrace.length` witnesses directly. -/
lemma E_iff_of_getBaseTrace_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hbt : getBaseTrace trace' = getBaseTrace trace) :
    E trace' ↔ E trace := by
  constructor
  · intro hE
    obtain ⟨j, hFirst⟩ := (E_iff_exists_E_first_at trace').mp hE
    have hj : j < (getBaseTrace trace).length := by
      have hj' := E_at_lt_length trace' hFirst.1
      simpa only [hbt] using hj'
    have hbt' : getBaseTrace trace' = getBaseTrace trace ++ [] := by
      simpa using hbt
    exact (E_iff_exists_E_first_at trace).mpr
      ⟨j, (E_first_at_iff_of_getBaseTrace_append_eq hbt' hj).mp hFirst⟩
  · intro hE
    have hbt' : getBaseTrace trace' = getBaseTrace trace ++ [] := by
      simpa using hbt
    exact E_of_getBaseTrace_append_eq hbt' hE

end BadEventDS

end DuplexSpongeFS

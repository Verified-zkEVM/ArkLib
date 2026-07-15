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

/-- A one-entry raw extension retains the old base trace and appends at most its representative.
This trace-only suffix decomposition is shared by the hash-credit and functional-invariant
runner proofs. -/
lemma getBaseTrace_append_singleton_exists_suffix
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) :
    ∃ extra : QueryLog (duplexSpongeChallengeOracle StmtIn U),
      getBaseTrace (trace ++ [entry]) = getBaseTrace trace ++ extra := by
  classical
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace trace) entry
  · refine ⟨[], ?_⟩
    rw [DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace entry hred]
    rw [List.append_nil]
  · refine ⟨[entry], ?_⟩
    exact DuplexSpongeFS.getBaseTrace_append_singleton_of_not_redundant_base trace entry hred

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

/-- Global bad-event monotonicity under a base-trace suffix extension. -/
lemma E_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (h : E trace) :
    E trace' := by
  obtain ⟨j, hj⟩ := (E_iff_exists_E_at trace).mp h
  exact (E_iff_exists_E_at trace').mpr ⟨j, E_at_of_getBaseTrace_append_eq hbt hj⟩

end BadEventDS

end DuplexSpongeFS

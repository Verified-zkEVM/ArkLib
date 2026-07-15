/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.HashStopping

/-!
# Lazy inverse-permutation stopping credit for Lemma 5.8

This module proves the trace-stability half of the sigma-side `E_{p^{-1}}` argument.  It is
deliberately independent of a global functionality hypothesis for `trΔ.p`: an `outlu` hit is
redundant by the mirror invariant, while on an `outlu` miss the handler samples a full state.
Whether that sampled raw answer survives `getBaseTrace` is immaterial: only a surviving answer can
occupy the new base position, and then its capacity is exactly the fresh sample.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : ℕ}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section PermInverseCredit

variable [Fintype U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

variable
  (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
  (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))

/-- The sigma-side inverse-permutation collision event after the `j`th base representative has
been created.  Its readout is the paper's `E_{p^{-1}}` target: the representative's sampled
preimage capacity matches one of its `2j+1` prior/self capacity targets. -/
def permBwdCredit
    (j : ℕ)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  j < (getBaseTrace st.trace).length ∧
    permBwdFreshHitAt (getBaseTrace st.trace) j

/-- The state-level stopping credit is exactly the public trace event, once the successful
inverse-capacity readout guarantees that index `j` exists. -/
lemma permBwdCredit_iff_freshHit
    {j : ℕ}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    permBwdCredit (T_H := T_H) (T_P := T_P) j st ↔
      permBwdFreshHitAt (getBaseTrace st.trace) j := by
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨_, c, hread, _⟩ := permBwdFreshHitAt_imp_exists_target
      (StmtIn := StmtIn) (U := U) (bt := getBaseTrace st.trace) (j := j) h
    unfold permInvRangeCapAt at hread
    cases hentry : (getBaseTrace st.trace)[j]? with
    | none =>
        rw [hentry] at hread
        simp only [Option.bind_none, reduceCtorEq] at hread
    | some entry =>
        exact ⟨(List.getElem?_eq_some_iff.mp hentry).1, h⟩

/-- A base-trace suffix cannot alter an already-created inverse-permutation credit. -/
lemma permBwdCredit_iff_of_getBaseTrace_append_eq
    {j : ℕ}
    {st st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hbt : getBaseTrace st'.trace = getBaseTrace st.trace ++ extra)
    (hj : j < (getBaseTrace st.trace).length) :
    permBwdCredit (T_H := T_H) (T_P := T_P) j st' ↔
      permBwdCredit (T_H := T_H) (T_P := T_P) j st := by
  have hlength : j < (getBaseTrace st'.trace).length := by
    rw [hbt, List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  have htake :
      (getBaseTrace st.trace ++ extra).take j = (getBaseTrace st.trace).take j := by
    rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
  have hentry :
      (getBaseTrace st.trace ++ extra)[j]? = (getBaseTrace st.trace)[j]? := by
    rw [List.getElem?_append_left hj]
  have hfresh :
      permBwdFreshHitAt (getBaseTrace st.trace ++ extra) j ↔
        permBwdFreshHitAt (getBaseTrace st.trace) j :=
    permBwdFreshHitAt_iff_of_take_eq_of_getElem?_eq
      (StmtIn := StmtIn) (U := U) htake hentry
  constructor
  · rintro ⟨_, hcredit⟩
    refine ⟨hj, ?_⟩
    rw [hbt] at hcredit
    exact hfresh.mp hcredit
  · rintro ⟨_, hcredit⟩
    refine ⟨hlength, ?_⟩
    rw [hbt]
    exact hfresh.mpr hcredit

/-- The target set for a newly appended inverse representative is determined before its preimage
sample: it consists of the old prior targets and the queried output state's capacity. -/
lemma permBwdCapacityTargetFinset_append_bwd_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateOut stateIn : CanonicalSpongeState U) :
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

/-- The pre-sampling target finset for the inverse `outlu`-miss branch. -/
def permBwdMissTargetFinset
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ) (stateOut : CanonicalSpongeState U) :
    Finset (Vector U SpongeSize.C) :=
  priorCapacityTargetFinset bt j ∪ {stateOut.capacitySegment}

lemma permBwdMissTargetFinset_card_le
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ) (stateOut : CanonicalSpongeState U) :
    (permBwdMissTargetFinset (StmtIn := StmtIn) (U := U) bt j stateOut).card ≤ 2 * j + 1 := by
  unfold permBwdMissTargetFinset
  calc
    (priorCapacityTargetFinset bt j ∪ {stateOut.capacitySegment}).card
        ≤ (priorCapacityTargetFinset bt j).card + ({stateOut.capacitySegment} :
            Finset (Vector U SpongeSize.C)).card := Finset.card_union_le _ _
    _ ≤ 2 * j + 1 := by
        rw [Finset.card_singleton]
        exact Nat.add_le_add (priorCapacityTargetFinset_card_le bt j) (by omega)

/-- If a newly retained inverse representative's preimage capacity avoids its pre-sampling target
set, it cannot realize the inverse credit at that new index. -/
lemma not_permBwdCredit_of_getBaseTrace_append_bwd_not_mem_target
    {st st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (stateOut stateIn : CanonicalSpongeState U)
    (hbase : getBaseTrace st'.trace =
      getBaseTrace st.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    (hnot : stateIn.capacitySegment ∉ permBwdMissTargetFinset
      (StmtIn := StmtIn) (U := U) (getBaseTrace st.trace)
      (getBaseTrace st.trace).length stateOut) :
    ¬ permBwdCredit (T_H := T_H) (T_P := T_P)
      (getBaseTrace st.trace).length st' := by
  intro hcredit
  obtain ⟨c, hrange, hmem⟩ := permBwdFreshHitAt_imp_mem_targetFinset
    (StmtIn := StmtIn) (U := U) (bt := getBaseTrace st'.trace)
    (j := (getBaseTrace st.trace).length) hcredit.2
  have hcap : c = stateIn.capacitySegment := by
    rw [hbase] at hrange
    rw [permInvRangeCapAt_append_bwd_length] at hrange
    exact Option.some.inj hrange.symm
  rw [hbase] at hmem
  rw [permBwdCapacityTargetFinset_append_bwd_length] at hmem
  rw [hcap] at hmem
  exact hnot hmem

lemma permInvRangeCapAt_append_hash_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (answer : Vector U SpongeSize.C) :
    permInvRangeCapAt (bt ++ [⟨dsHashQuery stmt, answer⟩]) bt.length = none := by
  unfold permInvRangeCapAt
  rw [getElem?_append_singleton_length]
  rfl

lemma permInvRangeCapAt_append_fwd_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateIn stateOut : CanonicalSpongeState U) :
    permInvRangeCapAt (bt ++ [⟨dsPermQuery stateIn, stateOut⟩]) bt.length = none := by
  unfold permInvRangeCapAt
  rw [getElem?_append_singleton_length]
  rfl

/-- A hash representative at the crossing index cannot later be read as an inverse-permutation
representative. -/
lemma d2sQueryImpl_support_permBwdCredit_false_of_hash_at_base_length
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (stmt : StmtIn)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsHashQuery stmt) st).run))
    {answer : Vector U SpongeSize.C}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (answer, st'))
    {j : ℕ} (hlen : (getBaseTrace st.trace).length = j) :
    ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j st' := by
  intro hcredit
  unfold permBwdCredit at hcredit
  have htrace := d2sQueryImpl_support_trace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl (dsHashQuery stmt) st hr answer st' hrEq
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace st.trace)
      ⟨dsHashQuery stmt, answer⟩
  · have hbase : getBaseTrace st'.trace = getBaseTrace st.trace := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_redundant_base st.trace
        ⟨dsHashQuery stmt, answer⟩ hred
    rw [hbase] at hcredit
    omega
  · have hbase : getBaseTrace st'.trace =
        getBaseTrace st.trace ++ [⟨dsHashQuery stmt, answer⟩] := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_not_redundant_base st.trace
        ⟨dsHashQuery stmt, answer⟩ hred
    obtain ⟨_, _, hrange, _⟩ := permBwdFreshHitAt_imp_exists_target
      (StmtIn := StmtIn) (U := U) (bt := getBaseTrace st'.trace) (j := j) hcredit.2
    rw [hbase] at hrange
    rw [← hlen] at hrange
    rw [permInvRangeCapAt_append_hash_length] at hrange
    cases hrange

/-- A forward-permutation representative at the crossing index cannot later be read as an
inverse-permutation representative. -/
lemma d2sQueryImpl_support_permBwdCredit_false_of_perm_at_base_length
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (stateIn : CanonicalSpongeState U)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsPermQuery stateIn) st).run))
    {stateOut : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (stateOut, st'))
    {j : ℕ} (hlen : (getBaseTrace st.trace).length = j) :
    ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j st' := by
  intro hcredit
  unfold permBwdCredit at hcredit
  have htrace := d2sQueryImpl_support_trace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl (dsPermQuery stateIn) st hr stateOut st' hrEq
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace st.trace)
      ⟨dsPermQuery stateIn, stateOut⟩
  · have hbase : getBaseTrace st'.trace = getBaseTrace st.trace := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_redundant_base st.trace
        ⟨dsPermQuery stateIn, stateOut⟩ hred
    rw [hbase] at hcredit
    omega
  · have hbase : getBaseTrace st'.trace =
        getBaseTrace st.trace ++ [⟨dsPermQuery stateIn, stateOut⟩] := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_not_redundant_base st.trace
        ⟨dsPermQuery stateIn, stateOut⟩ hred
    obtain ⟨_, _, hrange, _⟩ := permBwdFreshHitAt_imp_exists_target
      (StmtIn := StmtIn) (U := U) (bt := getBaseTrace st'.trace) (j := j) hcredit.2
    rw [hbase] at hrange
    rw [← hlen] at hrange
    rw [permInvRangeCapAt_append_fwd_length] at hrange
    cases hrange

/-- If an inverse response is discarded by the base-trace filter, its sampled preimage already
occurs as one of the old capacity targets.  This is the retry case omitted by the paper's
one-line "new entry is uniform" phrasing: a simulator `outlu` miss need not create a base entry
after `E_func`, but a discarded miss is still chargeable to the same pre-sampling target set. -/
lemma permBwdMiss_redundant_imp_sample_mem_target
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hred : isRedundantEntryOfPrefix bt ⟨dsPermInvQuery stateOut, stateIn⟩) :
    stateIn.capacitySegment ∈ permBwdMissTargetFinset
      (StmtIn := StmtIn) (U := U) bt bt.length stateOut := by
  unfold isRedundantEntryOfPrefix at hred
  unfold permBwdMissTargetFinset
  refine Finset.mem_union.mpr (Or.inl ?_)
  change stateIn.capacitySegment ∈ priorCapacityTargetFinset bt bt.length
  apply mem_optionListToFinset_of_mem_some
  rcases hred with hInv | hFwd
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hInv
    rw [List.getElem?_eq_some_iff] at hi
    obtain ⟨hiLt, hiEntry⟩ := hi
    apply mem_priorCapacityTargets_of_entryCapAt
      (bt := bt) (j := bt.length) (j' := i) hiLt 1
    rw [List.getElem?_eq_getElem hiLt, hiEntry]
    rfl
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hFwd
    rw [List.getElem?_eq_some_iff] at hi
    obtain ⟨hiLt, hiEntry⟩ := hi
    apply mem_priorCapacityTargets_of_entryCapAt
      (bt := bt) (j := bt.length) (j' := i) hiLt 0
    rw [List.getElem?_eq_getElem hiLt, hiEntry]
    rfl

/-- A successful public inverse-table hit is a consistent reply, hence it contributes no new base
representative.  This classification is valid without a global permutation-functionality claim. -/
lemma d2sQueryImpl_permInv_hit_support_baseTrace_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {stateOut recovered : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.outlu st.trΔ.p stateOut = some recovered)
    {r : Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsPermInvQuery stateOut) st).run))
    {stateIn : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (stateIn, st')) :
    stateIn = recovered ∧ getBaseTrace st'.trace = getBaseTrace st.trace := by
  have hstep := d2sQueryImpl_support_step_success
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl (dsPermInvQuery stateOut) st hr hrEq
  exact d2sHandleInversePermQuery_hit_support_baseTrace_eq
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st hLookup hstep rfl

/-- Every successful inverse-query step has one of two exact base-trace classifications.  Either
the raw inverse pair is retained as the next representative, or it is filtered as a duplicate;
in the latter case the sampled preimage capacity already belongs to the old `2j+1` target set.
This statement is deterministic and deliberately makes no functionality assumption on `trΔ.p`. -/
lemma d2sQueryImpl_permInv_support_baseTrace_append_or_sample_mem_target
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsPermInvQuery stateOut) st).run))
    {stateIn : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (stateIn, st')) :
    getBaseTrace st'.trace =
        getBaseTrace st.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩] ∨
      stateIn.capacitySegment ∈ permBwdMissTargetFinset
        (StmtIn := StmtIn) (U := U) (getBaseTrace st.trace)
        (getBaseTrace st.trace).length stateOut := by
  let bt := getBaseTrace st.trace
  have hraw : st'.trace = st.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩] :=
    d2sQueryImpl_support_trace_append
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) gImpl auxImpl (dsPermInvQuery stateOut) st hr stateIn st' hrEq
  by_cases hred : isRedundantEntryOfPrefix bt ⟨dsPermInvQuery stateOut, stateIn⟩
  · right
    exact permBwdMiss_redundant_imp_sample_mem_target
      (StmtIn := StmtIn) (U := U) bt stateOut stateIn hred
  · left
    rw [hraw]
    exact getBaseTrace_append_singleton_of_not_redundant_base st.trace
      ⟨dsPermInvQuery stateOut, stateIn⟩ hred

set_option maxHeartbeats 400000 in
-- One explicit D2S miss branch is normalized before applying the finite-target bound.
/-- The public one-query inverse-miss finite-target estimate.  It charges all sampled preimages
in `S`, including a sample whose raw response is later filtered as redundant. -/
lemma d2sQueryImpl_permInv_miss_sample_mem_finset_le
    [Nonempty U] [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.outlu st.trΔ.p stateOut = none)
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ fun r => (match r with
      | some (stateIn, _) => stateIn.capacitySegment ∈ S
      | none => False) |
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
        (auxImpl := fun aux => OptionT.lift
          ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux))
        (dsPermInvQuery stateOut) st).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  classical
  let gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp) :=
    fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)
  let auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp) :=
    fun aux => OptionT.lift
      ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux)
  let handler := OptionT.run ((ProverTransform.d2sHandleInversePermQuery
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st)
  have hrun :
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        gImpl auxImpl (dsPermInvQuery stateOut) st).run =
      Option.elimM (simulateQ (gImpl + auxImpl) handler).run (pure none)
      (fun x : Option (CanonicalSpongeState U ×
          ProverTransform.D2SQueryState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) =>
        match x with
        | none => pure none
        | some pair => pure (some pair)) := by
    rw [ProverTransform.d2sQueryImpl, OptionT.run_bind]
    simp only [ProverTransform.d2sQueryStep]
    congr
    funext x
    cases x <;> rfl
  rw [hrun]
  let P : Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) → Prop :=
    fun r => match r with
    | some (stateIn, _) => CanonicalSpongeState.capacitySegment stateIn ∈ S
    | none => False
  let mx := (simulateQ (gImpl + auxImpl) handler).run
  have hNone : ¬ P none := by
    simp [P]
  have hPQ :
      (fun o => ∃ pair, o = some (some pair) ∧ P (some pair)) =
        (fun o => match Option.map (Option.map Prod.fst) o with
          | some (some sampled) => sampled.capacitySegment ∈ S
          | _ => False) := by
    funext o
    cases o with
    | none => simp [P]
    | some inner =>
        cases inner with
        | none => simp [P]
        | some pair =>
            apply propext
            constructor
            · rintro ⟨pair', hEq, hP⟩
              have hpair : pair = pair' := Option.some.inj (Option.some.inj hEq)
              cases hpair
              exact hP
            · intro hP
              exact ⟨pair, rfl, hP⟩
  have hgoal :
      Pr[ P | Option.elimM (simulateQ (gImpl + auxImpl) handler).run (pure none)
        (fun x : Option (CanonicalSpongeState U ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) =>
          match x with
          | none => pure none
          | some pair => pure (some pair))] ≤
        (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
    have hjoin :
        Pr[ P | Option.elimM (simulateQ (gImpl + auxImpl) handler).run (pure none)
          (fun x : Option (CanonicalSpongeState U ×
              ProverTransform.D2SQueryState
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) =>
            match x with
            | none => pure none
            | some pair => pure (some pair))] =
          Pr[ fun o => ∃ pair, o = some (some pair) ∧ P (some pair) |
            (simulateQ (gImpl + auxImpl) handler).run] := by
      rw [Option.elimM, probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator]
      refine tsum_congr ?_
      intro o
      cases o with
      | none => simp [hNone]
      | some inner =>
          cases inner with
          | none => simp [hNone]
          | some pair =>
              by_cases hP : P (some pair)
              · have hmem : some (some pair) ∈
                    {x | ∃ pair', x = some (some pair') ∧ P (some pair')} :=
                  ⟨pair, rfl, hP⟩
                rw [Set.indicator_of_mem hmem]
                change Pr[= some (some pair) | (simulateQ (gImpl + auxImpl) handler).run] *
                    Pr[ P | pure (some pair)] =
                  Pr[= some (some pair) | (simulateQ (gImpl + auxImpl) handler).run]
                rw [probEvent_pure]
                simp only [if_pos hP, mul_one]
              · rw [Set.indicator_of_notMem
                    (show some (some pair) ∉
                      {x | ∃ pair', x = some (some pair') ∧ P (some pair')} from
                      fun h => by
                        rcases h with ⟨pair', hEq, hP'⟩
                        have hpair : pair = pair' := Option.some.inj (Option.some.inj hEq)
                        cases hpair
                        exact hP hP')]
                change Pr[= some (some pair) | (simulateQ (gImpl + auxImpl) handler).run] *
                    Pr[ P | pure (some pair)] = 0
                rw [probEvent_pure]
                simp only [if_neg hP, mul_zero]
    rw [hjoin, hPQ]
    exact d2sHandleInversePermQuery_miss_sigma_capacity_mem_finset_le
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) k_g st hLookup S
  convert hgoal using 1
  apply probEvent_congr'
  · intro r _
    cases r with
    | none => rfl
    | some pair => rfl
  · rfl

/-- The paper's aggregate inverse-permutation bound, held opaque while recursively exposing the
simulator program.  The factor `2j+1` is the cardinal bound for the already exposed capacity
targets plus the queried output capacity. -/
def permBwdCreditBound
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ) : Prop :=
  Pr[ fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 |
    sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st log] ≤
    ((2 * j + 1 : ℕ) : ℝ≥0∞) / capacitySpaceSize (U := U)

attribute [irreducible] permBwdCreditBound

set_option maxHeartbeats 400000 in
-- Unfolding one stateful query layer and applying the bind bound is elaborator-intensive.
/-- A one-layer runner rule for a fixed absolute probability bound.  This is the direct
`probEvent_bind_le_of_forall_le` lifting used by the inverse retry argument. -/
lemma sigmaHashRun_query_bind_le_of_step
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (A : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) → Prop)
    (ε : ℝ≥0∞)
    (hstep : ∀ first ∈ support
        ((ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
          (sigmaAuxImpl (U := U)) q st).run),
      Pr[ A | (match first with
        | none => pure (none, (st, log))
        | some (a, st') => sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
            (log ++ QueryLog.singleton (Sum.inr q) a))] ≤ ε) :
    Pr[ A | sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st log] ≤ ε := by
  unfold sigmaHashRun
  rw [combinedImpl_run_query_bind_eq]
  rw [wrappedDSImpl_run_eq_d2sQuery_bind]
  rw [bind_assoc]
  apply probEvent_bind_le_of_forall_le
  intro first hfirst
  cases first with
  | none =>
      rw [pure_bind]
      exact hstep none hfirst
  | some pair =>
      rcases pair with ⟨a, st'⟩
      rw [pure_bind]
      exact hstep (some (a, st')) hfirst

/-- A continuation can be charged to a predicate of the immediately preceding draw.  This is the
formal target-indicator step behind the paper's phrase “the new sample hits one of the exposed
capacities”.  It is reusable for both permutation directions. -/
lemma probEvent_bind_le_probEvent_of_indicator
    {α β : Type} (sample : ProbComp α) (cont : α → ProbComp β)
    (P : β → Prop) (Q : α → Prop) [DecidablePred Q]
    (hcont : ∀ x ∈ support sample,
      Pr[ P | cont x] ≤ if Q x then 1 else 0) :
    Pr[ P | sample >>= cont] ≤ Pr[ Q | sample] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator]
  refine ENNReal.tsum_le_tsum ?_
  intro x
  by_cases hx : x ∈ support sample
  · by_cases hQ : Q x
    · rw [Set.indicator_of_mem (show x ∈ {x | Q x} from hQ)]
      have h := hcont x hx
      rw [if_pos hQ] at h
      calc
        Pr[= x | sample] * Pr[ P | cont x] ≤ Pr[= x | sample] * 1 :=
          mul_le_mul' le_rfl h
        _ = Pr[= x | sample] := by rw [mul_one]
    · rw [Set.indicator_of_notMem (show x ∉ {x | Q x} from hQ)]
      have h := hcont x hx
      rw [if_neg hQ] at h
      calc
        Pr[= x | sample] * Pr[ P | cont x] ≤ Pr[= x | sample] * 0 :=
          mul_le_mul' le_rfl h
        _ = 0 := by rw [mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hx]
    rw [zero_mul]
    exact zero_le

set_option maxHeartbeats 400000 in
-- The indicator bind proof exposes the complete one-query lazy-simulator computation.
/-- Runner-level form of `probEvent_bind_le_probEvent_of_indicator`.  It transports a local
target charge through a complete lazy-simulator continuation, rather than requiring that the
fresh query itself survive base-trace filtering. -/
lemma sigmaHashRun_query_bind_le_probEvent_of_indicator
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (A : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) → Prop)
    (Q : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) → Prop)
    [DecidablePred Q]
    (hstep : ∀ first ∈ support
        ((ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
          (sigmaAuxImpl (U := U)) q st).run),
      Pr[ A | (match first with
        | none => pure (none, (st, log))
        | some (a, st') => sigmaHashRun (T_H := T_H) (T_P := T_P) k_g (mx a) st'
            (log ++ QueryLog.singleton (Sum.inr q) a))] ≤
        if Q first then 1 else 0) :
    Pr[ A | sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st log] ≤
      Pr[ Q | ((ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U)) q st).run)] := by
  unfold sigmaHashRun
  rw [combinedImpl_run_query_bind_eq]
  rw [wrappedDSImpl_run_eq_d2sQuery_bind]
  rw [bind_assoc]
  apply probEvent_bind_le_probEvent_of_indicator
  intro first hfirst
  cases first with
  | none =>
      rw [pure_bind]
      exact hstep none hfirst
  | some pair =>
      rcases pair with ⟨a, st'⟩
      rw [pure_bind]
      exact hstep (some (a, st')) hfirst

set_option maxHeartbeats 400000 in
-- The stopping runner is intentionally opaque while recursion exposes one query layer.
/-- The opaque inverse stopping invariant exposes one query layer without expanding the full
combined simulator in the continuation hypotheses. -/
lemma permBwdCreditBound_query_bind_of_step
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ)
    (hstep : ∀ a st', some (a, st') ∈ support
      ((ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U)) q st).run) →
      permBwdCreditBound (T_H := T_H) (T_P := T_P) k_g (mx a) st'
        (log ++ QueryLog.singleton (Sum.inr q) a) j)
    (hnone : Pr[ fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 |
      (pure (none, (st, log)) : ProbComp (Option α ×
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))] ≤
      ((2 * j + 1 : ℕ) : ℝ≥0∞) / capacitySpaceSize (U := U)) :
    permBwdCreditBound (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx) st log j := by
  unfold permBwdCreditBound
  apply sigmaHashRun_query_bind_le_of_step k_g q mx st log
    (fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1)
    (((2 * j + 1 : ℕ) : ℝ≥0∞) / capacitySpaceSize (U := U))
  intro first hfirst
  cases first with
  | none => exact hnone
  | some pair =>
      rcases pair with ⟨a, st'⟩
      unfold permBwdCreditBound at hstep
      exact hstep a st' hfirst

/-- A terminal pure state has no inverse credit while the incoming base trace has not passed the
distinguished index. -/
lemma permBwdCredit_prob_pure_state_eq_zero
    {α : Type}
    (x : Option α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ)
    (hlen : (getBaseTrace st.trace).length ≤ j) :
    Pr[ fun r : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) =>
      permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 |
      (pure (x, (st, log)) : ProbComp (Option α ×
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))] = 0 := by
  apply probEvent_eq_zero
  intro r hr hcredit
  rw [mem_support_pure_iff] at hr
  subst r
  change permBwdCredit (T_H := T_H) (T_P := T_P) j st at hcredit
  unfold permBwdCredit at hcredit
  exact (by omega : False)

/-- Once a base position has been fixed to a non-credit entry, no later D2S execution can create
an inverse credit at that position. -/
lemma combinedImpl_support_not_permBwdCredit_stable_of_index_lt
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)) oa).run).run (st, log)))
    {j : ℕ}
    (hj : j < (getBaseTrace st.trace).length)
    (hcredit : ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j st) :
    ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 := by
  refine combinedImpl_support_state_invariant
    (StmtIn := StmtIn) (U := U)
    (spongeImpl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)
    (I := fun s => j < (getBaseTrace s.trace).length ∧
      ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j s)
    ?_ (st, log) ⟨hj, hcredit⟩ hr |>.2
  intro q s step hs hstep
  cases step with
  | none => trivial
  | some pair =>
      rcases pair with ⟨a, s'⟩
      obtain ⟨extra, hbase⟩ := d2sQueryImpl_support_baseTrace_append
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) gImpl auxImpl q s hstep rfl
      have hj' : j < (getBaseTrace s'.trace).length := by
        rw [hbase, List.length_append]
        exact Nat.lt_of_lt_of_le hs.1 (Nat.le_add_right _ _)
      refine ⟨hj', ?_⟩
      intro hcredit'
      have hiff := permBwdCredit_iff_of_getBaseTrace_append_eq
        (T_H := T_H) (T_P := T_P) hbase hs.1
      exact hs.2 (hiff.mp hcredit')

/-- The terminal zero branch for inverse credits. -/
lemma combinedImpl_permBwdCredit_prob_eq_zero_of_index_lt
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ)
    (hj : j < (getBaseTrace st.trace).length)
    (hcredit : ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j st) :
    Pr[ fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 |
      ((simulateQ (lemma5_8CombinedImpl
        (ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)) oa).run).run (st, log)] = 0 := by
  apply probEvent_eq_zero
  intro r hr hfinal
  exact combinedImpl_support_not_permBwdCredit_stable_of_index_lt
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st log hr hj hcredit hfinal

/-- The terminal-zero invariant in the compact lazy-simulator runner notation.  Keeping this
bridge separate prevents the inverse crossing argument from unfolding the complete executor. -/
lemma sigmaHashRun_permBwdCredit_prob_eq_zero_of_index_lt
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ)
    (hj : j < (getBaseTrace st.trace).length)
    (hcredit : ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j st) :
    Pr[ fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 |
      sigmaHashRun (T_H := T_H) (T_P := T_P) k_g oa st log] = 0 := by
  unfold sigmaHashRun
  exact combinedImpl_permBwdCredit_prob_eq_zero_of_index_lt
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ)
    (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
    (sigmaAuxImpl (U := U)) st log j hj hcredit

set_option maxHeartbeats 400000 in
-- The fresh inverse crossing combines table classification with an indicator probability bound.
/-- The unique inverse-query crossing branch.  A non-target sample fixes a non-credit base
representative; a target sample is charged once, before its continuation is run. -/
lemma permBwdCreditBound_permInv_miss_crossing
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type} {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ)
    (hlen : (getBaseTrace st.trace).length = j)
    (hLookup : TraceTableOps.outlu st.trΔ.p stateOut = none)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range
      (Sum.inr (dsPermInvQuery stateOut)) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α) :
    permBwdCreditBound (T_H := T_H) (T_P := T_P) k_g
      (liftM (OracleSpec.query (Sum.inr (dsPermInvQuery stateOut))) >>= mx) st log j := by
  classical
  let S := permBwdMissTargetFinset (StmtIn := StmtIn) (U := U)
    (getBaseTrace st.trace) (getBaseTrace st.trace).length stateOut
  let A : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) → Prop :=
    fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1
  let Q : Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) → Prop :=
    fun first => match first with
    | none => False
    | some (stateIn, _) => stateIn.capacitySegment ∈ S
  have hcharge :
      Pr[ A | sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
        (liftM (OracleSpec.query (Sum.inr (dsPermInvQuery stateOut))) >>= mx) st log] ≤
        Pr[ Q | ((ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
          (sigmaAuxImpl (U := U)) (dsPermInvQuery stateOut) st).run)] := by
    apply sigmaHashRun_query_bind_le_probEvent_of_indicator k_g
      (dsPermInvQuery stateOut) mx st log A Q
    intro first hfirst
    cases first with
    | none =>
        dsimp only [Q, A]
        rw [if_false]
        have hzero := permBwdCredit_prob_pure_state_eq_zero
          (T_H := T_H) (T_P := T_P) (α := α)
          (x := (none : Option α)) (st := st) log j (by
            rw [hlen])
        exact hzero.le
    | some pair =>
        rcases pair with ⟨stateIn, st'⟩
        dsimp only [Q]
        by_cases htarget : stateIn.capacitySegment ∈ S
        · rw [if_pos htarget]
          exact probEvent_le_one
        · rw [if_neg htarget]
          have hclass := d2sQueryImpl_permInv_support_baseTrace_append_or_sample_mem_target
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ)
            (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
            (sigmaAuxImpl (U := U)) st hfirst rfl
          have hbase : getBaseTrace st'.trace =
              getBaseTrace st.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩] := by
            cases hclass with
            | inl happend => exact happend
            | inr hmem => exact False.elim (htarget hmem)
          have hj' : j < (getBaseTrace st'.trace).length := by
            rw [hbase, List.length_append]
            simp only [List.length_singleton]
            rw [hlen]
            omega
          have hnot : ¬ permBwdCredit (T_H := T_H) (T_P := T_P) j st' := by
            rw [← hlen]
            exact not_permBwdCredit_of_getBaseTrace_append_bwd_not_mem_target
              (T_H := T_H) (T_P := T_P) stateOut stateIn hbase htarget
          have hzero := sigmaHashRun_permBwdCredit_prob_eq_zero_of_index_lt
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ)
            k_g (mx stateIn) st'
            (log ++ QueryLog.singleton (Sum.inr (dsPermInvQuery stateOut)) stateIn)
            j hj' hnot
          exact hzero.le
  have hsample := d2sQueryImpl_permInv_miss_sample_mem_finset_le
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hLookup S
  have hsample' :
      Pr[ Q | ((ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
        (sigmaAuxImpl (U := U)) (dsPermInvQuery stateOut) st).run)] ≤
        (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
    unfold sigmaGImpl sigmaAuxImpl
    convert hsample using 1
    apply probEvent_congr'
    · intro r _
      cases r with
      | none => rfl
      | some pair => rfl
    · rfl
  unfold permBwdCreditBound
  calc
    Pr[ fun r => permBwdCredit (T_H := T_H) (T_P := T_P) j r.2.1 |
      sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
        (liftM (OracleSpec.query (Sum.inr (dsPermInvQuery stateOut))) >>= mx) st log]
        = Pr[ A | sigmaHashRun (T_H := T_H) (T_P := T_P) k_g
          (liftM (OracleSpec.query (Sum.inr (dsPermInvQuery stateOut))) >>= mx) st log] := by
            rfl
    _ ≤ Pr[ Q | ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
      (sigmaAuxImpl (U := U)) (dsPermInvQuery stateOut) st).run)] := hcharge
    _ ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := hsample'
    _ ≤ ((2 * j + 1 : ℕ) : ℝ≥0∞) / capacitySpaceSize (U := U) := by
      apply ENNReal.div_le_div_right
      rw [← hlen]
      exact_mod_cast permBwdMissTargetFinset_card_le
        (StmtIn := StmtIn) (U := U) (getBaseTrace st.trace)
        (getBaseTrace st.trace).length stateOut

set_option maxHeartbeats 400000 in
-- The structural stopping induction has several dependent simulator state invariants.
/-- The complete lazy-simulator stopping bound for one inverse-permutation index.  The induction
uses only the fact that a D2S query adds at most one base representative.  At the sole fresh
inverse crossing it invokes `permBwdCreditBound_permInv_miss_crossing`; other crossing tags are
deterministically excluded. -/
lemma permBwdCreditBound_of_base_length_le
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    (oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ)
    (hlen : (getBaseTrace st.trace).length ≤ j) :
    permBwdCreditBound (T_H := T_H) (T_P := T_P) k_g oa st log j := by
  classical
  induction oa using OracleComp.inductionOn generalizing st log with
  | pure x =>
      unfold permBwdCreditBound
      rw [sigmaHashRun_pure_eq (T_H := T_H) (T_P := T_P) k_g x st log]
      rw [permBwdCredit_prob_pure_state_eq_zero
        (T_H := T_H) (T_P := T_P) (x := some x) (st := st) log j hlen]
      exact zero_le
  | query_bind t mx ih =>
      match t with
      | Sum.inl e => exact PEmpty.elim e
      | Sum.inr q =>
          rcases q with stmt | (stateIn | stateOut)
          · refine permBwdCreditBound_query_bind_of_step k_g (dsHashQuery stmt) mx st log j
              ?_ ?_
            · intro answer st' hfirst
              have hstep := d2sQueryImpl_support_baseTrace_length_le_succ
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ)
                (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                (sigmaAuxImpl (U := U)) (dsHashQuery stmt) st hfirst rfl
              by_cases hlen' : (getBaseTrace st'.trace).length ≤ j
              · exact ih answer st'
                  (log ++ QueryLog.singleton (Sum.inr (dsHashQuery stmt)) answer) hlen'
              · have hcross : (getBaseTrace st.trace).length = j := by omega
                have hj' : j < (getBaseTrace st'.trace).length := by omega
                have hnot := d2sQueryImpl_support_permBwdCredit_false_of_hash_at_base_length
                  (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                  (U := U) (δ := δ)
                  (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                  (sigmaAuxImpl (U := U)) stmt st hfirst rfl hcross
                have hzero := combinedImpl_permBwdCredit_prob_eq_zero_of_index_lt
                  (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                  (U := U) (δ := δ)
                  (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                  (sigmaAuxImpl (U := U)) st'
                  (log ++ QueryLog.singleton (Sum.inr (dsHashQuery stmt)) answer)
                  j hj' hnot (oa := mx answer)
                unfold permBwdCreditBound sigmaHashRun
                rw [hzero]
                exact zero_le
            · rw [permBwdCredit_prob_pure_state_eq_zero
                (T_H := T_H) (T_P := T_P) (x := none) (st := st) log j hlen]
              exact zero_le
          · refine permBwdCreditBound_query_bind_of_step k_g (dsPermQuery stateIn) mx st log j
              ?_ ?_
            · intro stateOut' st' hfirst
              have hstep := d2sQueryImpl_support_baseTrace_length_le_succ
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ)
                (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                (sigmaAuxImpl (U := U)) (dsPermQuery stateIn) st hfirst rfl
              by_cases hlen' : (getBaseTrace st'.trace).length ≤ j
              · exact ih stateOut' st'
                  (log ++ QueryLog.singleton (Sum.inr (dsPermQuery stateIn)) stateOut') hlen'
              · have hcross : (getBaseTrace st.trace).length = j := by omega
                have hj' : j < (getBaseTrace st'.trace).length := by omega
                have hnot := d2sQueryImpl_support_permBwdCredit_false_of_perm_at_base_length
                  (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                  (U := U) (δ := δ)
                  (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                  (sigmaAuxImpl (U := U)) stateIn st hfirst rfl hcross
                have hzero := combinedImpl_permBwdCredit_prob_eq_zero_of_index_lt
                  (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                  (U := U) (δ := δ)
                  (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                  (sigmaAuxImpl (U := U)) st'
                  (log ++ QueryLog.singleton (Sum.inr (dsPermQuery stateIn)) stateOut')
                  j hj' hnot (oa := mx stateOut')
                unfold permBwdCreditBound sigmaHashRun
                rw [hzero]
                exact zero_le
            · rw [permBwdCredit_prob_pure_state_eq_zero
                (T_H := T_H) (T_P := T_P) (x := none) (st := st) log j hlen]
              exact zero_le
          · by_cases hmiss : TraceTableOps.outlu st.trΔ.p stateOut = none
            · by_cases hcross : (getBaseTrace st.trace).length = j
              · exact permBwdCreditBound_permInv_miss_crossing
                  (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                  (U := U) (δ := δ) k_g st log j hcross hmiss mx
              · refine permBwdCreditBound_query_bind_of_step k_g (dsPermInvQuery stateOut)
                  mx st log j ?_ ?_
                · intro stateIn' st' hfirst
                  have hstep := d2sQueryImpl_support_baseTrace_length_le_succ
                    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                    (U := U) (δ := δ)
                    (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                    (sigmaAuxImpl (U := U)) (dsPermInvQuery stateOut) st hfirst rfl
                  have hlt : (getBaseTrace st.trace).length < j := by omega
                  have hlen' : (getBaseTrace st'.trace).length ≤ j := by omega
                  exact ih stateIn' st'
                    (log ++ QueryLog.singleton (Sum.inr (dsPermInvQuery stateOut)) stateIn') hlen'
                · rw [permBwdCredit_prob_pure_state_eq_zero
                    (T_H := T_H) (T_P := T_P) (x := none) (st := st) log j hlen]
                  exact zero_le
            · cases hLookup : TraceTableOps.outlu st.trΔ.p stateOut with
              | none => exact (hmiss hLookup).elim
              | some recovered =>
                  refine permBwdCreditBound_query_bind_of_step k_g (dsPermInvQuery stateOut)
                    mx st log j ?_ ?_
                  · intro stateIn' st' hfirst
                    have hbase := d2sQueryImpl_permInv_hit_support_baseTrace_eq
                      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                      (U := U) (δ := δ)
                      (sigmaGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g)
                      (sigmaAuxImpl (U := U)) st hLookup hfirst rfl
                    have hlen' : (getBaseTrace st'.trace).length ≤ j := by
                      rw [hbase.2]
                      exact hlen
                    exact ih stateIn' st'
                      (log ++ QueryLog.singleton (Sum.inr (dsPermInvQuery stateOut)) stateIn') hlen'
                  · rw [permBwdCredit_prob_pure_state_eq_zero
                      (T_H := T_H) (T_P := T_P) (x := none) (st := st) log j hlen]
                    exact zero_le

end PermInverseCredit

end BadEventDS

end DuplexSpongeFS

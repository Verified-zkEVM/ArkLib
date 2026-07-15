/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Representatives
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SpongeTrace
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PrefixEvents

/-!
# One-step hash credits for Lemma 5.8

This module isolates the deterministic part of the lazy-sampling stopping-time argument for the
hash term of Lemma 5.8.  A genuine hash-table miss creates exactly one base representative; a
table hit creates none.  The probability calculation is deliberately kept separate from these
readout facts.
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

section HashCredit

variable [Fintype U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

variable
  (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
  (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))

/-- The hash-collision atom at the fixed base-trace index `j`. -/
def hashCreditA
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  j < (getBaseTrace st.trace).length ∧
    hashOutCapAt (getBaseTrace st.trace) j = some c ∧
    priorCapacityTargetAt (getBaseTrace st.trace) j i = some c

/-- The target-side credit paired with `hashCreditA`. -/
def hashCreditB
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  j < (getBaseTrace st.trace).length ∧
    priorCapacityTargetAt (getBaseTrace st.trace) j i = some c

/-- The target-side event charged by the hash freshness calculation.  Unlike
`hashCreditB`, it deliberately does *not* assert that base position `j` already exists: before
the stopping time, the old target readout may still be completed by later base representatives.
At and after the crossing step it is fixed by the strict prefix `bt.take j`. -/
def hashCreditTarget
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  priorCapacityTargetAt (getBaseTrace st.trace) j i = some c

/-- The state-level credit is exactly the paper-facing hash atom.  The explicit index-existence
conjunct in `hashCreditA` is derivable from a successful `hashOutCapAt` readout; retaining it in
the credit makes the stopping-time cases transparent. -/
lemma hashCreditA_iff_hash_atom
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hashCreditA (T_H := T_H) (T_P := T_P) j i c st ↔
      hashOutCapAt (getBaseTrace st.trace) j = some c ∧
        hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st := by
  constructor
  · rintro ⟨hj, hhash, htarget⟩
    exact ⟨hhash, htarget⟩
  · rintro ⟨hhash, htarget⟩
    unfold hashOutCapAt at hhash
    cases hentry : (getBaseTrace st.trace)[j]? with
    | none =>
        rw [hentry] at hhash
        simp only [Option.bind_none, reduceCtorEq] at hhash
    | some entry =>
        have hj : j < (getBaseTrace st.trace).length := by
          exact (List.getElem?_eq_some_iff.mp hentry).1
        exact ⟨hj, hhash, htarget⟩

/-- Once the base trace has reached position `j`, the target charged at `j` is invariant under
all later suffix extensions.  The weak inequality is intentional: at the crossing state
`length = j`, an appended representative is not among the *prior* targets. -/
lemma hashCreditTarget_iff_of_getBaseTrace_append_eq
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    {st st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hbt : getBaseTrace st'.trace = getBaseTrace st.trace ++ extra)
    (hj : j ≤ (getBaseTrace st.trace).length) :
    hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st' ↔
      hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st := by
  unfold hashCreditTarget
  have htake :
      (getBaseTrace st.trace ++ extra).take j = (getBaseTrace st.trace).take j := by
    rw [List.take_append_of_le_length hj]
  have htargetAppend := priorCapacityTargetAt_eq_of_take_eq htake i
  rw [hbt, htargetAppend]

/-- A realized hash credit is stable under every later base-trace suffix extension.  This is the
post-crossing branch of the stopping-time argument: later D2S queries cannot change the entry at
the fixed old base index nor its family of prior targets. -/
lemma hashCreditA_of_getBaseTrace_append_eq
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    {st st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hbt : getBaseTrace st'.trace = getBaseTrace st.trace ++ extra)
    (hcredit : hashCreditA (T_H := T_H) (T_P := T_P) j i c st) :
    hashCreditA (T_H := T_H) (T_P := T_P) j i c st' := by
  rcases hcredit with ⟨hj, hhash, htarget⟩
  have hjNew : j < (getBaseTrace st'.trace).length := by
    rw [hbt, List.length_append]
    exact Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)
  have hget :
      (getBaseTrace st.trace ++ extra)[j]? = (getBaseTrace st.trace)[j]? := by
    rw [List.getElem?_append_left hj]
  have hhashNew : hashOutCapAt (getBaseTrace st'.trace) j = some c := by
    unfold hashOutCapAt
    rw [hbt, hget]
    exact hhash
  have htake :
      (getBaseTrace st.trace ++ extra).take j = (getBaseTrace st.trace).take j := by
    rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
  have htargetAppend := priorCapacityTargetAt_eq_of_take_eq htake i
  have htargetNew : priorCapacityTargetAt (getBaseTrace st'.trace) j i = some c := by
    rw [hbt, htargetAppend]
    exact htarget
  exact ⟨hjNew, hhashNew, htargetNew⟩

/-- Once base index `j` already exists, extending the base trace neither creates nor destroys the
fixed hash credit at `j`.  This is the terminal (`length > j`) branch of the stopping argument. -/
lemma hashCreditA_iff_of_getBaseTrace_append_eq
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    {st st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hbt : getBaseTrace st'.trace = getBaseTrace st.trace ++ extra)
    (hj : j < (getBaseTrace st.trace).length) :
    hashCreditA (T_H := T_H) (T_P := T_P) j i c st' ↔
      hashCreditA (T_H := T_H) (T_P := T_P) j i c st := by
  constructor
  · intro hcredit
    rcases hcredit with ⟨_hjNew, hhashNew, htargetNew⟩
    refine ⟨hj, ?_, ?_⟩
    · unfold hashOutCapAt at hhashNew ⊢
      rw [hbt, List.getElem?_append_left hj] at hhashNew
      exact hhashNew
    · have htake :
          (getBaseTrace st.trace ++ extra).take j = (getBaseTrace st.trace).take j := by
        rw [List.take_append_of_le_length (Nat.le_of_lt hj)]
      have htargetAppend := priorCapacityTargetAt_eq_of_take_eq htake i
      rw [hbt, htargetAppend] at htargetNew
      exact htargetNew
  · intro hcredit
    exact hashCreditA_of_getBaseTrace_append_eq hbt hcredit


/-- Filtering a single raw extension can retain at most one additional base representative. -/
lemma getBaseTrace_append_singleton_length_le
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) :
    (getBaseTrace (trace ++ [entry])).length ≤ (getBaseTrace trace).length + 1 := by
  classical
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace trace) entry
  · rw [getBaseTrace_append_singleton_of_redundant_base trace entry hred]
    omega
  · rw [getBaseTrace_append_singleton_of_not_redundant_base trace entry hred]
    simp

/-- A freshly appended forward-permutation representative cannot be read as a hash answer. -/
lemma hashOutCapAt_append_perm_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sIn sOut : CanonicalSpongeState U) :
    hashOutCapAt (bt ++ [⟨dsPermQuery sIn, sOut⟩]) bt.length = none := by
  unfold hashOutCapAt
  rw [getElem?_append_singleton_length]
  rfl

/-- A freshly appended inverse-permutation representative cannot be read as a hash answer. -/
lemma hashOutCapAt_append_permInv_length
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sOut sIn : CanonicalSpongeState U) :
    hashOutCapAt (bt ++ [⟨dsPermInvQuery sOut, sIn⟩]) bt.length = none := by
  unfold hashOutCapAt
  rw [getElem?_append_singleton_length]
  rfl

/-- Peel a successful public D2S-query support point to the corresponding successful internal
`d2sQueryStep` support point.  This is the operational bridge needed when a handler-specific
semantic fact (such as a hash-table hit) has to be used at the public wrapper boundary. -/
lemma d2sQueryImpl_support_step_success
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run))
    {a : (duplexSpongeChallengeOracle StmtIn U).Range q}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (a, st')) :
    some (some (a, st')) ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sQueryStep
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run := by
  rw [ProverTransform.d2sQueryImpl] at hr
  simp only [Option.elimM, OptionT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨stepResult, hstepResult, hreturn⟩ := hr
  cases hstepEq : stepResult with
  | none =>
      have hreturn' : r ∈ support (pure none : ProbComp
          (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa [hstepEq] using hreturn
      rw [mem_support_pure_iff] at hreturn'
      rw [hrEq] at hreturn'
      simp at hreturn'
  | some inner =>
      cases inner with
      | none =>
          have hreturn' : r ∈ support
              ((failure : OptionT ProbComp
                ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                  ProverTransform.D2SQueryState
                    (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run) := by
            simpa [hstepEq] using hreturn
          rw [hrEq] at hreturn'
          simp at hreturn'
      | some pair =>
          rcases pair with ⟨a', st''⟩
          have hstep' : some (some (a', st'')) ∈ support
              (simulateQ (gImpl + auxImpl)
                (OptionT.run ((ProverTransform.d2sQueryStep
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run := by
            simpa [hstepEq] using hstepResult
          have hreturn' : r = some (a', st'') := by
            have hreturnPure : r ∈ support (pure (some (a', st'')) : ProbComp
                (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                  ProverTransform.D2SQueryState
                    (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
              simpa [hstepEq] using hreturn
            rw [mem_support_pure_iff] at hreturnPure
            exact hreturnPure
          have hpair : (a, st') = (a', st'') := by
            rw [hrEq] at hreturn'
            exact Option.some.inj hreturn'
          injection hpair with ha hs
          subst ha
          subst hs
          exact hstep'

/-- A public hash-table hit leaves the base trace unchanged. -/
lemma d2sQueryImpl_hash_hit_support_baseTrace_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = some cap)
    {r : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsHashQuery stmt) st).run))
    {a : Vector U SpongeSize.C}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (a, st')) :
    getBaseTrace st'.trace = getBaseTrace st.trace := by
  have hstep := d2sQueryImpl_support_step_success
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl (dsHashQuery stmt) st hr hrEq
  exact (d2sHandleHashQuery_hit_support_baseTrace_eq
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st hLookup hstep rfl).2


/-- Every successful public D2S query can create at most one new base representative.  This is
the deterministic stopping-time fact used to isolate the unique transition that reaches a fixed
base index. -/
lemma d2sQueryImpl_support_baseTrace_length_le_succ
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run))
    {a : (duplexSpongeChallengeOracle StmtIn U).Range q}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (a, st')) :
    (getBaseTrace st'.trace).length ≤ (getBaseTrace st.trace).length + 1 := by
  have htrace := d2sQueryImpl_support_trace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl q st hr a st' hrEq
  rw [htrace]
  exact getBaseTrace_append_singleton_length_le st.trace ⟨q, a⟩

/-- Every successful D2S query extends the base trace by some (empty or singleton) suffix. -/
lemma d2sQueryImpl_support_baseTrace_append
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run))
    {a : (duplexSpongeChallengeOracle StmtIn U).Range q}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (a, st')) :
    ∃ extra : QueryLog (duplexSpongeChallengeOracle StmtIn U),
      getBaseTrace st'.trace = getBaseTrace st.trace ++ extra := by
  have htrace := d2sQueryImpl_support_trace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl q st hr a st' hrEq
  rw [htrace]
  exact getBaseTrace_append_singleton_exists_suffix st.trace ⟨q, a⟩

/-- Once a hash collision atom has been realized at the fixed base index, every later successful
D2S step preserves it.  The only probabilistic work therefore occurs at the unique step that
first reaches that index. -/
lemma d2sQueryImpl_support_hashCreditA_stable
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run))
    {a : (duplexSpongeChallengeOracle StmtIn U).Range q}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (a, st'))
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    (hcredit : hashCreditA (T_H := T_H) (T_P := T_P) j i c st) :
    hashCreditA (T_H := T_H) (T_P := T_P) j i c st' := by
  obtain ⟨extra, hbase⟩ := d2sQueryImpl_support_baseTrace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl q st hr hrEq
  exact hashCreditA_of_getBaseTrace_append_eq hbase hcredit


/-- At the crossing index, a forward-permutation query cannot create a hash credit: if it is
new it has the wrong tag, and if it is redundant it creates no base representative. -/
lemma d2sQueryImpl_support_hashCreditA_false_of_perm_at_base_length
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (sIn : CanonicalSpongeState U)
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
      (m := OptionT ProbComp) gImpl auxImpl (dsPermQuery sIn) st).run))
    {sOut : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (sOut, st'))
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    (hlen : (getBaseTrace st.trace).length = j) :
    ¬ hashCreditA (T_H := T_H) (T_P := T_P) j i c st' := by
  intro hcredit
  unfold hashCreditA at hcredit
  have htrace := d2sQueryImpl_support_trace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl (dsPermQuery sIn) st hr sOut st' hrEq
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace st.trace)
      ⟨dsPermQuery sIn, sOut⟩
  · have hbase : getBaseTrace st'.trace = getBaseTrace st.trace := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_redundant_base st.trace
        ⟨dsPermQuery sIn, sOut⟩ hred
    rw [hbase] at hcredit
    exact (by omega : False)
  · have hbase : getBaseTrace st'.trace =
        getBaseTrace st.trace ++ [⟨dsPermQuery sIn, sOut⟩] := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_not_redundant_base st.trace
        ⟨dsPermQuery sIn, sOut⟩ hred
    have hhash := hcredit.2.1
    rw [hbase] at hhash
    have hnone := hashOutCapAt_append_perm_length
      (StmtIn := StmtIn) (U := U) (getBaseTrace st.trace) sIn sOut
    rw [← hlen] at hhash
    rw [hnone] at hhash
    cases hhash

/-- The inverse-permutation branch has the same tag exclusion at the crossing index. -/
lemma d2sQueryImpl_support_hashCreditA_false_of_permInv_at_base_length
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (sOut : CanonicalSpongeState U)
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
      (m := OptionT ProbComp) gImpl auxImpl (dsPermInvQuery sOut) st).run))
    {sIn : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (sIn, st'))
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    (hlen : (getBaseTrace st.trace).length = j) :
    ¬ hashCreditA (T_H := T_H) (T_P := T_P) j i c st' := by
  intro hcredit
  unfold hashCreditA at hcredit
  have htrace := d2sQueryImpl_support_trace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl (dsPermInvQuery sOut) st hr sIn st' hrEq
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace st.trace)
      ⟨dsPermInvQuery sOut, sIn⟩
  · have hbase : getBaseTrace st'.trace = getBaseTrace st.trace := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_redundant_base st.trace
        ⟨dsPermInvQuery sOut, sIn⟩ hred
    rw [hbase] at hcredit
    exact (by omega : False)
  · have hbase : getBaseTrace st'.trace =
        getBaseTrace st.trace ++ [⟨dsPermInvQuery sOut, sIn⟩] := by
      rw [htrace]
      exact getBaseTrace_append_singleton_of_not_redundant_base st.trace
        ⟨dsPermInvQuery sOut, sIn⟩ hred
    have hhash := hcredit.2.1
    rw [hbase] at hhash
    have hnone := hashOutCapAt_append_permInv_length
      (StmtIn := StmtIn) (U := U) (getBaseTrace st.trace) sOut sIn
    rw [← hlen] at hhash
    rw [hnone] at hhash
    cases hhash


/-- After the crossing point, a complete combined continuation cannot alter the target-side
readout of the fixed hash atom.  This includes aborting continuations because the wrapped oracle
keeps the current state on the `none` branch. -/
lemma combinedImpl_support_hashCreditTarget_iff_of_index_le
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
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    (hj : j ≤ (getBaseTrace st.trace).length) :
    hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 ↔
      hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st := by
  refine combinedImpl_support_state_invariant
    (StmtIn := StmtIn) (U := U)
    (spongeImpl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)
    (I := fun s =>
      j ≤ (getBaseTrace s.trace).length ∧
        (hashCreditTarget (T_H := T_H) (T_P := T_P) j i c s ↔
          hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st))
    ?_ (st, log) ⟨hj, Iff.rfl⟩ hr |>.2
  intro q s step hs hstep
  cases step with
  | none => trivial
  | some pair =>
      rcases pair with ⟨a, s'⟩
      obtain ⟨extra, hbase⟩ := d2sQueryImpl_support_baseTrace_append
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) gImpl auxImpl q s hstep rfl
      have hj' : j ≤ (getBaseTrace s'.trace).length := by
        rw [hbase, List.length_append]
        exact Nat.le_trans hs.1 (Nat.le_add_right _ _)
      refine ⟨hj', ?_⟩
      have hiff := hashCreditTarget_iff_of_getBaseTrace_append_eq
        (T_H := T_H) (T_P := T_P) (j := j) (i := i) (c := c) hbase hs.1
      exact hiff.trans hs.2

/-- A realized hash credit survives any complete combined prover or verifier continuation.  The
logging wrapper retains the state on abort, so this includes partial executions. -/
lemma combinedImpl_support_hashCreditA_stable
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
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    (hcredit : hashCreditA (T_H := T_H) (T_P := T_P) j i c st) :
    hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 := by
  refine combinedImpl_support_state_invariant
    (StmtIn := StmtIn) (U := U)
    (spongeImpl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)
    (I := fun s => hashCreditA (T_H := T_H) (T_P := T_P) j i c s)
    ?_ (st, log) hcredit hr
  intro q s step hs hstep
  cases step with
  | none => trivial
  | some pair =>
      rcases pair with ⟨a, s'⟩
      exact d2sQueryImpl_support_hashCreditA_stable
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) gImpl auxImpl q s hstep rfl hs

/-- If the fixed base position already lies in the incoming trace and has no hash credit, then no
combined continuation can create one. -/
lemma combinedImpl_support_not_hashCreditA_stable_of_index_lt
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
    {j : ℕ} {i : Fin (2 * j)} {c : Vector U SpongeSize.C}
    (hj : j < (getBaseTrace st.trace).length)
    (hcredit : ¬ hashCreditA (T_H := T_H) (T_P := T_P) j i c st) :
    ¬ hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 := by
  refine combinedImpl_support_state_invariant
    (StmtIn := StmtIn) (U := U)
    (spongeImpl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)
    (I := fun s => j < (getBaseTrace s.trace).length ∧
      ¬ hashCreditA (T_H := T_H) (T_P := T_P) j i c s)
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
      have hiff := hashCreditA_iff_of_getBaseTrace_append_eq
        (T_H := T_H) (T_P := T_P) (j := j) (i := i) (c := c) hbase hs.1
      exact hs.2 (hiff.mp hcredit')

/-- The terminal branch of the stopping-time calculation: after base index `j` has already been
fixed to a non-credit entry, an arbitrary combined continuation has zero chance of creating the
credit. -/
lemma combinedImpl_hashCreditA_prob_eq_zero_of_index_lt
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hj : j < (getBaseTrace st.trace).length)
    (hcredit : ¬ hashCreditA (T_H := T_H) (T_P := T_P) j i c st) :
    Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
      ((simulateQ (lemma5_8CombinedImpl
        (ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)) oa).run).run (st, log)] = 0 := by
  apply probEvent_eq_zero
  intro r hr hfinal
  exact combinedImpl_support_not_hashCreditA_stable_of_index_lt
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st log hr hj hcredit hfinal

/-- One query layer of a log-appending combined execution, exposed as an ordinary `ProbComp`
bind.  This is the monadic induction equation for the stopping-time argument.  In particular,
the first branch records the current state when the underlying D2S query aborts; it does not
silently discard the partial trace. -/
lemma combinedImpl_run_query_bind_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {α : Type}
    (spongeImpl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        (OptionT ProbComp)))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    ((simulateQ (lemma5_8CombinedImpl spongeImpl)
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx)).run).run st =
      ((lemma5_8WrappedDSImpl spongeImpl q).run).run st >>= fun first =>
        match first with
        | (none, st') => pure (none, st')
        | (some a, st') =>
            ((simulateQ (lemma5_8CombinedImpl spongeImpl) (mx a)).run).run st' := by
  simp only [simulateQ_query_bind, lemma5_8CombinedImpl, OracleQuery.input_query,
    QueryImpl.add_apply_inr, Option.elimM, monadLift_self, OptionT.run_bind,
    StateT.run_bind]
  apply bind_congr
  intro first
  rcases first with ⟨answer, st'⟩
  cases answer <;> rfl

/-- A support-wise equivalence of an event after every continuation identifies the event
probability with the corresponding event on the outer draw.  This is the probability form of
the continuation-invariance step used at the unique hash-miss crossing. -/
lemma probEvent_bind_eq_of_support_iff {α β : Type}
    (mx : ProbComp α) (my : α → ProbComp β)
    (P : β → Prop) (Q : α → Prop)
    (hfail : ∀ x ∈ support mx, Pr[⊥ | my x] = 0)
    (hiff : ∀ x ∈ support mx, ∀ y ∈ support (my x), P y ↔ Q x) :
    Pr[ P | mx >>= my] = Pr[ Q | mx] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator]
  refine tsum_congr ?_
  intro x
  by_cases hx : x ∈ support mx
  · by_cases hQ : Q x
    · have hinner : Pr[ P | my x] = 1 := by
        rw [probEvent_eq_one_iff]
        refine ⟨hfail x hx, ?_⟩
        intro y hy
        exact (hiff x hx y hy).mpr hQ
      rw [hinner]
      rw [Set.indicator_of_mem (show x ∈ {x | Q x} from hQ)]
      simp only [mul_one]
    · have hinner : Pr[ P | my x] = 0 := by
        apply probEvent_eq_zero
        intro y hy hP
        exact hQ ((hiff x hx y hy).mp hP)
      rw [hinner]
      rw [Set.indicator_of_notMem (show x ∉ {x | Q x} from hQ)]
      simp only [mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hx]
    simp only [zero_mul]
    by_cases hQ : Q x
    · rw [Set.indicator_of_mem (show x ∈ {x | Q x} from hQ)]
      rw [probOutput_eq_zero_of_not_mem_support hx]
    · rw [Set.indicator_of_notMem (show x ∉ {x | Q x} from hQ)]

/-- The wrapped one-query distribution is the public D2S query distribution followed by the
log-appending/state-retention map. -/
lemma wrappedDSImpl_run_eq_d2sQuery_bind
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    ((lemma5_8WrappedDSImpl
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl) q).run).run (st, log) =
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run >>= fun first =>
        match first with
        | none => pure (none, (st, log))
        | some (a, st') => pure (some a, (st', log ++ [⟨Sum.inr q, a⟩])) := by
  simp only [lemma5_8WrappedDSImpl, OptionT.run_mk]
  unfold StateT.run
  dsimp
  apply bind_congr
  intro first
  cases first with
  | none => rfl
  | some pair =>
      rcases pair with ⟨answer, st'⟩
      rfl

/-- Lift a relative probability bound for every possible public D2S-query result through one
combined query layer.  This is the non-crossing induction rule: unlike the hash-miss crossing,
the relative bound is valid after conditioning on the immediate query result, so
`probEvent_bind_rel_div_le` applies directly. -/
lemma combinedImpl_query_bind_rel_le_of_step
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {α : Type}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q) →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (A B : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) → Prop)
    (D : ℝ≥0∞)
    (hstep : ∀ first ∈ support
        ((ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl q st).run),
      Pr[ A |
        match first with
        | none => pure (none, (st, log))
        | some (a, st') =>
            ((simulateQ (lemma5_8CombinedImpl
              (ProverTransform.d2sQueryImpl
                (δ := δ) (T_H := T_H) (T_P := T_P)
                (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)) (mx a)).run).run
              (st', log ++ QueryLog.singleton (Sum.inr q) a)]
        ≤ Pr[ B |
          match first with
          | none => pure (none, (st, log))
          | some (a, st') =>
              ((simulateQ (lemma5_8CombinedImpl
                (ProverTransform.d2sQueryImpl
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl)) (mx a)).run).run
                (st', log ++ QueryLog.singleton (Sum.inr q) a)] / D) :
    Pr[ A |
      ((simulateQ (lemma5_8CombinedImpl
        (ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl))
        (liftM (OracleSpec.query (Sum.inr q)) >>= mx)).run).run (st, log)]
      ≤ Pr[ B |
        ((simulateQ (lemma5_8CombinedImpl
          (ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl))
          (liftM (OracleSpec.query (Sum.inr q)) >>= mx)).run).run (st, log)] / D := by
  let spongeImpl := ProverTransform.d2sQueryImpl
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl
  let step := (spongeImpl q st).run
  let cont : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) →
      ProbComp (Option α ×
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))) :=
    fun first => match first with
    | none => pure (none, (st, log))
    | some (a, st') =>
        ((simulateQ (lemma5_8CombinedImpl spongeImpl) (mx a)).run).run
          (st', log ++ [⟨Sum.inr q, a⟩])
  have hrun :
      ((simulateQ (lemma5_8CombinedImpl spongeImpl)
        (liftM (OracleSpec.query (Sum.inr q)) >>= mx)).run).run (st, log) =
        step >>= cont := by
    rw [combinedImpl_run_query_bind_eq]
    rw [wrappedDSImpl_run_eq_d2sQuery_bind]
    rw [bind_assoc]
    apply bind_congr
    intro first
    cases first with
    | none => rfl
    | some pair =>
        rcases pair with ⟨a, st'⟩
        rfl
  change Pr[ A | ((simulateQ (lemma5_8CombinedImpl spongeImpl)
    (liftM (OracleSpec.query (Sum.inr q)) >>= mx)).run).run (st, log)] ≤
    Pr[ B | ((simulateQ (lemma5_8CombinedImpl spongeImpl)
      (liftM (OracleSpec.query (Sum.inr q)) >>= mx)).run).run (st, log)] / D
  rw [hrun]
  apply probEvent_bind_rel_div_le step cont A B D
  intro first hfirst
  exact hstep first hfirst

/-- On a genuine hash-table miss, the raw trace extension is also a base-trace extension.  This
version needs only the hash-table invariant, which is the global invariant available to the sigma
simulator. -/
lemma d2sHandleHashQuery_miss_support_baseTrace_eq_of_hash_wf
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    {r : Option (Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hr : r ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleHashQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run)
    {a : Vector U SpongeSize.C}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (some (a, st'))) :
    getBaseTrace st'.trace =
      getBaseTrace st.trace ++ [⟨dsHashQuery stmt, a⟩] := by
  have hTrace : st'.trace = st.trace ++ [⟨dsHashQuery stmt, a⟩] :=
    ProverTransform.d2sHandleHashQuery_support_trace_append
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      gImpl auxImpl stmt st hr a st' hrEq
  rw [hTrace]
  exact getBaseTrace_append_hash_miss_eq_of_hash_wf
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
    hwf st.h_mirror hLookup

/-- A successful public fresh hash query creates exactly one new base representative, labelled
with its sampled capacity.  This is the crossing transition used by the hash stopping-time
argument. -/
lemma d2sQueryImpl_hash_miss_support_baseTrace_eq
    [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    {r : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsHashQuery stmt) st).run))
    {a : Vector U SpongeSize.C}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (a, st')) :
    getBaseTrace st'.trace =
      getBaseTrace st.trace ++ [⟨dsHashQuery stmt, a⟩] := by
  have hstep := d2sQueryImpl_support_step_success
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl (dsHashQuery stmt) st hr hrEq
  exact d2sHandleHashQuery_miss_support_baseTrace_eq_of_hash_wf
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st hwf hLookup hstep rfl

/-- On a genuine hash miss, the new representative's hash-capacity readout is the sampled
capacity. -/
lemma d2sHandleHashQuery_miss_support_hashOutCapAt_length_of_hash_wf
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    {r : Option (Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hr : r ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleHashQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run)
    {a : Vector U SpongeSize.C}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (some (a, st'))) :
    hashOutCapAt (getBaseTrace st'.trace) (getBaseTrace st.trace).length = some a := by
  have hbase := d2sHandleHashQuery_miss_support_baseTrace_eq_of_hash_wf
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st hwf hLookup hr hrEq
  rw [hbase]
  exact hashOutCapAt_append_hash_length (StmtIn := StmtIn) (U := U)
    (getBaseTrace st.trace) stmt a

/-- On a genuine hash miss, the old capacity-target readout is unaffected by the newly appended
representative. -/
lemma d2sHandleHashQuery_miss_support_priorCapacityTargetAt_length_of_hash_wf
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    {r : Option (Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hr : r ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleHashQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run)
    {a : Vector U SpongeSize.C}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hrEq : r = some (some (a, st')))
    (idx : Fin (2 * (getBaseTrace st.trace).length)) :
    priorCapacityTargetAt (getBaseTrace st'.trace) (getBaseTrace st.trace).length idx =
      priorCapacityTargetAt (getBaseTrace st.trace) (getBaseTrace st.trace).length idx := by
  have hbase := d2sHandleHashQuery_miss_support_baseTrace_eq_of_hash_wf
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st hwf hLookup hr hrEq
  rw [hbase]
  exact priorCapacityTargetAt_append_singleton_length
    (StmtIn := StmtIn) (U := U)
    (bt := getBaseTrace st.trace) (entry := ⟨.inl stmt, a⟩) idx

/-- The local hash-miss credit.  At the precise step where the old base trace has length `j`, a
new hash representative can satisfy the collision atom only when the fresh capacity sample is
`c`; the target side is already determined by the old trace. -/
lemma d2sHandleHashQuery_miss_credit_le
    [Nonempty U] [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length = j) :
    Pr[ fun r => ∃ a st', r = some (some (a, st')) ∧
        hashCreditA (T_H := T_H) (T_P := T_P) j i c st' |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleHashQuery
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run]
      ≤ (if priorCapacityTargetAt (getBaseTrace st.trace) j i = some c then 1 else 0) /
        capacitySpaceSize (U := U) := by
  subst j
  let gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp) :=
    fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)
  let auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp) :=
    fun aux => OptionT.lift
      (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux)
  let impl := gImpl + auxImpl
  let handler := OptionT.run ((ProverTransform.d2sHandleHashQuery
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st)
  change Pr[ fun r => ∃ a st', r = some (some (a, st')) ∧
      hashCreditA (T_H := T_H) (T_P := T_P)
        (getBaseTrace st.trace).length i c st' |
      (simulateQ impl handler).run]
    ≤ (if priorCapacityTargetAt (getBaseTrace st.trace)
        (getBaseTrace st.trace).length i = some c then 1 else 0) /
      capacitySpaceSize (U := U)
  calc
    Pr[ fun r => ∃ a st', r = some (some (a, st')) ∧
        hashCreditA (T_H := T_H) (T_P := T_P)
          (getBaseTrace st.trace).length i c st' |
      (simulateQ impl handler).run]
        ≤ Pr[ fun r =>
          Option.map (Option.map Prod.fst) r = some (some c) ∧
            priorCapacityTargetAt (getBaseTrace st.trace)
              (getBaseTrace st.trace).length i = some c |
          (simulateQ impl handler).run] := by
            refine probEvent_mono ?_
            intro r hr hcredit
            obtain ⟨a, st', hrEq, hcredit⟩ := hcredit
            rcases hcredit with ⟨_hj, hhash, htarget⟩
            have hhashAt :=
              d2sHandleHashQuery_miss_support_hashOutCapAt_length_of_hash_wf
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) gImpl auxImpl st hwf hLookup hr hrEq
            have htargetAt :=
              d2sHandleHashQuery_miss_support_priorCapacityTargetAt_length_of_hash_wf
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) gImpl auxImpl st hwf hLookup hr hrEq i
            have ha : a = c := Option.some.inj (hhashAt.symm.trans hhash)
            refine ⟨?_, ?_⟩
            · rw [hrEq, ha]
              rfl
            · rw [← htargetAt]
              exact htarget
    _ ≤ (if priorCapacityTargetAt (getBaseTrace st.trace)
          (getBaseTrace st.trace).length i = some c then 1 else 0) /
        capacitySpaceSize (U := U) := by
          exact d2sHandleHashQuery_miss_sigma_atom_le
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) k_g st hLookup i c

set_option maxHeartbeats 400000 in
/-- The local hash-miss credit on the public `d2sQueryImpl` surface.  This removes the
`OptionT`/state wrapper but leaves the stopping-time induction entirely outside this lemma. -/
lemma d2sQueryImpl_hash_miss_credit_le
    [Nonempty U] [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length = j) :
    Pr[ fun r => ∃ a st', r = some (a, st') ∧
        hashCreditA (T_H := T_H) (T_P := T_P) j i c st' |
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
        (auxImpl := fun aux => OptionT.lift
          ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux))
        (dsHashQuery stmt) st).run]
      ≤ (if priorCapacityTargetAt (getBaseTrace st.trace) j i = some c then 1 else 0) /
        capacitySpaceSize (U := U) := by
  let gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp) :=
    fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)
  let auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp) :=
    fun aux => OptionT.lift
      ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux)
  let handler := OptionT.run ((ProverTransform.d2sHandleHashQuery
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st)
  change Pr[ fun r => ∃ a st', r = some (a, st') ∧
      hashCreditA (T_H := T_H) (T_P := T_P) j i c st' |
    (ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      gImpl auxImpl (dsHashQuery stmt) st).run]
    ≤ (if priorCapacityTargetAt (getBaseTrace st.trace) j i = some c then 1 else 0) /
      capacitySpaceSize (U := U)
  have hrun :
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        gImpl auxImpl (dsHashQuery stmt) st).run =
      Option.elimM (simulateQ (gImpl + auxImpl) handler).run (pure none)
      (fun x : Option (Vector U SpongeSize.C ×
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
  let P : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) → Prop :=
    fun r => ∃ a st', r = some (a, st') ∧
      hashCreditA (T_H := T_H) (T_P := T_P) j i c st'
  let mx := (simulateQ (gImpl + auxImpl) handler).run
  let Q : Option (Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) → Prop :=
    fun o => ∃ a st', o = some (some (a, st')) ∧
      hashCreditA (T_H := T_H) (T_P := T_P) j i c st'
  have hNone : ¬ P none := by
    intro hnone
    rcases hnone with ⟨a, st', hEq, _⟩
    cases hEq
  have hjoin :
      Pr[ P | Option.elimM mx (pure none)
        (fun x : Option (Vector U SpongeSize.C ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) =>
          match x with
          | none => pure none
          | some pair => pure (some pair))] =
        Pr[ fun o => ∃ pair, o = some (some pair) ∧ P (some pair) | mx] :=
    by
      classical
      rw [Option.elimM, probEvent_bind_eq_tsum, probEvent_eq_tsum_indicator]
      refine tsum_congr ?_
      intro o
      cases o with
      | none => simp [hNone]
      | some oa =>
          cases oa with
          | none => simp [hNone]
          | some pair =>
              have hevent :
                  (∃ pair' : Vector U SpongeSize.C ×
                    ProverTransform.D2SQueryState
                      (δ := δ) (T_H := T_H) (T_P := T_P)
                      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
                    some (some pair) = some (some pair') ∧ P (some pair')) ↔
                    P (some pair) := by
                constructor
                · rintro ⟨pair', hEq, hP'⟩
                  have hpair : pair = pair' := Option.some.inj (Option.some.inj hEq)
                  rw [hpair]
                  exact hP'
                · intro hP'
                  exact ⟨pair, rfl, hP'⟩
              by_cases hP : P (some pair)
              · rw [Set.indicator_of_mem
                    (show some (some pair) ∈
                      {o | ∃ pair', o = some (some pair') ∧ P (some pair')} from
                      hevent.mpr hP)]
                simp [hP]
              · rw [Set.indicator_of_notMem
                    (show some (some pair) ∉
                      {o | ∃ pair', o = some (some pair') ∧ P (some pair')} from
                      fun h => hP (hevent.mp h))]
                simp [hP]
  have hPQ :
      (fun o => ∃ pair, o = some (some pair) ∧ P (some pair)) = Q := by
    funext o
    apply propext
    constructor
    · rintro ⟨pair, hpair, a, st', hsome, hcredit⟩
      have hpair' : pair = (a, st') := Option.some.inj hsome
      rw [hpair'] at hpair
      exact ⟨a, st', hpair, hcredit⟩
    · rintro ⟨a, st', hpair, hcredit⟩
      exact ⟨(a, st'), hpair, a, st', rfl, hcredit⟩
  change Pr[ P | Option.elimM mx (pure none)
    (fun x : Option (Vector U SpongeSize.C ×
        ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) =>
        match x with
        | none => pure none
        | some pair => pure (some pair))]
    ≤ (if priorCapacityTargetAt (getBaseTrace st.trace) j i = some c then 1 else 0) /
      capacitySpaceSize (U := U)
  rw [hjoin, hPQ]
  exact d2sHandleHashQuery_miss_credit_le
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hwf hLookup j i c hlen

/-- The aggregate hash-miss crossing bound, lifted through an arbitrary continuation.  At the
crossing state `length bt = j`, the continuation may inspect the sampled answer, but it cannot
change either the new hash atom at index `j` or the old target readout.  Hence the local uniform
capacity bound remains valid for the complete suffix execution. -/
lemma hashMiss_combinedImpl_credit_rel_le
    [Nonempty U] [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    (j : ℕ) (i : Fin (2 * j)) (c : Vector U SpongeSize.C)
    (hlen : (getBaseTrace st.trace).length = j)
    {α : Type}
    (mx : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range
      (Sum.inr (dsHashQuery stmt)) →
        OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    Pr[ fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1 |
      ((simulateQ (lemma5_8CombinedImpl
        (ProverTransform.d2sQueryImpl
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (gImpl := fun q => OptionT.lift
            ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
          (auxImpl := fun aux => OptionT.lift
            ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux))))
        (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx)).run).run (st, log)]
      ≤ Pr[ fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1 |
        ((simulateQ (lemma5_8CombinedImpl
          (ProverTransform.d2sQueryImpl
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (gImpl := fun q => OptionT.lift
              ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
            (auxImpl := fun aux => OptionT.lift
              ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux))))
          (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx)).run).run (st, log)] /
        capacitySpaceSize (U := U) := by
  classical
  let gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp) :=
    fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)
  let auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp) :=
    fun aux => OptionT.lift
      ((ProverTransform.d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) aux)
  let spongeImpl := ProverTransform.d2sQueryImpl
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) gImpl auxImpl
  let step := (spongeImpl (dsHashQuery stmt) st).run
  let cont : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) →
      ProbComp (Option α ×
        (ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))) :=
    fun first => match first with
    | none => pure (none, (st, log))
    | some (a, st') =>
        ((simulateQ (lemma5_8CombinedImpl spongeImpl) (mx a)).run).run
          (st', log ++ [⟨Sum.inr (dsHashQuery stmt), a⟩])
  have hrun :
      ((simulateQ (lemma5_8CombinedImpl spongeImpl)
        (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx)).run).run (st, log) =
        step >>= cont := by
    rw [combinedImpl_run_query_bind_eq]
    rw [wrappedDSImpl_run_eq_d2sQuery_bind]
    rw [bind_assoc]
    apply bind_congr
    intro first
    cases first with
    | none => rfl
    | some pair =>
        rcases pair with ⟨a, st'⟩
        rfl
  have hnotA : ¬ hashCreditA (T_H := T_H) (T_P := T_P) j i c st := by
    rintro ⟨hj, _hhash, _htarget⟩
    omega
  let A : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) → Prop :=
    fun r => hashCreditA (T_H := T_H) (T_P := T_P) j i c r.2.1
  let B : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) → Prop :=
    fun r => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c r.2.1
  let QA : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) → Prop :=
    fun first => ∃ a st', first = some (a, st') ∧
      hashCreditA (T_H := T_H) (T_P := T_P) j i c st'
  let QB : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) → Prop :=
    fun _ => hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st
  have hAeq : Pr[ A | step >>= cont] = Pr[ QA | step] := by
    apply probEvent_bind_eq_of_support_iff step cont A QA
    · intro _ _
      exact probFailure_eq_zero
    · intro first hfirst final hfinal
      cases first with
      | none =>
          rw [mem_support_pure_iff] at hfinal
          subst final
          dsimp only [A, QA]
          constructor
          · intro hA
            exact False.elim (hnotA hA)
          · rintro ⟨a, st', hEq, _hA⟩
            cases hEq
      | some pair =>
          rcases pair with ⟨a, st'⟩
          dsimp [cont] at hfinal
          have hbase := d2sQueryImpl_hash_miss_support_baseTrace_eq
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) gImpl auxImpl st hwf hLookup hfirst rfl
          have hj' : j < (getBaseTrace st'.trace).length := by
            rw [hbase, List.length_append]
            simp only [List.length_singleton]
            omega
          have hcontA : A final ↔ hashCreditA (T_H := T_H) (T_P := T_P) j i c st' := by
            constructor
            · intro hfinalA
              by_contra hnot
              have hnotFinal := combinedImpl_support_not_hashCreditA_stable_of_index_lt
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) gImpl auxImpl st'
                (log ++ [⟨Sum.inr (dsHashQuery stmt), a⟩]) hfinal hj' hnot
              exact hnotFinal hfinalA
            · intro hpostA
              exact combinedImpl_support_hashCreditA_stable
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) gImpl auxImpl st'
                (log ++ [⟨Sum.inr (dsHashQuery stmt), a⟩]) hfinal hpostA
          have hQA : QA (some (a, st')) ↔
              hashCreditA (T_H := T_H) (T_P := T_P) j i c st' := by
            constructor
            · rintro ⟨a', st'', hEq, hA'⟩
              have hpair : (a, st') = (a', st'') := Option.some.inj hEq
              cases hpair
              exact hA'
            · intro hA'
              exact ⟨a, st', rfl, hA'⟩
          exact hcontA.trans hQA.symm
  have hBeq : Pr[ B | step >>= cont] = Pr[ QB | step] := by
    apply probEvent_bind_eq_of_support_iff step cont B QB
    · intro _ _
      exact probFailure_eq_zero
    · intro first hfirst final hfinal
      cases first with
      | none =>
          rw [mem_support_pure_iff] at hfinal
          subst final
          exact Iff.rfl
      | some pair =>
          rcases pair with ⟨a, st'⟩
          dsimp [cont] at hfinal
          have hbase := d2sQueryImpl_hash_miss_support_baseTrace_eq
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) gImpl auxImpl st hwf hLookup hfirst rfl
          have hj' : j ≤ (getBaseTrace st'.trace).length := by
            rw [hbase, List.length_append]
            simp only [List.length_singleton]
            rw [← hlen]
            omega
          have hcont := combinedImpl_support_hashCreditTarget_iff_of_index_le
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) (j := j) (i := i) (c := c) gImpl auxImpl st'
            (log ++ [⟨Sum.inr (dsHashQuery stmt), a⟩]) hfinal hj'
          have hstate := hashCreditTarget_iff_of_getBaseTrace_append_eq
            (T_H := T_H) (T_P := T_P) (j := j) (i := i) (c := c) hbase (by omega)
          exact hcont.trans hstate
  have hstepA : Pr[ QA | step] ≤
      (if hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st then 1 else 0) /
        capacitySpaceSize (U := U) := by
    dsimp only [step, QA, spongeImpl, gImpl, auxImpl, hashCreditTarget]
    by_cases htarget : priorCapacityTargetAt (getBaseTrace st.trace) j i = some c
    · rw [if_pos htarget]
      have hlocal := d2sQueryImpl_hash_miss_credit_le
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) k_g st hwf hLookup j i c hlen
      rw [if_pos htarget] at hlocal
      exact hlocal
    · rw [if_neg htarget]
      have hlocal := d2sQueryImpl_hash_miss_credit_le
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) k_g st hwf hLookup j i c hlen
      rw [if_neg htarget] at hlocal
      exact hlocal
  have hstepB : Pr[ QB | step] =
      if hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st then 1 else 0 := by
    change Pr[ fun _ : Option (Vector U SpongeSize.C ×
        ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) =>
        hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st | step] = _
    by_cases htarget : hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st
    · rw [if_pos htarget]
      calc
        Pr[ fun _ : Option (Vector U SpongeSize.C ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) =>
            hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st | step]
            = 1 - Pr[⊥ | step] := by
              have hconst := probEvent_const step
                (hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st)
              rw [if_pos htarget] at hconst
              exact hconst
        _ = 1 := by
              rw [probFailure_eq_zero]
              rw [tsub_zero]
    · rw [if_neg htarget]
      have hconst := probEvent_const step
        (hashCreditTarget (T_H := T_H) (T_P := T_P) j i c st)
      rw [if_neg htarget] at hconst
      exact hconst
  change Pr[ A | ((simulateQ (lemma5_8CombinedImpl spongeImpl)
    (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx)).run).run (st, log)] ≤
    Pr[ B | ((simulateQ (lemma5_8CombinedImpl spongeImpl)
      (liftM (OracleSpec.query (Sum.inr (dsHashQuery stmt))) >>= mx)).run).run (st, log)] /
      capacitySpaceSize (U := U)
  rw [hrun, hAeq, hBeq, hstepB]
  exact hstepA

end HashCredit

end BadEventDS

end DuplexSpongeFS

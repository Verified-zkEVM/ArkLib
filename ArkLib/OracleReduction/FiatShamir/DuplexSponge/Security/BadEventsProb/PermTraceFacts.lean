/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SpongeTrace
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CapacityTargets

/-!
# Deterministic permutation trace facts for Lemma 5.8

This module contains the trace-only facts behind the paper's statement that a response chosen to
be consistent with a previous permutation query is not a fresh base-trace entry.  In the eager
sponge experiment every permutation entry is answered by the sampled bijection `p`; once
`getBaseTrace` has normalized duplicate forward/inverse pairs, the same normalized pair cannot
occur at two strict base positions.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-! ## Exposed sides of normalized permutation pairs

For the eager no-replacement argument, a prior forward query exposes its range state and a prior
inverse query exposes its queried-output state; both are the range of the same normalized
permutation pair.  Dually, the other side is the normalized-pair domain.  We keep these as
finite sets of full states, rather than only capacity segments: the deferred-decision swap must
avoid an already observed *state*, while the collision count later projects these sets to
capacity segments.

The two definitions deliberately inspect only the first `j` base entries.  Thus they describe
exactly the states observed before the charged representative at base index `j`. -/

/-- The range-side state exposed by a permutation base entry, if the entry is a permutation
query.  Forward entries expose their answer; inverse entries expose their queried output. -/
def permRangeStateAt
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (i : ℕ) :
    Option (CanonicalSpongeState U) :=
  (bt[i]?).bind fun e => match e with
    | ⟨.inr (.inl _), sOut⟩ => some sOut
    | ⟨.inr (.inr sOut), _⟩ => some sOut
    | ⟨.inl _, _⟩ => none

/-- The domain-side state exposed by a permutation base entry, if the entry is a permutation
query.  Forward entries expose their queried input; inverse entries expose their answer. -/
def permDomainStateAt
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (i : ℕ) :
    Option (CanonicalSpongeState U) :=
  (bt[i]?).bind fun e => match e with
    | ⟨.inr (.inl sIn), _⟩ => some sIn
    | ⟨.inr (.inr _), sIn⟩ => some sIn
    | ⟨.inl _, _⟩ => none

/-- All normalized-pair range states exposed strictly before base position `j`. -/
noncomputable def permExposedRangeFinset [Fintype U] [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Finset (CanonicalSpongeState U) :=
  (Finset.univ.filter fun y => ∃ i < j, permRangeStateAt bt i = some y)

/-- All normalized-pair domain states exposed strictly before base position `j`. -/
noncomputable def permExposedDomainFinset [Fintype U] [DecidableEq U]
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Finset (CanonicalSpongeState U) :=
  (Finset.univ.filter fun x => ∃ i < j, permDomainStateAt bt i = some x)

lemma mem_permExposedRangeFinset_iff [Fintype U] [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {y : CanonicalSpongeState U} :
    y ∈ permExposedRangeFinset bt j ↔ ∃ i < j, permRangeStateAt bt i = some y := by
  classical
  unfold permExposedRangeFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_permExposedDomainFinset_iff [Fintype U] [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {x : CanonicalSpongeState U} :
    x ∈ permExposedDomainFinset bt j ↔ ∃ i < j, permDomainStateAt bt i = some x := by
  classical
  unfold permExposedDomainFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The exposed range-side states depend only on the strict base-trace prefix. -/
lemma permExposedRangeFinset_eq_of_take_eq [Fintype U] [DecidableEq U]
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hprefix : bt₁.take j = bt₂.take j) :
    permExposedRangeFinset bt₁ j = permExposedRangeFinset bt₂ j := by
  classical
  apply Finset.ext
  intro y
  rw [mem_permExposedRangeFinset_iff, mem_permExposedRangeFinset_iff]
  constructor
  · rintro ⟨i, hi, hstate⟩
    refine ⟨i, hi, ?_⟩
    unfold permRangeStateAt at hstate ⊢
    rw [getElem?_eq_of_take_eq hprefix hi] at hstate
    exact hstate
  · rintro ⟨i, hi, hstate⟩
    refine ⟨i, hi, ?_⟩
    unfold permRangeStateAt at hstate ⊢
    rw [← getElem?_eq_of_take_eq hprefix hi] at hstate
    exact hstate

/-- The exposed domain-side states depend only on the strict base-trace prefix. -/
lemma permExposedDomainFinset_eq_of_take_eq [Fintype U] [DecidableEq U]
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hprefix : bt₁.take j = bt₂.take j) :
    permExposedDomainFinset bt₁ j = permExposedDomainFinset bt₂ j := by
  classical
  apply Finset.ext
  intro x
  rw [mem_permExposedDomainFinset_iff, mem_permExposedDomainFinset_iff]
  constructor
  · rintro ⟨i, hi, hstate⟩
    refine ⟨i, hi, ?_⟩
    unfold permDomainStateAt at hstate ⊢
    rw [getElem?_eq_of_take_eq hprefix hi] at hstate
    exact hstate
  · rintro ⟨i, hi, hstate⟩
    refine ⟨i, hi, ?_⟩
    unfold permDomainStateAt at hstate ⊢
    rw [← getElem?_eq_of_take_eq hprefix hi] at hstate
    exact hstate

/-- A forward target set is unchanged when the strict prefix and the queried input state are
unchanged; the answer component of the current entry is irrelevant. -/
lemma permFwdCapacityTargetFinset_eq_of_take_eq_of_permFwdInputAt_eq
    [DecidableEq U]
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {x : CanonicalSpongeState U}
    (hprefix : bt₁.take j = bt₂.take j)
    (hread₁ : permFwdInputAt bt₁ j = some x)
    (hread₂ : permFwdInputAt bt₂ j = some x) :
    permFwdCapacityTargetFinset bt₁ j = permFwdCapacityTargetFinset bt₂ j := by
  unfold permFwdCapacityTargetFinset
  rw [priorCapacityTargetFinset_eq_of_take_eq hprefix]
  have hcap₁ := permInCapAt_eq_of_permFwdInputAt hread₁
  have hcap₂ := permInCapAt_eq_of_permFwdInputAt hread₂
  rw [hcap₁, hcap₂]

/-- An inverse target set is unchanged when the strict prefix and the queried output state are
unchanged; the answer component of the current entry is irrelevant. -/
lemma permBwdCapacityTargetFinset_eq_of_take_eq_of_permBwdOutputAt_eq
    [DecidableEq U]
    {bt₁ bt₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {y : CanonicalSpongeState U}
    (hprefix : bt₁.take j = bt₂.take j)
    (hread₁ : permBwdOutputAt bt₁ j = some y)
    (hread₂ : permBwdOutputAt bt₂ j = some y) :
    permBwdCapacityTargetFinset bt₁ j = permBwdCapacityTargetFinset bt₂ j := by
  unfold permBwdCapacityTargetFinset
  rw [priorCapacityTargetFinset_eq_of_take_eq hprefix]
  have hcap₁ := permInvDomainCapAt_eq_of_permBwdOutputAt hread₁
  have hcap₂ := permInvDomainCapAt_eq_of_permBwdOutputAt hread₂
  rw [hcap₁, hcap₂]

/-- Every exposed normalized-pair range has a capacity already present among the prior capacity
targets. -/
lemma mem_priorCapacityTargetFinset_of_mem_permExposedRangeFinset
    [Fintype U] [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {y : CanonicalSpongeState U}
    (hy : y ∈ permExposedRangeFinset bt j) :
    y.capacitySegment ∈ priorCapacityTargetFinset bt j := by
  obtain ⟨i, hi, hrange⟩ := (mem_permExposedRangeFinset_iff (bt := bt) (j := j)).mp hy
  unfold permRangeStateAt at hrange
  cases hentry : bt[i]? with
  | none =>
      rw [hentry] at hrange
      simp only [Option.bind_none, reduceCtorEq] at hrange
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hentry] at hrange
          simp only [Option.bind_some, reduceCtorEq] at hrange
      | inr permDom =>
          cases permDom with
          | inl sIn =>
              rw [hentry] at hrange
              simp only [Option.bind_some, Option.some.injEq] at hrange
              subst rng
              exact mem_optionListToFinset_of_mem_some
                (mem_priorCapacityTargets_of_entryCapAt (bt := bt) (j := j) (j' := i) hi
                  (1 : Fin 2) (by
                    rw [hentry]
                    rfl))
          | inr sOut =>
              rw [hentry] at hrange
              simp only [Option.bind_some, Option.some.injEq] at hrange
              subst sOut
              exact mem_optionListToFinset_of_mem_some
                (mem_priorCapacityTargets_of_entryCapAt (bt := bt) (j := j) (j' := i) hi
                  (0 : Fin 2) (by
                    rw [hentry]
                    rfl))

/-- Every exposed normalized-pair domain has a capacity already present among the prior capacity
targets. -/
lemma mem_priorCapacityTargetFinset_of_mem_permExposedDomainFinset
    [Fintype U] [DecidableEq U]
    {bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    {x : CanonicalSpongeState U}
    (hx : x ∈ permExposedDomainFinset bt j) :
    x.capacitySegment ∈ priorCapacityTargetFinset bt j := by
  obtain ⟨i, hi, hdomain⟩ := (mem_permExposedDomainFinset_iff (bt := bt) (j := j)).mp hx
  unfold permDomainStateAt at hdomain
  cases hentry : bt[i]? with
  | none =>
      rw [hentry] at hdomain
      simp only [Option.bind_none, reduceCtorEq] at hdomain
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hentry] at hdomain
          simp only [Option.bind_some, reduceCtorEq] at hdomain
      | inr permDom =>
          cases permDom with
          | inl sIn =>
              rw [hentry] at hdomain
              simp only [Option.bind_some, Option.some.injEq] at hdomain
              subst sIn
              exact mem_optionListToFinset_of_mem_some
                (mem_priorCapacityTargets_of_entryCapAt (bt := bt) (j := j) (j' := i) hi
                  (0 : Fin 2) (by
                    rw [hentry]
                    rfl))
          | inr sOut =>
              rw [hentry] at hdomain
              simp only [Option.bind_some, Option.some.injEq] at hdomain
              subst rng
              exact mem_optionListToFinset_of_mem_some
                (mem_priorCapacityTargets_of_entryCapAt (bt := bt) (j := j) (j' := i) hi
                  (1 : Fin 2) (by
                    rw [hentry]
                    rfl))

section DeterministicPermutationTrace

/-- A forward permutation entry in the deterministic eager sponge base trace is answered by the
sampled permutation. -/
lemma spongeDetTrace_permFwd_entry_output_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j : ℕ} {sIn sOut : CanonicalSpongeState U}
    (hentry : (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2))[j]? =
        some ⟨.inr (.inl sIn), sOut⟩) :
    sOut = (show Equiv.Perm (CanonicalSpongeState U) from fam.2) sIn := by
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change bt[j]? = some ⟨.inr (.inl sIn), sOut⟩ at hentry
  have hcons := spongeDetTrace_baseTrace_consistent
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam
  have hmem : (⟨.inr (.inl sIn), sOut⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, hentry⟩
  have hAns : sOut = spongeAnswer fam (.inr (.inl sIn)) := hcons _ hmem
  simp only [spongeAnswer] at hAns
  exact hAns

/-- An inverse permutation entry in the deterministic eager sponge base trace is answered by the
sampled inverse permutation. -/
lemma spongeDetTrace_permBwd_entry_range_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j : ℕ} {sOut sIn : CanonicalSpongeState U}
    (hentry : (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2))[j]? =
        some ⟨.inr (.inr sOut), sIn⟩) :
    sIn = (show Equiv.Perm (CanonicalSpongeState U) from fam.2).symm sOut := by
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change bt[j]? = some ⟨.inr (.inr sOut), sIn⟩ at hentry
  have hcons := spongeDetTrace_baseTrace_consistent
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam
  have hmem : (⟨.inr (.inr sOut), sIn⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ bt := by
    rw [List.mem_iff_getElem?]
    exact ⟨j, hentry⟩
  have hAns : sIn = spongeAnswer fam (.inr (.inr sOut)) := hcons _ hmem
  simp only [spongeAnswer] at hAns
  exact hAns

/-- In the deterministic eager sponge trace, a forward-permutation input readout at base
position `j` has output capacity equal to the sampled permutation's image capacity. -/
lemma spongeDetTrace_permFwdInput_outputCap_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j : ℕ} {sIn : CanonicalSpongeState U}
    (hinput : permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sIn) :
    permOutCapAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j =
      some (((show Equiv.Perm (CanonicalSpongeState U) from fam.2) sIn).capacitySegment) := by
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permFwdInputAt bt j = some sIn at hinput
  change permOutCapAt bt j =
    some (((show Equiv.Perm (CanonicalSpongeState U) from fam.2) sIn).capacitySegment)
  obtain ⟨sOut, hentry⟩ := exists_getElem?_permFwd_of_permFwdInputAt
    (StmtIn := StmtIn) (U := U) hinput
  have hsOut := spongeDetTrace_permFwd_entry_output_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry
  unfold permOutCapAt
  rw [hentry]
  rw [hsOut]
  rfl

/-- In the deterministic eager sponge trace, an inverse-permutation output readout at base
position `j` has range/preimage capacity equal to the sampled inverse image capacity. -/
lemma spongeDetTrace_permBwdOutput_rangeCap_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j : ℕ} {sOut : CanonicalSpongeState U}
    (houtput : permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sOut) :
    permInvRangeCapAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j =
      some (((show Equiv.Perm (CanonicalSpongeState U) from fam.2).symm sOut).capacitySegment) := by
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permBwdOutputAt bt j = some sOut at houtput
  change permInvRangeCapAt bt j =
    some (((show Equiv.Perm (CanonicalSpongeState U) from fam.2).symm sOut).capacitySegment)
  obtain ⟨sIn, hentry⟩ := exists_getElem?_permBwd_of_permBwdOutputAt
    (StmtIn := StmtIn) (U := U) houtput
  have hsIn := spongeDetTrace_permBwd_entry_range_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry
  unfold permInvRangeCapAt
  rw [hentry]
  rw [hsIn]
  rfl

/-- In a deterministic eager sponge base trace, a forward permutation input occurs at most once. -/
lemma spongeDetTrace_no_prior_permFwdInput_same_shared
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j j' : ℕ} {sIn : CanonicalSpongeState U}
    (hj' : j' < j)
    (hnow : permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sIn) :
    permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j' ≠ some sIn := by
  classical
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permFwdInputAt bt j = some sIn at hnow
  intro hprior
  change permFwdInputAt bt j' = some sIn at hprior
  obtain ⟨sOut, hentry⟩ := exists_getElem?_permFwd_of_permFwdInputAt
    (StmtIn := StmtIn) (U := U) hnow
  obtain ⟨sOut', hentry'⟩ := exists_getElem?_permFwd_of_permFwdInputAt
    (StmtIn := StmtIn) (U := U) hprior
  have hsOut := spongeDetTrace_permFwd_entry_output_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry
  have hsOut' := spongeDetTrace_permFwd_entry_output_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry'
  rw [hsOut] at hentry
  rw [hsOut'] at hentry'
  exact noRedundant_perm_pair_not_prior
    (StmtIn := StmtIn) (U := U) (bt := bt)
    (getBaseTrace_noRedundant (StmtIn := StmtIn) (U := U) _)
    hj' hentry (Or.inl hentry')

/-- In a deterministic eager sponge base trace, if position `j` is the forward query `x`, no
strictly earlier base position can be the inverse query to the current output `p x`. -/
lemma spongeDetTrace_no_prior_permBwdOutput_of_permFwdInput_shared
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j j' : ℕ} {sIn : CanonicalSpongeState U}
    (hj' : j' < j)
    (hnow : permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sIn) :
    permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j' ≠
      some ((show Equiv.Perm (CanonicalSpongeState U) from fam.2) sIn) := by
  classical
  let p : Equiv.Perm (CanonicalSpongeState U) :=
    (show Equiv.Perm (CanonicalSpongeState U) from fam.2)
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permFwdInputAt bt j = some sIn at hnow
  intro hprior
  change permBwdOutputAt bt j' = some (p sIn) at hprior
  obtain ⟨sOut, hentry⟩ := exists_getElem?_permFwd_of_permFwdInputAt
    (StmtIn := StmtIn) (U := U) hnow
  obtain ⟨sIn', hentry'⟩ := exists_getElem?_permBwd_of_permBwdOutputAt
    (StmtIn := StmtIn) (U := U) hprior
  have hsOut := spongeDetTrace_permFwd_entry_output_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry
  have hsIn' := spongeDetTrace_permBwd_entry_range_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry'
  have hsIn'eq : sIn' = sIn := by
    rw [hsIn']
    change p.symm (p sIn) = sIn
    rw [Equiv.symm_apply_apply]
  rw [hsOut] at hentry
  rw [hsIn'eq] at hentry'
  exact noRedundant_perm_pair_not_prior
    (StmtIn := StmtIn) (U := U) (bt := bt)
    (getBaseTrace_noRedundant (StmtIn := StmtIn) (U := U) _)
    hj' hentry (Or.inr hentry')

/-- In a deterministic eager sponge base trace, an inverse permutation queried output occurs at
most once. -/
lemma spongeDetTrace_no_prior_permBwdOutput_same_shared
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j j' : ℕ} {sOut : CanonicalSpongeState U}
    (hj' : j' < j)
    (hnow : permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sOut) :
    permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j' ≠ some sOut := by
  classical
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permBwdOutputAt bt j = some sOut at hnow
  intro hprior
  change permBwdOutputAt bt j' = some sOut at hprior
  obtain ⟨sIn, hentry⟩ := exists_getElem?_permBwd_of_permBwdOutputAt
    (StmtIn := StmtIn) (U := U) hnow
  obtain ⟨sIn', hentry'⟩ := exists_getElem?_permBwd_of_permBwdOutputAt
    (StmtIn := StmtIn) (U := U) hprior
  have hsIn := spongeDetTrace_permBwd_entry_range_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry
  have hsIn' := spongeDetTrace_permBwd_entry_range_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry'
  rw [hsIn] at hentry
  rw [hsIn'] at hentry'
  exact noRedundant_perm_inv_pair_not_prior
    (StmtIn := StmtIn) (U := U) (bt := bt)
    (getBaseTrace_noRedundant (StmtIn := StmtIn) (U := U) _)
    hj' hentry (Or.inl hentry')

/-- In a deterministic eager sponge base trace, if position `j` is the inverse query `y`, no
strictly earlier base position can be the forward query to the current preimage `p⁻¹ y`. -/
lemma spongeDetTrace_no_prior_permFwdInput_of_permBwdOutput_shared
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j j' : ℕ} {sOut : CanonicalSpongeState U}
    (hj' : j' < j)
    (hnow : permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sOut) :
    permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j' ≠
      some ((show Equiv.Perm (CanonicalSpongeState U) from fam.2).symm sOut) := by
  classical
  let p : Equiv.Perm (CanonicalSpongeState U) :=
    (show Equiv.Perm (CanonicalSpongeState U) from fam.2)
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permBwdOutputAt bt j = some sOut at hnow
  intro hprior
  change permFwdInputAt bt j' = some (p.symm sOut) at hprior
  obtain ⟨sIn, hentry⟩ := exists_getElem?_permBwd_of_permBwdOutputAt
    (StmtIn := StmtIn) (U := U) hnow
  obtain ⟨sOut', hentry'⟩ := exists_getElem?_permFwd_of_permFwdInputAt
    (StmtIn := StmtIn) (U := U) hprior
  have hsIn := spongeDetTrace_permBwd_entry_range_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry
  have hsOut' := spongeDetTrace_permFwd_entry_output_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
    (U := U) (δ := δ) V maliciousProver fam hentry'
  have hsOut'eq : sOut' = sOut := by
    rw [hsOut']
    change p (p.symm sOut) = sOut
    rw [Equiv.apply_symm_apply]
  rw [hsIn] at hentry
  rw [hsOut'eq] at hentry'
  exact noRedundant_perm_inv_pair_not_prior
    (StmtIn := StmtIn) (U := U) (bt := bt)
    (getBaseTrace_noRedundant (StmtIn := StmtIn) (U := U) _)
    hj' hentry (Or.inr hentry')

/-- The image of the forward representative at base index `j` is not among the range-side
states exposed by strict earlier representatives.  This is the full-state (rather than merely
capacity) freshness fact needed before applying the no-replacement permutation argument. -/
lemma spongeDetTrace_permFwd_image_not_mem_exposedRange
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j : ℕ} {sIn : CanonicalSpongeState U}
    (hnow : permFwdInputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sIn) :
    (show Equiv.Perm (CanonicalSpongeState U) from fam.2) sIn ∉
      permExposedRangeFinset (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j := by
  classical
  let p : Equiv.Perm (CanonicalSpongeState U) :=
    (show Equiv.Perm (CanonicalSpongeState U) from fam.2)
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permFwdInputAt bt j = some sIn at hnow
  change p sIn ∉ permExposedRangeFinset bt j
  intro hmem
  obtain ⟨i, hi, hrange⟩ :=
    (mem_permExposedRangeFinset_iff (StmtIn := StmtIn) (U := U) (bt := bt) (j := j)).mp hmem
  unfold permRangeStateAt at hrange
  cases hentry : bt[i]? with
  | none =>
      rw [hentry] at hrange
      simp only [Option.bind_none, reduceCtorEq] at hrange
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hentry] at hrange
          simp only [Option.bind_some, reduceCtorEq] at hrange
      | inr permDom =>
          cases permDom with
          | inl sIn' =>
              rw [hentry] at hrange
              simp only [Option.bind_some, Option.some.injEq] at hrange
              have hsOut := spongeDetTrace_permFwd_entry_output_eq
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hentry
              have hsIn' : sIn' = sIn := by
                apply p.injective
                rw [← hsOut, hrange]
              have hprior : permFwdInputAt bt i = some sIn := by
                unfold permFwdInputAt
                rw [hentry, hsIn']
                rfl
              exact (spongeDetTrace_no_prior_permFwdInput_same_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hi hnow) hprior
          | inr sOut =>
              rw [hentry] at hrange
              simp only [Option.bind_some, Option.some.injEq] at hrange
              have hprior : permBwdOutputAt bt i = some (p sIn) := by
                unfold permBwdOutputAt
                rw [hentry, hrange]
                rfl
              exact (spongeDetTrace_no_prior_permBwdOutput_of_permFwdInput_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hi hnow) hprior

/-- The preimage of the inverse representative at base index `j` is not among the domain-side
states exposed by strict earlier representatives.  This is the inverse counterpart of
`spongeDetTrace_permFwd_image_not_mem_exposedRange`. -/
lemma spongeDetTrace_permBwd_preimage_not_mem_exposedDomain
    [Fintype U]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {j : ℕ} {sOut : CanonicalSpongeState U}
    (hnow : permBwdOutputAt (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j = some sOut) :
    (show Equiv.Perm (CanonicalSpongeState U) from fam.2).symm sOut ∉
      permExposedDomainFinset (getBaseTrace
        ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).1 ++
         (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
          (δ := δ) V maliciousProver fam).2)) j := by
  classical
  let p : Equiv.Perm (CanonicalSpongeState U) :=
    (show Equiv.Perm (CanonicalSpongeState U) from fam.2)
  let bt : QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
    getBaseTrace
      ((spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).1 ++
       (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
        (δ := δ) V maliciousProver fam).2)
  change permBwdOutputAt bt j = some sOut at hnow
  change p.symm sOut ∉ permExposedDomainFinset bt j
  intro hmem
  obtain ⟨i, hi, hdomain⟩ :=
    (mem_permExposedDomainFinset_iff (StmtIn := StmtIn) (U := U) (bt := bt) (j := j)).mp hmem
  unfold permDomainStateAt at hdomain
  cases hentry : bt[i]? with
  | none =>
      rw [hentry] at hdomain
      simp only [Option.bind_none, reduceCtorEq] at hdomain
  | some entry =>
      rcases entry with ⟨dom, rng⟩
      cases dom with
      | inl stmt =>
          rw [hentry] at hdomain
          simp only [Option.bind_some, reduceCtorEq] at hdomain
      | inr permDom =>
          cases permDom with
          | inl sIn =>
              rw [hentry] at hdomain
              simp only [Option.bind_some, Option.some.injEq] at hdomain
              have hprior : permFwdInputAt bt i = some (p.symm sOut) := by
                unfold permFwdInputAt
                rw [hentry, hdomain]
                rfl
              exact (spongeDetTrace_no_prior_permFwdInput_of_permBwdOutput_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hi hnow) hprior
          | inr sOut' =>
              rw [hentry] at hdomain
              simp only [Option.bind_some, Option.some.injEq] at hdomain
              have hsIn := spongeDetTrace_permBwd_entry_range_eq
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hentry
              have hsOut' : sOut' = sOut := by
                apply p.injective
                rw [← Equiv.apply_symm_apply p sOut', ← hsIn, hdomain,
                  Equiv.apply_symm_apply]
              have hprior : permBwdOutputAt bt i = some sOut := by
                unfold permBwdOutputAt
                rw [hentry, hsOut']
                rfl
              exact (spongeDetTrace_no_prior_permBwdOutput_same_shared
                (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
                (U := U) (δ := δ) V maliciousProver fam hi hnow) hprior

end DeterministicPermutationTrace

section PermutationSwapAnswers

/-- The four narrow sponge domains whose eager answers may change after the forward-image swap
`p' = p ∘ swap (p x) y'`. -/
def permFwdSwapAffected
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U) :
    (duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inl _ => false
  | .inr (.inl s) => decide (s = x ∨ s = p.symm y')
  | .inr (.inr y) => decide (y = p x ∨ y = y')

/-- The four narrow sponge domains whose eager answers may change after the inverse-image swap
`p' = swap (p⁻¹ y) x' ∘ p`. -/
def permBwdSwapAffected
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U) :
    (duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inl _ => false
  | .inr (.inl s) => decide (s = p.symm y ∨ s = x')
  | .inr (.inr z) => decide (z = y ∨ z = p x')

/-- Forward-image swap support for eager sponge answers.

If `p' = p ∘ swap (p x) y'`, then `spongeAnswer` can differ from the original family only on
four permutation oracle domains: forward `x`, forward `p⁻¹ y'`, inverse `p x`, and inverse `y'`.
This is the precise affected-domain set needed for the random-permutation deferred-decision
argument; a one-domain invariant is too strong for permutations. -/
lemma spongeAnswer_fwdSwap_eq_of_not_affected
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U)
    (dom : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hnotFx : dom ≠ .inr (.inl x))
    (hnotFy : dom ≠ .inr (.inl (p.symm y')))
    (hnotBx : dom ≠ .inr (.inr (p x)))
    (hnotBy : dom ≠ .inr (.inr y')) :
    spongeAnswer
        ((h, p.trans (Equiv.swap (p x) y')) : (D_𝔖 StmtIn U).Carrier) dom =
      spongeAnswer ((h, p) : (D_𝔖 StmtIn U).Carrier) dom := by
  classical
  cases dom with
  | inl q =>
      rfl
  | inr permDom =>
      cases permDom with
      | inl s =>
          change (p.trans (Equiv.swap (p x) y')) s = p s
          have hsx : s ≠ x := by
            intro hs
            apply hnotFx
            rw [hs]
          have hsy : s ≠ p.symm y' := by
            intro hs
            apply hnotFy
            rw [hs]
          have hpsx : p s ≠ p x := by
            intro hpEq
            exact hsx (p.injective hpEq)
          have hpsy : p s ≠ y' := by
            intro hpEq
            apply hsy
            rw [← hpEq]
            exact (Equiv.symm_apply_apply p s).symm
          rw [Equiv.trans_apply]
          exact Equiv.swap_apply_of_ne_of_ne hpsx hpsy
      | inr y =>
          change (p.trans (Equiv.swap (p x) y')).symm y = p.symm y
          have hyx : y ≠ p x := by
            intro hy
            apply hnotBx
            rw [hy]
          have hyy : y ≠ y' := by
            intro hy
            apply hnotBy
            rw [hy]
          rw [Equiv.symm_trans_apply]
          change p.symm ((Equiv.swap (p x) y') y) = p.symm y
          rw [Equiv.swap_apply_of_ne_of_ne hyx hyy]

/-- Inverse-image swap support for eager sponge answers.

If `p' = swap (p⁻¹ y) x' ∘ p`, then `spongeAnswer` can differ from the original family only on
forward `p⁻¹ y`, forward `x'`, inverse `y`, and inverse `p x'`. -/
lemma spongeAnswer_bwdSwap_eq_of_not_affected
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U)
    (dom : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hnotFx : dom ≠ .inr (.inl (p.symm y)))
    (hnotFy : dom ≠ .inr (.inl x'))
    (hnotBy : dom ≠ .inr (.inr y))
    (hnotBx : dom ≠ .inr (.inr (p x'))) :
    spongeAnswer
        ((h, (Equiv.swap (p.symm y) x').trans p) : (D_𝔖 StmtIn U).Carrier) dom =
      spongeAnswer ((h, p) : (D_𝔖 StmtIn U).Carrier) dom := by
  classical
  cases dom with
  | inl q =>
      rfl
  | inr permDom =>
      cases permDom with
      | inl s =>
          change ((Equiv.swap (p.symm y) x').trans p) s = p s
          have hsx : s ≠ p.symm y := by
            intro hs
            apply hnotFx
            rw [hs]
          have hsy : s ≠ x' := by
            intro hs
            apply hnotFy
            rw [hs]
          rw [Equiv.trans_apply]
          rw [Equiv.swap_apply_of_ne_of_ne hsx hsy]
      | inr z =>
          change ((Equiv.swap (p.symm y) x').trans p).symm z = p.symm z
          have hzy : z ≠ y := by
            intro hz
            apply hnotBy
            rw [hz]
          have hzx : z ≠ p x' := by
            intro hz
            apply hnotBx
            rw [hz]
          rw [Equiv.symm_trans_apply]
          have hpx_ne_preY : p.symm z ≠ p.symm y := by
            intro hpre
            apply hzy
            exact p.symm.injective hpre
          have hpx_ne_x' : p.symm z ≠ x' := by
            intro hpre
            apply hzx
            rw [← hpre]
            exact (Equiv.apply_symm_apply p z).symm
          change (Equiv.swap (p.symm y) x') (p.symm z) = p.symm z
          rw [Equiv.swap_apply_of_ne_of_ne hpx_ne_preY hpx_ne_x']

/-- Boolean-affected-set form of `spongeAnswer_fwdSwap_eq_of_not_affected`, ready for the
`takeWhile` prefix-causality lemmas. -/
lemma spongeAnswer_fwdSwap_eq_of_affected_false
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U)
    (dom : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hbad : permFwdSwapAffected (StmtIn := StmtIn) p x y' dom = false) :
    spongeAnswer
        ((h, p.trans (Equiv.swap (p x) y')) : (D_𝔖 StmtIn U).Carrier) dom =
      spongeAnswer ((h, p) : (D_𝔖 StmtIn U).Carrier) dom := by
  classical
  cases dom with
  | inl q =>
      rfl
  | inr permDom =>
      cases permDom with
      | inl s =>
          have hs : ¬ (s = x ∨ s = p.symm y') := by
            unfold permFwdSwapAffected at hbad
            exact of_decide_eq_false hbad
          exact spongeAnswer_fwdSwap_eq_of_not_affected
            (StmtIn := StmtIn) (U := U) h p x y' (.inr (.inl s))
            (by intro hEq; exact hs (Or.inl (by cases hEq; rfl)))
            (by intro hEq; exact hs (Or.inr (by cases hEq; rfl)))
            (by intro hEq; cases Sum.inr.inj hEq)
            (by intro hEq; cases Sum.inr.inj hEq)
      | inr z =>
          have hz : ¬ (z = p x ∨ z = y') := by
            unfold permFwdSwapAffected at hbad
            exact of_decide_eq_false hbad
          exact spongeAnswer_fwdSwap_eq_of_not_affected
            (StmtIn := StmtIn) (U := U) h p x y' (.inr (.inr z))
            (by intro hEq; cases Sum.inr.inj hEq)
            (by intro hEq; cases Sum.inr.inj hEq)
            (by intro hEq; exact hz (Or.inl (Sum.inr.inj (Sum.inr.inj hEq))))
            (by intro hEq; exact hz (Or.inr (Sum.inr.inj (Sum.inr.inj hEq))))

/-- Boolean-affected-set form of `spongeAnswer_bwdSwap_eq_of_not_affected`, ready for the
`takeWhile` prefix-causality lemmas. -/
lemma spongeAnswer_bwdSwap_eq_of_affected_false
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U)
    (dom : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hbad : permBwdSwapAffected (StmtIn := StmtIn) p y x' dom = false) :
    spongeAnswer
        ((h, (Equiv.swap (p.symm y) x').trans p) : (D_𝔖 StmtIn U).Carrier) dom =
      spongeAnswer ((h, p) : (D_𝔖 StmtIn U).Carrier) dom := by
  classical
  cases dom with
  | inl q =>
      rfl
  | inr permDom =>
      cases permDom with
      | inl s =>
          have hs : ¬ (s = p.symm y ∨ s = x') := by
            unfold permBwdSwapAffected at hbad
            exact of_decide_eq_false hbad
          exact spongeAnswer_bwdSwap_eq_of_not_affected
            (StmtIn := StmtIn) (U := U) h p y x' (.inr (.inl s))
            (by intro hEq; exact hs (Or.inl (by cases hEq; rfl)))
            (by intro hEq; exact hs (Or.inr (by cases hEq; rfl)))
            (by intro hEq; cases Sum.inr.inj hEq)
            (by intro hEq; cases Sum.inr.inj hEq)
      | inr z =>
          have hz : ¬ (z = y ∨ z = p x') := by
            unfold permBwdSwapAffected at hbad
            exact of_decide_eq_false hbad
          exact spongeAnswer_bwdSwap_eq_of_not_affected
            (StmtIn := StmtIn) (U := U) h p y x' (.inr (.inr z))
            (by intro hEq; cases Sum.inr.inj hEq)
            (by intro hEq; cases Sum.inr.inj hEq)
            (by intro hEq; exact hz (Or.inl (Sum.inr.inj (Sum.inr.inj hEq))))
            (by intro hEq; exact hz (Or.inr (Sum.inr.inj (Sum.inr.inj hEq))))

end PermutationSwapAnswers

section PermutationSwapPrefixCausality

/-- Forward-swap first-affected-domain synchronization for deterministic eager sponge traces. -/
lemma spongeDetTrace_append_first_bad_domain_fwdSwapAffected_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (x y' : CanonicalSpongeState U) :
    let fam₁ : (D_𝔖 StmtIn U).Carrier := (h, p.trans (Equiv.swap (p x) y'))
    let fam₀ : (D_𝔖 StmtIn U).Carrier := (h, p)
    let bad := permFwdSwapAffected (StmtIn := StmtIn) p x y'
    let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
    let raw₁ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).2
    let raw₀ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₀).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₀).2
    List.takeWhile good raw₁ = List.takeWhile good raw₀ ∧
      ((List.takeWhile good raw₁).length < raw₁.length ↔
        (List.takeWhile good raw₀).length < raw₀.length) ∧
      (∀ (h₁ : (List.takeWhile good raw₁).length < raw₁.length)
          (h₀ : (List.takeWhile good raw₀).length < raw₀.length),
        raw₁[(List.takeWhile good raw₁).length].1 =
          raw₀[(List.takeWhile good raw₀).length].1) := by
  classical
  let fam₁ : (D_𝔖 StmtIn U).Carrier := (h, p.trans (Equiv.swap (p x) y'))
  let fam₀ : (D_𝔖 StmtIn U).Carrier := (h, p)
  let bad := permFwdSwapAffected (StmtIn := StmtIn) p x y'
  exact spongeDetTrace_append_first_bad_domain_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
    V maliciousProver fam₁ fam₀ bad (by
      intro dom hbad
      exact spongeAnswer_fwdSwap_eq_of_affected_false
        (StmtIn := StmtIn) (U := U) h p x y' dom hbad)

/-- Inverse-swap first-affected-domain synchronization for deterministic eager sponge traces. -/
lemma spongeDetTrace_append_first_bad_domain_bwdSwapAffected_eq
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (h : StmtIn → Vector U SpongeSize.C)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (y x' : CanonicalSpongeState U) :
    let fam₁ : (D_𝔖 StmtIn U).Carrier := (h, (Equiv.swap (p.symm y) x').trans p)
    let fam₀ : (D_𝔖 StmtIn U).Carrier := (h, p)
    let bad := permBwdSwapAffected (StmtIn := StmtIn) p y x'
    let good := eagerDetNarrowEntryGood (StmtIn := StmtIn) (U := U) bad
    let raw₁ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₁).2
    let raw₀ :=
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₀).1 ++
      (spongeDetTrace (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) (δ := δ) V maliciousProver fam₀).2
    List.takeWhile good raw₁ = List.takeWhile good raw₀ ∧
      ((List.takeWhile good raw₁).length < raw₁.length ↔
        (List.takeWhile good raw₀).length < raw₀.length) ∧
      (∀ (h₁ : (List.takeWhile good raw₁).length < raw₁.length)
          (h₀ : (List.takeWhile good raw₀).length < raw₀.length),
        raw₁[(List.takeWhile good raw₁).length].1 =
          raw₀[(List.takeWhile good raw₀).length].1) := by
  classical
  let fam₁ : (D_𝔖 StmtIn U).Carrier := (h, (Equiv.swap (p.symm y) x').trans p)
  let fam₀ : (D_𝔖 StmtIn U).Carrier := (h, p)
  let bad := permBwdSwapAffected (StmtIn := StmtIn) p y x'
  exact spongeDetTrace_append_first_bad_domain_eq
    (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
    V maliciousProver fam₁ fam₀ bad (by
      intro dom hbad
      exact spongeAnswer_bwdSwap_eq_of_affected_false
        (StmtIn := StmtIn) (U := U) h p y x' dom hbad)

end PermutationSwapPrefixCausality

end BadEventDS

end DuplexSpongeFS

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PrefixUpdateNoAbort
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SpongeTrace
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.SecurityGames
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SMonitoredState
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.AbortAnalysis
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Statement.ConcreteHybrids

/-!
# H₀ prefix-normalization bridge

This is the executable part of the H₀ side of Claim 5.21.  A fixed sampled sponge family answers
all hash, forward-permutation, and inverse-permutation calls consistently.  Therefore the revised
offline `PrefixUpdate` never stops on its raw trace.  This fact is deliberately separate from the
first-bad-event bound: hash functionality is oracle semantics and is not encoded by `E`.
-/

namespace DuplexSpongeFS.BadEventDS

open OracleSpec

open DuplexSpongeFS DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [VCVCompatible U] [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- A raw trace whose answers come from one fixed sampled sponge family has a completed revised
`PrefixUpdate` table.  In particular, H₀'s `StdTrace` cannot fail merely because its table fold
sees an earlier equal hash/permutation query; only the subsequent explicit bad-event monitor is
responsible for the first-stop charge. -/
theorem prefixUpdateTrace_some_of_spongeConsistent
    (fam : (D_𝔖 StmtIn U).Carrier)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hConsistent : ∀ entry ∈ trace, entry.2 = spongeAnswer fam entry.1) :
    ∃ trDelta : TraceNabla T_H T_P StmtIn U,
      ProverTransform.prefixUpdateTrace trace = some trDelta := by
  let p : Equiv.Perm (CanonicalSpongeState U) := fam.2
  apply ProverTransform.prefixUpdateTrace_some_of_agrees
    (hashAnswer := fam.1) (permAnswer := p) (permInvAnswer := p.symm)
    p.injective (fun stateOut => p.apply_symm_apply stateOut) trace
  intro entry hEntry
  rcases entry with ⟨query, answer⟩
  cases query with
  | inl stmt =>
      exact hConsistent ⟨.inl stmt, answer⟩ hEntry
  | inr permutationQuery =>
      cases permutationQuery with
      | inl stateIn =>
          exact hConsistent ⟨.inr (.inl stateIn), answer⟩ hEntry
      | inr stateOut =>
          exact hConsistent ⟨.inr (.inr stateOut), answer⟩ hEntry

end DuplexSpongeFS.BadEventDS

/-! ### Actual Hyb₀ source normalization

The preceding generic theorem is useful only once it is connected to an *actual* H₀ source
execution.  The following support invariant makes that connection.  It is intentionally about the
pre-`D2STrace` source log: a fixed sampled sponge family answers every duplex query in both the
prover and verifier logs, while ambient queries are discarded by `dsTraceOfLog`.  Consequently
the complete source trace admits `PrefixUpdate`; on an `E`-good prefix it also yields the genuine
reusable `D2SNormalState` used by the revised online handlers.

This is a normalization bridge, not the H₀/H₁ coupling itself.  In particular, it does not claim
that the later strict-prefix replay, Backtrack, or LookAhead calls have succeeded.  Those are the
remaining whole-loop obligations for Claim 5.21.
-/

namespace DuplexSpongeFS.KeyLemma

open OracleComp OracleSpec ProtocolSpec

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [CodecCore pSpec U]
  {δ : Nat} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Uniformly simulating the private `Unit →ₒ U` sampler cannot manufacture a return value that
was not already possible in the underlying `UnitSampleM` computation.  We use precisely this
support projection below to transfer the concrete H₀ `D2STrace` no-abort fact through its actual
line-4 random-fibre interpreter. -/
private theorem support_simulateQ_d2sUnit_subset
    {U α : Type} [SpongeUnit U] [SampleableType U]
    (oa : OracleComp (Unit →ₒ U) α) :
    support (simulateQ (d2sUnitSampleImpl (U := U)) oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind query next ih =>
      intro x hx
      rw [simulateQ_query_bind, support_bind] at hx
      rw [support_bind]
      simp only [Set.mem_iUnion, exists_prop] at hx ⊢
      obtain ⟨answer, _hAnswer, hx⟩ := hx
      exact ⟨answer, mem_support_query query answer, ih answer hx⟩

/-- The duplex portion of a log produced by H₀ is consistent with its single sampled sponge
family.  Ambient-oracle entries do not occur in this predicate because `dsTraceOfLog` removes
them before the offline replay starts. -/
abbrev Hyb0LogConsistent (fam : (D_𝔖 StmtIn U).Carrier)
    (log : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ entry ∈ TraceTransform.dsTraceOfLog log,
    entry.2 = BadEventDS.spongeAnswer fam entry.1

private lemma hyb0_ds_run_eq
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (fam : (D_𝔖 StmtIn U).Carrier)
    (query : (duplexSpongeChallengeOracle StmtIn U).Domain) :
    (hyb0Impl oSpecImpl (.inr query)).run fam =
      pure (BadEventDS.spongeAnswer fam query, fam) := by
  rcases query with query | (query | query) <;> rfl

private lemma hyb0_query_preserves_family
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (fam : (D_𝔖 StmtIn U).Carrier)
    (query : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    {out : (oSpec + duplexSpongeChallengeOracle StmtIn U).Range query ×
      (D_𝔖 StmtIn U).Carrier}
    (hOut : out ∈ support ((hyb0Impl oSpecImpl query).run fam)) :
    out.2 = fam := by
  cases query with
  | inl query =>
      simp [hyb0Impl] at hOut
      rcases hOut with ⟨answer, _hAnswer, rfl⟩
      rfl
  | inr query =>
      rw [hyb0_ds_run_eq] at hOut
      have hEq : out = (BadEventDS.spongeAnswer fam query, fam) := by
        simpa using hOut
      exact congrArg Prod.snd hEq

/-- Running any oracle computation under the actual fixed-family H₀ implementation preserves the
family and records only its deterministic duplex answers. -/
lemma hyb0_logged_run_consistent {α : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {result : (α × QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) ×
      (D_𝔖 StmtIn U).Carrier}
    (hResult : result ∈ support
      ((simulateQ (hyb0Impl oSpecImpl) ((simulateQ loggingOracle oa).run)).run fam)) :
    result.2 = fam ∧ Hyb0LogConsistent fam result.1.2 := by
  revert result
  induction oa using OracleComp.inductionOn with
  | pure value =>
      intro result hResult
      have hEq : result = ((value, []), fam) := by simpa using hResult
      subst result
      constructor
      · rfl
      · intro entry hEntry
        simp [TraceTransform.dsTraceOfLog] at hEntry
  | query_bind query next ih =>
      intro result hResult
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind,
        simulateQ_bind, StateT.run_bind, support_bind] at hResult
      rcases Set.mem_iUnion.mp hResult with ⟨queryResult, hQueryResult⟩
      rcases Set.mem_iUnion.mp hQueryResult with ⟨hQueryResult, hResult⟩
      have hQueryResult' : queryResult ∈ support ((hyb0Impl oSpecImpl query).run fam) := by
        simpa only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          Functor.map_id] using hQueryResult
      have hState : queryResult.2 = fam :=
        hyb0_query_preserves_family oSpecImpl fam query hQueryResult'
      rw [hState] at hResult
      rw [simulateQ_map, StateT.run_map, support_map] at hResult
      rcases hResult with ⟨continuationResult, hContinuation, hResultEq⟩
      have hIH := ih queryResult.1 hContinuation
      rw [← hResultEq]
      constructor
      · change continuationResult.2 = fam
        exact hIH.1
      · change Hyb0LogConsistent fam (⟨query, queryResult.1⟩ :: continuationResult.1.2)
        cases query with
        | inl query =>
            simpa [Hyb0LogConsistent, TraceTransform.dsTraceOfLog] using hIH.2
        | inr query =>
            rw [hyb0_ds_run_eq] at hQueryResult'
            have hEq : queryResult = (BadEventDS.spongeAnswer fam query, fam) := by
              simpa using hQueryResult'
            have hAnswer : queryResult.1 = BadEventDS.spongeAnswer fam query :=
              congrArg Prod.fst hEq
            simpa [Hyb0LogConsistent, TraceTransform.dsTraceOfLog, hAnswer] using hIH.2

/-- A successful support point of the real H₀ source game has one fixed-family-consistent raw
duplex trace.  This joins the separately logged prover and verifier computations before any
offline transformation takes place. -/
theorem dsfsGame_hyb0_source_consistent_of_support
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {source : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)}
    {state : (D_𝔖 StmtIn U).Carrier}
    (hSource : (some source, state) ∈ support
      ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver).run).run fam)) :
    state = fam ∧ Hyb0LogConsistent fam (TaggedQueryLog.untagged source.2.2.2) := by
  unfold dsfsGame at hSource
  vcv_norm at hSource
  simp only [StateT.run_bind, StateT.run_pure] at hSource
  rw [support_bind] at hSource
  rcases Set.mem_iUnion.mp hSource with ⟨proverRun, hProverRun⟩
  rcases Set.mem_iUnion.mp hProverRun with ⟨hProverRun, hSource⟩
  rcases proverRun with ⟨proverData, proverState⟩
  rw [support_bind] at hSource
  rcases Set.mem_iUnion.mp hSource with ⟨verifierRun, hVerifierRun⟩
  rcases Set.mem_iUnion.mp hVerifierRun with ⟨hVerifierRun, hSource⟩
  have hProver := hyb0_logged_run_consistent oSpecImpl maliciousProver fam hProverRun
  have hProverState : proverState = fam := by simpa using hProver.1
  have hProverLog : Hyb0LogConsistent fam proverData.2 := by simpa using hProver.2
  subst proverState
  have hVerifier := hyb0_logged_run_consistent oSpecImpl
    (runForwardVerifierWide δ verifier proverData.1.1 proverData.1.2) fam hVerifierRun
  rcases verifierRun with ⟨⟨stmtOut?, verifierLog⟩, verifierState⟩
  cases stmtOut? with
  | none =>
      have hImpossible : (some source, state) = (none, verifierState) := by
        simpa using hSource
      injection hImpossible with hFalse _
      cases hFalse
  | some stmtOut =>
      have hEq : (some source, state) =
          (some ⟨proverData.1.1, stmtOut, proverData.1.2,
            proverData.2.map (fun entry => (SourceTag.prover, entry)) ++
              verifierLog.map (fun entry => (SourceTag.verifier, entry))⟩, verifierState) := by
        simpa using hSource
      injection hEq with hTaggedSource hState
      have hTaggedSource' := Option.some.inj hTaggedSource
      subst source
      subst state
      constructor
      · exact hVerifier.1
      · intro entry hEntry
        simp only [TaggedQueryLog.untagged, List.map_append, TraceTransform.dsTraceOfLog,
          List.filterMap_append, List.mem_append] at hEntry
        rcases hEntry with hEntry | hEntry
        · apply hProverLog entry
          simpa [TaggedQueryLog.untagged, TraceTransform.dsTraceOfLog] using hEntry
        · apply hVerifier.2 entry
          simpa [TaggedQueryLog.untagged, TraceTransform.dsTraceOfLog] using hEntry

/-- The actual H₀ source trace never causes the complete normalized-table fold to fail. -/
theorem dsfsGame_hyb0_source_prefixUpdate_of_support
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {source : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)}
    {state : (D_𝔖 StmtIn U).Carrier}
    (hSource : (some source, state) ∈ support
      ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver).run).run fam)) :
    state = fam ∧ ∃ trDelta : TraceNabla T_H T_P StmtIn U,
      prefixUpdateTrace (TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2)) =
        some trDelta := by
  have hConsistent := dsfsGame_hyb0_source_consistent_of_support
    oSpecImpl verifier maliciousProver fam hSource
  refine ⟨hConsistent.1, ?_⟩
  exact BadEventDS.prefixUpdateTrace_some_of_spongeConsistent fam _ hConsistent.2

/-- Before the first monitored bad event, the real H₀ source trace constructs the exact reusable
normal state expected by revised `D2SQuery`.  This is the concrete table/trace half of the H₀
side of Claim 5.21; the remaining replay-loop and lazy-coupling construction is deliberately not
hidden in this theorem. -/
theorem dsfsGame_hyb0_source_normalState_of_support
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {source : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)}
    {state : (D_𝔖 StmtIn U).Carrier}
    (hSource : (some source, state) ∈ support
      ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver).run).run fam))
    (hGood : ¬ BadEventDS.E
      (TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2))) :
    ∃ normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
      normal.state.trace =
        TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2) := by
  rcases dsfsGame_hyb0_source_prefixUpdate_of_support
    (T_H := T_H) (T_P := T_P) oSpecImpl verifier maliciousProver fam hSource with
    ⟨_hState, trDelta, hUpdate⟩
  refine ⟨D2SNormalState.ofPrefixUpdate _ trDelta hUpdate hGood, rfl⟩

/-- Every strict raw prefix used by the live H₀ offline replay inherits both pieces of the
normal-state invariant from the one sampled sponge family: `PrefixUpdate` is total on the prefix,
and a bad prefix would already be a bad complete source trace.  This is the exact bridge needed
at a `StdTrace` forward occurrence, where Backtrack receives the strict prefix rather than the
complete table. -/
theorem hyb0_normalState_of_consistent_prefix
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (fam : (D_𝔖 StmtIn U).Carrier)
    (trace processed : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hPrefix : processed <+: trace)
    (hConsistent : ∀ entry ∈ trace,
      entry.2 = BadEventDS.spongeAnswer fam entry.1)
    (hGood : ¬ BadEventDS.E trace) :
    ∃ normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
      normal.state.trace = processed := by
  have hProcessedConsistent : ∀ entry ∈ processed,
      entry.2 = BadEventDS.spongeAnswer fam entry.1 := by
    intro entry hEntry
    exact hConsistent entry (hPrefix.sublist.subset hEntry)
  have hUpdate : ∃ trDelta : TraceNabla T_H T_P StmtIn U,
      prefixUpdateTrace processed = some trDelta :=
    BadEventDS.prefixUpdateTrace_some_of_spongeConsistent fam processed hProcessedConsistent
  have hGoodPrefix : ¬ BadEventDS.E processed := by
    intro hBad
    exact hGood (BadEventDS.E_mono_of_raw_prefix hPrefix hBad)
  rcases hUpdate with ⟨trDelta, hUpdate⟩
  exact ⟨D2SNormalState.ofPrefixUpdate processed trDelta hUpdate hGoodPrefix, rfl⟩

/-- The immediately usable no-hidden-abort consequence for a live H₀ replay prefix.  This is not
an extra Backtrack assumption: the returned normal state is built from that very strict prefix,
and Claim 5.19 then rules out exactly the `.err` branch taken by `stdTraceHandlePQuery`.

The remaining `.noResult` outcome is intentionally allowed here; Algorithm 5.5 treats it as the
ordinary no-ancestor branch and continues its replay. -/
theorem hyb0_prefix_backTrack_noAbort
    [HasMessageSize pSpec] [HasChallengeSize pSpec]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (fam : (D_𝔖 StmtIn U).Carrier)
    (trace processed : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hPrefix : processed <+: trace)
    (hConsistent : ∀ entry ∈ trace,
      entry.2 = BadEventDS.spongeAnswer fam entry.1)
    (hGood : ¬ BadEventDS.E trace) :
    ∃ normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
      normal.state.trace = processed ∧
        ∀ state : CanonicalSpongeState U,
          Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
            normal.state.trace normal.state.trΔ normal.state.h_inv state ≠ .err := by
  rcases hyb0_normalState_of_consistent_prefix
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (T_H := T_H) (T_P := T_P) fam trace processed hPrefix hConsistent hGood with
    ⟨normal, hTrace⟩
  refine ⟨normal, hTrace, ?_⟩
  intro state
  exact AbortAnalysis.claim_5_19_backTrack_noAbort normal state

/-- Concrete H₀ form of `hyb0_prefix_backTrack_noAbort`.  It starts from an actual support point
of the eager ideal-sponge source game, not from a caller-supplied trace: each strict replay prefix
of that source has a real normalized table and cannot take Backtrack's non-monitor `.err` branch.
This is the first executable half of the H₀/H₁ no-hidden-abort bridge. -/
theorem dsfsGame_hyb0_source_prefix_backTrack_noAbort_of_support
    [HasMessageSize pSpec] [HasChallengeSize pSpec]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {source : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)}
    {state : (D_𝔖 StmtIn U).Carrier}
    (hSource : (some source, state) ∈ support
      ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver).run).run fam))
    (processed : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hPrefix : processed <+: TraceTransform.dsTraceOfLog
      (TaggedQueryLog.untagged source.2.2.2))
    (hGood : ¬ BadEventDS.E (TraceTransform.dsTraceOfLog
      (TaggedQueryLog.untagged source.2.2.2))) :
    ∃ normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
      normal.state.trace = processed ∧
        ∀ state : CanonicalSpongeState U,
          Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
            normal.state.trace normal.state.trΔ normal.state.h_inv state ≠ .err := by
  have hConsistent := dsfsGame_hyb0_source_consistent_of_support
    oSpecImpl verifier maliciousProver fam hSource
  exact hyb0_prefix_backTrack_noAbort
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
    fam _ processed hPrefix hConsistent.2 hGood

/-- A genuine H₀ source execution cannot make the live corrected `StdTrace`/`D2STrace` pipeline
fail before the explicit monitor.  The proof is an end-to-end refinement of the executable loop:
the sampled ideal sponge makes every strict `PrefixUpdate` total; its `E`-good complete trace
makes Backtrack error-free; and the complete normalized table supplies the forward witness that
makes each invoked LookAhead return an encoded challenge.

This is the delivery bridge for Claim 5.21.  It is intentionally stated about the actual support
of `d2sTraceSaltedObserved.run`, so the forthcoming H₀/H₁ coupling can consume it directly rather
than re-implementing an abstract replay. -/
theorem dsfsGame_hyb0_source_d2sTraceSaltedObserved_none_not_mem_support
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {source : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)}
    {state : (D_𝔖 StmtIn U).Carrier}
    (hSource : (some source, state) ∈ support
      ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver).run).run fam))
    (hGood : ¬ BadEventDS.E
      (TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2))) :
    none ∉ support
      (TraceTransform.d2sTraceSaltedObserved (T_H := T_H) (T_P := T_P)
        (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) source.2.2.2).run := by
  let raw := TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2)
  have hConsistent := dsfsGame_hyb0_source_consistent_of_support
    oSpecImpl verifier maliciousProver fam hSource
  have hFullUpdate : ∃ fullTrΔ : TraceNabla T_H T_P StmtIn U,
      ProverTransform.prefixUpdateTrace raw = some fullTrΔ := by
    apply BadEventDS.prefixUpdateTrace_some_of_spongeConsistent fam raw
    intro entry hEntry
    exact hConsistent.2 entry hEntry
  obtain ⟨fullTrΔ, hFullUpdate⟩ := hFullUpdate
  have hFullGood : ¬ BadEventDS.E raw := by
    simpa only [raw] using hGood
  letI : Decidable (BadEventDS.E raw) := Classical.propDecidable _
  unfold TraceTransform.d2sTraceSaltedObserved
  simp only [OptionT.run_bind, OptionT.run_pure, OptionT.run_failure, Option.elimM]
  split
  · rename_i actualDelta hActualDelta
    change ProverTransform.prefixUpdateTrace raw = some actualDelta at hActualDelta
    have hDelta : actualDelta = fullTrΔ :=
      Option.some.inj (hActualDelta.symm.trans hFullUpdate)
    subst actualDelta
    have hSourceGood : ¬ BadEventDS.E
        (TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2)) := by
      simpa only [raw] using hFullGood
    simp [hSourceGood]
    apply TraceTransform.d2sTraceSaltedObservedGo_none_not_mem_support fullTrΔ raw
      (remaining := source.2.2.2) (processed := []) (st := { trStd := [], trStdLA := [] })
      (out := [])
    · intro processed hProcessedPrefix
      apply BadEventDS.prefixUpdateTrace_some_of_spongeConsistent fam processed
      intro entry hEntry
      exact hConsistent.2 entry (hProcessedPrefix.sublist.subset hEntry)
    · intro processed prefixTrΔ hPrefixUpdate hPrefixTrΔ hProcessedPrefix stateIn stateOut st hEntry
      have hProcessedGood : ¬ BadEventDS.E processed := by
        intro hBad
        exact hFullGood (BadEventDS.E_mono_of_raw_prefix hProcessedPrefix hBad)
      let prefixNormal : D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
        D2SNormalState.ofPrefixUpdate processed prefixTrΔ
          (by simpa using hPrefixUpdate) hProcessedGood
      let fullNormal : D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) :=
        D2SNormalState.ofPrefixUpdate raw fullTrΔ hFullUpdate hFullGood
      have hBacktrack : Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
          processed prefixTrΔ hPrefixTrΔ stateIn (processed.length + 1) ≠ .err := by
        simpa [prefixNormal] using AbortAnalysis.claim_5_19_backTrack_noAbort
          (pSpec := pSpec) prefixNormal stateIn
      have hFullForward : (stateIn, stateOut) ∈ TraceTableOps.entries fullTrΔ.p := by
        exact (ProverTransform.prefixUpdateTrace_mirrors hFullUpdate).2 stateIn stateOut |>.mp
          (Or.inl hEntry)
      apply TraceTransform.stdTraceHandlePQuery_none_not_mem_support
        processed prefixTrΔ hPrefixTrΔ fullTrΔ.p (processed.length + 1) stateIn st hBacktrack
      intro q result hResult
      apply AbortAnalysis.claim_5_20_lookAhead_support_some_of_forward_mem
        (pSpec := pSpec) fullNormal q.roundIdx stateIn stateOut hFullForward result
      simpa [fullNormal] using hResult
    · simp only [raw, List.nil_append]
  · rename_i hActualDelta
    change ProverTransform.prefixUpdateTrace raw = none at hActualDelta
    rw [hFullUpdate] at hActualDelta
    simp at hActualDelta

/-- The lossless observed H₀ endpoint has no *non-monitor* line-4 abort.  More precisely, at
every support point of the real game, an absent `D2STrace` observation means either that the
underlying DSFS source already failed or that the retained raw duplex trace satisfies `E`.

This is the executable H₀-side no-abort fact consumed by the future H₀/H₁ lazy-sampling joint
construction.  It is stronger and less error-prone than treating `StdTrace` totality as a
semantic premise: the proof follows the sampled `D_𝔖` family, the actual source run, and the
actual uniform-fibre interpreter used by `Hyb0Observed`. -/
theorem hyb0Observed_traceObservation_none_implies_badEvent
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    {observation : Statement.Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)}
    (hObservation : observation ∈ support
      (Statement.Hyb0Observed (T_H := T_H) (T_P := T_P) (Salt := Salt)
        oSpecImpl verifier maliciousProver))
    (hNone : observation.traceObservation = none) :
    observation.sourceOutput = none ∨ BadEventDS.E observation.baseTrace := by
  classical
  unfold Statement.Hyb0Observed at hObservation
  unfold mappedDSFSGameDistD2STraceObserved at hObservation
  rw [mem_support_bind_iff] at hObservation
  rcases hObservation with ⟨source?, hSource?, hObservation⟩
  cases source? with
  | none =>
      subst observation
      exact Or.inl rfl
  | some source =>
      rw [mem_support_bind_iff] at hObservation
      rcases hObservation with ⟨traceObservation?, hTraceObservation?, hObservation⟩
      simp only [mem_support_pure_iff] at hObservation
      have hObserved := hObservation
      subst observation
      simp only [MappedDSFSGameD2STraceObservation.baseTrace]
      have hTraceNone : traceObservation? = none := by
        simpa using hNone
      subst traceObservation?
      by_cases hBad : BadEventDS.E (TraceTransform.dsTraceOfLog source.2.2.2.untagged)
      · exact Or.inr hBad
      exfalso
      unfold dsfsGameDist at hSource?
      rw [mem_support_bind_iff] at hSource?
      rcases hSource? with ⟨fam, hFam, hSource⟩
      rw [StateT.run'_eq, support_map] at hSource
      rcases hSource with ⟨sourceState, hSource, hSourceEq⟩
      have hSourceState : (some source, sourceState.2) ∈ support
          ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver)).run fam) := by
        change sourceState.1 = some source at hSourceEq
        convert hSource using 1
        exact Prod.ext hSourceEq.symm rfl
      have hNoAbort := dsfsGame_hyb0_source_d2sTraceSaltedObserved_none_not_mem_support
        (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt) oSpecImpl verifier
          maliciousProver fam hSourceState hBad
      have hRawNone : none ∈ support
          (TraceTransform.d2sTraceSaltedObserved (T_H := T_H) (T_P := T_P)
            (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) source.2.2.2).run := by
        apply support_simulateQ_d2sUnit_subset
        exact hTraceObservation?
      exact hNoAbort hRawNone

/-- On an E-good, successful H₀ support point, the concrete observed offline transformer has not
aborted.  This is the exact form needed by the H₀/H₁ stop certificate: H₀ has no independent
non-monitor stopping time, so the revised coupling stops only for `E₀`, `E₁`, or the direct H₁
abort recorded in the paper. -/
theorem hyb0Observed_abortIndex_eq_none_of_good
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    {observation : Statement.Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)}
    (hObservation : observation ∈ support
      (Statement.Hyb0Observed (T_H := T_H) (T_P := T_P) (Salt := Salt)
        oSpecImpl verifier maliciousProver))
    (hSource : observation.sourceOutput ≠ none)
    (hGood : ¬ BadEventDS.E observation.baseTrace) :
    observation.abortIndex? = none := by
  unfold Statement.Hyb0Observation.abortIndex?
  cases hSourceOutput : observation.sourceOutput with
  | none =>
      exact (hSource hSourceOutput).elim
  | some source =>
      cases hTraceObservation : observation.traceObservation with
      | none =>
          exfalso
          have hBad := hyb0Observed_traceObservation_none_implies_badEvent
            (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
            oSpecImpl verifier maliciousProver hObservation hTraceObservation
          rcases hBad with hNoSource | hBad
          · exact hSource hNoSource
          · exact hGood hBad
      | some traceObservation =>
          rfl

/-- The concrete H₀ data available on its successful E-good branch.  This packages the actual
sampled sponge family and source-support certificate with the source base trace, reusable
normalized replay state, and lossless offline `D2STrace` observation.  The H₀/H₁ joint simulator
can therefore resume from this object without postulating a separate source execution.  It is not
a new game or an assumed semantic relation. -/
structure Hyb0ObservedSuccessfulReplay
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (observation : Statement.Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)) where
  source : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
  fam : (D_𝔖 StmtIn U).Carrier
  sourceState : (D_𝔖 StmtIn U).Carrier
  source_support : (some source, sourceState) ∈ support
    ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver).run).run fam)
  sourceOutput_eq : observation.sourceOutput = some source
  source_baseTrace : TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2) =
    observation.baseTrace
  normal : D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
  normal_trace : normal.state.trace = observation.baseTrace
  traceObservation : TraceTransform.D2STraceSaltedObservation
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)
  traceObservation_eq : observation.traceObservation = some traceObservation

/-- Extract the actual normalized replay state and lossless offline observation from a successful,
E-good H₀ support point.  Together with the direct H₁ no-underlying-abort result, this is the
no-hidden-abort input to the *concrete* Claim 5.21 lazy-permutation construction. -/
theorem hyb0Observed_successfulReplay_of_good
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    {observation : Statement.Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)}
    (hObservation : observation ∈ support
      (Statement.Hyb0Observed (T_H := T_H) (T_P := T_P) (Salt := Salt)
        oSpecImpl verifier maliciousProver))
    (hSource : observation.sourceOutput ≠ none)
    (hGood : ¬ BadEventDS.E observation.baseTrace) :
    Nonempty (Hyb0ObservedSuccessfulReplay (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U)
      (δ := δ) (Salt := Salt) oSpecImpl verifier maliciousProver observation) := by
  classical
  unfold Statement.Hyb0Observed at hObservation
  unfold mappedDSFSGameDistD2STraceObserved at hObservation
  rw [mem_support_bind_iff] at hObservation
  rcases hObservation with ⟨source?, hSource?, hObservation⟩
  cases source? with
  | none =>
      subst observation
      exact (hSource rfl).elim
  | some source =>
      rw [mem_support_bind_iff] at hObservation
      rcases hObservation with ⟨traceObservation?, hTraceObservation?, hObservation⟩
      simp only [mem_support_pure_iff] at hObservation
      subst observation
      unfold dsfsGameDist at hSource?
      rw [mem_support_bind_iff] at hSource?
      rcases hSource? with ⟨fam, hFam, hSourceRun⟩
      rw [StateT.run'_eq, support_map] at hSourceRun
      rcases hSourceRun with ⟨sourceState, hSourceRun, hSourceEq⟩
      have hSourceState : (some source, sourceState.2) ∈ support
          ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame verifier maliciousProver)).run fam) := by
        change sourceState.1 = some source at hSourceEq
        convert hSourceRun using 1
        exact Prod.ext hSourceEq.symm rfl
      have hSourceGood : ¬ BadEventDS.E
          (TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2)) := by
        simpa using hGood
      cases hTrace : traceObservation? with
      | none =>
          exfalso
          have hNoAbort := dsfsGame_hyb0_source_d2sTraceSaltedObserved_none_not_mem_support
            (T_H := T_H) (T_P := T_P) (δ := δ) (Salt := Salt)
            oSpecImpl verifier maliciousProver fam hSourceState hSourceGood
          have hRawNone : none ∈ support
              (TraceTransform.d2sTraceSaltedObserved (T_H := T_H) (T_P := T_P)
                (δ := δ) (Salt := Salt) (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) source.2.2.2).run := by
            apply support_simulateQ_d2sUnit_subset
            simpa [hTrace] using hTraceObservation?
          exact hNoAbort hRawNone
      | some traceObservation =>
          obtain ⟨normal, hNormal⟩ := dsfsGame_hyb0_source_normalState_of_support
            (T_H := T_H) (T_P := T_P) oSpecImpl verifier maliciousProver fam hSourceState
              hSourceGood
          refine ⟨⟨source, fam, sourceState.2, hSourceState, rfl, rfl,
            normal, ?_, traceObservation, by simp⟩⟩
          change normal.state.trace =
            TraceTransform.dsTraceOfLog (TaggedQueryLog.untagged source.2.2.2)
          exact hNormal

end DuplexSpongeFS.KeyLemma

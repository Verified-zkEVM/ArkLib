/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Execution
public import ArkLib.VCVioStaging.OracleComp.Constructions.RandomPermutation.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable

/-!
# Exact eager/lazy sampling for arbitrary duplex-sponge oracle programs

The equivalence preserves every observable returned by the source program, including query logs
recorded before interpretation. It needs no protocol, query budget, nondegeneracy, or bad-event
hypothesis. The historical declaration namespace is retained for existing coupling clients.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec DuplexSpongeFS.Execution
open scoped ENNReal

namespace DuplexSpongeFS.KeyLemma.LazyReal

noncomputable section

/-! ## Generic `StateT`-carrier lemmas

Two shapes of "the carrier does not influence the answers" occur below: the eagerly sampled
`𝒟_𝔖` carrier, which is *read-only*, and `RandomPermutation`'s eager edge trace, which is
*write-only*.  In both cases the state can be discarded from a `run'`, as an equality of
computations (not merely of distributions). -/

section Generic

variable {ιf : Type} {fullSpec : OracleSpec ιf} {σ α : Type}

private lemma run'_simulateQ_query_bind
    (impl : QueryImpl fullSpec (StateT σ ProbComp))
    (t : fullSpec.Domain) (k : fullSpec.Range t → OracleComp fullSpec α) (s : σ) :
    (simulateQ impl (liftM (fullSpec.query t) >>= k)).run' s
      = (impl t).run s >>= fun p => (simulateQ impl (k p.1)).run' p.2 := by
  rw [simulateQ_bind, simulateQ_spec_query]
  change (fun x => x.1) <$> ((impl t).run s >>= fun p => (simulateQ impl (k p.1)).run p.2) = _
  rw [map_bind]
  rfl

/-- **Read-only carrier.** If every query answer distribution at the fixed state `s` is that of
a stateless handler `impl₀` and leaves the state untouched, then running under `impl` from `s`
and projecting away the state is running under `impl₀`. -/
theorem simulateQ_run'_eq_of_readOnly
    (impl : QueryImpl fullSpec (StateT σ ProbComp)) (impl₀ : QueryImpl fullSpec ProbComp) (s : σ)
    (h : ∀ q : fullSpec.Domain, (impl q).run s = (do let a ← impl₀ q; pure (a, s)))
    (oa : OracleComp fullSpec α) :
    (simulateQ impl oa).run' s = simulateQ impl₀ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      rw [simulateQ_pure, simulateQ_pure]
      change (fun x => x.1) <$> (pure (a, s) : ProbComp _) = pure a
      rw [map_pure]
  | query_bind q k ih =>
      rw [run'_simulateQ_query_bind, h q, simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact bind_congr fun a => by rw [pure_bind]; exact ih a

/-- **Write-only carrier.** If every query answer comes from a stateless handler `impl₀` and the
state is only updated (never read), the state can be discarded from a `run'` at any start
value. -/
theorem simulateQ_run'_eq_of_writeOnly
    (impl : QueryImpl fullSpec (StateT σ ProbComp)) (impl₀ : QueryImpl fullSpec ProbComp)
    (upd : (q : fullSpec.Domain) → fullSpec.Range q → σ → σ)
    (h : ∀ (q : fullSpec.Domain) (s : σ),
      (impl q).run s = (do let a ← impl₀ q; pure (a, upd q a s)))
    (oa : OracleComp fullSpec α) (s : σ) :
    (simulateQ impl oa).run' s = simulateQ impl₀ oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      rw [simulateQ_pure, simulateQ_pure]
      change (fun x => x.1) <$> (pure (a, s) : ProbComp _) = pure a
      rw [map_pure]
  | query_bind q k ih =>
      rw [run'_simulateQ_query_bind, h q, simulateQ_bind, simulateQ_spec_query, bind_assoc]
      exact bind_congr fun a => by rw [pure_bind]; exact ih a _

/-- A state-independent probabilistic step commutes with an eagerly sampled table: swap the two
independent draws, then apply the per-outcome equivalence.  (Generalization of the private
`evalDist_bind_uniform_pass_through` of `Hyb1Hyb2.LazySampling` to an arbitrary first draw.) -/
private lemma evalDist_bind_pass_through {T ρ β : Type} [MeasurableSpace β]
    (mg : ProbComp T) (A : ProbComp ρ) (F : T → ρ → ProbComp β) (G : ρ → ProbComp β)
    (h : ∀ r : ρ, 𝒟[do let g ← mg; F g r] = 𝒟[G r]) :
    𝒟[do let g ← mg; let r ← A; F g r] = 𝒟[do let r ← A; G r] := by
  rw [OracleComp.evalDist_bind_bind_swap]
  exact evalDist_bind_congr _ _ _ h

end Generic

/-! ## Answer-projected form of the exact eager/lazy permutation bridge

`RandomPermutation.lazyRunWith_empty_eq_uniform` retains the whole final edge trace *and* the
installed completion.  A game only observes the answers, so the useful form projects onto the
first component; the projection is legitimate because the final completion is drawn from a
total (mass-one) sampler, so `OracleComp.evalDist_bind_const` removes it. -/

section PermutationBridge

open OracleComp.RandomPermutation

variable {α : Type} [Fintype α] [DecidableEq α] {κ : Type} {spec : OracleSpec κ}

/-- **Exact eager/lazy permutation bridge, answer-projected and executable.**

Running an arbitrary adaptive computation against `RandomPermutation`'s executable lazy dual
table from the empty trace has exactly the distribution of running it against one uniformly
sampled permutation, for any interleaved stateless auxiliary handler `aux`.  The permutation
sampler is taken as a parameter (with its uniformity law as a hypothesis) so that the caller
may pin whichever `SampleableType` instance its ambient definitions use. -/
theorem evalDist_run'_lazyImplWith_empty (aux : QueryImpl spec ProbComp) {β : Type}
    [MeasurableSpace β] [SampleableType (Equiv.Perm α)]
    (ob : OracleComp (permutationOracle α + spec) β)
    (permSample : ProbComp (Equiv.Perm α))
    (hperm : (letI : MeasurableSpace (Equiv.Perm α) := ⊤
      𝒟[permSample] = 𝒟[$ᵗ (Equiv.Perm α)])) :
    𝒟[(simulateQ (lazyImplWith aux) ob).run' emptyTrace]
      = 𝒟[do
          let p ← permSample
          (simulateQ (eagerImplWith aux p) ob).run' []] := by
  let : MeasurableSpace ((β × List (α × α)) × Equiv.Perm α) := ⊤
  have h := congrArg (fun μ => μ.map (fun z : (β × List (α × α)) × Equiv.Perm α => z.1.1))
    (lazyRunWith_empty_eq_uniform aux ob)
  simp only [← evalDist_map_of_discrete] at h
  have hL : 𝒟[(fun z : (β × List (α × α)) × Equiv.Perm α => z.1.1) <$>
      lazyRunWith aux ob emptyTrace]
      = 𝒟[(simulateQ (lazyImplWith aux) ob).run' emptyTrace] := by
    rw [StateT.run'_eq, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    simp only [lazyRunWith, bind_assoc, pure_bind, Function.comp_apply]
    exact evalDist_bind_congr _ _ _ fun bt => OracleComp.evalDist_bind_const _ _
  have hR : ((fun z : (β × List (α × α)) × Equiv.Perm α => z.1.1) <$>
      (($ᵗ (Equiv.Perm α)) >>= fun p => (fun z => (z, p)) <$> eagerRunWith aux p ob []))
      = ($ᵗ (Equiv.Perm α)) >>= fun p => (simulateQ (eagerImplWith aux p) ob).run' [] := by
    simp only [map_bind, Functor.map_map, eagerRunWith, StateT.run'_eq]
  rw [← hL, h, hR]
  exact (((evalDistEq_iff_evalDist_eq.mpr hperm).bind_left _).evalDist_eq).symm

end PermutationBridge

/-! ## The DSFS instantiation -/

section DSFS

open OracleComp.RandomPermutation

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} [VCVCompatible StmtIn]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]

/-- The permutation-free part of the `Hyb₀` handler, as one stateless auxiliary handler:
ambient `oSpec` queries go to `oSpecImpl`, hash queries are answered from the eager table `h`.
This is `RandomPermutation`'s `aux` slot. -/
def dsAuxImpl (oSpecImpl : QueryImpl oSpec ProbComp)
    (h : QueryImpl (DSHashSpec StmtIn U) Id) :
    QueryImpl (oSpec + DSHashSpec StmtIn U) ProbComp
  | .inl q => oSpecImpl q
  | .inr qh => pure (h qh)

/-- Reindex the DSFS query surface `oSpec + ((𝕏 →ₒ Σ^c) + permutationOracle Σ^{r+c})` into the
permutation-first surface `permutationOracle Σ^{r+c} + (oSpec + (𝕏 →ₒ Σ^c))` expected by
`RandomPermutation.lazyImplWith` / `eagerImplWith`.  Answers are unchanged. -/
def dsPermFirstReindex :
    QueryImpl (oSpec + duplexSpongeOracle StmtIn U)
      (OracleComp (permutationOracle (CanonicalSpongeState U) + (oSpec + DSHashSpec StmtIn U)))
  | .inl q =>
      (permutationOracle (CanonicalSpongeState U) + (oSpec + DSHashSpec StmtIn U)).query
        (.inr (.inl q))
  | .inr (.inl qh) =>
      (permutationOracle (CanonicalSpongeState U) + (oSpec + DSHashSpec StmtIn U)).query
        (.inr (.inr qh))
  | .inr (.inr qp) =>
      (permutationOracle (CanonicalSpongeState U) + (oSpec + DSHashSpec StmtIn U)).query
        (.inl qp)

/-- **Intermediate handler (Stage A target).** Ambient `oSpec` queries go to `oSpecImpl`, hash
queries are answered from the eagerly sampled table `h`, and permutation queries (both
directions) are answered by `RandomPermutation`'s lazy dual table. -/
def eagerHashLazyPermImpl (oSpecImpl : QueryImpl oSpec ProbComp)
    (h : QueryImpl (DSHashSpec StmtIn U) Id) :
    QueryImpl (oSpec + duplexSpongeOracle StmtIn U) (StateT (DSPermTrace U) ProbComp)
  | .inl q => StateT.mk fun t => (fun r => (r, t)) <$> oSpecImpl q
  | .inr (.inl qh) => StateT.mk fun t => pure (h qh, t)
  | .inr (.inr qp) => lazyImpl qp

/-- The `Hyb₀` handler at a *fixed* realization `(h, p)`, with the read-only carrier removed. -/
def dsEagerImpl (oSpecImpl : QueryImpl oSpec ProbComp)
    (k : DuplexSpongeOracleFamily StmtIn U) :
    QueryImpl (oSpec + duplexSpongeOracle StmtIn U) ProbComp
  | .inl q => oSpecImpl q
  | .inr qDS => duplexSpongeOracleQueryImpl k qDS

/-- The state update performed by the eager permutation handler: permutation queries append the
normalized forward edge, all other slots leave the trace alone. -/
def dsEdgeUpd : (q : (oSpec + duplexSpongeOracle StmtIn U).Domain) →
    (oSpec + duplexSpongeOracle StmtIn U).Range q →
    List (CanonicalSpongeState U × CanonicalSpongeState U) →
    List (CanonicalSpongeState U × CanonicalSpongeState U)
  | .inl _, _, t => t
  | .inr (.inl _), _, t => t
  | .inr (.inr qp), a, t => edge qp a :: t

omit [VCVCompatible StmtIn] in
/-- `eagerHashLazyPermImpl` is `RandomPermutation`'s lazy handler composed with the reindexing. -/
lemma eagerHashLazyPermImpl_eq_compose (oSpecImpl : QueryImpl oSpec ProbComp)
    (h : QueryImpl (DSHashSpec StmtIn U) Id) :
    eagerHashLazyPermImpl (StmtIn := StmtIn) oSpecImpl h
      = (lazyImplWith (dsAuxImpl oSpecImpl h)) ∘ₛ dsPermFirstReindex := by
  funext q
  rcases q with q | qh | qp
  · exact (simulateQ_spec_query (lazyImplWith (dsAuxImpl oSpecImpl h)) (.inr (.inl q))).symm
  · exact (simulateQ_spec_query (lazyImplWith (dsAuxImpl oSpecImpl h)) (.inr (.inr qh))).symm
  · exact (simulateQ_spec_query (lazyImplWith (dsAuxImpl oSpecImpl h)) (.inl qp)).symm

/-- The eager counterpart of `eagerHashLazyPermImpl`: one fixed permutation `p`, with
`RandomPermutation`'s write-only edge trace, in explicit slot form. -/
def dsEagerTraceImpl (oSpecImpl : QueryImpl oSpec ProbComp)
    (h : QueryImpl (DSHashSpec StmtIn U) Id)
    (p : Equiv.Perm (CanonicalSpongeState U)) :
    QueryImpl (oSpec + duplexSpongeOracle StmtIn U)
      (StateT (List (CanonicalSpongeState U × CanonicalSpongeState U)) ProbComp)
  | .inl q => StateT.mk fun t => (fun r => (r, t)) <$> oSpecImpl q
  | .inr (.inl qh) => StateT.mk fun t => pure (h qh, t)
  | .inr (.inr qp) => StateT.mk fun t => pure (reply p qp, edge qp (reply p qp) :: t)

omit [VCVCompatible StmtIn] [VCVCompatible U] in
/-- `dsEagerTraceImpl` is `RandomPermutation`'s eager handler composed with the reindexing. -/
lemma dsEagerTraceImpl_eq_compose (oSpecImpl : QueryImpl oSpec ProbComp)
    (h : QueryImpl (DSHashSpec StmtIn U) Id)
    (p : Equiv.Perm (CanonicalSpongeState U)) :
    dsEagerTraceImpl (StmtIn := StmtIn) oSpecImpl h p
      = (eagerImplWith (dsAuxImpl oSpecImpl h) p) ∘ₛ dsPermFirstReindex := by
  funext q
  rcases q with q | qh | qp
  · exact (simulateQ_spec_query (eagerImplWith (dsAuxImpl oSpecImpl h) p)
      (.inr (.inl q))).symm
  · exact (simulateQ_spec_query (eagerImplWith (dsAuxImpl oSpecImpl h) p)
      (.inr (.inr qh))).symm
  · exact (simulateQ_spec_query (eagerImplWith (dsAuxImpl oSpecImpl h) p) (.inl qp)).symm

omit [VCVCompatible StmtIn] [VCVCompatible U] in
/-- The eager permutation handler is write-only over the stateless `dsEagerImpl`. -/
lemma dsEagerTraceImpl_run (oSpecImpl : QueryImpl oSpec ProbComp)
    (h : QueryImpl (DSHashSpec StmtIn U) Id)
    (p : Equiv.Perm (CanonicalSpongeState U))
    (q : (oSpec + duplexSpongeOracle StmtIn U).Domain)
    (t : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
    (dsEagerTraceImpl oSpecImpl h p q).run t
      = (do let a ← dsEagerImpl oSpecImpl (h, p) q; pure (a, dsEdgeUpd q a t)) := by
  rcases q with q | qh | qp
  · change ((fun r => (r, t)) <$> oSpecImpl q) = _
    exact (bind_pure_comp _ _).symm
  · rfl
  · cases qp with
    | inl s => rfl
    | inr s => rfl

omit [VCVCompatible StmtIn] in
/-- **Stage A.** With the hash table `h` eager, the eagerly sampled permutation may be replaced
by `RandomPermutation`'s lazy dual table, exactly.  This is the exact eager/lazy permutation
bridge of `RandomPermutation`, transported to the DSFS query surface. -/
theorem evalDist_run'_eagerHashLazyPermImpl
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (h : QueryImpl (DSHashSpec StmtIn U) Id)
    {γ : Type} [MeasurableSpace γ]
    (oa : OracleComp (oSpec + duplexSpongeOracle StmtIn U) γ) :
    𝒟[(simulateQ (eagerHashLazyPermImpl oSpecImpl h) oa).run' emptyTrace]
      = 𝒟[do
          let p ← uniformSample (Equiv.Perm (CanonicalSpongeState U))
            (h := VCVCompatible.toSampleableTypePerm)
          simulateQ (dsEagerImpl oSpecImpl (h, p)) oa] := by
  have hcont : ∀ p : Equiv.Perm (CanonicalSpongeState U),
      (simulateQ (eagerImplWith (dsAuxImpl oSpecImpl h) p)
        (simulateQ dsPermFirstReindex oa)).run' []
        = simulateQ (dsEagerImpl oSpecImpl (h, p)) oa := by
    intro p
    rw [← QueryImpl.simulateQ_compose, ← dsEagerTraceImpl_eq_compose]
    exact simulateQ_run'_eq_of_writeOnly _ _ dsEdgeUpd (dsEagerTraceImpl_run oSpecImpl h p) oa []
  let _ := VCVCompatible.toSampleableTypePerm (α := CanonicalSpongeState U)
  rw [eagerHashLazyPermImpl_eq_compose, QueryImpl.simulateQ_compose,
    evalDist_run'_lazyImplWith_empty (dsAuxImpl oSpecImpl h)
      (simulateQ dsPermFirstReindex oa) _ rfl]
  simp only [hcont]

section SlotLemmas

variable (oSpecImpl : QueryImpl oSpec ProbComp)

omit [VCVCompatible StmtIn] in
/-- Ambient slot of the Stage-A handler. -/
lemma eagerHashLazyPermImpl_run_oSpec (h : QueryImpl (DSHashSpec StmtIn U) Id)
    (q : ι) (t : DSPermTrace U) :
    (eagerHashLazyPermImpl oSpecImpl h (.inl q)).run t
      = (do let r ← oSpecImpl q; pure (r, t)) := by
  change (fun r => (r, t)) <$> oSpecImpl q = _
  rw [map_eq_bind_pure_comp]
  rfl

omit [VCVCompatible StmtIn] in
/-- Hash slot of the Stage-A handler: a table read. -/
lemma eagerHashLazyPermImpl_run_hash (h : QueryImpl (DSHashSpec StmtIn U) Id)
    (qh : StmtIn) (t : DSPermTrace U) :
    (eagerHashLazyPermImpl oSpecImpl h (.inr (.inl qh))).run t = pure (h qh, t) := rfl

omit [VCVCompatible StmtIn] in
/-- Permutation slot of the Stage-A handler. -/
lemma eagerHashLazyPermImpl_run_perm (h : QueryImpl (DSHashSpec StmtIn U) Id)
    (qp : (permutationOracle (CanonicalSpongeState U)).Domain) (t : DSPermTrace U) :
    (eagerHashLazyPermImpl (StmtIn := StmtIn) oSpecImpl h (.inr (.inr qp))).run t
      = (lazyImpl qp).run t := rfl

end SlotLemmas

/-! ### Stage B: lazify the hash table -/

/-- The uniform full hash table, with the `SampleableType` instance pinned to the one used by
`duplexSpongeHashOracleDistribution` (`OracleReduction.sampleableTypePiVCV`). -/
abbrev dsHashTableSample (StmtIn U : Type) [VCVCompatible StmtIn] [SpongeUnit U]
    [VCVCompatible U] : ProbComp (QueryImpl (DSHashSpec StmtIn U) Id) :=
  uniformSample (QueryImpl (DSHashSpec StmtIn U) Id)
    (h := OracleReduction.sampleableTypePiVCV)

/-- **Stage B, cache-parametrized.** Running against the Stage-A handler with a uniform hash
table conditioned to extend the partial cache `c` is distributionally identical to running
against the fully lazy handler from the joint state `(c, t)`.

The cache is generalized so that the miss case can recurse through `Function.update`; fresh
on-demand draws are absorbed into the eager table by the dependent-table law
`evalDist_bind_bind_update_dependent`.  Structure mirrors
`Hyb1Hyb2.LazySampling.evalDist_uniformTable_simulateQ_hybVerifierMessageImpl_run'_completeTable`,
here with the permutation half of the carrier threaded through untouched. -/
theorem evalDist_dsHashTableSample_bind_run'_eagerHashLazyPermImpl_completeTable
    (oSpecImpl : QueryImpl oSpec ProbComp) {γ : Type} [MeasurableSpace γ]
    (oa : OracleComp (oSpec + duplexSpongeOracle StmtIn U) γ)
    (c : (DSHashSpec StmtIn U).QueryCache) (t : DSPermTrace U) :
    𝒟[do
      let g ← dsHashTableSample StmtIn U
      (simulateQ (eagerHashLazyPermImpl oSpecImpl (completeTable c g)) oa).run' t]
      = 𝒟[(simulateQ (lazyRealImpl oSpecImpl) oa).run' ⟨c, t⟩] := by
  classical
  induction oa using OracleComp.inductionOn generalizing c t with
  | pure a =>
      have hE : ∀ g : QueryImpl (DSHashSpec StmtIn U) Id,
          (simulateQ (eagerHashLazyPermImpl oSpecImpl (completeTable c g))
            (pure a : OracleComp _ γ)).run' t = (pure a : ProbComp γ) := by
        intro g
        rw [simulateQ_pure]
        change (fun x => x.1) <$> (pure (a, t) : ProbComp _) = pure a
        rw [map_pure]
      have hL : (simulateQ (lazyRealImpl oSpecImpl) (pure a : OracleComp _ γ)).run'
          (⟨c, t⟩ : LazyRealState StmtIn U) = (pure a : ProbComp γ) := by
        rw [simulateQ_pure]
        change (fun x => x.1) <$>
          (pure (a, (⟨c, t⟩ : LazyRealState StmtIn U)) : ProbComp _) = pure a
        rw [map_pure]
      rw [hL]
      simp only [hE]
      exact OracleComp.evalDist_bind_const _ _
  | query_bind q k ih =>
      simp only [run'_simulateQ_query_bind]
      rcases q with qS | qh | qp
      · simp only [eagerHashLazyPermImpl_run_oSpec, lazyRealImpl_run_oSpec,
          bind_assoc, pure_bind]
        exact evalDist_bind_pass_through _ (oSpecImpl qS) _ _ fun r => ih r c t
      · rcases hc : c qh with _ | v
        · have hval : ∀ g : QueryImpl (DSHashSpec StmtIn U) Id,
              completeTable c g qh = g qh := by
            intro g; simp [completeTable, hc]
          simp only [eagerHashLazyPermImpl_run_hash,
            lazyRealImpl_run_hash_miss oSpecImpl qh ⟨c, t⟩ hc,
            bind_assoc, pure_bind, hval]
          let : SampleableType ((d : StmtIn) → Vector U SpongeSize.C) :=
            OracleReduction.sampleableTypePiVCV
          let : SampleableType (Vector U SpongeSize.C) := VCVCompatible.toSampleableType
          let : MeasurableSpace (Vector U SpongeSize.C) := ⊤
          have hmarg := evalDist_bind_bind_update_dependent (D := StmtIn)
            (R := fun _ => Vector U SpongeSize.C) qh
            ($ᵗ (Vector U SpongeSize.C)) ($ᵗ ((d : StmtIn) → Vector U SpongeSize.C))
            SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
            (fun g' => (simulateQ (eagerHashLazyPermImpl oSpecImpl (completeTable c g'))
              (k (g' qh))).run' t)
          refine Eq.trans hmarg.symm (evalDist_bind_congr _ _ _ fun u => ?_)
          have hstate : ∀ g : QueryImpl (DSHashSpec StmtIn U) Id,
              completeTable c (Function.update g qh u) = completeTable (c.cacheQuery qh u) g :=
            fun g =>
              (completeTable_update_of_none c g hc u).symm.trans
                (completeTable_cacheQuery c g qh u).symm
          simp only [Function.update_self, hstate]
          exact ih u (c.cacheQuery qh u) t
        · have hval : ∀ g : QueryImpl (DSHashSpec StmtIn U) Id,
              completeTable c g qh = v := by
            intro g; simp [completeTable, hc]
          simp only [eagerHashLazyPermImpl_run_hash,
            lazyRealImpl_run_hash_hit oSpecImpl qh ⟨c, t⟩ v hc, hval]
          exact ih v c t
      · simp only [eagerHashLazyPermImpl_run_perm, lazyRealImpl_run_perm,
          bind_assoc, pure_bind]
        exact evalDist_bind_pass_through _ ((lazyImpl qp).run t) _ _ fun r => ih r.1 c r.2

/-- Sampling the ideal hash table and permutation eagerly gives exactly the same law as
answering an arbitrary adaptive oracle program with the shared lazy hash cache and permutation
trace. Source-program outputs may include the full query log. -/
theorem evalDist_sample_bind_simulateQ_eq_lazyRealImpl
    (oSpecImpl : QueryImpl oSpec ProbComp) {γ : Type} [MeasurableSpace γ]
    (oa : OracleComp (oSpec + duplexSpongeOracle StmtIn U) γ) :
    𝒟[do
      let fam ← D_𝔖.sample StmtIn U
      simulateQ (dsEagerImpl oSpecImpl fam) oa]
      = 𝒟[(simulateQ (lazyRealImpl oSpecImpl) oa).run'
          (emptyLazyRealState (StmtIn := StmtIn) (U := U))] := by
  have hB := evalDist_dsHashTableSample_bind_run'_eagerHashLazyPermImpl_completeTable
    oSpecImpl oa ∅ emptyTrace
  simp only [completeTable_empty] at hB
  refine Eq.trans ?_ hB
  rw [D_𝔖.sample_eq]
  simp only [bind_assoc, pure_bind]
  exact evalDist_bind_congr _ _ _ fun h =>
    (evalDist_run'_eagerHashLazyPermImpl oSpecImpl h oa).symm

end DSFS

end

end DuplexSpongeFS.KeyLemma.LazyReal

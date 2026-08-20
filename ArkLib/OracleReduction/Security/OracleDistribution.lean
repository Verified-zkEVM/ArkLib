/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.Execution

/-!
  # Oracle Distributions: First-Class Sampled Oracles

  This file introduces a paper-faithful abstraction for "sample an oracle from a distribution,
  then run an adversary against it":

  ```
  let O ← D.sample
  simulateQ (D.toImpl O) A
  ```

  The mathematical primitive is `OracleDistribution`: a triple of a `Carrier` (one realization),
  a `sample : ProbComp Carrier`, and a derivation `Carrier → QueryImpl spec ProbComp` that turns a
  sampled realization into something `simulateQ` can run against.

  The function-table case (`OracleFamily`) is one realization, suitable for random-function
  oracles such as `D_Σ`, `D_IP`, `D_ROM`. Permutation components use a different carrier
  (`Equiv.Perm State`) that satisfies the bijection invariant by construction; paper `D_𝔖`
  combines this permutation carrier with a random-function carrier for `h`.

  Layered probability laws are the API surface (Level 3, post-`simulateQ`); this file states
  the foundational pieces (Levels 1-2) and leaves the lifts (Level 3) as `sorry` for downstream
  development.
-/

namespace OracleReduction

open OracleComp OracleSpec
open scoped ENNReal

variable {ι : Type}

/-! ## §1. Function-table carriers -/

/-- A deterministic answer table for an `OracleSpec`: each query gets a fixed response. -/
abbrev OracleFamily (spec : OracleSpec ι) : Type _ := (q : spec.Domain) → spec.Range q

/-- Promote a deterministic answer table to a `QueryImpl spec ProbComp`. -/
@[reducible]
def tableQueryImpl {spec : OracleSpec ι} (g : OracleFamily spec) :
    QueryImpl spec ProbComp := fun q => pure (g q)

/-- `VCVCompatible` on both domain and range implies `SampleableType (α → β)`.

`OracleFamily (α →ₒ β)` is definitionally `α → β`, so this instance also fires for
`[SampleableType (OracleFamily (StartType →ₒ Vector U n))]` via reducibility of `OracleFamily`. -/
noncomputable instance instSampleableTypePiVCV
    {α β : Type} [VCVCompatible α] [VCVCompatible β] :
    SampleableType (α → β) := by
  letI : FinEnum α := VCVCompatible.instFinEnum
  letI : FinEnum β := VCVCompatible.instFinEnum
  letI : Nonempty (α → β) := ⟨fun _ => default⟩
  infer_instance

/-! ## §2. The `OracleDistribution` primitive

`Carrier` lets us cover not just random-function oracles (`Carrier := OracleFamily spec`) but
also permutations (`Carrier := Equiv.Perm State`), ideal ciphers, and parameter-keyed schemes
(`Carrier := K`) — all via the same abstraction.
-/

/-! A distribution over deterministic interpretations of `spec`.
TODO: should we use `PMF`? -/
structure OracleDistribution (spec : OracleSpec ι) where
  /-- Internal carrier: what is sampled and then fixed. -/
  Carrier : Type
  /-- Sampling procedure for one realization. -/
  sample  : ProbComp Carrier
  /-- Turn a fixed realization into a deterministic interpreter. -/
  toImpl  : Carrier → QueryImpl spec ProbComp

namespace OracleDistribution

variable {spec : OracleSpec ι}

/-- Run an oracle adversary against a sampled realization. Paper-faithful syntax:
`let O ← D.sample; simulateQ (D.toImpl O) A`. -/
def runWith (D : OracleDistribution spec) {α : Type} (A : OracleComp spec α) : ProbComp α := do
  let c ← D.sample
  simulateQ (D.toImpl c) A

/-- Eager state-based implementation wrapper.
Turns a stateless `toImpl` bound to a specific carrier into a `StateT` querying interpreter
that reads the pre-sampled carrier from the state. -/
def eagerImpl (D : OracleDistribution spec) :
    QueryImpl spec (StateT D.Carrier ProbComp) :=
  fun q => do
    let k ← StateT.get
    StateT.lift (D.toImpl k q)

/-- The function-table realization (random-function oracles).
Used for `D_ROM`, `D_IP`, `D_Σ`, , etc. -/
def functionTable (D : ProbComp (OracleFamily spec)) : OracleDistribution spec where
  Carrier := OracleFamily spec
  sample  := D
  toImpl  := tableQueryImpl

/-- Uniform full-table sampling. Requires `SampleableType` over the dependent product
`OracleFamily spec`, which holds when `ι` and each `spec i` are finite + decidable. -/
def uniform (spec : OracleSpec ι) [SampleableType (OracleFamily spec)] :
    OracleDistribution spec :=
  functionTable (D := $ᵗ OracleFamily spec)

/-- Bridge to the existing VCVio pattern `let k ← keygen; simulateQ (mkImpl k) A`.
Wraps a parameter sampler + table builder into a paper-faithful `OracleDistribution`. -/
def ofKeygen {K : Type} (keygen : ProbComp K) (table : K → OracleFamily spec) :
    OracleDistribution spec where
  Carrier := K
  sample  := keygen
  toImpl  := fun k => tableQueryImpl (table k)

/-- Independent product of two oracle distributions over disjoint oracle specs.

This models paper syntax such as `(O₁, O₂) ← D₁ × D₂`: sample one realization from `D₁`,
sample one realization from `D₂`, and answer sum-oracle queries by dispatching to the
corresponding sampled component. -/
def prod {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (D₁ : OracleDistribution spec₁) (D₂ : OracleDistribution spec₂) :
    OracleDistribution (spec₁ + spec₂) where
  Carrier := D₁.Carrier × D₂.Carrier
  sample := do
    let c₁ ← D₁.sample
    let c₂ ← D₂.sample
    pure (c₁, c₂)
  toImpl := fun c q =>
    match q with
    | Sum.inl q₁ => D₁.toImpl c.1 q₁
    | Sum.inr q₂ => D₂.toImpl c.2 q₂

end OracleDistribution

/-! ## Dependent full-table sampling -/

end OracleReduction

namespace OracleComp

open scoped ENNReal
open OracleSpec

/-- **Overwriting one coordinate of a dependent uniform table is measure-preserving.**

This is the dependent-range counterpart of VCVio's
`evalDist_uniformSample_bind_update`.  An `OracleFamily spec` is a dependent function
`(q : spec.Domain) → spec.Range q`, so a fresh oracle response replaces one coordinate using
the dependent form of `Function.update`.  Sampling that coordinate freshly and independently
before the full table leaves the uniform full-table distribution unchanged.

It is the finite-product marginalization step needed to relate eager and lazy realizations of
an `OracleSpec` whose query ranges vary with the query. -/
lemma evalDist_uniformSample_bind_update_dependent
    {D : Type} {R : D → Type} [Finite D] [DecidableEq D]
    [∀ d, Finite (R d)] [∀ d, Nonempty (R d)]
    [∀ d, SampleableType (R d)] [SampleableType ((d : D) → R d)]
    (t : D) :
    𝒟[do let u ← $ᵗ R t; let g ← $ᵗ ((d : D) → R d); pure (Function.update g t u)] =
      𝒟[$ᵗ ((d : D) → R d)] := by
  classical
  letI := Fintype.ofFinite D
  letI : ∀ d, Fintype (R d) := fun d => Fintype.ofFinite (R d)
  haveI : Nonempty ((d : D) → R d) :=
    ⟨fun d => Classical.arbitrary (R d)⟩
  refine evalDist_ext fun h => ?_
  rw [probOutput_uniformSample ((d : D) → R d) h, probOutput_bind_eq_sum_fintype]
  have hinner : ∀ u : R t,
      Pr[= h | (do let g ← $ᵗ ((d : D) → R d); pure (Function.update g t u))]
        = (if u = h t then
            (Fintype.card (R t) : ℝ≥0∞) *
              (Fintype.card (∀ d : D, R d) : ℝ≥0∞)⁻¹ else 0) := by
    intro u
    have hmap : (do let g ← $ᵗ ((d : D) → R d); pure (Function.update g t u))
        = (fun g => Function.update g t u) <$> ($ᵗ ((d : D) → R d)) := by
      rw [bind_pure_comp]
    rw [hmap, probOutput_map_eq_sum_fintype_ite]
    simp only [probOutput_uniformSample ((d : D) → R d)]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.filter fun g : (d : D) → R d => h = Function.update g t u).card : ℝ≥0∞)
          = if u = h t then (Fintype.card (R t) : ℝ≥0∞) else 0 := by
      by_cases hu : u = h t
      · have hset :
          (Finset.univ.filter fun g : (d : D) → R d => h = Function.update g t u)
            = Finset.univ.image (fun r : R t => Function.update h t r) := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hg
            refine ⟨g t, ?_⟩
            rw [eq_comm, Function.update_eq_iff] at hg
            obtain ⟨_, hg2⟩ := hg
            funext x
            by_cases hx : x = t
            · subst hx
              simp
            · simp [Function.update_of_ne hx, hg2 x hx]
          · rintro ⟨r, rfl⟩
            rw [eq_comm, Function.update_eq_iff]
            exact ⟨by simp [hu], fun x hx => by simp [Function.update_of_ne hx]⟩
        rw [hset, Finset.card_image_of_injective _
          (fun r₁ r₂ hr => by simpa using congrFun hr t), Finset.card_univ, if_pos hu]
      · have hempty :
          (Finset.univ.filter fun g : (d : D) → R d => h = Function.update g t u) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro g _ hg
          rw [eq_comm, Function.update_eq_iff] at hg
          exact hu hg.1
        rw [hempty, Finset.card_empty, Nat.cast_zero, if_neg hu]
    rw [hcard]
    by_cases hu : u = h t <;> simp [hu]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (h t)]
  rw [if_pos (Finset.mem_univ _), probOutput_uniformSample (R t), ← mul_assoc,
      ENNReal.inv_mul_cancel, one_mul]
  · simp [Fintype.card_ne_zero]
  · exact ENNReal.natCast_ne_top _

/-- The total answer table obtained by overlaying a dependent query cache on a full table.

Cached coordinates take priority; every uncached coordinate reads the pre-sampled table. -/
@[reducible]
def dependentTableExtending {ι : Type} {spec : OracleSpec ι}
    (cache : spec.QueryCache) (table : OracleReduction.OracleFamily spec) :
    OracleReduction.OracleFamily spec :=
  fun q => (cache q).getD (table q)

/-- Installing a cached answer is a dependent table update. -/
lemma dependentTableExtending_cacheQuery
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    (cache : spec.QueryCache) (table : OracleReduction.OracleFamily spec)
    (q : spec.Domain) (answer : spec.Range q) :
    dependentTableExtending (cache.cacheQuery q answer) table =
      Function.update (dependentTableExtending cache table) q answer := by
  funext q'
  by_cases hq : q' = q
  · subst q'
    simp [dependentTableExtending, QueryCache.cacheQuery]
  · simp [dependentTableExtending, QueryCache.cacheQuery_of_ne _ _ hq,
      Function.update_of_ne hq]

/-- If `q` is uncached, updating the overlaid table is equivalent to updating the full table. -/
lemma dependentTableExtending_update_of_none
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    (cache : spec.QueryCache) (table : OracleReduction.OracleFamily spec)
    {q : spec.Domain} (hcache : cache q = none) (answer : spec.Range q) :
    Function.update (dependentTableExtending cache table) q answer =
      dependentTableExtending cache (Function.update table q answer) := by
  funext q'
  by_cases hq : q' = q
  · subst q'
    simp [dependentTableExtending, hcache]
  · simp [dependentTableExtending, Function.update_of_ne hq]

/-- **Lazy dependent random oracle equals eager full-table sampling.**

This is VCVio's homogeneous `EagerTable` argument lifted to an arbitrary dependent
`OracleSpec`.  Starting with a cache, lazily sampling an uncached query is distributionally
identical to reading the same coordinate of a uniformly sampled full `OracleFamily`; cached
answers override the corresponding full-table coordinate. -/
theorem evalDist_simulateQ_randomOracle_run'_eq_dependentTableExtending
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [Finite spec.Domain] [∀ q, Finite (spec.Range q)] [∀ q, Nonempty (spec.Range q)]
    [∀ q, SampleableType (spec.Range q)]
    [SampleableType (OracleReduction.OracleFamily spec)]
    {α : Type} (oa : OracleComp spec α) (cache : spec.QueryCache) :
    𝒟[(simulateQ randomOracle oa).run' cache] =
      𝒟[do let table ← $ᵗ (OracleReduction.OracleFamily spec);
            pure (evalWithAnswerFn (QueryImpl.ofFn
              (dependentTableExtending cache table)) oa)] := by
  classical
  letI := Fintype.ofFinite spec.Domain
  letI : ∀ q, Fintype (spec.Range q) := fun q => Fintype.ofFinite (spec.Range q)
  haveI : Nonempty (OracleReduction.OracleFamily spec) :=
    ⟨fun q => Classical.arbitrary (spec.Range q)⟩
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      have hlhs : (simulateQ randomOracle (pure a : OracleComp spec α)).run' cache =
          (pure a : ProbComp α) := by
        rw [simulateQ_pure]
        change (fun x => x.1) <$> (pure (a, cache) : ProbComp (α × _)) = pure a
        rw [map_pure]
      rw [hlhs]
      simp only [evalWithAnswerFn_pure]
      symm
      refine evalDist_ext fun x => ?_
      rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (mx := $ᵗ (OracleReduction.OracleFamily spec)) (by simp), one_mul]
  | query_bind q k ih =>
      have hred :
          (simulateQ randomOracle (liftM (spec.query q) >>= k)).run' cache =
            ((randomOracle (spec := spec) q).run cache) >>=
              fun pair : spec.Range q × spec.QueryCache =>
              (simulateQ randomOracle (k pair.1)).run' pair.2 := by
        rw [simulateQ_bind, simulateQ_spec_query]
        change Prod.fst <$> (((randomOracle (spec := spec) q).run cache) >>= fun pair =>
          (simulateQ randomOracle (k pair.1)).run pair.2) = _
        rw [map_bind]
        rfl
      have heval : ∀ table : OracleReduction.OracleFamily spec,
          evalWithAnswerFn (QueryImpl.ofFn (dependentTableExtending cache table))
              (liftM (spec.query q) >>= k) =
            evalWithAnswerFn (QueryImpl.ofFn (dependentTableExtending cache table))
              (k (dependentTableExtending cache table q)) := by
        intro table
        rw [evalWithAnswerFn_bind]
        change evalWithAnswerFn (QueryImpl.ofFn (dependentTableExtending cache table))
          (k (simulateQ (QueryImpl.ofFn (dependentTableExtending cache table))
            (liftM (spec.query q)))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [hred]
      simp_rw [heval]
      rcases hcache : cache q with _ | answer
      · rw [show ((randomOracle (spec := spec) q).run cache) =
            (fun answer => (answer, cache.cacheQuery q answer)) <$> ($ᵗ spec.Range q) from
            QueryImpl.withCaching_run_none _ hcache]
        rw [show (((fun answer => (answer, cache.cacheQuery q answer)) <$> ($ᵗ spec.Range q)) >>=
              fun pair : spec.Range q × spec.QueryCache =>
                (simulateQ randomOracle (k pair.1)).run' pair.2)
              = (($ᵗ spec.Range q) >>= fun answer =>
                (simulateQ randomOracle (k answer)).run' (cache.cacheQuery q answer)) from by
              rw [map_eq_bind_pure_comp]
              simp [bind_assoc]]
        set ψ : OracleReduction.OracleFamily spec → α := fun table =>
          evalWithAnswerFn (QueryImpl.ofFn (dependentTableExtending cache table))
            (k (dependentTableExtending cache table q)) with hψ
        have hfun : ∀ answer : spec.Range q,
            (fun table : OracleReduction.OracleFamily spec =>
              evalWithAnswerFn (QueryImpl.ofFn
                (dependentTableExtending (cache.cacheQuery q answer) table)) (k answer)) =
              fun table : OracleReduction.OracleFamily spec =>
                ψ (Function.update table q answer) := by
          intro answer
          funext table
          simp only [hψ]
          rw [dependentTableExtending_cacheQuery,
            ← dependentTableExtending_update_of_none cache table hcache answer]
          simp only [Function.update_self]
        trans 𝒟[do let answer ← $ᵗ spec.Range q
                    let table ← $ᵗ (OracleReduction.OracleFamily spec)
                    pure (ψ (Function.update table q answer))]
        · rw [evalDist_bind, evalDist_bind]
          refine congrArg _ (funext fun answer => ?_)
          rw [ih answer (cache.cacheQuery q answer), bind_pure_comp, bind_pure_comp, hfun answer]
        · have hmap :
            (do let answer ← $ᵗ spec.Range q
                let table ← $ᵗ (OracleReduction.OracleFamily spec)
                pure (ψ (Function.update table q answer))) =
              ψ <$> (do let answer ← $ᵗ spec.Range q
                        let table ← $ᵗ (OracleReduction.OracleFamily spec)
                        pure (Function.update table q answer)) := by
              simp [map_bind, bind_pure_comp]
          have htable :
            (do let table ← $ᵗ (OracleReduction.OracleFamily spec); pure (ψ table)) =
              ψ <$> ($ᵗ (OracleReduction.OracleFamily spec)) := by
              simp [bind_pure_comp]
          rw [hmap, htable, evalDist_map, evalDist_map,
            evalDist_uniformSample_bind_update_dependent q]
      · rw [show ((randomOracle (spec := spec) q).run cache) =
            (pure (answer, cache) : ProbComp _) from
            QueryImpl.withCaching_run_some _ hcache]
        rw [pure_bind]
        rw [ih answer cache]
        refine congrArg _ ?_
        refine congrArg _ (funext fun table => ?_)
        congr 1
        have hlookup : dependentTableExtending cache table q = answer := by
          simp [dependentTableExtending, hcache]
        rw [hlookup]

/-- Overlaying the empty cache leaves a dependent full table unchanged. -/
lemma dependentTableExtending_empty
    {ι : Type} {spec : OracleSpec ι}
    (table : OracleReduction.OracleFamily spec) :
    dependentTableExtending (∅ : spec.QueryCache) table = table := by
  classical
  funext q
  simp [dependentTableExtending]

/-- **Lazy dependent random oracle equals eager uniform full-table sampling.**

The empty-cache specialization of
`evalDist_simulateQ_randomOracle_run'_eq_dependentTableExtending`. -/
theorem evalDist_simulateQ_randomOracle_run'_empty_eq_dependentUniformTable
    {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [Finite spec.Domain] [∀ q, Finite (spec.Range q)] [∀ q, Nonempty (spec.Range q)]
    [∀ q, SampleableType (spec.Range q)]
    [SampleableType (OracleReduction.OracleFamily spec)]
    {α : Type} (oa : OracleComp spec α) :
    𝒟[(simulateQ randomOracle oa).run' ∅] =
      𝒟[do let table ← $ᵗ (OracleReduction.OracleFamily spec);
            pure (evalWithAnswerFn (QueryImpl.ofFn table) oa)] := by
  rw [evalDist_simulateQ_randomOracle_run'_eq_dependentTableExtending oa ∅]
  refine congrArg _ ?_
  refine congrArg _ (funext fun table => ?_)
  rw [dependentTableExtending_empty]

end OracleComp

namespace OracleReduction

open scoped ENNReal

variable {ι : Type}

/-! ## §3. Probability laws on `OracleDistribution.uniform`

Pointwise marginal at a single query for the uniform full-table distribution.
Lifts through `runWith` are left to downstream game proofs.
-/

section MarginalLaws

variable {spec : OracleSpec ι}

private noncomputable def mapRangeAt {spec : OracleSpec ι} (q : spec.Domain)
    (e : spec.Range q ≃ spec.Range q) : OracleFamily spec ≃ OracleFamily spec :=
  letI : DecidableEq spec.Domain := Classical.typeDecidableEq _
  { toFun := fun g => Function.update g q (e (g q))
    invFun := fun g => Function.update g q (e.symm (g q))
    left_inv := by
      intro g
      funext q'
      by_cases h : q' = q
      · subst q'
        simp [Function.update]
      · simp [Function.update, h]
    right_inv := by
      intro g
      funext q'
      by_cases h : q' = q
      · subst q'
        simp [Function.update]
      · simp [Function.update, h] }

private lemma mapRangeAt_apply_self {spec : OracleSpec ι} (q : spec.Domain)
    (e : spec.Range q ≃ spec.Range q) (g : OracleFamily spec) :
    (mapRangeAt q e g) q = e (g q) := by
  letI : DecidableEq spec.Domain := Classical.typeDecidableEq _
  simp [mapRangeAt, Function.update]

private theorem probOutput_uniform_marginal_eq
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    (y z : spec.Range q) :
    Pr[= y | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] =
      Pr[= z | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] := by
  letI : DecidableEq (spec.Range q) := Classical.typeDecidableEq _
  let e : spec.Range q ≃ spec.Range q := Equiv.swap y z
  let T : OracleFamily spec ≃ OracleFamily spec := mapRangeAt q e
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  change (∑' (x : OracleFamily spec),
      Pr[= x | (OracleDistribution.uniform spec).sample] *
        Pr[= y | (pure (x q) : ProbComp (spec.Range q))]) =
    ∑' (x : OracleFamily spec),
      Pr[= x | (OracleDistribution.uniform spec).sample] *
        Pr[= z | (pure (x q) : ProbComp (spec.Range q))]
  rw [← Equiv.tsum_eq T (fun g =>
    Pr[= g | (OracleDistribution.uniform spec).sample] *
      Pr[= y | (pure (g q) : ProbComp (spec.Range q))])]
  apply tsum_congr
  intro g
  have hsample : Pr[= T g | (OracleDistribution.uniform spec).sample] =
      Pr[= g | (OracleDistribution.uniform spec).sample] := by
    exact SampleableType.probOutput_selectElem_eq (T g) g
  have hpure : Pr[= y | (pure ((T g) q) : ProbComp (spec.Range q))] =
      Pr[= z | (pure (g q) : ProbComp (spec.Range q))] := by
    rw [probOutput_pure, probOutput_pure]
    change (if y = (mapRangeAt q (Equiv.swap y z) g) q then 1 else 0) =
      if z = g q then 1 else 0
    rw [mapRangeAt_apply_self]
    by_cases hz : z = g q
    · have hy : y = (Equiv.swap y z) (g q) := by
        calc
          y = (Equiv.swap y z) z := (Equiv.swap_apply_right y z).symm
          _ = (Equiv.swap y z) (g q) := congrArg (Equiv.swap y z) hz
      rw [if_pos hy, if_pos hz]
    · have hy : y ≠ (Equiv.swap y z) (g q) := by
        intro hy
        have hswap : (Equiv.swap y z) (g q) = y := hy.symm
        rw [Equiv.swap_apply_eq_iff] at hswap
        rw [Equiv.swap_apply_left] at hswap
        exact hz hswap.symm
      rw [if_neg hy, if_neg hz]
  rw [hsample, hpure]

/-- **Level 2.** Marginal at a single query is uniform over the range. -/
theorem probOutput_uniform_marginal
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    [Fintype (spec.Range q)] (y : spec.Range q) :
    Pr[= y | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] =
      (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹ := by
  let M : ProbComp (spec.Range q) := do
    let g ← (OracleDistribution.uniform spec).sample
    pure (g q)
  change Pr[= y | M] = (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹
  have hsum : ∑ z, Pr[= z | M] = 1 := by
    exact sum_probOutput_eq_one probFailure_eq_zero
  have hconst : ∑ _z : spec.Range q, Pr[= y | M] = 1 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro z _hz
    change Pr[= y | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)] =
      Pr[= z | do let g ← (OracleDistribution.uniform spec).sample; pure (g q)]
    exact probOutput_uniform_marginal_eq q y z
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hconst
  rw [mul_comm] at hconst
  exact ENNReal.eq_inv_of_mul_eq_one_left hconst

/-- **Modular pointwise uniform query.** *"Given `g` sampled from `uniform spec`, the
probability that `g q = y` is `1 / |Range q|`."* `g` is the predicate's bound variable,
**not** a do-binding — the surrounding security experiment can keep
`(uniform spec).sample` as an opaque step and apply this lemma at any point that reads
its result via a query. -/
lemma probEvent_uniform_query_eq
    [SampleableType (OracleFamily spec)] (q : spec.Domain)
    [Fintype (spec.Range q)] (y : spec.Range q) :
    Pr[ fun g => g q = y | (OracleDistribution.uniform spec).sample ] =
      (Fintype.card (spec.Range q) : ℝ≥0∞)⁻¹ := by
  rw [← probOutput_uniform_marginal (spec := spec) q y, ← probEvent_eq_eq_probOutput]
  change Pr[ (fun x => x = y) ∘ (fun g => g q) | (OracleDistribution.uniform spec).sample ] =
    Pr[ (· = y) | (OracleDistribution.uniform spec).sample >>=
      pure ∘ (fun g : OracleFamily spec => g q) ]
  rw [probEvent_bind_pure_comp]
  rfl

end MarginalLaws

/-! ## §6. Examples — random-function oracle distributions

This section demonstrates the *random-function* `OracleDistribution` shape — sample a uniform
function-table over a finite spec, then expose it as a deterministic interpreter. All examples
below are instances of `OracleDistribution.uniform`. They cover three reusable shapes:

- `D_ROM` — generic random oracle `Input →ₒ Output` (not DSFS-specific).
- `D_IP`  — uniform random function over `fsChallengeOracle Statement pSpec`. Generic; DSFS uses
  this with a salted statement type at the call sites (see "DSFS mapping" below).
- (concrete `D_Σ` / Hyb2 — illustrated as code sketches; concrete instances live downstream.)

Permutation-carrier distributions (paper `D_𝔖`) do *not* fit this random-function template — they
require `Carrier := Equiv.Perm State` to enforce the bijection invariant. The concrete DSFS
`D_𝔖` lives in `FiatShamir/DuplexSponge/Defs.lean`.

### DSFS Section 5 mapping

- `D_𝔖`  — base IPM. Spec `duplexSpongeChallengeOracle StmtIn U`. Shape:
  `OracleFamily × Equiv.Perm`. Defined in `DuplexSponge/Defs.lean`.
- `D_Σ`  — Hyb1 (encoded). Spec `section58EncodedChallengeOracle StmtIn pSpec δ`.
  Shape: random function. Defined in
  `DuplexSponge/Security/TraceTransform.lean`.
- Eq. 52 — Hyb2 (decoded). Spec `section58DecodedChallengeOracle StmtIn pSpec δ`.
  Shape: random function (this is *not* `D_Σ`). Same file as Hyb1.
- `D_IP` — Hyb3 / Hyb4 (salted). Spec
  `fsChallengeOracle (StmtIn × Salt) pSpec` (paper's pre-encoded `{0,1}^{δ⋆}`; the on-sponge
  `Vector U δ` salt is bridged via `SaltCodec.encode = bin`). Shape: random function.
  Realized at call sites.

The §5.8-specific encoded/decoded challenge oracles currently live in
`Security/TraceTransform.lean`; if they grow theorem-facing uses they may deserve their own
`Defs`-level module. To keep `OracleDistribution.lean` import-light, this file demonstrates only
the *generic* random-function shapes; concrete DSFS instances are produced at the call sites by
partial application of `OracleDistribution.uniform`.
-/

section OracleDistribution.Examples

/-! ### `D_ROM` — random-function constructor. -/

/-- Generic `D_ROM` constructor for any random-function oracle spec:
uniformly sample one deterministic table realization. -/
@[reducible]
def D_ROM {ι : Type} (spec : OracleSpec ι) [SampleableType (OracleFamily spec)] :
    OracleDistribution spec :=
  OracleDistribution.uniform spec

/-! ### `D_IP` — ideal-protocol Fiat-Shamir challenger.

The Fiat-Shamir challenge oracle (`fsChallengeOracle` / `srChallengeOracle`) is keyed by
`(challenge index, statement, prover-prefix)` and returns the round-`i` challenge type.
`D_IP` samples a single deterministic such function.

DSFS Hyb3 / Hyb4 (salted) instantiate `D_IP` with the *salted* statement type
`Statement := StmtIn × Vector U δ`, i.e. `D_IP (StmtIn × Vector U δ) pSpec`. -/

/-- Bridge instance: granular `VCVCompatible` hypotheses on statement, message, and challenge
types suffice to derive `SampleableType (OracleFamily (fsChallengeOracle Statement pSpec))`. -/
noncomputable instance instSampleableTypeFSChallengeOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {Statement : Type}
    [VCVCompatible Statement]
    [∀ i, VCVCompatible (pSpec.Message i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    SampleableType (OracleFamily (ProtocolSpec.fsChallengeOracle Statement pSpec)) := by
  -- `OracleFamily spec = (q : Domain) → spec.Range q` (a dependent Pi over the
  -- finite challenge-indexed domain).  A message in a finite prefix is merely a
  -- message of the original protocol at the corresponding global prover index.
  letI : FinEnum Statement := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum (pSpec.MessagesUpTo i.1.castSucc) := by
    letI : FinEnum (pSpec.MessageIdxUpTo i.1.castSucc) := inferInstance
    letI (j : pSpec.MessageIdxUpTo i.1.castSucc) :
        FinEnum (pSpec.MessageUpTo i.1.castSucc j) := by
      change FinEnum (pSpec.Message ⟨j.1.castLE (by omega), j.2⟩)
      exact VCVCompatible.instFinEnum
    infer_instance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((ProtocolSpec.challengeOracleInterfaceSR Statement pSpec i).Query) := by
    change FinEnum (Statement × pSpec.MessagesUpTo i.1.castSucc)
    infer_instance
  letI : FinEnum ((ProtocolSpec.fsChallengeOracle Statement pSpec).Domain) := inferInstance
  letI (q : (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain) :
      FinEnum ((ProtocolSpec.fsChallengeOracle Statement pSpec).Range q) := by
    change FinEnum (pSpec.Challenge q.1)
    exact VCVCompatible.instFinEnum
  letI (q : (ProtocolSpec.fsChallengeOracle Statement pSpec).Domain) :
      Inhabited ((ProtocolSpec.fsChallengeOracle Statement pSpec).Range q) := by
    change Inhabited (pSpec.Challenge q.1)
    infer_instance
  letI : Nonempty (OracleFamily (ProtocolSpec.fsChallengeOracle Statement pSpec)) :=
    ⟨fun _ => default⟩
  exact SampleableType.ofFintype _

/-- `D_IP` over `fsChallengeOracle Statement pSpec`: uniform random function from prover-prefix
queries to challenges. DSFS Hyb3 / Hyb4 use this with `Statement := StmtIn × Vector U δ`. -/
@[reducible]
noncomputable def D_IP {n : ℕ} (Statement : Type) (pSpec : ProtocolSpec n)
    [VCVCompatible Statement]
    [∀ i, VCVCompatible (pSpec.Message i)]
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleDistribution (ProtocolSpec.fsChallengeOracle Statement pSpec) :=
  D_ROM (spec := ProtocolSpec.fsChallengeOracle Statement pSpec)

/-! ### `D_Σ` — §5.8 encoded-challenge oracle.

Paper `D_Σ` (Hyb1) has domain
`(i : pSpec.ChallengeIdx) × (StmtIn × Vector U δ × List <prover-prefix entries>)`
and range `Vector U (challengeSize i)`.

The realization lives at the call site (e.g. `FiatShamir/DuplexSponge/Security/...`):
```
def DΣ_encoded {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : ℕ) … :
    OracleDistribution (section58EncodedChallengeOracle StmtIn pSpec δ) :=
  OracleDistribution.uniform _
```
The pattern is identical to `D_ROM` / `D_IP`; only the underlying spec differs. -/

/-! ### Hyb2 decoded challenge distribution.

Hyb2 samples `e_i` with the same input domain as `D_Σ`, but range `pSpec.Challenge i`
(`𝓜_{V,i}` in the paper). This is not `D_Σ`; it is the decoded verifier-message oracle family
from Eq. (52). At the concrete DSFS call site:
```
def DHyb2_decoded {n : ℕ} (StmtIn : Type) (pSpec : ProtocolSpec n) (δ : ℕ) … :
    OracleDistribution (section58DecodedChallengeOracle StmtIn pSpec δ) :=
  OracleDistribution.uniform _
```
-/

end OracleDistribution.Examples

/-! ## §7. Probes — FinEnum-route inference for `SampleableType (OracleFamily spec)`

These probes verify that `[FinEnum ι] + [∀ q, FinEnum (spec.Range q)] + Nonempty` is enough
for typeclass synthesis to find `SampleableType (OracleFamily spec)` via
`Pi.finEnum` ∘ `FinEnum.SampleableType`. If they typecheck, the FinEnum route is free.
-/

section BridgeProbes

noncomputable def VCVCompatible.toFinEnum_aux {α : Type} [VCVCompatible α] : FinEnum α where
  card := Fintype.card α
  equiv := Fintype.equivFin α
  decEq := inferInstance

-- rootVectorEquivFin : Vector α n ≃ (Fin n → α), direction: from Vector to Pi
noncomputable def Vector.toFinEnum_aux {α : Type} {n : ℕ} [FinEnum α] : FinEnum (Vector α n) :=
  FinEnum.ofEquiv _ Equiv.rootVectorEquivFin

-- Composite probe 1: hash oracle family
noncomputable example {StartType U : Type} (n : ℕ) [VCVCompatible StartType] [VCVCompatible U] :
    SampleableType (OracleFamily (StartType →ₒ Vector U n)) := by
  letI : FinEnum StartType := VCVCompatible.toFinEnum_aux
  letI : FinEnum U := VCVCompatible.toFinEnum_aux
  letI : FinEnum (Vector U n) := Vector.toFinEnum_aux
  infer_instance

-- Composite probe 2: Equiv.Perm of Vector (manual FinEnum construction for Perm)
noncomputable example {U : Type} (n : ℕ) [VCVCompatible U] :
    SampleableType (Equiv.Perm (Vector U n)) := by
  letI : FinEnum U := VCVCompatible.toFinEnum_aux
  letI : FinEnum (Vector U n) := Vector.toFinEnum_aux
  -- FinEnum → Fintype + DecidableEq on Vector U n
  letI : Fintype (Vector U n) := inferInstance
  letI : DecidableEq (Vector U n) := inferInstance
  -- Fintype + DecidableEq on Perm
  letI : Fintype (Equiv.Perm (Vector U n)) := inferInstance
  letI : DecidableEq (Equiv.Perm (Vector U n)) := inferInstance
  -- Build FinEnum (Perm ...) noncomputably
  letI : FinEnum (Equiv.Perm (Vector U n)) :=
    { card := Fintype.card (Equiv.Perm (Vector U n))
      equiv := Fintype.equivFin _
      decEq := inferInstance }
  letI : Nonempty (Equiv.Perm (Vector U n)) := ⟨Equiv.refl _⟩
  infer_instance

end BridgeProbes

end OracleReduction

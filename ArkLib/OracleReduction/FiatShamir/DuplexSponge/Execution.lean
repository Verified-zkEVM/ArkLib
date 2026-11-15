/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
public import ArkLib.VCVioStaging.OracleComp.Constructions.RandomPermutation.Basic

/-!
# Lazy oracle execution for DSFS

`lazyRealImpl` interprets the ambient and public sponge queries using a shared hash cache and
compatible permutation table. Use it with `simulateQ` across the whole reduction execution,
starting from `emptyLazyRealState`, so prover and verifier observe the same oracle realization.

This is a probabilistic semantics, not an efficient executable random-sampling backend:
`RandomPermutation.lazyImpl` samples a compatible permutation completion. The exact
comparison with eager ideal-oracle sampling is proved in `Security.KeyLemma.Hyb0Hyb1.LazyReal`.
-/

@[expose] public section

open OracleComp OracleSpec OracleComp.RandomPermutation

namespace DuplexSpongeFS.Execution

noncomputable section

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} [VCVCompatible StmtIn]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]

/-- The `h` component of the DSFS query surface: `𝕏 →ₒ Σ^c` ([CO25, Definition 4.3]). -/
abbrev DSHashSpec (StmtIn U : Type) [SpongeUnit U] : OracleSpec StmtIn :=
  StmtIn →ₒ Vector U SpongeSize.C

/-- The lazy permutation table: `RandomPermutation`'s compatible forward-edge trace over sponge
states.  A forward query `p(s)` and a backward query `p⁻¹(s')` both record the same normalized
edge, so one list represents the dual table. -/
abbrev DSPermTrace (U : Type) [SpongeUnit U] [VCVCompatible U] : Type :=
  Trace (CanonicalSpongeState U)

/-! ### The joint lazy carrier -/

/-- The lazy real-world carrier: a partial hash cache together with the dual permutation
table.  Replaces the eagerly sampled `𝒟_𝔖` realization `(h, p)`. -/
structure LazyRealState (StmtIn U : Type) [SpongeUnit U] [SpongeSize] [VCVCompatible U] where
  /-- Partial hash cache. -/
  hashCache : (DSHashSpec StmtIn U).QueryCache
  /-- Dual permutation table. -/
  permTrace : DSPermTrace U

/-- The initial lazy state: nothing cached, no permutation edge constrained. -/
def emptyLazyRealState : LazyRealState StmtIn U := ⟨∅, emptyTrace⟩

/-- **The lazily sampling real-world handler.**

* ambient `oSpec` queries → `oSpecImpl`, carrier untouched;
* hash query `h(𝕩)` → the cached capacity value, or a fresh uniform `Σ^c` value which is then
  inserted into the cache;
* permutation query `p(s)` / `p⁻¹(s')` → `RandomPermutation.lazyImpl`, i.e. a value drawn
  from the uniform completion of the current dual table, with the normalized edge recorded.
  Recorded answers are forced; fresh answers are uniform among the states still unused in
  the requested direction. -/
def lazyRealImpl (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl (oSpec + duplexSpongeOracle StmtIn U)
      (StateT (LazyRealState StmtIn U) ProbComp)
  | .inl q => StateT.mk fun s => (fun r => (r, s)) <$> oSpecImpl q
  | .inr (.inl qh) => StateT.mk fun s =>
      match s.hashCache qh with
      | some v => pure (v, s)
      | none =>
          (fun v => (v, ⟨s.hashCache.cacheQuery qh v, s.permTrace⟩)) <$>
            (uniformSample (Vector U SpongeSize.C) (h := VCVCompatible.toSampleableType))
  | .inr (.inr qp) => StateT.mk fun s =>
      (fun rt => (rt.1, ⟨s.hashCache, rt.2⟩)) <$> (lazyImpl qp).run s.permTrace

section SlotLemmas

variable (oSpecImpl : QueryImpl oSpec ProbComp)

/-- Ambient slot: defer to `oSpecImpl`, carrier untouched. -/
lemma lazyRealImpl_run_oSpec (q : ι) (s : LazyRealState StmtIn U) :
    (lazyRealImpl (StmtIn := StmtIn) (U := U) oSpecImpl (.inl q)).run s
      = (do let r ← oSpecImpl q; pure (r, s)) := by
  change (fun r => (r, s)) <$> oSpecImpl q = _
  rw [map_eq_bind_pure_comp]
  rfl

/-- Hash slot, cache hit: deterministic, carrier untouched. -/
lemma lazyRealImpl_run_hash_hit (qh : StmtIn) (s : LazyRealState StmtIn U)
    (v : Vector U SpongeSize.C) (hc : s.hashCache qh = some v) :
    (lazyRealImpl (U := U) oSpecImpl (.inr (.inl qh))).run s = pure (v, s) := by
  change (match s.hashCache qh with
    | some v => pure (v, s)
    | none => _) = _
  rw [hc]

/-- Hash slot, cache miss: one fresh uniform `Σ^c` value, inserted into the cache. -/
lemma lazyRealImpl_run_hash_miss (qh : StmtIn) (s : LazyRealState StmtIn U)
    (hc : s.hashCache qh = none) :
    (lazyRealImpl (U := U) oSpecImpl (.inr (.inl qh))).run s
      = (do
          let v ← uniformSample (Vector U SpongeSize.C) (h := VCVCompatible.toSampleableType)
          pure (v, (⟨s.hashCache.cacheQuery qh v, s.permTrace⟩ :
            LazyRealState StmtIn U))) := by
  change (match s.hashCache qh with
    | some v => pure (v, s)
    | none => _) = _
  rw [hc]
  change (fun v => (v, (⟨s.hashCache.cacheQuery qh v, s.permTrace⟩ :
    LazyRealState StmtIn U))) <$> _ = _
  rw [map_eq_bind_pure_comp]
  rfl

/-- Permutation slot: `RandomPermutation`'s lazy step on the dual table, hash cache untouched. -/
lemma lazyRealImpl_run_perm (qp : (permutationOracle (CanonicalSpongeState U)).Domain)
    (s : LazyRealState StmtIn U) :
    (lazyRealImpl (StmtIn := StmtIn) oSpecImpl (.inr (.inr qp))).run s
      = (do
          let rt ← (lazyImpl qp).run s.permTrace
          pure (rt.1, (⟨s.hashCache, rt.2⟩ : LazyRealState StmtIn U))) := by
  change (fun rt => (rt.1, (⟨s.hashCache, rt.2⟩ : LazyRealState StmtIn U))) <$>
    (lazyImpl qp).run s.permTrace = _
  rw [map_eq_bind_pure_comp]
  rfl

end SlotLemmas

/-! ## Permutation completion laws

These laws expose the underlying compatible-completion sampler for coupling proofs. -/

section StepLaws

open OracleComp.PermutationConditioning

variable (oSpecImpl : QueryImpl oSpec ProbComp)

/-- **State ↔ query mirror for the permutation slot.**  A permutation query is exactly: draw a
uniform completion of the current dual table, answer in the requested direction, and append the
normalized edge.  The hash cache is untouched. -/
theorem lazyRealImpl_run_perm_eq (qp : (permutationOracle (CanonicalSpongeState U)).Domain)
    (s : LazyRealState StmtIn U) :
    (lazyRealImpl oSpecImpl (.inr (.inr qp))).run s
      = (do
          let p ← sampleExtensions s.permTrace
          pure (reply p.1 qp,
            (⟨s.hashCache, record s.permTrace qp p⟩ : LazyRealState StmtIn U))) := by
  rw [lazyRealImpl_run_perm]
  change (do
      let rt ← ((fun p : Extensions s.permTrace.edges =>
        (reply p.1 qp, record s.permTrace qp p)) <$> sampleExtensions s.permTrace)
      pure (rt.1, (⟨s.hashCache, rt.2⟩ : LazyRealState StmtIn U))) = _
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

omit [VCVCompatible StmtIn] in
/-- The edge appended by a permutation step is the normalized `(input, output)` pair of that very
query and its answer — the one-step form of the "the table mirrors the DS query log" invariant. -/
theorem lazyRealImpl_run_perm_edges (qp : (permutationOracle (CanonicalSpongeState U)).Domain)
    (s : LazyRealState StmtIn U) (p : Extensions s.permTrace.edges) :
    (record s.permTrace qp p).edges = edge qp (reply p.1 qp) :: s.permTrace.edges := rfl

end StepLaws

end

end DuplexSpongeFS.Execution

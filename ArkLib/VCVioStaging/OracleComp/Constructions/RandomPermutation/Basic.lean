/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Orrù
-/
module

public import ArkLib.Data.Hash.DuplexSponge
public import
  VCVio.OracleComp.Constructions.RandomPermutation.Conditioning
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Adaptive lazy sampling of a permutation

A compatible list of forward edges records the answers to both forward and inverse queries.
The lazy oracle samples a uniform compatible completion at each call and records the new edge.
At termination another uniform compatible completion is installed. The eager/lazy bridge keeps
this entire final permutation, not just the answers exposed during execution.

All handlers are `ProbComp`-valued. Equalities of laws are stated for `𝒟[·]` under the discrete
σ-algebra on the observed outputs. Statements that sample one uniform eager permutation take its
sampler as an instance argument; `SampleableType.ofFintype` supplies one.
-/

@[expose] public section

noncomputable section

open OracleSpec OracleComp MeasureTheory

namespace OracleComp.RandomPermutation

open PermutationConditioning OracleComp.UniformPreimage

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The two directions use one and the same underlying permutation. -/
def reply (p : Equiv.Perm α) : QueryImpl (permutationOracle α) Id
  | .inl x => p x
  | .inr y => p.symm y

/-- Normalize either query direction to a forward edge. -/
def edge (q : (permutationOracle α).Domain) : (permutationOracle α).Range q → α × α :=
  match q with
  | .inl x => fun y => (x, y)
  | .inr y => fun x => (x, y)

omit [Fintype α] [DecidableEq α] in
/-- An answer is correct exactly when its normalized edge belongs to the permutation. -/
theorem reply_eq_iff (p : Equiv.Perm α) (q : (permutationOracle α).Domain)
    (r : (permutationOracle α).Range q) :
    reply p q = r ↔ p (edge q r).1 = (edge q r).2 := by
  cases q with
  | inl x => rfl
  | inr y => exact p.symm_apply_eq.trans eq_comm

/-- A trace is compatible if it admits at least one permutation completion. Repeated edges
are allowed, so repeated or cross-direction queries need no special-case semantics. -/
structure Trace (α : Type) where
  edges : List (α × α)
  compatible : Nonempty (Extensions edges)

/-- No constraints have been exposed initially. This also works for the empty state type. -/
def emptyTrace : Trace α := ⟨[], ⟨⟨Equiv.refl α, by simp⟩⟩⟩

/-- Recording an answer from a compatible completion preserves compatibility. -/
def record (t : Trace α) (q : (permutationOracle α).Domain) (p : Extensions t.edges) :
    Trace α :=
  ⟨edge q (reply p.1 q) :: t.edges, ⟨⟨p.1, by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (reply_eq_iff p.1 q _).mp rfl
    · exact p.2 e he⟩⟩⟩

omit [Fintype α] [DecidableEq α] in
/-- **The dual table is a partial function.**  Compatibility (`Trace.compatible`) is exactly the
statement that some permutation realizes every recorded edge, so a recorded input determines its
output.  This is an invariant *by construction*: no reachability induction is needed. -/
theorem traceEdges_functional (t : Trace α) {x y y' : α}
    (h : (x, y) ∈ t.edges) (h' : (x, y') ∈ t.edges) : y = y' := by
  obtain ⟨p⟩ := t.compatible
  exact (p.2 (x, y) h).symm.trans (p.2 (x, y') h')

omit [Fintype α] [DecidableEq α] in
/-- **The dual table is a partial injection.**  Dual of `traceEdges_functional`: a recorded output
determines its input, so the backward direction is a partial function too. -/
theorem traceEdges_injective (t : Trace α) {x x' y : α}
    (h : (x, y) ∈ t.edges) (h' : (x', y) ∈ t.edges) : x = x' := by
  obtain ⟨p⟩ := t.compatible
  exact p.1.injective ((p.2 (x, y) h).trans (p.2 (x', y) h').symm)

omit [Fintype α] [DecidableEq α] in
/-- Every completion of a trace answers a recorded forward query by the recorded output. -/
theorem reply_eq_of_mem_edges_forward (t : Trace α) {x y : α} (h : (x, y) ∈ t.edges)
    (p : Extensions t.edges) : reply p.1 (Sum.inl x) = y := p.2 (x, y) h

omit [Fintype α] [DecidableEq α] in
/-- Every completion of a trace answers a recorded backward query by the recorded input. -/
theorem reply_eq_of_mem_edges_inverse (t : Trace α) {x y : α} (h : (x, y) ∈ t.edges)
    (p : Extensions t.edges) : reply p.1 (Sum.inr y) = x :=
  p.1.symm_apply_eq.mpr (p.2 (x, y) h).symm

private def observation (t : Trace α) (q : (permutationOracle α).Domain) :=
  Set.rangeFactorization (fun p : Extensions t.edges => reply p.1 q)

omit [Fintype α] [DecidableEq α] in
private theorem observation_surjective (t : Trace α) (q : (permutationOracle α).Domain) :
    Function.Surjective (observation t q) := Set.rangeFactorization_surjective

private def observationFiberEquiv (t : Trace α) (q : (permutationOracle α).Domain)
    (a : Set.range (fun p : Extensions t.edges => reply p.1 q)) :
    OracleComp.UniformPreimage.Preimage (observation t q) a ≃
      Extensions (edge q a.1 :: t.edges) where
  toFun p := ⟨p.1.1, by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact (reply_eq_iff p.1.1 q a.1).mp (congrArg Subtype.val p.2)
    · exact p.1.2 e he⟩
  invFun p := ⟨⟨p.1, fun e he => p.2 e (List.mem_cons_of_mem _ he)⟩, by
    apply Subtype.ext
    exact (reply_eq_iff p.1 q a.1).mpr (p.2 _ (List.mem_cons_self ..))⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem map_observationFiber (t : Trace α) (q : (permutationOracle α).Domain)
    (a : Set.range (fun p : Extensions t.edges => reply p.1 q))
    (ha : Nonempty (Extensions (edge q a.1 :: t.edges))) :
    (letI : MeasurableSpace (Equiv.Perm α) := ⊤
    𝒟[Subtype.val <$> @OracleComp.UniformPreimage.sampleUniformPreimage _ _ (Classical.decEq _) _
      (observation t q) a
        (OracleComp.UniformPreimage.preimage_nonempty (observation t q)
          (observation_surjective t q) a)] =
    𝒟[Subtype.val <$> uniformExtensions (edge q a.1 :: t.edges) ha]) := by
  classical
  let : MeasurableSpace (Equiv.Perm α) := ⊤
  let : MeasurableSpace (Extensions (edge q a.1 :: t.edges)) := ⊤
  let _ : DecidableEq (Set.range (fun p : Extensions t.edges => reply p.1 q)) :=
    Classical.decEq _
  let _ := OracleComp.UniformPreimage.preimage_nonempty (observation t q)
    (observation_surjective t q) a
  let _ : SampleableType (OracleComp.UniformPreimage.Preimage (observation t q) a) :=
    SampleableType.ofFintype _
  let _ := ha
  let _ := SampleableType.ofFintype (Extensions (edge q a.1 :: t.edges))
  have hmap := ((SampleableType.map_uniformSample_evalDistEq_of_bijective
      (observationFiberEquiv t q a).bijective).map
    (Subtype.val : Extensions (edge q a.1 :: t.edges) → Equiv.Perm α)).evalDist_eq
  rw [Functor.map_map] at hmap
  change 𝒟[Subtype.val <$> Subtype.val <$>
    ($ᵗ (OracleComp.UniformPreimage.Preimage (observation t q) a))] = _
  rw [Functor.map_map]
  exact hmap

/-- One-step disintegration, retaining both the answer and the entire installed permutation.
It holds for arbitrary forward/inverse queries, including repeated and adaptive queries. -/
theorem bind_uniformExtensions_record (t : Trace α) (q : (permutationOracle α).Domain)
    {β : Type} [MeasurableSpace β]
    (k : (permutationOracle α).Range q → Equiv.Perm α → ProbComp β) :
    𝒟[uniformExtensions t.edges t.compatible >>= fun p =>
      uniformExtensions (record t q p).edges (record t q p).compatible >>=
        fun p' => k (reply p.1 q) p'.1] =
    𝒟[uniformExtensions t.edges t.compatible >>= fun p => k (reply p.1 q) p.1] := by
  classical
  let _ : DecidableEq (Set.range (fun p : Extensions t.edges => reply p.1 q)) :=
    Classical.decEq _
  let _ := t.compatible
  let _ := SampleableType.ofFintype (Extensions t.edges)
  have h := bind_uniform_fiber_observe (observation t q)
    (fun a p => k a.1 p.1)
  refine Eq.trans ?_ h
  refine evalDist_bind_congr _ _ _ fun p => ?_
  let : MeasurableSpace (Equiv.Perm α) := ⊤
  have hm := ((evalDistEq_iff_evalDist_eq.mpr
    (map_observationFiber t q (observation t q p) (record t q p).compatible)).bind_left
    (k (reply p.1 q))).evalDist_eq
  simp only [bind_map_left] at hm
  exact hm.symm

/-- Uniform sampling among permutations compatible with a recorded trace.
This uses the abstract finite sampler; it is not an efficient random-sampling backend. -/
def sampleExtensions (t : Trace α) : ProbComp (Extensions t.edges) :=
  uniformExtensions t.edges t.compatible

/-- The actual lazy oracle: draw a uniform compatible completion, answer in the requested
direction, and append the normalized edge. No freshness premise is required. -/
def lazyImpl : QueryImpl (permutationOracle α) (StateT (Trace α) ProbComp) :=
  fun q => StateT.mk fun t =>
    (fun p => (reply p.1 q, record t q p)) <$> sampleExtensions t

/-- The uniform completion of the empty trace, observed through a continuation, is one uniform
permutation. -/
theorem uniformExtensions_empty_bind {γ : Type} [MeasurableSpace γ]
    [SampleableType (Equiv.Perm α)] (ht : Nonempty (Extensions ([] : List (α × α))))
    (k : Equiv.Perm α → ProbComp γ) :
    𝒟[uniformExtensions [] ht >>= fun p => k p.1] = 𝒟[($ᵗ (Equiv.Perm α)) >>= k] := by
  let _ := ht
  let _ := SampleableType.ofFintype (Extensions ([] : List (α × α)))
  have h := ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (f := (Subtype.val : Extensions ([] : List (α × α)) → Equiv.Perm α))
    ⟨Subtype.val_injective, fun p => ⟨⟨p, by simp⟩, rfl⟩⟩).bind_left k).evalDist_eq
  rw [bind_map_left] at h
  exact h

section Auxiliary

variable {ι : Type} {spec : OracleSpec ι}

/-- Add an auxiliary probabilistic oracle (in particular, private randomness) without altering
the permutation trace. Its queries may be interleaved adaptively with either direction. -/
def lazyImplWith (aux : QueryImpl spec ProbComp) :
    QueryImpl (permutationOracle α + spec) (StateT (Trace α) ProbComp)
  | .inl q => lazyImpl q
  | .inr q => StateT.mk fun t => (fun r => (r, t)) <$> aux q

/-- The same auxiliary oracle alongside one fixed permutation. -/
def eagerImplWith (aux : QueryImpl spec ProbComp) (p : Equiv.Perm α) :
    QueryImpl (permutationOracle α + spec) (StateT (List (α × α)) ProbComp)
  | .inl q => StateT.mk fun t => pure (reply p q, edge q (reply p q) :: t)
  | .inr q => StateT.mk fun t => (fun r => (r, t)) <$> aux q

/-- Eager execution, with auxiliary randomness, retaining the final edge trace. -/
def eagerRunWith (aux : QueryImpl spec ProbComp) (p : Equiv.Perm α) {β : Type}
    (oa : OracleComp (permutationOracle α + spec) β) (t : List (α × α)) :
    ProbComp (β × List (α × α)) := (simulateQ (eagerImplWith aux p) oa).run t

/-- Lazy execution with auxiliary randomness and final uniform completion installation. -/
def lazyRunWith (aux : QueryImpl spec ProbComp) {β : Type}
    (oa : OracleComp (permutationOracle α + spec) β) (t : Trace α) :
    ProbComp ((β × List (α × α)) × Equiv.Perm α) :=
  (simulateQ (lazyImplWith aux) oa).run t >>= fun bt =>
    uniformExtensions bt.2.edges bt.2.compatible >>= fun p =>
      pure ((bt.1, bt.2.edges), p.1)

/-- Exact adaptive eager/lazy equality in the presence of an auxiliary probabilistic oracle.
No independence is assumed for exposed answers; only the sampler specified by the handlers is
used. The whole final permutation remains in the joint result. -/
theorem lazyRunWith_eq_eagerRunWith (aux : QueryImpl spec ProbComp) {β : Type}
    (oa : OracleComp (permutationOracle α + spec) β) (t : Trace α) :
    (letI : MeasurableSpace ((β × List (α × α)) × Equiv.Perm α) := ⊤
    𝒟[lazyRunWith aux oa t] = 𝒟[uniformExtensions t.edges t.compatible >>=
      fun p => (fun z => (z, p.1)) <$> eagerRunWith aux p.1 oa t.edges]) := by
  let : MeasurableSpace ((β × List (α × α)) × Equiv.Perm α) := ⊤
  induction oa using OracleComp.inductionOn generalizing t with
  | pure b =>
    simp only [lazyRunWith, eagerRunWith, simulateQ_pure, StateT.run_pure, pure_bind,
      map_pure]
  | query_bind q f ih =>
    cases q with
    | inl q =>
      have hlazy : lazyRunWith aux
          ((liftM (OracleSpec.query (Sum.inl q)) :
            OracleComp (permutationOracle α + spec) _) >>= f) t =
          uniformExtensions t.edges t.compatible >>= fun p =>
            lazyRunWith aux (f (reply p.1 q)) (record t q p) := by
        simp only [lazyRunWith, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
          lazyImplWith, lazyImpl, sampleExtensions, StateT.run_mk, bind_map_left, bind_assoc]
      rw [hlazy, evalDist_bind_congr _ _ _ fun p => ih (reply p.1 q) (record t q p)]
      refine (bind_uniformExtensions_record t q (fun r p =>
        (fun z => (z, p)) <$> eagerRunWith aux p (f r) (edge q r :: t.edges))).trans ?_
      refine evalDist_bind_congr _ _ _ fun p => ?_
      simp only [eagerRunWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        eagerImplWith, StateT.run_mk, pure_bind]
    | inr q =>
      have hlazy : lazyRunWith aux
          ((liftM (OracleSpec.query (Sum.inr q)) :
            OracleComp (permutationOracle α + spec) _) >>= f) t =
          aux q >>= fun r => lazyRunWith aux (f r) t := by
        simp only [lazyRunWith, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
          lazyImplWith, StateT.run_mk, bind_map_left, bind_assoc]
        rfl
      rw [hlazy]
      refine (evalDist_bind_congr _ _ _ fun r => ih r t).trans ?_
      refine (OracleComp.evalDist_bind_bind_swap (aux q)
        (uniformExtensions t.edges t.compatible) _).trans ?_
      refine evalDist_bind_congr _ _ _ fun p => ?_
      simp only [eagerRunWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        eagerImplWith, StateT.run_mk, bind_map_left, map_bind]
      rfl

/-- Empty-trace specialization: one uniform eager permutation versus the concrete lazy oracle,
allowing adaptively interleaved private random choices. -/
theorem lazyRunWith_empty_eq_uniform [SampleableType (Equiv.Perm α)]
    (aux : QueryImpl spec ProbComp) {β : Type}
    (oa : OracleComp (permutationOracle α + spec) β) :
    (letI : MeasurableSpace ((β × List (α × α)) × Equiv.Perm α) := ⊤
    𝒟[lazyRunWith aux oa emptyTrace] = 𝒟[($ᵗ (Equiv.Perm α)) >>=
      fun p => (fun z => (z, p)) <$> eagerRunWith aux p oa []]) := by
  let : MeasurableSpace ((β × List (α × α)) × Equiv.Perm α) := ⊤
  rw [lazyRunWith_eq_eagerRunWith]
  exact uniformExtensions_empty_bind _ (fun p => (fun z => (z, p)) <$> eagerRunWith aux p oa [])

end Auxiliary

/-! ## Explicit fresh-answer samplers -/

/-- Record a fresh input/output pair. Every such pair has a compatible completion. -/
def recordFresh (t : Trace α) (x : UnusedInputs t.edges) (y : UnusedOutputs t.edges) :
    Trace α := ⟨(x.1, y.1) :: t.edges, extensions_cons_nonempty t.edges x y t.compatible⟩

/-- A fresh forward query is exactly a uniform unused-output draw, with the edge then recorded.
This equality concerns the actual handler, including its state update. -/
theorem lazyImpl_forward_fresh (t : Trace α) (x : UnusedInputs t.edges) :
    (letI : MeasurableSpace (α × Trace α) := ⊤
    letI : MeasurableSpace ((permutationOracle α).Range (.inl x.1) × Trace α) := ⊤;
    𝒟[(lazyImpl (.inl x.1)).run t] =
      𝒟[(fun y => (y.1, recordFresh t x y)) <$> uniformUnusedOutputs t.edges x t.compatible]) := by
  let : MeasurableSpace (α × Trace α) := ⊤
  let : MeasurableSpace ((permutationOracle α).Range (.inl x.1) × Trace α) := ⊤
  have h := ((evalDistEq_iff_evalDist_eq.mpr
    (map_answer_uniformExtensions t.edges x t.compatible)).map
    (fun y => (y.1, recordFresh t x y))).evalDist_eq
  rw [Functor.map_map] at h
  exact h

/-- The unused output space of the reversed trace is the original unused input space. -/
def reversedUnusedEquiv (t : List (α × α)) :
    UnusedOutputs (t.map Prod.swap) ≃ UnusedInputs t where
  toFun x := ⟨x.1, fun e he => x.2 e.swap (List.mem_map.mpr ⟨e, he, rfl⟩)⟩
  invFun x := ⟨x.1, by
    intro e he
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp he
    exact x.2 original horiginal⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A fresh inverse query as a fresh forward query to the reversed trace. -/
def reversedInput (t : Trace α) (y : UnusedOutputs t.edges) :
    UnusedInputs (t.edges.map Prod.swap) := ⟨y.1, by
  intro e he
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp he
  exact y.2 original horiginal⟩

/-- A fresh inverse answer must be an unused input. -/
def inverseAnswer (t : Trace α) (y : UnusedOutputs t.edges) (p : Extensions t.edges) :
    UnusedInputs t.edges :=
  reversedUnusedEquiv t.edges
    (answer (t.edges.map Prod.swap) (reversedInput t y) (inverseExtensionsEquiv t.edges p))

/-- Uniform sampling of the inputs still available to a fresh inverse query. -/
def uniformUnusedInputs (t : Trace α) (y : UnusedOutputs t.edges) :
    ProbComp (UnusedInputs t.edges) :=
  letI := t.compatible.map (inverseAnswer t y)
  letI := SampleableType.ofFintype (UnusedInputs t.edges)
  $ᵗ (UnusedInputs t.edges)

/-- A uniform compatible permutation answers a fresh inverse query with a uniform unused input. -/
theorem map_inverseAnswer_uniformExtensions (t : Trace α) (y : UnusedOutputs t.edges) :
    (letI : MeasurableSpace (UnusedInputs t.edges) := ⊤
    𝒟[inverseAnswer t y <$> uniformExtensions t.edges t.compatible] =
      𝒟[uniformUnusedInputs t y]) := by
  let : MeasurableSpace (UnusedInputs t.edges) := ⊤
  let : MeasurableSpace (UnusedOutputs (t.edges.map Prod.swap)) := ⊤
  let : MeasurableSpace (Extensions (t.edges.map Prod.swap)) := ⊤
  let _ := t.compatible.map (inverseAnswer t y)
  let _ := SampleableType.ofFintype (UnusedInputs t.edges)
  let ht := t.compatible.map (inverseExtensionsEquiv t.edges)
  let _ := unusedOutputs_nonempty (t.edges.map Prod.swap) (reversedInput t y) ht
  let _ := SampleableType.ofFintype (UnusedOutputs (t.edges.map Prod.swap))
  calc
    _ = 𝒟[(reversedUnusedEquiv t.edges ∘ answer (t.edges.map Prod.swap) (reversedInput t y)) <$>
        (inverseExtensionsEquiv t.edges <$> uniformExtensions t.edges t.compatible)] := by
      rw [Functor.map_map]
      rfl
    _ = 𝒟[reversedUnusedEquiv t.edges <$> (answer (t.edges.map Prod.swap) (reversedInput t y) <$>
        uniformExtensions (t.edges.map Prod.swap) ht)] := by
      rw [Functor.map_map _ _ (uniformExtensions (t.edges.map Prod.swap) ht)]
      exact ((evalDistEq_iff_evalDist_eq.mpr
        (map_inverse_uniformExtensions t.edges t.compatible)).map
        (reversedUnusedEquiv t.edges ∘
          answer (t.edges.map Prod.swap) (reversedInput t y))).evalDist_eq
    _ = 𝒟[reversedUnusedEquiv t.edges <$>
        uniformUnusedOutputs (t.edges.map Prod.swap) (reversedInput t y) ht] :=
      ((evalDistEq_iff_evalDist_eq.mpr
        (map_answer_uniformExtensions (t.edges.map Prod.swap) (reversedInput t y) ht)).map
          _).evalDist_eq
    _ = _ := (SampleableType.map_uniformSample_evalDistEq_of_bijective
      (reversedUnusedEquiv t.edges).bijective).evalDist_eq

/-- A fresh inverse query is exactly a uniform unused-input draw, with the forward edge recorded. -/
theorem lazyImpl_inverse_fresh (t : Trace α) (y : UnusedOutputs t.edges) :
    (letI : MeasurableSpace (α × Trace α) := ⊤
    letI : MeasurableSpace ((permutationOracle α).Range (.inr y.1) × Trace α) := ⊤;
    𝒟[(lazyImpl (.inr y.1)).run t] =
      𝒟[(fun x => (x.1, recordFresh t x y)) <$> uniformUnusedInputs t y]) := by
  let : MeasurableSpace (α × Trace α) := ⊤
  let : MeasurableSpace ((permutationOracle α).Range (.inr y.1) × Trace α) := ⊤
  have h := ((evalDistEq_iff_evalDist_eq.mpr (map_inverseAnswer_uniformExtensions t y)).map
    (fun x => (x.1, recordFresh t x y))).evalDist_eq
  rw [Functor.map_map] at h
  exact h

end OracleComp.RandomPermutation

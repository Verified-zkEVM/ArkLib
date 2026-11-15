/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.Data.Hash.DuplexSponge
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Recovering salts from a capacity forest

This is the finite combinatorial ingredient of the long-salt bound in the
Hybrid 0--1 analysis. A fixed permutation trace labels directed capacity edges with the
rate segment of their input. If the underlying graph is acyclic, no edge is traversable
in both directions, and each capacity edge has a unique rate label, a root and terminal
state determine at most one absorbed salt of a fixed length.

`MatchesSalt` records whole input-rate blocks along a trace walk followed by a prefix of
the terminal rate segment. It handles a zero-length salt and a partial final block without
padding the salt. The prover message following the salt is a fixed parameter. This relation
forgets unused rate coordinates, so it is an overapproximation suitable for a guessing bound.
Connecting an operational sponge trace to this relation is a separate refinement obligation.

Neither a unique-salt hypothesis nor independence of fresh permutation capacities is assumed.
The graph hypotheses must be established from the permutation trace's capacity freshness event.
-/

@[expose] public section

namespace DuplexSpongeFS.ZeroKnowledge.SaltForest

open SimpleGraph

section DirectedWalks

variable {C : Type*} {G : SimpleGraph C}

/-- A graph walk follows a directed relation at every step. -/
def Directed (step : C → C → Prop) : {a b : C} → G.Walk a b → Prop
  | _, _, .nil => True
  | a, _, .cons (v := b) _ tail => step a b ∧ Directed step tail

/-- In an acyclic undirected graph, a walk following an asymmetric orientation is a path.
The asymmetry hypothesis excludes immediate backtracking; acyclicity excludes all other repeats. -/
theorem directed_isPath (hForest : G.IsAcyclic) (step : C → C → Prop)
    (hAsymm : ∀ {a b}, step a b → step b a → False)
    {a b : C} (walk : G.Walk a b) (hDirected : Directed step walk) : walk.IsPath := by
  induction walk with
  | nil => exact Walk.IsPath.nil
  | @cons a b c edge tail ih =>
    have hTail := ih hDirected.2
    apply hTail.cons
    intro hMem
    have hNext := hForest.eq_snd_of_adj_start hTail edge.symm hMem
    cases tail with
    | nil =>
      have hab : a = b := by simpa using hNext
      exact edge.ne hab
    | cons nextEdge rest =>
      simp only [Walk.snd_cons] at hNext
      have hBack := hDirected.2.1
      rw [← hNext] at hBack
      exact hAsymm hDirected.1 hBack

/-- Directed walks between fixed endpoints are unique in an acyclic graph with asymmetric
orientation. Their lengths need not be fixed in advance. -/
theorem directed_walk_unique (hForest : G.IsAcyclic) (step : C → C → Prop)
    (hAsymm : ∀ {a b}, step a b → step b a → False)
    {a b : C} (p q : G.Walk a b)
    (hLeft : Directed step p) (hRight : Directed step q) : p = q := by
  exact congrArg Subtype.val ((hForest.subsingleton_path a b).elim
    ⟨p, directed_isPath hForest step hAsymm p hLeft⟩
    ⟨q, directed_isPath hForest step hAsymm q hRight⟩)

end DirectedWalks

section TraceWords

variable {S C U : Type*}

/-- A permutation edge in a fixed trace, projected to its capacity endpoints.
Inverse query answers are represented by the same forward pair. -/
def CapacityEdge (trace : List (S × S)) (capacity : S → C) (a b : C) : Prop :=
  ∃ input output, (input, output) ∈ trace ∧ capacity input = a ∧ capacity output = b

/-- The undirected simple graph underlying the trace's capacity edges. -/
def capacityGraph (trace : List (S × S)) (capacity : S → C) : SimpleGraph C where
  Adj a b := a ≠ b ∧ (CapacityEdge trace capacity a b ∨ CapacityEdge trace capacity b a)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Local graph and labeling conditions supplied by a collision-free capacity trace.
Parallel identical entries are harmless; distinct rate labels on the same capacity edge are not. -/
structure CapacityForest (trace : List (S × S)) (capacity : S → C) (rate : S → List U) :
    Prop where
  acyclic : (capacityGraph trace capacity).IsAcyclic
  asymmetric : ∀ {a b}, CapacityEdge trace capacity a b →
    CapacityEdge trace capacity b a → False
  rate_unique : ∀ e ∈ trace, ∀ f ∈ trace,
    capacity e.1 = capacity f.1 → capacity e.2 = capacity f.2 → rate e.1 = rate f.1

/-- A capacity has not occurred at either endpoint of the preceding trace. -/
def CapacityFresh (trace : List (S × S)) (capacity : S → C) (value : C) : Prop :=
  ∀ edge ∈ trace, capacity edge.1 ≠ value ∧ capacity edge.2 ≠ value

/-- Adding a trace pair adds its single directed capacity edge. -/
theorem capacityEdge_cons (trace : List (S × S)) (capacity : S → C)
    (input output : S) (a b : C) :
    CapacityEdge ((input, output) :: trace) capacity a b ↔
      (capacity input = a ∧ capacity output = b) ∨ CapacityEdge trace capacity a b := by
  simp only [CapacityEdge, List.mem_cons, Prod.mk.injEq]
  aesop

/-- The capacity graph adds the corresponding undirected edge. -/
theorem capacityGraph_cons (trace : List (S × S)) (capacity : S → C) (input output : S) :
    capacityGraph ((input, output) :: trace) capacity =
      capacityGraph trace capacity ⊔ SimpleGraph.edge (capacity input) (capacity output) := by
  ext a b
  simp only [capacityGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj, capacityEdge_cons]
  aesop

/-- A capacity absent from the trace is isolated in its capacity graph. -/
theorem not_reachable_of_fresh {trace : List (S × S)} {capacity : S → C} {a b : C}
    (hFresh : CapacityFresh trace capacity a) (hNe : a ≠ b) :
    ¬(capacityGraph trace capacity).Reachable a b := by
  rintro ⟨walk⟩
  cases walk with
  | nil => exact hNe rfl
  | cons edge tail =>
    rcases edge.2 with h | h
    · obtain ⟨input, output, hMem, hInput, _⟩ := h
      exact (hFresh (input, output) hMem).1 hInput
    · obtain ⟨input, output, hMem, _, hOutput⟩ := h
      exact (hFresh (input, output) hMem).2 hOutput

/-- The empty trace is a capacity forest for every choice of capacity and rate projections. -/
theorem CapacityForest.nil (capacity : S → C) (rate : S → List U) :
    CapacityForest [] capacity rate := by
  have hGraph : capacityGraph ([] : List (S × S)) capacity = ⊥ := by
    ext a b
    simp [capacityGraph, CapacityEdge]
  refine ⟨?_, ?_, ?_⟩
  · rw [hGraph]
    exact SimpleGraph.isAcyclic_bot
  · intro a b h
    simp [CapacityEdge] at h
  · intro edge h
    simp at h

/-- A newly exposed permutation pair preserves the forest when its endpoints differ and
either endpoint has a fresh capacity. The two cases cover forward and inverse queries. -/
theorem CapacityForest.cons {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) (input output : S)
    (hNe : capacity input ≠ capacity output)
    (hFresh : CapacityFresh trace capacity (capacity input) ∨
      CapacityFresh trace capacity (capacity output)) :
    CapacityForest ((input, output) :: trace) capacity rate := by
  have hNoOld : ¬CapacityEdge trace capacity (capacity input) (capacity output) ∧
      ¬CapacityEdge trace capacity (capacity output) (capacity input) := by
    constructor
    · rintro ⟨x, y, hMem, hX, hY⟩
      rcases hFresh with hFresh | hFresh
      · exact (hFresh (x, y) hMem).1 hX
      · exact (hFresh (x, y) hMem).2 hY
    · rintro ⟨x, y, hMem, hX, hY⟩
      rcases hFresh with hFresh | hFresh
      · exact (hFresh (x, y) hMem).2 hY
      · exact (hFresh (x, y) hMem).1 hX
  refine ⟨?_, ?_, ?_⟩
  · rw [capacityGraph_cons]
    apply hForest.acyclic.sup_edge_of_not_reachable
    rcases hFresh with hFresh | hFresh
    · exact not_reachable_of_fresh hFresh hNe
    · intro hReach
      exact not_reachable_of_fresh hFresh hNe.symm hReach.symm
  · intro a b hAB hBA
    rw [capacityEdge_cons] at hAB hBA
    have hAsymm := hForest.asymmetric (a := a) (b := b)
    grind
  · intro e he f hf hInput hOutput
    have hRate := hForest.rate_unique
    grind [CapacityEdge]

/-- Removing or reordering trace entries preserves a directed capacity edge that remains. -/
theorem CapacityEdge.mono {trace subtrace : List (S × S)} {capacity : S → C} {a b : C}
    (hSubset : subtrace ⊆ trace) (h : CapacityEdge subtrace capacity a b) :
    CapacityEdge trace capacity a b := by
  obtain ⟨input, output, hMem, hInput, hOutput⟩ := h
  exact ⟨input, output, hSubset hMem, hInput, hOutput⟩

/-- Forest invariants depend only on edge membership; filtering, reordering, and duplicating
already present trace entries preserve them. -/
theorem CapacityForest.of_subset {trace subtrace : List (S × S)}
    {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) (hSubset : subtrace ⊆ trace) :
    CapacityForest subtrace capacity rate := by
  have hGraphs : capacityGraph subtrace capacity ≤ capacityGraph trace capacity := by
    intro a b hAdj
    exact ⟨hAdj.1, hAdj.2.elim (fun h => Or.inl (h.mono hSubset))
      (fun h => Or.inr (h.mono hSubset))⟩
  refine ⟨hForest.acyclic.anti hGraphs, ?_, ?_⟩
  · intro a b hAB hBA
    exact hForest.asymmetric (hAB.mono hSubset) (hBA.mono hSubset)
  · intro e he f hf hInput hOutput
    exact hForest.rate_unique e (hSubset he) f (hSubset hf) hInput hOutput

/-- Repeating an already known permutation answer requires no freshness hypothesis. -/
theorem CapacityForest.cons_of_mem {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) {edge : S × S} (hMem : edge ∈ trace) :
    CapacityForest (edge :: trace) capacity rate := by
  apply hForest.of_subset
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hMem
  · exact he

/-- Rate blocks read from the inputs of permutation edges following a given capacity walk.
An absorb overwrites the next input rate; it does not require consecutive output/input rates
to agree. Only the capacity segments link consecutive trace edges. -/
def Traced (trace : List (S × S)) (capacity : S → C) (rate : S → List U)
    {G : SimpleGraph C} : {a b : C} → G.Walk a b → List U → Prop
  | _, _, .nil, units => units = []
  | a, _, .cons (v := b) _ tail, units =>
    ∃ input output, (input, output) ∈ trace ∧ capacity input = a ∧ capacity output = b ∧
      ∃ rest, Traced trace capacity rate tail rest ∧ units = rate input ++ rest

/-- A trace-labeled walk follows the forward capacity relation. -/
theorem Traced.directed {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    {G : SimpleGraph C} {a b : C} {walk : G.Walk a b} {units : List U}
    (h : Traced trace capacity rate walk units) :
    Directed (CapacityEdge trace capacity) walk := by
  induction walk generalizing units with
  | nil => trivial
  | cons edge tail ih =>
    obtain ⟨input, output, hMem, hInput, hOutput, rest, hRest, _⟩ := h
    exact ⟨⟨input, output, hMem, hInput, hOutput⟩, ih hRest⟩

/-- Local uniqueness of rate labels determines the entire word along a fixed walk. -/
theorem Traced.word_unique {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hLabels : ∀ e ∈ trace, ∀ f ∈ trace,
      capacity e.1 = capacity f.1 → capacity e.2 = capacity f.2 → rate e.1 = rate f.1)
    {G : SimpleGraph C} {a b : C} {walk : G.Walk a b} {units₁ units₂ : List U}
    (h₁ : Traced trace capacity rate walk units₁)
    (h₂ : Traced trace capacity rate walk units₂) : units₁ = units₂ := by
  induction walk generalizing units₁ units₂ with
  | nil => exact h₁.trans h₂.symm
  | cons edge tail ih =>
    obtain ⟨input₁, output₁, hMem₁, hInput₁, hOutput₁, rest₁, hRest₁, hUnits₁⟩ := h₁
    obtain ⟨input₂, output₂, hMem₂, hInput₂, hOutput₂, rest₂, hRest₂, hUnits₂⟩ := h₂
    have hRate := hLabels (input₁, output₁) hMem₁ (input₂, output₂) hMem₂
      (hInput₁.trans hInput₂.symm) (hOutput₁.trans hOutput₂.symm)
    rw [hUnits₁, hUnits₂, hRate, ih hRest₁ hRest₂]

/-- In a capacity forest, fixed endpoints determine all fully absorbed rate blocks. -/
theorem traced_word_unique {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) {a b : C}
    {p q : (capacityGraph trace capacity).Walk a b} {units₁ units₂ : List U}
    (h₁ : Traced trace capacity rate p units₁)
    (h₂ : Traced trace capacity rate q units₂) : units₁ = units₂ := by
  have hWalk := directed_walk_unique hForest.acyclic (CapacityEdge trace capacity)
    hForest.asymmetric p q h₁.directed h₂.directed
  subst q
  exact h₁.word_unique hForest.rate_unique h₂

/-- The salt followed by a fixed first prover message matches a trace path from the fixed hash
root to a terminal permutation state. Whole rate blocks are the trace inputs; the remaining units
form a prefix of the terminal rate segment, which may be empty, partial, or complete. -/
def MatchesSalt (trace : List (S × S)) (capacity : S → C) (rate : S → List U)
    (root : C) (message : List U) (target : S) {δ : ℕ} (salt : Vector U δ) : Prop :=
  ∃ (walk : (capacityGraph trace capacity).Walk root (capacity target)) (blocks tail : List U),
    Traced trace capacity rate walk blocks ∧ tail.IsPrefix (rate target) ∧
      salt.toList ++ message = blocks ++ tail

/-- A prefix of a fixed length is recovered by taking that length. This explicitly accounts
for the terminal partial rate block rather than adding zero padding to the salt. -/
theorem reconstruct_absorbed_word {δ : ℕ} (salt : Vector U δ) (message blocks tail endRate : List U)
    (hTail : tail.IsPrefix endRate) (hWord : salt.toList ++ message = blocks ++ tail) :
    salt.toList ++ message = (blocks ++ endRate).take (δ + message.length) := by
  have hPrefix : (salt.toList ++ message).IsPrefix (blocks ++ endRate) := by
    rw [hWord]
    exact (List.prefix_append_right_inj blocks).mpr hTail
  simpa only [List.length_append, Vector.length_toList] using
    List.prefix_iff_eq_take.mp hPrefix

/-- A fixed capacity forest, hash root, and terminal state determine every absorbed prefix
of a specified length. The suffixes may differ and may depend on the prefixes. -/
theorem matchesSalt_unique {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) {root : C}
    {message₁ message₂ : List U} {target : S} {δ : ℕ} {salt₁ salt₂ : Vector U δ}
    (h₁ : MatchesSalt trace capacity rate root message₁ target salt₁)
    (h₂ : MatchesSalt trace capacity rate root message₂ target salt₂) : salt₁ = salt₂ := by
  obtain ⟨walk₁, blocks₁, tail₁, hTrace₁, hTail₁, hWord₁⟩ := h₁
  obtain ⟨walk₂, blocks₂, tail₂, hTrace₂, hTail₂, hWord₂⟩ := h₂
  have hBlocks := traced_word_unique hForest hTrace₁ hTrace₂
  have hReconstruct₁ := congrArg (List.take δ)
    (reconstruct_absorbed_word salt₁ message₁ blocks₁ tail₁ (rate target) hTail₁ hWord₁)
  have hReconstruct₂ := congrArg (List.take δ)
    (reconstruct_absorbed_word salt₂ message₂ blocks₂ tail₂ (rate target) hTail₂ hWord₂)
  simp only [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    at hReconstruct₁ hReconstruct₂
  have hTake (salt : Vector U δ) (message : List U) :
      (salt.toList ++ message).take δ = salt.toList := by
    simpa only [Vector.length_toList] using
      (List.take_left : (salt.toList ++ message).take salt.toList.length = salt.toList)
  rw [hTake] at hReconstruct₁ hReconstruct₂
  rw [hBlocks] at hReconstruct₁
  exact Vector.toList_inj.mp (hReconstruct₁.trans hReconstruct₂.symm)

/-- Block-by-block absorption witnessed entirely by a fixed permutation trace.
At each permutation boundary, consume its complete input rate block and continue from its
output capacity. The final unpermuted units are a prefix of the terminal state's rate.
Unused terminal rate coordinates are intentionally not constrained. -/
inductive AbsorbTrace (trace : List (S × S)) (capacity : S → C) (rate : S → List U) :
    C → List U → S → Prop
  | done {target : S} {tail : List U} (hTail : tail.IsPrefix (rate target)) :
      AbsorbTrace trace capacity rate (capacity target) tail target
  | step {input output target : S} {rest : List U} (hMem : (input, output) ∈ trace)
      (hRest : AbsorbTrace trace capacity rate (capacity output) rest target) :
      AbsorbTrace trace capacity rate (capacity input) (rate input ++ rest) target

/-- Convert the block-by-block trace relation to a capacity walk and the word it carries.
This construction uses only the local no-reverse-edge condition, not path uniqueness. -/
theorem AbsorbTrace.exists_traced {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hAsymm : ∀ {a b}, CapacityEdge trace capacity a b →
      CapacityEdge trace capacity b a → False)
    {root : C} {units : List U} {target : S}
    (h : AbsorbTrace trace capacity rate root units target) :
    ∃ (walk : (capacityGraph trace capacity).Walk root (capacity target)) (blocks tail : List U),
      Traced trace capacity rate walk blocks ∧ tail.IsPrefix (rate target) ∧
        units = blocks ++ tail := by
  induction h with
  | done hTail => exact ⟨.nil, [], _, rfl, hTail, by simp⟩
  | @step input output target rest hMem hRest ih =>
    obtain ⟨walk, blocks, tail, hTrace, hTail, hUnits⟩ := ih
    have hEdge : CapacityEdge trace capacity (capacity input) (capacity output) :=
      ⟨input, output, hMem, rfl, rfl⟩
    have hNe : capacity input ≠ capacity output := by
      intro hEq
      have hLoop := hEdge
      rw [hEq] at hLoop
      exact hAsymm hLoop hLoop
    have hAdj : (capacityGraph trace capacity).Adj (capacity input) (capacity output) :=
      ⟨hNe, Or.inl hEdge⟩
    refine ⟨.cons hAdj walk, rate input ++ blocks, tail, ?_, hTail, ?_⟩
    · exact ⟨input, output, hMem, rfl, rfl, blocks, hTrace, rfl⟩
    · simp only [hUnits, List.append_assoc]

/-- A trace of absorbing the salt followed by the fixed message supplies the matching-salt
witness required by the counting theorem. -/
theorem AbsorbTrace.matchesSalt {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hAsymm : ∀ {a b}, CapacityEdge trace capacity a b →
      CapacityEdge trace capacity b a → False)
    {root : C} {message : List U} {target : S} {δ : ℕ} {salt : Vector U δ}
    (h : AbsorbTrace trace capacity rate root (salt.toList ++ message) target) :
    MatchesSalt trace capacity rate root message target salt :=
  h.exists_traced hAsymm

/-- There are at most as many matching salts as candidate terminal states. No finite-type
assumption is needed: this statement applies to any finite sets of salts and targets. -/
theorem card_matching_salts_le {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) (root : C) (message : List U) {δ : ℕ}
    (salts : Finset (Vector U δ)) (targets : Finset S)
    (hMatch : ∀ salt ∈ salts, ∃ target ∈ targets,
      MatchesSalt trace capacity rate root message target salt) :
    salts.card ≤ targets.card := by
  classical
  choose endpoint hEndpoint hWitness using fun salt : salts => hMatch salt.1 salt.2
  let f : salts → targets := fun salt => ⟨endpoint salt, hEndpoint salt⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro a b hab
  apply Subtype.ext
  have hTarget : endpoint a = endpoint b := congrArg Subtype.val hab
  have hb := hWitness b
  rw [← hTarget] at hb
  exact matchesSalt_unique hForest (hWitness a) hb

/-- Counting corollary directly for block-by-block absorb traces. -/
theorem card_absorbTrace_salts_le {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) (root : C) (message : List U) {δ : ℕ}
    (salts : Finset (Vector U δ)) (targets : Finset S)
    (hMatch : ∀ salt ∈ salts, ∃ target ∈ targets,
      AbsorbTrace trace capacity rate root (salt.toList ++ message) target) :
    salts.card ≤ targets.card := by
  apply card_matching_salts_le hForest root message salts targets
  intro salt hSalt
  obtain ⟨target, hTarget, hTrace⟩ := hMatch salt hSalt
  exact ⟨target, hTarget, hTrace.matchesSalt hForest.asymmetric⟩

/-- If the terminal state is a known permutation input, at most `trace.length` salts can
produce a trace-backed absorb. Repeated query entries only make this upper bound looser. -/
theorem card_absorbTrace_salts_le_trace_length
    {trace : List (S × S)} {capacity : S → C} {rate : S → List U}
    (hForest : CapacityForest trace capacity rate) (root : C) (message : List U) {δ : ℕ}
    (salts : Finset (Vector U δ))
    (hMatch : ∀ salt ∈ salts, ∃ input output, (input, output) ∈ trace ∧
      AbsorbTrace trace capacity rate root (salt.toList ++ message) input) :
    salts.card ≤ trace.length := by
  classical
  have hCard := card_absorbTrace_salts_le hForest root message salts
    (trace.map Prod.fst).toFinset (by
      intro salt hSalt
      obtain ⟨input, output, hMem, hTrace⟩ := hMatch salt hSalt
      refine ⟨input, ?_, hTrace⟩
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(input, output), hMem, rfl⟩))
  exact hCard.trans (by simpa using (trace.map Prod.fst).toFinset_card_le)

end TraceWords

end DuplexSpongeFS.ZeroKnowledge.SaltForest

/-!
## Incremental capacity exposure

A new forward answer preserves the capacity forest when its capacity avoids the old trace
endpoints and the current input's capacity. The input itself may be old or new. The additional
current-input exclusion is necessary: freshness against an empty trace alone permits a loop.

The corresponding forbidden set contains at most `2 * trace.length + 1` capacities. These
are pointwise statements at a fixed execution prefix, suitable for use with a conditional
fresh-answer sampler. They do not assert unconditional uniformity of adaptive answers.
-/

namespace DuplexSpongeFS.ZeroKnowledge.CapacityExposure

open SaltForest

variable {S C U : Type*}

section FiniteExposure

variable [DecidableEq C]

/-- Capacities already exposed at either endpoint. Duplicated queries do not enlarge this set. -/
def endpointCapacities (trace : List (S × S)) (capacity : S → C) : Finset C :=
  (trace.map (fun edge => capacity edge.1) ++ trace.map (fun edge => capacity edge.2)).toFinset

/-- An exposed capacity is one of the endpoints of a recorded edge. -/
theorem mem_endpointCapacities {trace : List (S × S)} {capacity : S → C} {value : C} :
    value ∈ endpointCapacities trace capacity ↔
      ∃ edge ∈ trace, capacity edge.1 = value ∨ capacity edge.2 = value := by
  simp only [endpointCapacities, List.mem_toFinset, List.mem_append, List.mem_map]
  aesop

/-- Set nonmembership is exactly the trace-level freshness predicate. -/
theorem capacityFresh_iff_notMem_endpointCapacities
    {trace : List (S × S)} {capacity : S → C} {value : C} :
    CapacityFresh trace capacity value ↔ value ∉ endpointCapacities trace capacity := by
  simp only [CapacityFresh, mem_endpointCapacities, not_exists, not_and, not_or]

/-- Each recorded pair contributes at most two exposed capacities. -/
theorem card_endpointCapacities_le (trace : List (S × S)) (capacity : S → C) :
    (endpointCapacities trace capacity).card ≤ 2 * trace.length := by
  exact (List.toFinset_card_le _).trans_eq (by simp [List.length_append, two_mul])

/-- Answer capacities forbidden at this prefix: the current query endpoint plus all prior
endpoints. For an inverse query, pass its known output as `known`. -/
def forbiddenCapacities (trace : List (S × S)) (capacity : S → C) (known : S) : Finset C :=
  insert (capacity known) (endpointCapacities trace capacity)

/-- The extra current-endpoint exclusion is exactly the no-self-loop condition. -/
theorem notMem_forbiddenCapacities_iff
    {trace : List (S × S)} {capacity : S → C} {known answer : S} :
    capacity answer ∉ forbiddenCapacities trace capacity known ↔
      capacity known ≠ capacity answer ∧ CapacityFresh trace capacity (capacity answer) := by
  simp only [forbiddenCapacities, Finset.mem_insert, not_or,
    capacityFresh_iff_notMem_endpointCapacities, ne_comm]

/-- At most two prior endpoints per trace entry, plus the current query endpoint, are forbidden. -/
theorem card_forbiddenCapacities_le
    (trace : List (S × S)) (capacity : S → C) (known : S) :
    (forbiddenCapacities trace capacity known).card ≤ 2 * trace.length + 1 := by
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (card_endpointCapacities_le trace capacity) 1)

end FiniteExposure

end DuplexSpongeFS.ZeroKnowledge.CapacityExposure

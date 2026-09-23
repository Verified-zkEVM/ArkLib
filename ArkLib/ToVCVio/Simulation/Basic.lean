/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license vec described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.OracleReduction.Execution
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import Mathlib.Data.ENNReal.Basic
public import VCVio.OracleComp.EvalDist
public import ArkLib.OracleReduction.OracleInterface
public import VCVio.EvalDist.Instances.OptionT
public import ArkLib.Data.Probability.Instances

/-!
## Monad-to-Logic Bridge Lemmas

This file contains lemmas that simplify the execution of *oracle reductions*.
The goal is to provide a **clean path** from `simulateQ` and `StateT`
to the underlying deterministic protocol logic.

### Layer 1: Protocol Unrolling

**Goal:** Strip away the `Fin.induction` and `processRound` abstractions.

Key lemmas:
- `Reduction.run_step`
  Breaks a protocol execution into a sequential `do` block.
- `Prover.run_succ`
  Specifically handles the `Fin.induction` inside the `Prover.run` code.
- `Transcript.equiv_eval`
  Simplifies the conversion between transcripts and individual
  message/challenge pairs.

### Layer 2: Simulation & Query Mapping

**Goal:** Map queries to their implementations and handle spec-lifting.

Key lemmas:
- `simulateQ_liftComp`
  Simplifies simulating a computation lifted from a smaller specification.
- `simulateQ_append_inl` / `simulateQ_append_inr`
  The *workhorse* lemmas that route queries through `impl₁ ++ₛₒ impl₂`.
- `simulateQ_pure_bind`
  Eliminates pure calls inside simulation blocks.

### Layer 3: State & Support Bridge

**Goal:** Connect `ProbComp` support reasoning to logical relations.

Key lemmas:
- `run'_pure_bind`
  Simplifies `(pure x >>= f).run' s` to `(f x).run' s`.
- `support_pure_bind`
  Flattens the support of nested pure operations in the probability space.
- `probEvent_eq_one_pure_iff`
  Converts a probability statement `Pr[P x] = 1` into the logical claim `P x`.

-/

@[expose] public section




open OracleSpec OracleComp ProtocolSpec Sum

open scoped OracleSpec.PrimitiveQuery

universe u v w

section ProbOutputNone

variable {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m] {α β : Type u}

omit [LawfulMonadLiftT m SPMF] in
/--
`probOutput (mx >>= my) none = 0` iff every branch reachable from `mx`
has zero probability of returning `none`.
-/
@[simp]
lemma probOutput_none_bind_eq_zero_iff
    (mx : m α) (my : α → m (Option β)) :
    probOutput (m := m) (α := Option β) (mx := mx >>= my) (none : Option β) = 0 ↔
      ∀ x ∈ support mx, probOutput (m := m) (α := Option β) (mx := my x) (none : Option β) = 0 := by
  constructor
  · intro h x hx
    apply (probOutput_eq_zero_iff (my x) (none : Option β)).2
    intro hnone
    have hnone_bind : (none : Option β) ∉ support (mx >>= my) :=
      (probOutput_eq_zero_iff (mx >>= my) (none : Option β)).1 h
    exact hnone_bind <|
      (mem_support_bind_iff (mx := mx) (my := my)
        (y := (none : Option β))).2 ⟨x, hx, hnone⟩
  · intro h
    apply (probOutput_eq_zero_iff (mx >>= my) (none : Option β)).2
    intro hnone_bind
    rcases (mem_support_bind_iff (mx := mx) (my := my)
      (y := (none : Option β))).1 hnone_bind with ⟨x, hx, hnone⟩
    have hnone_x : (none : Option β) ∉ support (my x) :=
      (probOutput_eq_zero_iff (my x) (none : Option β)).1 (h x hx)
    exact hnone_x hnone

omit [LawfulMonadLiftT m SPMF] in
/--
Explicit `OptionT` version of `probOutput_none_bind_eq_zero_iff`.
This avoids relying on reducibility of `OptionT` during inference.
-/
@[simp]
lemma OptionT.probOutput_none_bind_eq_zero_iff
    (mx : OptionT m α) (my : α → OptionT m β) :
    probOutput (m := m) (α := Option β)
      (mx := OptionT.run (OptionT.bind mx my)) (none : Option β) = 0 ↔
      ∀ x ∈ support (m := m) (α := Option α) (mx := OptionT.run mx),
        probOutput (m := m) (α := Option β)
          (mx := match x with
            | some a => OptionT.run (my a)
            | none => (pure none : m (Option β))) (none : Option β) = 0 := by
  change probOutput (m := m) (α := Option β)
      (mx := OptionT.run mx >>= fun x : Option α => match x with
        | some a => OptionT.run (my a)
        | none => (pure none : m (Option β))) none = 0 ↔ _
  exact _root_.probOutput_none_bind_eq_zero_iff
    (mx := OptionT.run mx)
    (my := fun x : Option α => match x with
      | some a => OptionT.run (my a)
      | none => (pure none : m (Option β)))

end ProbOutputNone

namespace SimOracle

abbrev Stateless {ι ι' : Type*} (spec : OracleSpec ι) (superSpec : OracleSpec ι') :=
  QueryImpl spec (OracleComp superSpec)

end SimOracle

section NestedMonadLiftLemmas

instance instMonadLift_left_right {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift (OracleQuery T₁) (OracleQuery (T₃ + (T₁ + T₂))) where
  monadLift q := liftM (liftM q : OracleQuery (T₁ + T₂) _)

instance instMonadLift_right_right {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift (OracleQuery T₁) (OracleQuery (T₃ + (T₂ + T₁))) where
  monadLift q := liftM (liftM q : OracleQuery (T₂ + T₁) _)

instance instMonadLift_left_left {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift (OracleQuery T₁) (OracleQuery ((T₁ + T₂) + T₃)) where
  monadLift q := liftM (liftM q : OracleQuery (T₁ + T₂) _)

instance instMonadLift_right_left {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift (OracleQuery T₁) (OracleQuery ((T₂ + T₁) + T₃)) where
  monadLift q := liftM (liftM q : OracleQuery (T₂ + T₁) _)

end NestedMonadLiftLemmas

section SimulationLemmas

variable {ι ι₁ ι₂ : Type*} {spec : OracleSpec ι}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {m : Type u → Type v} [AlternativeMonad m] [LawfulMonad m] [LawfulAlternative m]
  {α β σ : Type u}

/-- Lift an implementation for `spec₂` to `spec₁` via `MonadLift`. -/
@[reducible]
def QueryImpl.lift {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)] (so : QueryImpl spec₂ m) :
    QueryImpl spec₁ m :=
    fun (q : spec₁.Domain) => so.mapQuery (liftM (query q) : OracleQuery spec₂ _)

/-- Commute simulation with spec-lifting: simulating a lifted computation
is the same vec simulating the original computation with the lifted implementation. -/
@[simp]
lemma simulateQ_liftComp
    {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)]
    (so : QueryImpl spec₂ (OracleComp spec))
    (oa : OracleComp spec₁ α) :
    simulateQ so (liftComp oa spec₂) =
      simulateQ (fun t ↦ simulateQ so
        (liftM (query (t := t)) : OracleComp spec₂ _)) oa := by
  rw [OracleComp.liftComp_def]
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t mx ih =>
      simp [simulateQ_bind, ih]

/-- `OptionT`-typed specialization of `simulateQ_liftComp`. -/
@[simp]
lemma OptionT.simulateQ_liftComp
    {ι₁ ι₂ : Type*} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)]
    (so : QueryImpl spec₂ (OracleComp spec))
    {δ : Type v} (oa : OptionT (OracleComp spec₁) δ) :
    simulateQ so (liftComp oa spec₂ : OptionT (OracleComp spec₂) δ) =
      (simulateQ (fun t ↦ simulateQ so
        (liftM (query (t := t)) : OracleComp spec₂ _)) oa :
        OptionT (OracleComp spec) δ) := by
  simpa using (_root_.simulateQ_liftComp (spec₁ := spec₁) (spec₂ := spec₂)
    (so := so) (oa := (oa : OracleComp spec₁ (Option δ))))

/--
**Step 2 Helper: Collapse Monadic Bind and Composition**
This lemma resolves the pattern `pure x >>= (simulateQ ∘ f)` that often appears
when simulating sequential code. It forces the function `f` to be applied to `x`
inside the simulation immediately.
-/
@[simp]
lemma bind_pure_simulateQ_comp
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α β : Type v} (x : α) (f : α → OracleComp spec β) :
    (pure x >>= (simulateQ so ∘ f)) = simulateQ so (f x) := by rfl

@[simp]
lemma mem_support_simulateQ_id'_liftM_query {ι : Type*} {spec : OracleSpec ι}
    (t : spec.Domain) (x : spec.Range t) :
    x ∈ support (simulateQ (fun s => liftM (spec.query s))
      (liftM (spec.query t)) : OracleComp spec (spec.Range t)) := by
  have heq : (fun s : spec.Domain => liftM (spec.query s)) = QueryImpl.id' spec := by
    ext s
    exact QueryImpl.id'_apply s
  rw [heq, simulateQ_id', OracleComp.support_query]
  exact Set.mem_univ x

@[simp]
lemma OptionT.bind_pure_simulateQ_comp
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    {α β : Type v} (x : α) (f : α → OptionT (OracleComp spec) β) :
    OptionT.bind (m := OracleComp spec') (OptionT.pure x) (simulateQ so ∘ f) =
      simulateQ so (f x) := by
  rfl

@[simp]
lemma OptionT.simulateQ_bind
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β) :
    simulateQ so (OptionT.bind mx my) =
      OptionT.bind (simulateQ so mx) (fun x => simulateQ so (my x)) := by
  change
    simulateQ so (mx >>= fun z => match z with | some a => my a | none => pure none) =
      OptionT.bind (simulateQ so mx) (fun x => simulateQ so (my x))
  rw [_root_.simulateQ_bind]
  simp only [OptionT.bind, OptionT.mk]
  apply bind_congr
  intro z
  cases z <;> simp only [simulateQ_pure]

@[simp]
lemma OptionT.simulateQ_pure
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec')) (x : α) :
    simulateQ so (OptionT.pure x : OptionT (OracleComp spec) α) =
      (OptionT.pure x : OptionT (OracleComp spec') α) := by
  rfl

@[simp]
lemma OptionT.simulateQ_failure
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec')) :
    simulateQ so (failure : OptionT (OracleComp spec) α) =
      (failure : OptionT (OracleComp spec') α) := by
  rfl

@[simp]
lemma OptionT.simulateQ_ite
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec'))
    (p : Prop) [Decidable p]
    (mx mx' : OptionT (OracleComp spec) α) :
    simulateQ so (ite p mx mx') = ite p (simulateQ so mx) (simulateQ so mx') := by
  split_ifs <;> rfl

@[simp]
lemma OptionT.simulateQ_map
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec')) (f : α → β)
    (mx : OptionT (OracleComp spec) α) :
    simulateQ so ((f <$> mx : OptionT (OracleComp spec) β)) =
      (f <$> (simulateQ so (OptionT.run mx) : OptionT (OracleComp spec') α) :
        OptionT (OracleComp spec') β) := by
  change simulateQ so ((f <$> mx).run) =
    (f <$> (simulateQ so (OptionT.run mx) : OptionT (OracleComp spec') α) :
      OptionT (OracleComp spec') β)
  rw [OptionT.run_map]
  change simulateQ so (Option.map f <$> OptionT.run mx) =
    ((f <$> (simulateQ so (OptionT.run mx) : OptionT (OracleComp spec') α) :
      OptionT (OracleComp spec') β)).run
  rw [OptionT.run_map]
  exact (_root_.simulateQ_map (impl := so) (mx := OptionT.run mx) (f := Option.map f))

@[simp]
lemma OptionT.simulateQ_map' {α β : Type u}
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : QueryImpl spec (OracleComp spec')) (f : α → β)
    (mx : OptionT (OracleComp spec) α) :
    simulateQ so (Option.map f <$> (OptionT.run mx)) =
      Option.map f <$> (simulateQ so (OptionT.run mx)) := by
  simp only [_root_.simulateQ_map (impl := so)
    (mx := OptionT.run mx) (f := Option.map f)]

@[simp]
lemma OptionT.support_map_run
    {ι : Type*} {spec : OracleSpec ι} (f : Option α → Option β)
    (mx : OptionT (OracleComp spec) α) :
    support (m := OracleComp spec) (α := Option β) (f <$> mx) =
      f '' (support (m := OracleComp spec) (α := Option α) mx) := by
  exact (_root_.support_map (m := OracleComp spec) (f := f) (mx := mx))

@[simp]
lemma OptionT.support_ite_run
    {ι : Type*} {spec : OracleSpec ι}
    (p : Prop) [Decidable p] (mx mx' : OptionT (OracleComp spec) α) :
    support (m := OracleComp spec) (α := Option α) (ite p mx mx') =
      ite p (support (m := OracleComp spec) (α := Option α) mx)
        (support (m := OracleComp spec) (α := Option α) mx') := by
  split_ifs <;> rfl

@[simp]
lemma OptionT.support_failure_run
    {ι : Type*} {spec : OracleSpec ι} :
    support (m := OracleComp spec) (α := Option α)
      ((failure : OptionT (OracleComp spec) α)) = {(none : Option α)} := by
  rfl

end SimulationLemmas

section SimulationSafety

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited] {α β : Type}

/-- Challenge query implementation never fails (stateful version). -/
lemma probFailure_challengeQueryImpl_run {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (q : OracleQuery ([pSpec.Challenge]ₒ'challengeOracleInterface) β) (s : σ) :
    Pr[⊥ | (liftM (QueryImpl.mapQuery challengeQueryImpl q) : StateT σ ProbComp β).run s] = 0 := by
  rcases q with ⟨⟨i, u⟩, cont⟩
  cases u
  unfold challengeQueryImpl
  simp only [StateT.run, liftM, ChallengeIdx, Challenge, ofPFunctor_toPFunctor,
    probFailure_of_liftM_PMF]

/-- A stateful `simulateQ` computation has zero failure probability. -/
theorem simulateQ_preserves_safety_stateful
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    Pr[⊥ | (simulateQ impl oa).run s] = 0 := by
  simp only [probFailure_of_liftM_PMF]

/-- An oracle computation has zero failure probability. This stateful alias is retained for
callers that use the corresponding simulation lemma. -/
lemma neverFails_of_simulateQ_stateful
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec]
    {α : Type} (oa : OracleComp oSpec α) :
    Pr[⊥ | oa] = 0 := by
  simp only [probFailure_of_liftM_PMF]

/-- **Stateful Safety Biconditional**

For stateful oracle implementations, the simulated computation is safe if and only if
the specification computation is safe. This requires:
1. The implementation itself never fails (hImplSafe).
2. The implementation has the same support vec the specification (hImplSupp).

This is the stateful version of `probFailure_simulateQ_iff` and is useful for
simplifying completeness proofs where you need to establish equivalence between
simulated and specification safety.

**Note**: Unlike `simulateQ_preserves_safety_stateful` which only requires support subset (⊆),
this biconditional requires support **equality** (=) to enable the reverse direction.
-/
@[simp]
theorem probFailure_simulateQ_iff_stateful
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    Pr[⊥ | (simulateQ impl oa).run s] = 0 ↔ Pr[⊥ | oa] = 0 := by
  simp only [probFailure_of_liftM_PMF]

/-- **Stateful Safety Biconditional (run' version)**

This is the `run'` version of `probFailure_simulateQ_iff_stateful`. It works with
`StateT.run'` which projects out only the result (discarding the final state),
rather than `StateT.run` which returns the full `(result, state)` pair.

This lemma is useful when the goal involves `(simulateQ impl oa).run' s` instead of
`(simulateQ impl oa).run s`.
-/
@[simp]
theorem probFailure_simulateQ_iff_stateful_run'
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    Pr[⊥ | (simulateQ impl oa).run' s] = 0 ↔ Pr[⊥ | oa] = 0 := by
  simp only [probFailure_of_liftM_PMF]

/-- **Safety Preservation Lemma for Stateless Implementations**

If an oracle implementation is safe and support-faithful, then simulation preserves safety
from the specification level to the implementation level (stateless version).

This is the stateless counterpart to `simulateQ_preserves_safety_stateful`.
-/
theorem simulateQ_preserves_safety
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec]
    (so : QueryImpl oSpec ProbComp)
    {α : Type} (oa : OracleComp oSpec α) :
    Pr[⊥ | simulateQ so oa] = 0 := by
  simp only [probFailure_of_liftM_PMF]

omit [spec.Fintype] [spec.Inhabited] in
/--
Safety preservation: A simulated protocol is safe if and only if the original
protocol is safe. This requires:
1. The implementation itself never fails (h_so).
2. The implementation doesn't return "illegal" values outside the spec (h_supp).
-/
@[simp]
lemma probFailure_simulateQ_iff [IsUniformSpec spec]
    (so : QueryImpl spec ProbComp) (oa : OracleComp spec α) :
    Pr[⊥ | simulateQ so oa] = 0 ↔ Pr[⊥ | oa] = 0 := by
  simp only [probFailure_of_liftM_PMF]

set_option backward.isDefEq.respectTransparency false in
/-- Challenge query implementations have the same support as the specification.
    This is trivially true for uniform distributions. -/
@[simp]
lemma support_challengeQueryImpl_eq {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (i : pSpec.ChallengeIdx) :
    support (challengeQueryImpl.mapQuery
      (([pSpec.Challenge]ₒ'challengeOracleInterface).query ⟨i, ()⟩)) =
    support (liftM (([pSpec.Challenge]ₒ'challengeOracleInterface).query ⟨i, ()⟩) :
      OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) _) := by
  let : SampleableType (([pSpec.Challenge]ₒ'challengeOracleInterface).Range ⟨i, ()⟩) := by
    exact (inferInstance : SampleableType (pSpec.Challenge i))
  rw [OracleComp.support_query]
  simp only [challengeQueryImpl, QueryImpl.mapQuery, OracleQuery.input_query,
    OracleQuery.cont_query, id_map]
  exact support_uniformSample _

end SimulationSafety

section ProtocolUnrolling

variable {ι : Type} {n : ℕ} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- Simplification lemma for `processRound` when the direction is `P_to_V`. -/
@[simp]
lemma Prover.processRound_P_to_V (j : Fin n)
    (h : pSpec.dir j = .P_to_V)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      (prover.processRound j currentResult = do
        let ⟨transcript, state⟩ ← currentResult
        let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, h⟩ state
        return ⟨transcript.concat msg, newState⟩) := by
  unfold processRound
  split
  · rename_i hDir
    rw [h] at hDir
    contradiction
  · simp

/-- Simplification lemma for `processRound` when the direction is `V_to_P`. -/
@[simp]
lemma Prover.processRound_V_to_P (j : Fin n)
    (h : pSpec.dir j = .V_to_P)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      (prover.processRound j currentResult = do
        let ⟨transcript, state⟩ ← currentResult
        let challenge ← pSpec.getChallenge ⟨j, h⟩
        letI newState := (← prover.receiveChallenge ⟨j, h⟩ state) challenge
        return ⟨transcript.concat challenge, newState⟩) := by
  unfold processRound
  split
  · simp
  · rename_i hDir
    rw [h] at hDir
    contradiction

end ProtocolUnrolling

section ReductionUnrolling

variable {ι : Type} {n : ℕ} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [∀ i, SampleableType (pSpec.Challenge i)]

omit [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)] in
/-- Specifically handles the `Fin.induction` inside the `Prover.run` code. -/
@[simp]
lemma Prover.run_succ (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : Fin n) :
    prover.runToRound i.succ stmt wit =
      prover.processRound i (prover.runToRound i.castSucc stmt wit) :=
by simp [Prover.runToRound, Fin.induction_succ]

set_option maxHeartbeats 200000 in
-- Bound this helper for the same reason: it normalizes nested `OptionT` and `simulateQ` binds.
lemma OptionT.liftM_run_getM_bind {α β} {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)]
    (x : OptionT (OracleComp spec₁) α) (f : α → OptionT (OracleComp spec₂) β) :
    (liftM x.run : OptionT (OracleComp spec₂) (Option α)) >>= (fun a => Option.getM a >>= f) =
      liftM x >>= f := by
  apply OptionT.ext
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_lift]
  let so : QueryImpl spec₁ (OracleComp spec₂) :=
    fun t => PFunctor.FreeM.liftObj (MonadLift.monadLift (query t))
  rw [show (do let a ← x.run; pure (some a) : OracleComp spec₁ (Option (Option α))) =
    some <$> x.run by
      simp [map_eq_bind_pure_comp]]
  change (Option.elimM (simulateQ so (some <$> x.run))
      (pure none) fun a =>
        Option.elimM ((Option.getM a : OptionT (OracleComp spec₂) α).run)
          (pure none) fun x => (f x).run) =
    Option.elimM (simulateQ so x.run) (pure none) fun x => (f x).run
  have hmap : simulateQ so (some <$> x.run) = some <$> simulateQ so x.run :=
    _root_.simulateQ_map so x.run some
  rw [hmap]
  rw [Option.elimM, map_eq_bind_pure_comp, bind_assoc]
  congr 1
  funext a
  cases a <;> simp [Option.getM, Option.elimM]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
-- Bound the main unfolding lemma as well; it rewrites through the same nested lift structure.
lemma Reduction_run_def (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    reduction.run stmtIn witIn = (do
      let ⟨transcript, stmtOut, witOut⟩ ← reduction.prover.run stmtIn witIn
      let verifierStmtOut ← reduction.verifier.verify stmtIn transcript
      return ((transcript, stmtOut, witOut), verifierStmtOut)) := by
  unfold Reduction.run Verifier.run
  simp only [ChallengeIdx, Challenge, map_eq_bind_pure_comp, bind_pure_comp,
    OracleComp.liftM_OptionT_eq, Prod.mk.eta]
  congr 1
  funext proverResult
  cases proverResult
  dsimp only
  rw [OptionT.liftM_run_getM_bind]
  rfl

attribute [simp] Reduction_run_def

end ReductionUnrolling

section TranscriptLemmas

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Simplifies the extraction of a message from a full transcript. -/
@[simp]
lemma Transcript_get_message (tr : pSpec.FullTranscript) (j : Fin n) (h : pSpec.dir j = .P_to_V) :
    tr.messages ⟨j, h⟩ = tr j :=
by rfl

/-- Simplifies the extraction of a challenge from a full transcript. -/
@[simp]
lemma Transcript_get_challenge (tr : pSpec.FullTranscript) (j : Fin n) (h : pSpec.dir j = .V_to_P) :
    tr.challenges ⟨j, h⟩ = tr j :=
by rfl

/-- Simplifies the conversion between transcripts and individual message/challenge pairs. -/
@[simp]
lemma Transcript.equiv_eval (tr : pSpec.FullTranscript) :
    FullTranscript.equivMessagesChallenges tr = (tr.messages, tr.challenges) :=
by rfl

end TranscriptLemmas

section SupportPreservation

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] {α β : Type}
  {m : Type → Type} -- [AlternativeMonad m] [LawfulAlternative m]

omit [spec.Fintype] in
@[simp]
lemma support_simulateQ_eq (so : QueryImpl spec ProbComp) (oa : OracleComp spec α)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      support ((QueryImpl.mapQuery so q)) = support ((liftM q : OracleComp spec β))) :
    support ((simulateQ so oa)) = support oa := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, support_bind, ih]
    congr 1
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      (QueryImpl.mapQuery_query so t).symm, h_supp (query t)]

/-! Same vec `support_simulateQ_eq` but for implementation in `OracleComp spec` (e.g. liftComp). -/
omit [spec.Fintype] in
@[simp]
lemma support_simulateQ_eq_OracleComp_of_superSpec {ι' : Type} {superSpec : OracleSpec ι'}
    (so : QueryImpl superSpec (OracleComp spec)) (oa : OracleComp superSpec α)
    (h_supp : ∀ {β} (q : OracleQuery superSpec β),
      support ((QueryImpl.mapQuery so q)) = support ((liftM q : OracleComp superSpec β))) :
    support (simulateQ so oa) = support oa := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, support_bind, ih]
    congr 1
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      (QueryImpl.mapQuery_query so t).symm, h_supp (query t)]

/-! Support of `OptionT.run oa` equals the support of the underlying `oa`. -/
omit [spec.Fintype] in
@[simp]
lemma OptionT.support_run_eq
    (oa : OracleComp spec (Option α)) :
    support (m := OracleComp spec) (α := Option α) (OptionT.run oa) =
    support (m := OracleComp spec) (α := Option α) oa := by rfl

/-
  `spec.Fintype` is not needed for this support-level bridge.
-/
omit [spec.Fintype] in
/-- OptionT run-level wrapper of `support_simulateQ_eq`. -/
@[simp]
lemma OptionT.support_run_simulateQ_eq_of_superSpec {ι' : Type}
    {superSpec : OracleSpec ι'}
    (so : QueryImpl superSpec (OracleComp spec)) (oa : OptionT (OracleComp superSpec) α)
    (h_supp : ∀ {β} (q : OracleQuery superSpec β),
      support ((QueryImpl.mapQuery so q)) = support ((liftM q : OracleComp superSpec β))) :
    support (m := OracleComp spec) (α := Option α)
      (OptionT.run (m := OracleComp spec) (simulateQ so oa)) =
    support (m := OracleComp superSpec) (α := Option α) (OptionT.run oa) := by
  have h_res :=
    (support_simulateQ_eq_OracleComp_of_superSpec (spec := spec) (superSpec := superSpec) (so := so)
      (oa := oa) (h_supp := h_supp))
  rw [OptionT.support_run_eq, OptionT.support_run_eq]
  rw [h_res]

set_option backward.isDefEq.respectTransparency false in
/-- Challenge query implementations have full support (stateful version).
    The first component of the result has the same support as the spec. -/
@[simp]
lemma support_challengeQueryImpl_run_eq {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (q : OracleQuery ([pSpec.Challenge]ₒ'challengeOracleInterface) β) (s : σ) :
    Prod.fst <$> support
      ((liftM (QueryImpl.mapQuery challengeQueryImpl q) : StateT σ ProbComp β).run s) =
    support (liftM q : OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) β) := by
  rcases q with ⟨⟨i, u⟩, cont⟩
  cases u
  simp only [challengeQueryImpl, QueryImpl.mapQuery, OracleQuery.input,
    ChallengeIdx, Challenge, ofPFunctor_toPFunctor, Set.fmap_eq_image]
  have hq : support
      (liftM (OracleQuery.mk ⟨i, ()⟩ cont :
        OracleQuery ([pSpec.Challenge]ₒ'challengeOracleInterface) β) :
        OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) β) = Set.range cont := by
      simpa only [OracleQuery.cont_apply] using
        (OracleComp.support_liftM
          (OracleQuery.mk ⟨i, ()⟩ cont :
            OracleQuery ([pSpec.Challenge]ₒ'challengeOracleInterface) β))
  rw [hq]
  rw [StateT.run_monadLift]
  simp only [monadLift_self, bind_pure_comp, support_map]
  have hs : support ($ᵗ (pSpec.Challenge i) : ProbComp (pSpec.Challenge i)) = Set.univ :=
    support_uniformSample _
  erw [hs]
  simp [OracleQuery.cont, Set.image_image]

/-- **Helper: Support of run' for stateful simulateQ**

If a stateful oracle implementation is support-faithful, then for any state `s`,
the support of `(simulateQ impl oa).run' s` equals the support of `oa`.

This is the stateful version of `support_simulateQ_eq` and is used vec a building
block for `support_bind_simulateQ_run'_eq`.

**Proof Strategy**: The proof requires careful handling of state transitions.
The key insight is that `run'` projects out the result component via `map Prod.fst`,
and `hImplSupp` ensures that the first component of the stateful implementation's
support matches the spec's support. The proof proceeds by induction on `oa`,
using the support-faithfulness at each query step.
-/
@[simp]
lemma support_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    support ((simulateQ impl oa).run' s) = support oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, support_map, support_pure,
      Set.image_singleton]
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, support_map,
      support_bind]
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨z, ⟨u, hu, hz⟩, hzy⟩
      have h_impl : Prod.fst <$> support ((impl t).run s) =
          support (liftM (OracleSpec.query t) : OracleComp oSpec (oSpec.Range t)) := by
        simpa using hImplSupp (OracleSpec.query t) s
      have hu_spec : u.1 ∈ support
          (liftM (OracleSpec.query t) : OracleComp oSpec (oSpec.Range t)) := by
        rw [← h_impl]
        exact ⟨u, hu, rfl⟩
      have hy_sim : y ∈ support ((simulateQ impl (oa u.1)).run' u.2) := by
        rw [StateT.run'_eq, support_map]
        exact ⟨z, hz, hzy⟩
      have hy_spec : y ∈ support (oa u.1) := by
        rw [← ih u.1 u.2]
        exact hy_sim
      exact ⟨u.1, hu_spec, hy_spec⟩
    · rintro ⟨x, hx, hy⟩
      have h_impl : Prod.fst <$> support ((impl t).run s) =
          support (liftM (OracleSpec.query t) : OracleComp oSpec (oSpec.Range t)) := by
        simpa using hImplSupp (OracleSpec.query t) s
      have hx_impl : x ∈ Prod.fst <$> support ((impl t).run s) := by
        rw [h_impl]
        exact hx
      obtain ⟨u, hu, hux⟩ := hx_impl
      have hy_sim : y ∈ support ((simulateQ impl (oa u.1)).run' u.2) := by
        rw [ih u.1 u.2, hux]
        exact hy
      rw [StateT.run'_eq, support_map, Set.mem_image] at hy_sim
      obtain ⟨z, hz, hzy⟩ := hy_sim
      exact ⟨z, ⟨u, hu, hz⟩, hzy⟩

/-- OptionT run-level wrapper of `support_simulateQ_run'_eq` (stateful implementation). -/
@[simp]
lemma OptionT.support_run_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OptionT (OracleComp oSpec) α) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    support (m := ProbComp) (α := Option α) ((simulateQ impl oa).run' s) =
      support (m := OracleComp oSpec) (α := Option α) oa := by
  simpa using
    (support_simulateQ_run'_eq (impl := impl) (oa := oa) (s := s)
      (hImplSupp := hImplSupp))

/-- OptionT-wrapper version of `neverFails_of_simulateQ` for option-valued computations. -/
lemma neverFails_of_simulateQ_mk
    {spec : OracleSpec ι} [IsUniformSpec spec]
    (so : QueryImpl spec ProbComp) (oa : OracleComp spec (Option α))
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      support (so.mapQuery q) = support (liftM q : OracleComp spec β))
    (h : Pr[⊥ | (OptionT.mk (simulateQ so oa) : OptionT ProbComp α)] = 0) :
    Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp spec) α)] = 0 := by
  rw [OptionT.probFailure_eq] at h ⊢
  -- rw [probOutput_eq_zero_iff] at h ⊢
  simpa [support_simulateQ_eq so oa h_supp] using h

/-- OptionT-wrapper version of `simulateQ_preserves_safety` for option-valued computations. -/
theorem simulateQ_preserves_safety_mk
    {spec : OracleSpec ι} [IsUniformSpec spec]
    (so : QueryImpl spec ProbComp) (oa : OracleComp spec (Option α))
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      support (so.mapQuery q) = support (liftM q : OracleComp spec β))
    (h_oa : Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp spec) α)] = 0) :
    Pr[⊥ | (OptionT.mk (simulateQ so oa) : OptionT ProbComp α)] = 0 := by
  rw [OptionT.probFailure_eq] at h_oa ⊢
  -- rw [probOutput_eq_zero_iff] at h_oa ⊢
  simpa [support_simulateQ_eq so oa h_supp] using h_oa

/-- OptionT-wrapper version of `probFailure_simulateQ_iff` for option-valued computations. -/
@[simp]
lemma probFailure_simulateQ_iff_mk
    {spec : OracleSpec ι} [IsUniformSpec spec]
    (so : QueryImpl spec ProbComp) (oa : OracleComp spec (Option α))
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      support (so.mapQuery q) = support (liftM q : OracleComp spec β)) :
    Pr[⊥ | (OptionT.mk (simulateQ so oa) : OptionT ProbComp α)] = 0 ↔
      Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp spec) α)] = 0 := by
  constructor
  · intro h
    exact neverFails_of_simulateQ_mk so oa h_supp h
  · intro h
    exact simulateQ_preserves_safety_mk so oa h_supp h

/-- OptionT-wrapper version of `simulateQ_preserves_safety_stateful` (run' form). -/
theorem simulateQ_preserves_safety_stateful_run'_mk
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (h_oa : Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp oSpec) α)] = 0) :
    Pr[⊥ | (OptionT.mk ((simulateQ impl oa).run' s) : OptionT ProbComp α)] = 0 := by
  rw [OptionT.probFailure_eq] at h_oa ⊢
  simp only [probFailure_of_liftM_PMF, zero_add] at h_oa ⊢
  have h_none_oa : none ∉ support oa := (probOutput_eq_zero_iff oa none).1 h_oa
  have h_support_eq : support ((simulateQ impl oa).run' s) = support oa :=
    support_simulateQ_run'_eq impl oa s hImplSupp
  have h_none_sim : none ∉ support ((simulateQ impl oa).run' s) := by
    intro h_mem
    apply h_none_oa
    rwa [h_support_eq] at h_mem
  exact (probOutput_eq_zero_iff ((simulateQ impl oa).run' s) none).2 h_none_sim

/-- OptionT-wrapper version of `neverFails_of_simulateQ_stateful` (run' form). -/
lemma neverFails_of_simulateQ_stateful_run'_mk
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (h : Pr[⊥ | (OptionT.mk ((simulateQ impl oa).run' s) : OptionT ProbComp α)] = 0) :
    Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp oSpec) α)] = 0 := by
  rw [OptionT.probFailure_eq] at h ⊢
  simp only [probFailure_of_liftM_PMF, zero_add] at h ⊢
  have h_none_sim : none ∉ support ((simulateQ impl oa).run' s) :=
    (probOutput_eq_zero_iff ((simulateQ impl oa).run' s) none).1 h
  have h_support_eq : support ((simulateQ impl oa).run' s) = support oa :=
    support_simulateQ_run'_eq impl oa s hImplSupp
  have h_none_oa : none ∉ support oa := by
    intro h_mem
    apply h_none_sim
    rwa [h_support_eq]
  exact (probOutput_eq_zero_iff oa none).2 h_none_oa

/-- OptionT-wrapper version of `probFailure_simulateQ_iff_stateful_run'`. -/
@[simp]
theorem probFailure_simulateQ_iff_stateful_run'_mk
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (oa : OracleComp oSpec (Option α)) (s : σ) :
    Pr[⊥ | (OptionT.mk ((simulateQ impl oa).run' s) : OptionT ProbComp α)] = 0 ↔
      Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp oSpec) α)] = 0 := by
  constructor
  · intro h
    exact neverFails_of_simulateQ_stateful_run'_mk impl hImplSupp oa s h
  · intro h
    exact simulateQ_preserves_safety_stateful_run'_mk impl hImplSupp oa s h

/-- **Support Nonemptiness from Never-Fails**

If a computation never fails, then its support is nonempty. This is a fundamental
property: if `Pr[⊥ | oa] = 0`, then there must be at least one possible output value.

**Intuition**: If a computation never fails, the sum of probabilities over all outputs
equals 1. Since probabilities are non-negative and sum to 1, at least one output
must have positive probability, which means it's in the support.

**Application**: This lemma is useful in completeness proofs where we need to eliminate
quantifiers over support. If we have `∀ x ∈ support oa, P x` and `NeverFail oa`,
we can instantiate the quantifier with a witness from the nonempty support.
-/
theorem support_nonempty_of_neverFails
    {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (h : NeverFail oa) :
    (support oa).Nonempty := by
  have h_probFailure_eq_zero : Pr[⊥ | oa] = 0 := (probFailure_eq_zero_iff oa).2 h
  have h_event_pos : 0 < Pr[fun _ => True | oa] := by
    simp only [probEvent_True_eq_sub, probFailure_of_liftM_PMF, tsub_zero, zero_lt_one]
  rcases (probEvent_pos_iff (mx := oa) (p := fun _ => True)).1 h_event_pos with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

/-- **Support Preservation for Stateful Bind-SimulateQ Pattern**

If a stateful oracle implementation is support-faithful, then the support of
`(do let s ← init; (simulateQ impl oa).run' s)` equals the support of `oa`.

This is the stateful bind version of `support_simulateQ_eq` and is essential
for reasoning about support in oracle reductions where:
- `init : ProbComp σ` samples the initial oracle state
- `impl : QueryImpl oSpec (StateT σ ProbComp)` is a stateful oracle implementation
- `oa : OracleComp oSpec α` is the specification computation (which doesn't depend on state)

**Pattern**: This lemma handles the common pattern in completeness proofs:
```lean
support (do let s ← init; (simulateQ impl oa).run' s) = support oa
```

**Application**: When proving completeness, we often need to show that the support
of the simulated execution matches the support of the specification. This lemma
bridges that gap for stateful implementations.

**Note**: The RHS is just `support oa` (not bound with `init`) because `oa` is
a pure specification computation that doesn't depend on the oracle state.
-/
@[simp]
lemma support_bind_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ α : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support ((liftM q : OracleComp oSpec β))) :
    support (do let s ← init; (simulateQ impl oa).run' s) = support oa := by
  -- Expand the bind structure
  simp only [support_bind]
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · -- Forward direction: simulated support ⊆ spec support
    intro ⟨s, hs_init, hx_sim⟩
    -- Use the helper lemma
    have h_supp_eq := support_simulateQ_run'_eq impl oa s hImplSupp
    rw [h_supp_eq] at hx_sim
    exact hx_sim
  · -- Backward direction: spec support ⊆ simulated support
    intro hx_spec
    -- We need to show there exists s ∈ support init such that
    -- x ∈ support ((simulateQ impl oa).run' s)
    -- Since NeverFail init (or we can use support init.Nonempty), we can pick any s
    -- Use the helper lemma
    have h_init_nonempty : (support init).Nonempty :=
      support_nonempty_of_neverFails init hInit
    obtain ⟨s, hs_init⟩ := h_init_nonempty
    have h_supp_eq := support_simulateQ_run'_eq impl oa s hImplSupp
    -- h_supp_eq: support ((simulateQ impl oa).run' s) = support oa
    -- We have hx_spec: x ∈ support oa
    -- Need: x ∈ support ((simulateQ impl oa).run' s)
    rw [← h_supp_eq] at hx_spec
    exact ⟨s, hs_init, hx_spec⟩

/-- OptionT-wrapper version of `support_bind_simulateQ_run'_eq`. -/
@[simp]
lemma support_bind_simulateQ_run'_eq_mk
    {oSpec : OracleSpec ι} [IsUniformSpec oSpec] {σ α : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec (Option α))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support ((liftM q : OracleComp oSpec β))) :
    support (OptionT.mk (do let s ← init; (simulateQ impl oa).run' s) : OptionT ProbComp α) =
      support (OptionT.mk oa : OptionT (OracleComp oSpec) α) := by
  ext x
  simp only [OptionT.mem_support_iff, OptionT.run_mk]
  simpa using congrArg (fun S => (some x) ∈ S)
    (support_bind_simulateQ_run'_eq init impl oa hInit hImplSupp)

end SupportPreservation

section SimOracle2Lemmas
open OracleInterface OracleComp OracleSpec OracleQuery SimOracle

variable {ι : Type} {oSpec : OracleSpec ι} [IsUniformSpec oSpec]
  {ι₁ : Type} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]

/-- **Weak Safety Preservation for simOracle2** when `oa` is pure computation
  (no oracle queries). -/
@[simp]
lemma probFailure_simulateQ_simOracle2_eq_zero
    [[T₁]ₒ.Fintype] [[T₂]ₒ.Fintype] [[T₁]ₒ.Inhabited] [[T₂]ₒ.Inhabited]
    [IsUniformSpec (oSpec + ([T₁]ₒ + [T₂]ₒ))]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α : Type w} (oa : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) α)
    (h_oa : Pr[⊥ | oa] = 0) :
    Pr[⊥ |  simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) oa] = 0 := by
  -- simOracle2 returns QueryImpl spec (OracleComp specₜ), which is Stateless
  -- We prove this directly by induction, following the pattern of simulateQ_preserves_safety
  let so := OracleInterface.simOracle2 oSpec t₁ t₂
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, probFailure_bind_eq_zero_iff]
    constructor
    · -- The oracle implementation never fails
      exact probFailure_of_liftM_PMF (OracleInterface.simOracle2 oSpec t₁ t₂ t)
    · -- For each result in the support, the continuation is safe
      intro result h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      have h_result_in_spec : result ∈
          support (query t : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) := by
        simp only [input_query, OracleComp.support_liftM, cont_query, Set.range_id]
        exact Set.mem_univ result
      exact ih result (h_oa.2 result h_result_in_spec)

/--
**Generic Simulation Reduction**

This lemma reduces `simulateQ (simOracle2 ...) (liftM q)` to the
raw implementation `QueryImpl.mapQuery ((simOracle2 ...)) q`.

This allows you to eliminate `simulateQ` even if the specific query index
is generic or unknown at the moment.
-/
@[simp]
lemma simulateQ_simOracle2_liftM
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.Fintype]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α : Type w} (q : OracleQuery (oSpec + ([T₁]ₒ + [T₂]ₒ)) α) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (liftM q) =
    QueryImpl.mapQuery ((OracleInterface.simOracle2 oSpec t₁ t₂)) q := by
  -- This follows directly from the definition of simulateQ on a single query
  simp only [simulateQ_query, QueryImpl.mapQuery]

/-- Unfolds simOracle2 implementation for transcript 1. -/
@[simp]
lemma simOracle2_impl_inr_inl
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.Fintype]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₁) (t : OracleInterface.Query (T₁ i)) :
    QueryImpl.mapQuery ((OracleInterface.simOracle2 oSpec t₁ t₂)) (query (.inr (.inl ⟨i, t⟩))) =
    pure (OracleInterface.answer (t₁ i) t) :=
by rfl

/-- Unfolds simOracle2 implementation for transcript 2. -/
@[simp]
lemma simOracle2_impl_inr_inr
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.Fintype]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₂) (t : OracleInterface.Query (T₂ i)) :
    QueryImpl.mapQuery ((OracleInterface.simOracle2 oSpec t₁ t₂)) (query (.inr (.inr ⟨i, t⟩))) =
    pure (OracleInterface.answer (t₂ i) t) :=
by rfl

/-- Unfolds simOracle2 implementation for base queries. -/
@[simp]
lemma simOracle2_impl_inl
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.Fintype]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι) :
    QueryImpl.mapQuery ((OracleInterface.simOracle2 oSpec t₁ t₂)) (query (.inl i)) =
    liftM (query i) :=
by rfl

/-- **Oracle query unfolding**: This is the main lemma that converts the OracleComp
lifted from oracle queries into an almost deterministic form -/
@[simp]
lemma simulateQ_simOracle2_lift_liftComp_query_T1
    {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (j : ι₁) (pt : OracleInterface.Query (T₁ j)) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      ((OracleComp.lift (query ⟨j, pt⟩ : OracleQuery [T₁]ₒ _)).liftComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) =
    pure (OracleInterface.answer (t₁ j) pt) := by
  rfl

/-- **Oracle query unfolding (T2)**: Unfolds a query to the second transcript (T₂)
lifted into the full specification, resolving it to the deterministic honest answer. -/
@[simp]
lemma simulateQ_simOracle2_lift_liftComp_query_T2
    {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (j : ι₂) (pt : OracleInterface.Query (T₂ j)) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      ((OracleComp.lift (query ⟨j, pt⟩ : OracleQuery [T₂]ₒ _)).liftComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) =
    pure (OracleInterface.answer (t₂ j) pt) := by
  rfl

/-- `liftM` variant of `simulateQ_simOracle2_lift_liftComp_query_T1`. -/
@[simp]
lemma simulateQ_simOracle2_liftM_query_T1
    {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (j : ι₁) (pt : OracleInterface.Query (T₁ j)) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (query ⟨j, pt⟩ : OracleQuery [T₁]ₒ _) :
        OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) =
    pure (OracleInterface.answer (t₁ j) pt) := by
  rfl

/-- `liftM` variant of `simulateQ_simOracle2_lift_liftComp_query_T2`.
This is the form that matches terms like `simulateQ ... (liftM (query ⟨j, pt⟩))`. -/
@[simp]
lemma simulateQ_simOracle2_liftM_query_T2
    {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (j : ι₂) (pt : OracleInterface.Query (T₂ j)) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (query ⟨j, pt⟩ : OracleQuery [T₂]ₒ _) :
        OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) =
    pure (OracleInterface.answer (t₂ j) pt) := by
  rfl

/-- OptionT `liftM` variant of `simulateQ_simOracle2_liftM_query_T1`.
This matches goals where the lifted query lives in `OptionT (OracleComp ...)`. -/
@[simp]
lemma OptionT.simulateQ_simOracle2_liftM_query_T1
    {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (j : ι₁) (pt : OracleInterface.Query (T₁ j)) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (query ⟨j, pt⟩ : OracleQuery [T₁]ₒ _) :
        OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _) =
    pure (some (OracleInterface.answer (t₁ j) pt)) := by
  rfl

/-- OptionT `liftM` variant of `simulateQ_simOracle2_liftM_query_T2`.
This matches goals where the lifted query lives in `OptionT (OracleComp ...)`. -/
@[simp]
lemma OptionT.simulateQ_simOracle2_liftM_query_T2
    {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (j : ι₂) (pt : OracleInterface.Query (T₂ j)) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (query ⟨j, pt⟩ : OracleQuery [T₂]ₒ _) :
        OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _) =
    pure (some (OracleInterface.answer (t₂ j) pt)) := by
  rfl

end SimOracle2Lemmas

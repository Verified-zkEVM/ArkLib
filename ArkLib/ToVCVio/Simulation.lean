/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license vec described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.SimOracle
import ArkLib.ToVCVio.Lemmas
import ArkLib.OracleReduction.Execution
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ
import Mathlib.Data.ENNReal.Basic
import VCVio.OracleComp.EvalDist
import ArkLib.OracleReduction.OracleInterface
import VCVio.EvalDist.Instances.OptionT
import ArkLib.Data.Probability.Instances

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

open OracleSpec OracleComp ProtocolSpec Sum  HasEvalPMF

universe u v w

/-! Compatibility shims for legacy projection-style syntax used in this file. -/
postfix:102 ".support" => support
postfix:102 ".neverFails" => NeverFail
postfix:102 ".impl" => QueryImpl.mapQuery
postfix:102 ".OracleQuery" => OracleQuery

section ProbOutputNone

variable {m : Type u → Type v} [Monad m] [HasEvalSPMF m] {α β : Type u}

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
  simpa only [OptionT.bind, OptionT.run, OptionT.mk] using
    (_root_.probOutput_none_bind_eq_zero_iff
      (mx := OptionT.run mx)
      (my := fun x : Option α => match x with
        | some a => OptionT.run (my a)
        | none => (pure none : m (Option β))))

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
        (liftM (query (spec := spec₁) t) : OracleComp spec₂ _)) oa := by
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
        (liftM (query (spec := spec₁) t) : OracleComp spec₂ _)) oa :
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
    x ∈ support (simulateQ (fun s => liftM (query (spec := spec) s))
      (liftM (query (spec := spec) t)) : OracleComp spec (spec.Range t)) := by
  have heq : (fun s => liftM (query (spec := spec) s)) = QueryImpl.id' spec := by
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
lemma OptionT.simulateQ_failure' {α : Type u}
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
    HasEvalPMF.probFailure_eq_zero]

/-- **Generic Safety Preservation Lemma for Stateful Implementations**

If an oracle implementation is safe and support-faithful, then simulation preserves safety
from the specification level to the implementation level.

This is a key building block for completeness proofs: it shows that if the spec says
"this computation never fails" and the implementation only returns valid values
(support-faithful), then running the simulated implementation also never fails.

**Parameters:**
- `impl`: The stateful oracle implementation
- `hImplSafe`: Each query implementation is safe (never fails)
- `hImplSupp`: The implementation is support-faithful (only returns valid values)
- `oa`: The oracle computation at the spec level
- `s`: The current state
- `h_oa`: The spec computation is safe

**Conclusion:** The simulated computation is also safe. -/
theorem simulateQ_preserves_safety_stateful
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    Pr[⊥ | (simulateQ impl oa).run s] = 0 := by
  simp only [HasEvalPMF.probFailure_eq_zero]

/-- **Reverse Safety Preservation for Stateful Implementations**

If the simulated stateful computation is safe and the implementation has the same support
vec the specification, then the original specification computation is safe.

This is the reverse direction of `simulateQ_preserves_safety_stateful`.

**Note**: This requires support **equality** rather than just subset (⊆) because we need
to extract witnesses: if a result is valid in the spec, we need to know that the implementation
can actually produce it (surjectivity).
-/
lemma neverFails_of_simulateQ_stateful
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {α : Type} (oa : OracleComp oSpec α) :
    Pr[⊥ | oa] = 0 := by
  simp only [HasEvalPMF.probFailure_eq_zero]

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
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    Pr[⊥ | (simulateQ impl oa).run s] = 0 ↔ Pr[⊥ | oa] = 0 := by
  simp only [HasEvalPMF.probFailure_eq_zero]

/-- **Stateful Safety Biconditional (run' version)**

This is the `run'` version of `probFailure_simulateQ_iff_stateful`. It works with
`StateT.run'` which projects out only the result (discarding the final state),
rather than `StateT.run` which returns the full `(result, state)` pair.

This lemma is useful when the goal involves `(simulateQ impl oa).run' s` instead of
`(simulateQ impl oa).run s`.
-/
@[simp]
theorem probFailure_simulateQ_iff_stateful_run'
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    Pr[⊥ | (simulateQ impl oa).run' s] = 0 ↔ Pr[⊥ | oa] = 0 := by
  simp only [HasEvalPMF.probFailure_eq_zero]

/-- **Safety Preservation Lemma for Stateless Implementations**

If an oracle implementation is safe and support-faithful, then simulation preserves safety
from the specification level to the implementation level (stateless version).

This is the stateless counterpart to `simulateQ_preserves_safety_stateful`.
-/
theorem simulateQ_preserves_safety
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    (so : QueryImpl oSpec ProbComp)
    {α : Type} (oa : OracleComp oSpec α) :
    Pr[⊥ | simulateQ so oa] = 0 := by
  simp only [HasEvalPMF.probFailure_eq_zero]

/--
Safety preservation: A simulated protocol is safe if and only if the original
protocol is safe. This requires:
1. The implementation itself never fails (h_so).
2. The implementation doesn't return "illegal" values outside the spec (h_supp).
-/
@[simp]
lemma probFailure_simulateQ_iff (so : QueryImpl spec ProbComp) (oa : OracleComp spec α) :
    Pr[⊥ | simulateQ so oa] = 0 ↔ Pr[⊥ | oa] = 0 := by
  simp only [HasEvalPMF.probFailure_eq_zero]

/-- Challenge query implementations have the same support vec the specification.
    This is trivially true for uniform distributions. -/
@[simp]
lemma support_challengeQueryImpl_eq {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] (i : pSpec.ChallengeIdx) :
    (challengeQueryImpl.mapQuery
      (query (spec := [pSpec.Challenge]ₒ'challengeOracleInterface) ⟨i, ()⟩)).support =
    (liftM (query (spec := [pSpec.Challenge]ₒ'challengeOracleInterface) ⟨i, ()⟩) :
      OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) _).support := by
  simp [challengeQueryImpl, support_uniformSample (α := pSpec.Type i.val)]

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

/-- Simplifies `Reduction.run` by unfolding it into the prover's run and verifier's check. -/
@[simp]
lemma Reduction_run_def (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    reduction.run stmtIn witIn = (do
      let ⟨transcript, stmtOut, witOut⟩ ← reduction.prover.run stmtIn witIn
      let verifierStmtOut ← reduction.verifier.verify stmtIn transcript
      return ((transcript, stmtOut, witOut), verifierStmtOut)) :=
by
  unfold Reduction.run Verifier.run
  simp only [ChallengeIdx, Challenge, map_eq_bind_pure_comp, bind_pure_comp, OracleComp.liftM_OptionT_eq, Prod.mk.eta]
  congr 1
  funext proverResult
  rw [← OracleComp.liftM_OptionT_eq]
  simp only [Option.getM, liftM_OptionT_eq]
  dsimp [Bind.bind, OptionT.bind, OptionT.mk, Functor.map]
  -- LHS evaluates to OptionT lift matching while RHS evaluates to simulateQ
  -- Without exact simulation unification this cannot be proved by bind_congr.
  sorry

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

#check support_liftM

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

/-- Challenge query implementations have full support (stateful version).
    The first component of the result has the same support vec the spec. -/
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
    ChallengeIdx, Challenge, ofPFunctor_toPFunctor, support_liftM, Set.fmap_eq_image]
  change Prod.fst '' ((fun a => (a, s)) <$> _).support = _
  rw [support_map, Set.image_image]
  simp only [Set.image_id']
  -- monadLift : ProbComp → ProbComp is id by instMonadLiftSelf
  simp only [OracleQuery.cont_apply, liftM_map, support_map]
  dsimp only [liftM, instMonadLiftTOfOracleQuery, liftComp]
  rw [support_simulateQ_eq _ _ (fun q => ?_)]
  · simp only [support_uniformSample (α := pSpec.Challenge i), Challenge, Set.image_univ]
  · simp only [QueryImpl.mapQuery, support_map, support_liftM, OracleQuery.input_query,
    OracleQuery.cont_query, Set.range_id, Set.image_univ]

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
    simp only [simulateQ_pure, StateT.run'_pure_lib, support_pure]
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, StateT.run'_bind_lib, support_bind]
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro ⟨⟨x, s'⟩, h_pair, h_y⟩
      have h_x_spec : x ∈ support ((query t : OracleComp oSpec _)) := by
        exact mem_support_query t x
      have h_y_spec : y ∈ support ((oa x)) := by
        rw [← ih x s']
        exact h_y
      exact ⟨x, h_x_spec, h_y_spec⟩
    · intro ⟨x, h_x_spec, h_y_spec⟩
      have h_supp_eq := hImplSupp (query t) s
      have h_x_in_image : x ∈ Prod.fst <$> support ((QueryImpl.mapQuery impl (query t)).run s) := by
        rw [h_supp_eq]
        exact h_x_spec
      simp only [Set.fmap_eq_image, Set.mem_image] at h_x_in_image
      obtain ⟨pair, h_pair, h_fst_eq⟩ := h_x_in_image
      cases pair with | mk x' s' =>
      have h_x'_eq_x : x' = x := h_fst_eq
      have h_y_sim : y ∈ support ((simulateQ impl (oa x')).run' s') := by
        rw [ih x' s']
        rw [h_x'_eq_x]
        exact h_y_spec
      have h_y_sim' : y ∈ support (((simulateQ impl ∘ oa) x').run' s') := by
        simp only [Function.comp_apply]
        exact h_y_sim
      simp only [QueryImpl.mapQuery_query] at h_pair
      exact ⟨(x', s'), h_pair, h_y_sim'⟩

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
    {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (so : QueryImpl spec ProbComp) (oa : OracleComp spec (Option α))
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      support (so.mapQuery q) = support (liftM q : OracleComp spec β))
    (h : Pr[⊥ | (OptionT.mk (simulateQ so oa) : OptionT ProbComp α)] = 0) :
    Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp spec) α)] = 0 := by
  rw [OptionT.probFailure_mk] at h ⊢
  -- rw [probOutput_eq_zero_iff] at h ⊢
  simpa [support_simulateQ_eq so oa h_supp] using h

/-- OptionT-wrapper version of `simulateQ_preserves_safety` for option-valued computations. -/
theorem simulateQ_preserves_safety_mk
    {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (so : QueryImpl spec ProbComp) (oa : OracleComp spec (Option α))
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      support (so.mapQuery q) = support (liftM q : OracleComp spec β))
    (h_oa : Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp spec) α)] = 0) :
    Pr[⊥ | (OptionT.mk (simulateQ so oa) : OptionT ProbComp α)] = 0 := by
  rw [OptionT.probFailure_mk] at h_oa ⊢
  -- rw [probOutput_eq_zero_iff] at h_oa ⊢
  simpa [support_simulateQ_eq so oa h_supp] using h_oa

/-- OptionT-wrapper version of `probFailure_simulateQ_iff` for option-valued computations. -/
@[simp]
lemma probFailure_simulateQ_iff_mk
    {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
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
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (h_oa : Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp oSpec) α)] = 0) :
    Pr[⊥ | (OptionT.mk ((simulateQ impl oa).run' s) : OptionT ProbComp α)] = 0 := by
  rw [OptionT.probFailure_mk] at h_oa ⊢
  simp only [HasEvalPMF.probFailure_eq_zero, zero_add] at h_oa ⊢
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
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (oa : OracleComp oSpec (Option α)) (s : σ)
    (h : Pr[⊥ | (OptionT.mk ((simulateQ impl oa).run' s) : OptionT ProbComp α)] = 0) :
    Pr[⊥ | (OptionT.mk oa : OptionT (OracleComp oSpec) α)] = 0 := by
  rw [OptionT.probFailure_mk] at h ⊢
  simp only [HasEvalPMF.probFailure_eq_zero, zero_add] at h ⊢
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
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
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
    {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited] {α : Type}
    (oa : OracleComp spec α) (h : NeverFail oa) :
    (support oa).Nonempty := by
  have h_probFailure_eq_zero : Pr[⊥ | oa] = 0 := (probFailure_eq_zero_iff oa).2 h
  have h_event_pos : 0 < Pr[fun _ => True | oa] := by
    simp only [probEvent_True_eq_sub, HasEvalPMF.probFailure_eq_zero, tsub_zero, zero_lt_one]
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
(do let s ← init; (simulateQ impl oa).run' s).support = support oa
```

**Application**: When proving completeness, we often need to show that the support
of the simulated execution matches the support of the specification. This lemma
bridges that gap for stateful implementations.

**Note**: The RHS is just `support oa` (not bound with `init`) because `oa` is
a pure specification computation that doesn't depend on the oracle state.
-/
@[simp]
lemma support_bind_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((QueryImpl.mapQuery impl q).run s).support
        = support ((liftM q : OracleComp oSpec β))) :
    (do let s ← init; (simulateQ impl oa).run' s).support = support oa := by
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
    -- x ∈ (simulateQ impl oa).run' s).support
    -- Since NeverFail init (or we can use support init.Nonempty), we can pick any s
    -- Use the helper lemma
    have h_init_nonempty : (support init).Nonempty :=
      support_nonempty_of_neverFails init hInit
    obtain ⟨s, hs_init⟩ := h_init_nonempty
    have h_supp_eq := support_simulateQ_run'_eq impl oa s hImplSupp
    -- h_supp_eq: ((simulateQ impl oa).run' s).support = support oa
    -- We have hx_spec: x ∈ support oa
    -- Need: x ∈ ((simulateQ impl oa).run' s).support
    rw [← h_supp_eq] at hx_spec
    exact ⟨s, hs_init, hx_spec⟩

/-- OptionT-wrapper version of `support_bind_simulateQ_run'_eq`. -/
@[simp]
lemma support_bind_simulateQ_run'_eq_mk
    {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited] {σ α : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec (Option α))
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((QueryImpl.mapQuery impl q).run s).support
        = support ((liftM q : OracleComp oSpec β))) :
    support (OptionT.mk (do let s ← init; (simulateQ impl oa).run' s) : OptionT ProbComp α) =
      support (OptionT.mk oa : OptionT (OracleComp oSpec) α) := by
  ext x
  simp only [OptionT.mem_support_mk]
  simpa using congrArg (fun S => (some x) ∈ S)
    (support_bind_simulateQ_run'_eq init impl oa hInit hImplSupp)

end SupportPreservation

section SimOracle2Lemmas
open OracleInterface OracleComp OracleSpec OracleQuery SimOracle

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {ι₁ : Type} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]

/-- **Weak Safety Preservation for simOracle2** when `oa` is pure computation
  (no oracle queries). -/
@[simp]
lemma probFailure_simulateQ_simOracle2_eq_zero
    [[T₁]ₒ.Fintype] [[T₂]ₒ.Fintype] [[T₁]ₒ.Inhabited] [[T₂]ₒ.Inhabited]
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
      exact HasEvalPMF.probFailure_eq_zero (OracleInterface.simOracle2 oSpec t₁ t₂ t)
    · -- For each result in the support, the continuation is safe
      intro result h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      have h_result_in_spec : result ∈
          (query t : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _).support := by
        simp only [input_query, OracleComp.support_liftM, cont_query, Set.range_id, Set.mem_univ]
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

section ForInLemmas

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α β σ : Type}

/--
**Safety of forIn Loops (Sufficient Condition)**

If the loop body is safe for every element in the list and every possible state,
then the `forIn` loop is safe (never fails).

**Note:** The Right-Hand Side (`∀ s`) quantifies over *all* states `s`,
not just reachable ones. This makes the lemma useful for proving safety
"by inspection" without tracking complex state invariants.
For singleton states (like `PUnit`), this condition is both necessary and sufficient.

**Usage**: This is the key lemma for completeness proofs.
To show `Pr[⊥ | forIn l init f] = 0`, it suffices to show that each step
`Pr[⊥ | f x s] = 0` is safe for all elements and all states.
-/
lemma probFailure_forIn_eq_zero_of_body_safe
  {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]
    (l : List α) (init : σ) (f : α → σ → m (ForInStep σ))
    (h : ∀ x ∈ l, ∀ s, Pr[⊥ | f x s] = 0) :
    Pr[⊥ | forIn l init f] = 0 := by
  induction l generalizing init with
  | nil =>
    -- Base case: empty list returns `pure init`, which never fails.
    simp only [forIn, List.forIn'_nil, probFailure_pure]
  | cons x xs ih =>
    -- Inductive step: x :: xs
    -- Use List.forIn'_cons to expand into the bind structure
    simp only [forIn, List.forIn'_cons]
    -- Now apply the bind rewrite
    rw [probFailure_bind_eq_zero_iff]
    constructor
    · -- Head is safe
      apply h x List.mem_cons_self
    · -- Tail is safe
      intro step _
      cases step with
      | done s' =>
        -- If 'done', we return pure, which is safe
        simp only [probFailure_pure]
      | yield s' =>
        -- If 'yield', we continue the loop (recurse)
        -- Apply inductive hypothesis
        apply ih s'
        intro y hy_xs s_next
        -- Use the premise that all steps are safe
        apply h y (List.mem_cons_of_mem _ hy_xs)

/-- `OptionT` wrapper of `probFailure_forIn_eq_zero_of_body_safe`. -/
lemma OptionT.probFailure_forIn_eq_zero_of_body_safe
    {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    {α σ : Type}
    (l : List α) (init : σ)
    (f : α → σ → OptionT (OracleComp spec) (ForInStep σ))
    (h : ∀ x ∈ l, ∀ s, Pr[⊥ | f x s] = 0) :
    Pr[⊥ | forIn l init f] = 0 := by
  simpa using
    (_root_.probFailure_forIn_eq_zero_of_body_safe
      (m := OptionT (OracleComp spec)) (l := l) (init := init) (f := f) h)

/-- Convenience wrapper for goals written vec `Pr[⊥ | OptionT.mk (forIn ...)] = 0`. -/
lemma OptionT.probFailure_mk_forIn_eq_zero_of_body_safe
    {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    {α σ : Type}
    (l : List α) (init : σ)
    (f : α → σ → OptionT (OracleComp spec) (ForInStep σ))
    (h : ∀ x ∈ l, ∀ s, Pr[⊥ | f x s] = 0) :
    Pr[⊥ | OptionT.mk (forIn l init f : OptionT (OracleComp spec) σ)] = 0 := by
  simpa using
    (OptionT.probFailure_forIn_eq_zero_of_body_safe
      (spec := spec) (l := l) (init := init) (f := f) h)

/-- Prove forIn safety using an invariant.
    P done s: Predicate meaning state 's' is correct after processing 'done'. -/
lemma probFailure_forIn_of_invariant
    {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]
    {α σ : Type} (P : List α → σ → Prop)
    (l : List α) (init : σ) (f : α → σ → m (ForInStep σ))
    -- 1. Base: Invariant holds at start
    (h_start : P [] init)
    -- 2. Step: Preserves invariant and is safe
    (h_step : ∀ (done : List α) (x : α) (s : σ),
       x ∈ l → P done s →
       Pr[⊥ | f x s] = 0 ∧ ∀ s' ∈ support ((f x s)),
         match s' with
         | .yield next => P (done ++ [x]) next
         | .done next => P (done ++ [x]) next) :
    Pr[⊥ | forIn l init f] = 0 := by
  -- We define a helper that iterates over a suffix 'xs' given a prefix 'done'
  let rec aux (xs : List α) (done : List α) (s : σ)
      (h_decomp : l = done ++ xs) (h_inv : P done s) :
      Pr[⊥ |  forIn xs s f] = 0 := by
    induction xs generalizing done s with
    | nil =>
      simp only [forIn, List.forIn'_nil, probFailure_pure]
    | cons y ys ih =>
      simp only [forIn, List.forIn'_cons]
      rw [probFailure_bind_eq_zero_iff]
      -- Use h_step for the head element y
      have h_mem : y ∈ l := by
        rw [h_decomp]
        apply List.mem_append_right
        apply List.mem_cons_self
      obtain ⟨h_safe, h_next⟩ := h_step done y s h_mem h_inv
      constructor
      · exact h_safe
      · intro step h_step_supp
        cases step with
        | done next =>
          simp only [probFailure_pure]
        | yield next =>
          -- Apply IH for the tail with updated done list
          apply ih (done ++ [y]) next
          · -- Show l = (done ++ [y]) ++ ys
            rw [h_decomp]
            simp only [List.append_assoc, List.singleton_append]
          · -- Show P (done ++ [y]) next
            exact h_next (.yield next) h_step_supp
  -- Apply the helper to the full list
  exact aux l [] init (by simp) h_start

/--
Safety of a forIn loop using a sequence of relations.

- `l`: The list of items to iterate over.
- `rel`: A family of relations indexed by step count `i` and state `s`.
  `rel i s` means "After `i` steps, the state `s` is correct".
-/
lemma probFailure_forIn_of_relations
    {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]
    {α σ : Type}
    (l : List α)
    (init : σ)
    (f : α → σ → m (ForInStep σ))
    -- The sequence of relations: rel i s
    (rel : Fin (l.length + 1) → σ → Prop)
    -- 1. Base Case: Relation 0 holds for initial state
    (h_start : rel 0 init)
    -- 2. Inductive Step: rel i -> step safe -> rel (i+1)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       -- Given the relation holds at step k
       rel (k.castSucc) s →
       -- Then the step using the k-th element of the list is safe
       Pr[⊥ | f (l.get k) s] = 0 ∧
       -- And the result satisfies the relation at step k+1
       ∀ s' ∈ (f (l.get k) s).support,
         match s' with
         | .yield next => rel (k.succ) next
         | .done next => rel (k.succ) next) :
    Pr[⊥ | forIn l init f] = 0 := by
  -- Instead of using `probFailure_forIn_of_invariant` which has a weaker inductive hypothesis
  -- (it quantifies ∀ x ∈ l, losing the index information), we use a direct recursive helper.
  -- Helper: Proves safety for a suffix `xs` starting at index `k`.
  -- k: The current index in the original list `l`.
  -- xs: The suffix of `l` remaining to process.
  -- s: The current state.
  -- h_suffix: xs is indeed the suffix of l starting at k.
  -- h_len: k + xs.length = l.length (ensures indices are valid).
  -- h_rel: The relation holds for the current index k.
  let rec aux (k : ℕ) (xs : List α) (s : σ)
      (h_suffix : l.drop k = xs)
      (h_len : k + xs.length = l.length)
      (h_rel : rel ⟨k, by omega⟩ s) :
      Pr[⊥ |  forIn xs s f] = 0 := by
    induction xs generalizing k s with
    | nil =>
      simp only [forIn, List.forIn'_nil, probFailure_pure]
    | cons y ys ih =>
      simp only [forIn, List.forIn'_cons]
      rw [probFailure_bind_eq_zero_iff]
      -- Derive k < l.length from h_len
      have h_k_lt : k < l.length := by simp only [List.length_cons] at h_len; omega
      -- 1. Establish that y corresponds to l[k]
      have h_get : l.get ⟨k, h_k_lt⟩ = y := by
        have h_drop_eq : l[k]'h_k_lt = (l.drop k)[0]'(by simp [h_suffix]) := by
          simp only [List.getElem_drop, add_zero]
        simp only [List.get_eq_getElem, h_drop_eq, h_suffix, List.getElem_cons_zero]
      -- 2. Apply the hypothesis step
      let k_fin : Fin l.length := ⟨k, h_k_lt⟩
      -- We need to massage the types to match h_step
      have h_rel_cast : rel k_fin.castSucc s := by
        exact h_rel
      -- Get safety and next-state property
      obtain ⟨h_safe, h_next⟩ := h_step k_fin s h_rel_cast
      -- Rewrite l.get k to y
      rw [h_get] at h_safe h_next
      constructor
      · exact h_safe
      · intro step h_in_supp
        cases step with
        | done next =>
          simp only [probFailure_pure]
        | yield next =>
          -- 3. Recursive step
          specialize h_next (.yield next) h_in_supp
          -- Prepare arguments for recursion
          -- ih : ∀ (k : ℕ) (s : σ), l.drop k = ys → k + ys.length = l.length → rel ⟨k, _⟩ s → ...
          refine ih (k + 1) next ?h_suffix ?h_len ?h_rel
          case h_suffix =>
            -- Prove suffix maintenance: l.drop (k+1) = ys
            have : l.drop (k + 1) = (l.drop k).drop 1 := by rw [List.drop_drop]
            rw [this, h_suffix]
            simp only [List.drop_succ_cons, List.drop_zero]
          case h_len =>
            -- Prove length maintenance: (k+1) + ys.length = l.length
            simp only [List.length_cons] at h_len
            omega
          case h_rel =>
            -- Prove relation maintenance: rel ⟨k+1, _⟩ next
            exact h_next
  -- Apply the helper starting at index 0
  exact aux 0 l init (by simp only [List.drop_zero]) (by simp only [zero_add]) h_start

/-- Helper to extract the state from ForInStep, ignoring the control flow tag. -/
def ForInStep.state : ForInStep σ → σ
  | .yield s => s
  | .done s => s

/--
Safety of a forIn loop using a sequence of relations (Simplified).
Using `ForInStep.state` removes the need to pattern match on yield/done in the proof.
-/
lemma probFailure_forIn_of_relations_simplified
    {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]
    {α σ : Type} (l : List α) (init : σ)
    (f : α → σ → m (ForInStep σ))
    (rel : Fin (l.length + 1) → σ → Prop)
    -- 1. Base Case
    (h_start : rel 0 init)
    -- 2. Inductive Step (Simplified)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       rel (k.castSucc) s →
       Pr[⊥ | f (l.get k) s] = 0 ∧
       -- Simplified: Just check the result state, no 'match' needed
       ∀ res ∈ (f (l.get k) s).support, rel (k.succ) res.state) :
    Pr[⊥ | forIn l init f] = 0 := by
  apply probFailure_forIn_of_relations l init f rel h_start
  intro k s h_rel
  obtain ⟨h_safe, h_next⟩ := h_step k s h_rel
  constructor
  · exact h_safe
  · intro s' h_supp
    specialize h_next s' h_supp
    -- The original lemma expects the match; we prove it holds using our simplified assumption
    cases s' <;> exact h_next

/--
If a relation `rel` is inductive over a `forIn` loop, then any output `x`
in the support of the loop satisfies `rel l.length x`.
-/
lemma support_forIn_subset_rel
    {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]
    {α σ : Type}
    (l : List α) (init : σ) (f : α → σ → m (ForInStep σ))
    (rel : Fin (l.length + 1) → σ → Prop)
    (h_start : rel 0 init)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       rel k.castSucc s →
       ∀ res ∈ (f (l.get k) s).support,
         match res with
         | .yield next => rel k.succ next
         | .done next => rel ⟨l.length, by omega⟩ next) :
    ∀ x ∈ support ((forIn l init f)), rel ⟨l.length, by omega⟩ x := by
  -- Helper: Proves safety for a suffix `xs` starting at index `k`.
  let rec aux (k : ℕ) (xs : List α) (s : σ)
      (h_suffix : l.drop k = xs)
      (h_len : k + xs.length = l.length)
      (h_rel : rel ⟨k, by omega⟩ s) :
      ∀ x ∈ support ((forIn xs s f)), rel ⟨l.length, by omega⟩ x := by
    induction xs generalizing k s with
    | nil =>
      -- Base case: xs is empty, so we are at the end.
      simp only [List.length_nil, add_zero] at h_len
      have h_k_eq : k = l.length := h_len
      subst h_k_eq
      simp only [forIn, List.forIn'_nil, support_pure, Set.mem_singleton_iff,
        forall_eq]
      exact h_rel
    | cons y ys ih =>
      simp only [forIn, List.forIn'_cons, support_bind, Set.mem_iUnion, exists_prop]
      intro x h_supp
      obtain ⟨step, h_step_supp, h_x_in_step⟩ := h_supp
      -- Prepare to use h_step
      have h_k_lt : k < l.length := by simp only [List.length_cons] at h_len; omega
      have h_get : l.get ⟨k, h_k_lt⟩ = y := by
        have h_drop_eq : l[k]'h_k_lt = (l.drop k)[0]'(by simp [h_suffix]) := by
            simp only [List.getElem_drop, add_zero]
        simp only [List.get_eq_getElem, h_drop_eq, h_suffix, List.getElem_cons_zero]
      let k_fin : Fin l.length := ⟨k, h_k_lt⟩
      have h_rel_cast : rel k_fin.castSucc s := h_rel
      specialize h_step k_fin s h_rel_cast step
      rw [h_get] at h_step
      specialize h_step h_step_supp
      cases step with
      | done next =>
        -- Early termination: result is next
        simp only [support_pure, Set.mem_singleton_iff] at h_x_in_step
        rw [h_x_in_step]
        exact h_step
      | yield next =>
        -- Continue loop: recurse
        -- h_step : rel k.succ next
        have h_len' : k + 1 + ys.length = l.length := by
          simp only [List.length_cons] at h_len
          rw [add_assoc, add_comm 1, ←add_assoc]
          exact h_len
        -- Apply IH
        -- ih type: ∀ (k : ℕ) (s : σ), l.drop k = ys → k + ys.length = l.length →
        -- rel ... → ∀ x ∈ ..., ...
        exact ih (k + 1) next
          (by rw [←List.drop_drop, h_suffix]; rfl)
          h_len'
          h_step
          x
          h_x_in_step
  -- Apply helper
  exact aux 0 l init (by simp) (by simp) h_start

/--
A simplified version of `support_forIn_subset_rel` for loops that **never abort early**.
This is perfect for Sumcheck folding, which processes the entire list.

It requires proving two things for each step result `res`:
1. `res = .yield res.state` (The loop continues)
2. `rel k.succ res.state` (The invariant is preserved)
-/
lemma support_forIn_subset_rel_yield_only
    {m : Type _ → Type _} [Monad m] [HasEvalSPMF m]
    {α σ : Type}
    (l : List α) (init : σ) (f : α → σ → m (ForInStep σ))
    (rel : Fin (l.length + 1) → σ → Prop)
    -- 1. Base Case
    (h_start : rel 0 init)
    -- 2. Inductive Step (Yield Only)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       rel k.castSucc s →
       ∀ res ∈ (f (l.get k) s).support,
         res = .yield res.state ∧ rel k.succ res.state) :
    ∀ x ∈ support ((forIn l init f)), rel ⟨l.length, by omega⟩ x := by
  -- We apply the general lemma
  apply support_forIn_subset_rel l init f rel h_start
  -- We prove the general hypothesis using our "yield only" assumption
  intro k s h_rel res h_mem
  specialize h_step k s h_rel res h_mem
  -- Use the fact that it is a yield to satisfy the match
  rcases h_step with ⟨h_is_yield, h_next_rel⟩
  rw [h_is_yield]
  exact h_next_rel

/-- Distributes `liftComp` over a `forIn` loop.
    Corrected to allow specs with DIFFERENT index types (ι and ι'). -/
@[simp]
lemma liftComp_forIn {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [spec.Fintype] [superSpec.Fintype]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    {α β : Type} (l : List α) (init : β)
    (f : α → β → OracleComp spec (ForInStep β)) :
    (forIn l init f).liftComp superSpec =
    forIn l init (fun a b ↦ (f a b).liftComp superSpec) := by
  induction l generalizing init with
  | nil =>
    simp only [forIn, List.forIn'_nil, liftComp_pure]
  | cons x xs ih =>
    simp only [forIn, List.forIn'_cons, liftComp_bind]
    congr; funext s
    cases s <;> simp only [liftComp_pure, forIn'_eq_forIn, ih]

/-- Distributes `simulateQ` over a `forIn` loop.
This allows us to verify the body of the loop under simulation.
-/
@[simp]
lemma simulateQ_forIn {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (l : List α) (init : β)
    (f : α → β → OracleComp spec (ForInStep β)) :
    simulateQ so (forIn l init f) =
    forIn l init (fun a b ↦ simulateQ so (f a b)) := by
  induction l generalizing init with
  | nil =>
    -- Base case: pure init
    simp only [forIn, List.forIn'_nil, simulateQ_pure]
  | cons x xs ih =>
    -- Inductive case: step >>= ...
    simp only [forIn, List.forIn'_cons, simulateQ_bind]
    -- Use the induction hypothesis for the continuation
    congr; funext s
    cases s
    · -- Done: pure
      simp only [simulateQ_pure]
    · -- Yield: recurse (apply IH)
      apply ih

/-- `OptionT` variant of `simulateQ_forIn`. -/
@[simp]
lemma OptionT.simulateQ_forIn
    {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (l : List α) (init : β)
    (f : α → β → OptionT (OracleComp spec) (ForInStep β)) :
    simulateQ so (forIn l init f : OptionT (OracleComp spec) β) =
      (forIn l init (fun a b ↦ simulateQ so (f a b)) :
        OptionT (OracleComp superSpec) β) := by
  induction l generalizing init with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [forIn, List.forIn'_cons]
      change simulateQ so (OptionT.bind (f x init) (fun step =>
        match step with
        | ForInStep.done b => pure b
        | ForInStep.yield b => forIn' xs b (fun a' _ b => f a' b))) =
        OptionT.bind (simulateQ so (f x init)) (fun step =>
          match step with
          | ForInStep.done b => pure b
          | ForInStep.yield b => forIn' xs b (fun a' _ b => simulateQ so (f a' b)))
      rw [OptionT.simulateQ_bind]
      apply bind_congr
      intro step
      cases step with
      | none => simp
      | some step =>
          cases step with
          | done res => rfl
          | yield res => simpa [forIn'_eq_forIn] using ih res

/-- Stateful version of simulateQ_forIn.
    Distributes simulation over a loop where the oracle implementation itself has state. -/
@[simp]
lemma simulateQ_forIn_stateful_run_eq {ι : Type} {spec : OracleSpec ι}
    {σ α β : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (l : List α) (init : β) (f : α → β → OracleComp spec (ForInStep β)) (s : σ) :
    (simulateQ impl (forIn l init f)).run s =
    (forIn l init (fun a b => simulateQ impl (f a b))).run s := by
  induction l generalizing init s with
  | nil =>
      -- Base case: both sides reduce to pure init
      simp only [forIn, List.forIn'_nil, simulateQ_pure, StateT.run_pure]
  | cons x xs ih =>
      -- Inductive case: x :: xs
      simp only [forIn, List.forIn'_cons, simulateQ_bind, StateT.run_bind]
      congr
      funext pair
      rcases pair with ⟨step, s'⟩
      cases step with
      | done res => simp only [forIn'_eq_forIn, Function.comp_apply, simulateQ_pure,
        StateT.run_pure]
      | yield res => exact ih res s'

/-- Distributes stateful simulation over forIn at the StateT level. -/
@[simp]
lemma simulateQ_forIn_stateful_comp {ι : Type} {spec : OracleSpec ι}
    {σ α β : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (l : List α) (init : β) (f : α → β → OracleComp spec (ForInStep β)) :
    simulateQ impl (forIn l init f) =
    forIn l init (fun a b => simulateQ impl (f a b)) := by
  -- Proof is by induction on l, matching the structure of forIn unrolling
  induction l generalizing init with
  | nil => simp [forIn, simulateQ_pure]
  | cons x xs ih =>
      simp only [forIn, List.forIn'_cons, simulateQ_bind]
      congr; funext step
      cases step with
      | done res => simp [simulateQ_pure]
      | yield res => exact ih res

/-- Stateful `StateT` specialization of `OptionT.simulateQ_bind`. -/
@[simp]
lemma OptionT.simulateQ_bind_stateful {ι : Type} {spec : OracleSpec ι}
    {σ α β : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (mx : OptionT (OracleComp spec) α) (my : α → OptionT (OracleComp spec) β) :
    simulateQ impl (OptionT.bind mx my) =
      OptionT.bind (m := StateT σ ProbComp) (simulateQ impl mx)
        (fun x => simulateQ impl (my x)) := by
  change
    simulateQ impl (mx >>= fun z => match z with | some a => my a | none => pure none) =
      OptionT.bind (m := StateT σ ProbComp) (simulateQ impl mx) (fun x => simulateQ impl (my x))
  rw [_root_.simulateQ_bind]
  simp only [OptionT.bind, OptionT.mk]
  apply bind_congr
  intro z
  cases z <;> rfl

/-- `OptionT` version of `simulateQ_forIn_stateful_comp`. -/
@[simp]
lemma OptionT.simulateQ_forIn_stateful_comp {ι : Type} {spec : OracleSpec ι}
    {σ α β : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (l : List α) (init : β) (f : α → β → OptionT (OracleComp spec) (ForInStep β)) :
    simulateQ impl (forIn l init f : OptionT (OracleComp spec) β) =
      (forIn l init (fun a b => simulateQ impl (f a b)) :
        OptionT (StateT σ ProbComp) β) := by
  induction l generalizing init with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [forIn, List.forIn'_cons]
      change simulateQ impl (OptionT.bind (f x init) (fun step =>
        match step with
        | ForInStep.done b => pure b
        | ForInStep.yield b => forIn' xs b (fun a' _ b => f a' b))) =
        OptionT.bind (m := StateT σ ProbComp) (simulateQ impl (f x init)) (fun step =>
          match step with
          | ForInStep.done b => pure b
          | ForInStep.yield b => forIn' xs b (fun a' _ b => simulateQ impl (f a' b)))
      rw [OptionT.simulateQ_bind_stateful]
      apply bind_congr
      intro step
      cases step with
      | none => simp
      | some step =>
          cases step with
          | done res => rfl
          | yield res => simpa [forIn'_eq_forIn] using ih res

/-- **Loop Path Extraction**:
    If a stateful forIn loop over PUnit reaches a final state, then for every element
    in the list, there must exist a local start state and end state such that the
    body of that iteration succeeded.
    **Important:** this requires the loop body to be yield-only on support
    (i.e. no early `.done`). -/
lemma exists_path_of_mem_support_forIn_unit {σ α : Type} [spec.Fintype]
    (l : List α) (f : α → PUnit → StateT σ ProbComp (ForInStep PUnit))
    (s_init s_final : σ) (u : PUnit)
    (h_yield : ∀ (x : α) (s_pre : σ) (res_step : ForInStep PUnit × σ),
      res_step ∈ ((f x PUnit.unit).run s_pre).support →
      res_step.1 = ForInStep.yield PUnit.unit)
    (h_mem : (u, s_final) ∈ ((forIn l PUnit.unit f).run s_init).support) :
    ∀ x ∈ l, ∃ s_pre s_post,
      (ForInStep.yield PUnit.unit, s_post) ∈ ((f x PUnit.unit).run s_pre).support := by
    induction l generalizing s_init s_final u with
    | nil => simp
    | cons a t ih =>
      simp only [forIn, List.forIn'_cons] at h_mem
      intro x hx
      simp only [List.mem_cons] at hx
      simp only [StateT.run_bind, support_bind,
        Set.mem_iUnion, exists_prop, Prod.exists] at h_mem
      obtain ⟨step, s_mid, h_step_mem, h_rest⟩ := h_mem
      have h_y := h_yield a s_init (step, s_mid) h_step_mem
      simp only at h_y; subst h_y
      simp only [forIn'_eq_forIn] at h_rest
      rcases hx with rfl | hx
      · exact ⟨s_init, s_mid, h_step_mem⟩
      · exact ih s_mid s_final u h_rest x hx

lemma OptionT.exists_path_of_mem_support_forIn_unit {σ α : Type} [spec.Fintype]
    (l : List α) (f : α → PUnit → OptionT (StateT σ ProbComp) (ForInStep PUnit))
    (s_init s_final : σ) (u : PUnit)
    (h_yield : ∀ (x : α) (s_pre : σ) (res_step : ForInStep PUnit × σ),
      (some res_step.1, res_step.2) ∈ ((f x PUnit.unit).run s_pre).support →
      res_step.1 = ForInStep.yield PUnit.unit)
    (h_mem : (some u, s_final) ∈ ((forIn l PUnit.unit f).run s_init).support) :
    ∀ x ∈ l, ∃ s_pre s_post,
      (some (ForInStep.yield PUnit.unit), s_post) ∈
        ((f x PUnit.unit).run s_pre).support := by
    induction l generalizing s_init s_final u with
    | nil => simp
    | cons a t ih =>
      simp only [forIn, List.forIn'_cons] at h_mem
      rw [OptionT.run_bind] at h_mem
      simp only [Option.elimM, OptionT.run] at h_mem
      rw [show ∀ (m : StateT σ ProbComp _)
          (g : _ → StateT σ ProbComp _) (s : σ),
          (m >>= g) s = m.run s >>= fun p => (g p.1).run p.2
        from fun _ _ _ => rfl] at h_mem
      rw [_root_.mem_support_bind_iff] at h_mem
      obtain ⟨⟨opt_step, s_mid⟩, h_step_mem, h_rest⟩ := h_mem
      cases h_opt : opt_step with
      | none =>
          simp [h_opt] at h_rest
      | some step =>
          have h_step_some_mem : (some step, s_mid) ∈ ((f a PUnit.unit).run s_init).support := by
            simpa [h_opt] using h_step_mem
          have h_step_yield : step = ForInStep.yield PUnit.unit :=
            h_yield a s_init (step, s_mid) h_step_some_mem
          cases h_step_yield
          simp only [h_opt, Option.elim, forIn'_eq_forIn] at h_rest
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨s_init, s_mid, h_step_some_mem⟩
          · exact ih s_mid s_final u h_rest x hx

/-- **Stateful forIn: path + relation from support** (combines path extraction and
relation induction).
Given a stateful forIn loop, a relation `rel : Fin (l.length + 1) → β → σ → Prop`, base case and
step preservation, and a result `res` in the loop support, this lemma provides:
1. The final relation holds: `rel ⟨l.length, _⟩ res.1 res.2`
2. A constructive path: sequences `bs` and `ss` such that `(bs 0, ss 0) = (init, s)`,
   `(bs ⟨l.length, _⟩, ss ⟨l.length, _⟩) = (res.1, res.2)`, each step
   `(.yield (bs k.succ), ss k.succ)` is in the support of the body run from
      `(bs k.castSucc, ss k.castSucc)`, and `rel k (bs k) (ss k)` for all `k`.
So you get both "exists_path_of_mem_support_forIn_unit"-style per-step membership and
"support_forIn_stateful_of_relations"-style relation at every index (including the final one).
**Note:** This also assumes the loop body is yield-only on support, so the loop does not stop
early via `.done`.
The loop's `.run` support is `Set (β × σ)` (the accumulated value and state); each body step's
support is `Set (ForInStep β × σ)`, hence `h_step` uses `ForInStep.state res_step.1`. -/
@[simp]
lemma exists_rel_path_of_mem_support_forIn_stateful {ι : Type} {spec : OracleSpec ι} [spec.Fintype]
    {α σ β : Type} (l : List α) (init : β) (f : α → β → StateT σ ProbComp (ForInStep β))
    (s : σ)
    (rel : Fin (l.length + 1) → β → σ → Prop)
    (h_start : rel 0 init s)
    (h_step : ∀ (k : Fin l.length) (b : β) (s_curr : σ),
      rel k.castSucc b s_curr →
      ∀ res_step ∈ ((f (l.get k) b).run s_curr).support,
        rel k.succ (ForInStep.state res_step.1) res_step.2)
    (h_yield : ∀ (x : α) (b : β) (s_curr : σ) (res_step : ForInStep β × σ),
      res_step ∈ ((f x b).run s_curr).support →
      ∃ b', res_step.1 = ForInStep.yield b')
    (res : β × σ)
    (h_mem : res ∈ ((forIn l init f).run s).support) :
    rel ⟨l.length, by omega⟩ res.1 res.2 ∧
    ∃ (bs : Fin (l.length + 1) → β) (ss : Fin (l.length + 1) → σ),
      bs 0 = init ∧ ss 0 = s ∧
      bs ⟨l.length, by omega⟩ = res.1 ∧ ss ⟨l.length, by omega⟩ = res.2 ∧
      (∀ k : Fin l.length,
        (ForInStep.yield (bs k.succ), ss k.succ) ∈
          ((f (l.get k) (bs k.castSucc)).run (ss k.castSucc)).support) ∧
      (∀ k : Fin (l.length + 1), rel k (bs k) (ss k)) := by
  -- Helper: suffix induction parameterized by k (number of elements already processed).
  -- Simultaneously constructs the relation proof and the path witnesses.
  let rec aux (k : ℕ) (xs : List α) (b₀ : β) (s₀ : σ)
      (h_suffix : l.drop k = xs)
      (h_len : k + xs.length = l.length)
      (h_rel : rel ⟨k, by omega⟩ b₀ s₀)
      -- Accumulated path from step 0 to step k
      (bs_acc : Fin (k + 1) → β) (ss_acc : Fin (k + 1) → σ)
      (h_bs0 : bs_acc 0 = init) (h_ss0 : ss_acc 0 = s)
      (h_bsk : bs_acc ⟨k, by omega⟩ = b₀) (h_ssk : ss_acc ⟨k, by omega⟩ = s₀)
      (h_acc_steps : ∀ j : Fin k, (j.val < l.length) →
        (ForInStep.yield (bs_acc ⟨j.val + 1, by omega⟩), ss_acc ⟨j.val + 1, by omega⟩) ∈
          ((f (l.get ⟨j.val, by omega⟩) (bs_acc ⟨j.val, by omega⟩)).run
            (ss_acc ⟨j.val, by omega⟩)).support)
      (h_acc_rels : ∀ j : Fin (k + 1), rel ⟨j.val, by omega⟩ (bs_acc j) (ss_acc j))
      (res' : β × σ)
      (h_mem' : res' ∈ ((forIn xs b₀ f : StateT σ ProbComp β).run s₀).support) :
      rel ⟨l.length, by omega⟩ res'.1 res'.2 ∧
      ∃ (bs : Fin (l.length + 1) → β) (ss : Fin (l.length + 1) → σ),
        bs 0 = init ∧ ss 0 = s ∧
        bs ⟨l.length, by omega⟩ = res'.1 ∧ ss ⟨l.length, by omega⟩ = res'.2 ∧
        (∀ j : Fin l.length,
          (ForInStep.yield (bs j.succ), ss j.succ) ∈
            ((f (l.get j) (bs j.castSucc)).run (ss j.castSucc)).support) ∧
        (∀ j : Fin (l.length + 1), rel j (bs j) (ss j)) := by
    induction xs generalizing k b₀ s₀ bs_acc ss_acc with
    | nil =>
      -- xs = [], so k = l.length
      simp only [List.length_nil, add_zero] at h_len
      have h_k_eq : k = l.length := h_len
      have h_run : ((forIn ([] : List α) b₀ f : StateT σ ProbComp β).run s₀) =
          pure (b₀, s₀) := rfl
      rw [h_run, support_pure, Set.mem_singleton_iff] at h_mem'
      subst h_mem'
      subst h_k_eq
      refine ⟨h_rel, ?_⟩
      -- Extend bs_acc and ss_acc to Fin (l.length + 1) — already the right size
      exact ⟨bs_acc, ss_acc, h_bs0, h_ss0, h_bsk, h_ssk,
        fun j => h_acc_steps ⟨j.val, by exact j.isLt⟩ j.isLt,
        fun j => by exact h_acc_rels j⟩
    | cons y ys ih =>
      -- Unfold forIn for (y :: ys)
      simp only [forIn, List.forIn'_cons, support_bind, Set.mem_iUnion, exists_prop,
        StateT.run_bind] at h_mem'
      obtain ⟨⟨step, s'⟩, h_step_sup, h_rest_sup⟩ := h_mem'
      -- step must be yield
      obtain ⟨b', h_yield_eq⟩ := h_yield y b₀ s₀ _ h_step_sup
      subst h_yield_eq
      -- Simplify match in h_rest_sup
      simp only [ForInStep.casesOn] at h_rest_sup
      -- y = l.get ⟨k, ...⟩
      have h_k_lt : k < l.length := by simp only [List.length_cons] at h_len; omega
      have h_y_eq : y = l.get ⟨k, h_k_lt⟩ := by
        have h_len_drop : 0 < (l.drop k).length := by rw [h_suffix]; exact Nat.zero_lt_succ _
        have : l[k]'h_k_lt = (l.drop k)[0]'h_len_drop := by
          simp only [List.getElem_drop, Nat.add_zero]
        simp only [List.get_eq_getElem, this, h_suffix, List.getElem_cons_zero]
      -- From h_step: relation advances
      have h_rel_next : rel ⟨k + 1, by omega⟩ b' s' := by
        have h_app := h_step ⟨k, h_k_lt⟩ b₀ s₀
          h_rel
          ⟨.yield b', s'⟩
          (by
            have hn := h_step_sup
            rw [← h_y_eq]
            exact hn)
        simp only [Fin.succ, ForInStep.state] at h_app
        exact h_app
      -- Extend accumulated path by one step
      let bs_next : Fin (k + 1 + 1) → β := fun j =>
        if h : j.val ≤ k then bs_acc ⟨j.val, by omega⟩ else b'
      let ss_next : Fin (k + 1 + 1) → σ := fun j =>
        if h : j.val ≤ k then ss_acc ⟨j.val, by omega⟩ else s'
      have h_suffix_ys : l.drop (k + 1) = ys := by
        rw [← List.drop_drop, h_suffix]; rfl
      -- Apply IH
      exact ih (k + 1) b' s'
        h_suffix_ys
        (by simp only [List.length_cons] at h_len; omega)
        h_rel_next
        bs_next ss_next
        (by simp [bs_next, h_bs0])
        (by simp [ss_next, h_ss0])
        (by simp [bs_next])
        (by simp [ss_next])
        (by
          intro j h_j_lt
          by_cases hj : j.val < k
          · have h_from_acc := h_acc_steps ⟨j.val, by omega⟩ (by omega)
            simp only [bs_next, ss_next,
              show j.val + 1 ≤ k from by omega, show j.val ≤ k from by omega, ↓reduceDIte]
            exact h_from_acc
          · have h_j_eq : j.val = k := by omega
            simp only [h_j_eq, List.get_eq_getElem, le_refl, ↓reduceDIte, add_le_iff_nonpos_right,
              nonpos_iff_eq_zero, one_ne_zero, bs_next, ss_next]
            have hn := h_step_sup
            rw [h_y_eq, h_bsk.symm, h_ssk.symm] at hn
            exact hn)
        (by
          intro j
          by_cases hj : j.val ≤ k
          · simp only [bs_next, ss_next, hj, ↓reduceDIte]
            exact h_acc_rels ⟨j.val, by omega⟩
          · have h_j_eq : j.val = k + 1 := by omega
            have h_neg : ¬ (k + 1 ≤ k) := by omega
            simp only [bs_next, ss_next, h_j_eq, h_neg, ↓reduceDIte]
            exact h_rel_next)
        h_rest_sup
  -- Apply the helper starting at index 0
  exact aux 0 l init s rfl (by omega) h_start
    (fun _ => init) (fun _ => s) rfl rfl rfl rfl
    (fun j => by exact Fin.elim0 j)
    (fun j => by have : j = 0 := Fin.eq_zero j; subst this; simpa using h_start)
    res h_mem

/-- `OptionT` variant of `exists_rel_path_of_mem_support_forIn_stateful`.

This keeps the same path/relation conclusion over `β`, while all support facts are
expressed through the `some` branch of `OptionT.run`. -/
@[simp]
lemma OptionT.exists_rel_path_of_mem_support_forIn_stateful {ι : Type} {spec : OracleSpec ι}
    [spec.Fintype]
    {α σ β : Type} (l : List α) (init : β)
    (f : α → β → OptionT (StateT σ ProbComp) (ForInStep β))
    (s : σ)
    (rel : Fin (l.length + 1) → Option β → σ → Prop)
    (h_start : rel 0 (some init) s)
    (h_step : ∀ (k : Fin l.length) (b : β) (s_curr : σ),
      rel k.castSucc (some b) s_curr →
      ∀ (res_step : ForInStep β × σ),
        (some res_step.1, res_step.2) ∈ ((f (l.get k) b).run s_curr).support →
        rel k.succ (some (ForInStep.state res_step.1)) res_step.2)
    (h_yield : ∀ (x : α) (b : β) (s_curr : σ) (res_step : ForInStep β × σ),
      (some res_step.1, res_step.2) ∈ ((f x b).run s_curr).support →
      ∃ b', res_step.1 = ForInStep.yield b')
    (res : β × σ)
    (h_mem : (some res.1, res.2) ∈ ((forIn l init f).run s).support) :
    rel ⟨l.length, by omega⟩ (some res.1) res.2 ∧
    ∃ (bs : Fin (l.length + 1) → β) (ss : Fin (l.length + 1) → σ),
      bs 0 = init ∧ ss 0 = s ∧
      bs ⟨l.length, by omega⟩ = res.1 ∧ ss ⟨l.length, by omega⟩ = res.2 ∧
      (∀ k : Fin l.length,
        (some (ForInStep.yield (bs k.succ)), ss k.succ) ∈
          ((f (l.get k) (bs k.castSucc)).run (ss k.castSucc)).support) ∧
      (∀ k : Fin (l.length + 1), rel k (some (bs k)) (ss k)) := by
  let rec aux (k : ℕ) (xs : List α) (b₀ : β) (s₀ : σ)
      (h_suffix : l.drop k = xs)
      (h_len : k + xs.length = l.length)
      (h_rel : rel ⟨k, by omega⟩ (some b₀) s₀)
      (bs_acc : Fin (k + 1) → β) (ss_acc : Fin (k + 1) → σ)
      (h_bs0 : bs_acc 0 = init) (h_ss0 : ss_acc 0 = s)
      (h_bsk : bs_acc ⟨k, by omega⟩ = b₀) (h_ssk : ss_acc ⟨k, by omega⟩ = s₀)
      (h_acc_steps : ∀ j : Fin k, (j.val < l.length) →
        (some (ForInStep.yield (bs_acc ⟨j.val + 1, by omega⟩)), ss_acc ⟨j.val + 1, by omega⟩) ∈
          ((f (l.get ⟨j.val, by omega⟩) (bs_acc ⟨j.val, by omega⟩)).run
            (ss_acc ⟨j.val, by omega⟩)).support)
      (h_acc_rels : ∀ j : Fin (k + 1), rel ⟨j.val, by omega⟩ (some (bs_acc j)) (ss_acc j))
      (res' : β × σ)
      (h_mem' : (some res'.1, res'.2) ∈
        ((forIn xs b₀ f : OptionT (StateT σ ProbComp) β).run s₀).support) :
      rel ⟨l.length, by omega⟩ (some res'.1) res'.2 ∧
      ∃ (bs : Fin (l.length + 1) → β) (ss : Fin (l.length + 1) → σ),
        bs 0 = init ∧ ss 0 = s ∧
        bs ⟨l.length, by omega⟩ = res'.1 ∧ ss ⟨l.length, by omega⟩ = res'.2 ∧
        (∀ j : Fin l.length,
          (some (ForInStep.yield (bs j.succ)), ss j.succ) ∈
            ((f (l.get j) (bs j.castSucc)).run (ss j.castSucc)).support) ∧
        (∀ j : Fin (l.length + 1), rel j (some (bs j)) (ss j)) := by
    induction xs generalizing k b₀ s₀ bs_acc ss_acc with
    | nil =>
      simp only [List.length_nil, add_zero] at h_len
      have h_k_eq : k = l.length := h_len
      have h_run : ((forIn ([] : List α) b₀ f : OptionT (StateT σ ProbComp) β).run s₀) =
          pure (some b₀, s₀) := rfl
      rw [h_run, support_pure, Set.mem_singleton_iff] at h_mem'
      have h_res_eq : res'.1 = b₀ ∧ res'.2 = s₀ := by
        simpa [Prod.mk.injEq, Option.some.injEq] using h_mem'
      rcases h_res_eq with ⟨h_res1, h_res2⟩
      subst h_res1; subst h_res2
      subst h_k_eq
      refine ⟨h_rel, ?_⟩
      exact ⟨bs_acc, ss_acc, h_bs0, h_ss0, h_bsk, h_ssk,
        fun j => h_acc_steps ⟨j.val, by exact j.isLt⟩ j.isLt,
        fun j => by exact h_acc_rels j⟩
    | cons y ys ih =>
      simp only [forIn, List.forIn'_cons] at h_mem'
      rw [OptionT.run_bind] at h_mem'
      simp only [Option.elimM, OptionT.run] at h_mem'
      rw [show ∀ (m : StateT σ ProbComp _)
          (g : _ → StateT σ ProbComp _) (s0 : σ),
          (m >>= g) s0 = m.run s0 >>= fun p => (g p.1).run p.2
        from fun _ _ _ => rfl] at h_mem'
      rw [_root_.mem_support_bind_iff] at h_mem'
      obtain ⟨⟨opt_step, s'⟩, h_step_sup, h_rest_sup⟩ := h_mem'
      cases h_opt : opt_step with
      | none =>
        simp [h_opt] at h_rest_sup
      | some step =>
        have h_step_some_mem : (some step, s') ∈ ((f y b₀).run s₀).support := by
          simpa [h_opt] using h_step_sup
        obtain ⟨b', h_yield_eq⟩ := h_yield y b₀ s₀ (step, s') h_step_some_mem
        subst h_yield_eq
        simp [h_opt] at h_rest_sup
        have h_k_lt : k < l.length := by simp only [List.length_cons] at h_len; omega
        have h_y_eq : y = l.get ⟨k, h_k_lt⟩ := by
          have h_len_drop : 0 < (l.drop k).length := by rw [h_suffix]; exact Nat.zero_lt_succ _
          have : l[k]'h_k_lt = (l.drop k)[0]'h_len_drop := by
            simp only [List.getElem_drop, Nat.add_zero]
          simp only [List.get_eq_getElem, this, h_suffix, List.getElem_cons_zero]
        have h_rel_next : rel ⟨k + 1, by omega⟩ (some b') s' := by
          have h_app := h_step ⟨k, h_k_lt⟩ b₀ s₀ h_rel
            (ForInStep.yield b', s')
            (by
              have hn := h_step_some_mem
              rw [h_y_eq] at hn
              exact hn)
          simp [ForInStep.state, Fin.succ] at h_app
          exact h_app
        let bs_next : Fin (k + 1 + 1) → β := fun j =>
          if h : j.val ≤ k then bs_acc ⟨j.val, by omega⟩ else b'
        let ss_next : Fin (k + 1 + 1) → σ := fun j =>
          if h : j.val ≤ k then ss_acc ⟨j.val, by omega⟩ else s'
        have h_suffix_ys : l.drop (k + 1) = ys := by
          rw [← List.drop_drop, h_suffix]; rfl
        exact ih (k + 1) b' s'
          h_suffix_ys
          (by simp only [List.length_cons] at h_len; omega)
          h_rel_next
          bs_next ss_next
          (by simp [bs_next, h_bs0])
          (by simp [ss_next, h_ss0])
          (by simp [bs_next])
          (by simp [ss_next])
          (by
            intro j h_j_lt
            by_cases hj : j.val < k
            · have h_from_acc := h_acc_steps ⟨j.val, by omega⟩ (by omega)
              simp only [bs_next, ss_next, show j.val + 1 ≤ k from by omega,
                show j.val ≤ k from by omega, ↓reduceDIte]
              exact h_from_acc
            · have h_j_eq : j.val = k := by omega
              simp only [h_j_eq, List.get_eq_getElem, le_refl, ↓reduceDIte, add_le_iff_nonpos_right,
                nonpos_iff_eq_zero, one_ne_zero, bs_next, ss_next]
              have hn := h_step_some_mem
              rw [h_y_eq, h_bsk.symm, h_ssk.symm] at hn
              exact hn)
          (by
            intro j
            by_cases hj : j.val ≤ k
            · simp only [bs_next, ss_next, hj, ↓reduceDIte]
              exact h_acc_rels ⟨j.val, by omega⟩
            · have h_j_eq : j.val = k + 1 := by omega
              have h_neg : ¬ (k + 1 ≤ k) := by omega
              simp only [bs_next, ss_next, h_j_eq, h_neg, ↓reduceDIte]
              exact h_rel_next)
          h_rest_sup
  exact aux 0 l init s rfl (by omega) h_start
    (fun _ => init) (fun _ => s) rfl rfl rfl rfl
    (fun j => by exact Fin.elim0 j)
    (fun j => by have : j = 0 := Fin.eq_zero j; subst this; simpa using h_start)
    res h_mem
/-- Distributes `simulateQ` over `Vector.mapM`.

TODO: This proof is non-trivial because `Vector.mapM` is implemented via an auxiliary
`mapM.go` function that doesn't decompose cleanly. Attempted approaches:
- Vector induction produces `insertIdx` terms that don't match `mapM` structure
- toArray representation doesn't work since we're proving equality of `OracleComp` values
- Need either: (1) a lemma relating `simulateQ` to Array.mapM, or
  (2) a custom induction principle, or (3) direct reasoning about `mapM.go`. -/
lemma simulateQ_list_mapM {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (f : α → OracleComp spec β) :
    ∀ xs : List α, simulateQ so (xs.mapM f) = xs.mapM (fun x ↦ simulateQ so (f x)) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.mapM_cons, simulateQ_bind, ih]

lemma simulateQ_array_mapM {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (f : α → OracleComp spec β) (xs : Array α) :
    simulateQ so (xs.mapM f) = xs.mapM (fun x ↦ simulateQ so (f x)) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  simp [simulateQ_list_mapM]

omit [spec.Fintype] [spec.Inhabited] in
lemma singleton_mapM_gen
    {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    {α β : Type} (f : α → m β) (a : α) :
    Vector.mapM f (#v[a] : Vector α 1) =
      ((fun b => (#v[b] : Vector β 1)) <$> f a : m (Vector β 1)) := by
  apply (Vector.map_toArray_inj (m := m)).mp
  simp [Array.mapM_eq_mapM_toList, List.mapM_cons]

lemma support_vector_mapM_gen
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSet m]
    {α β : Type} (f : α → m β) :
    ∀ {n} (vec : Vector α n) (x : Vector β n),
      x ∈ support (Vector.mapM f vec) ↔ ∀ i : Fin n, x[i] ∈ support (f vec[i]) := by
  intro n
  induction n with
  | zero =>
      intro vec x
      obtain rfl : vec = #v[] := by
        ext i h
        simp at h
      obtain rfl : x = #v[] := by
        ext i h
        simp at h
      simp
  | succ n ih =>
      intro vec x
      have has : vec = vec.pop.push vec.back := by simp
      have hx : x = x.pop.push x.back := by simp
      rw [has, hx, ← Vector.append_singleton, ← Vector.append_singleton]
      rw [Vector.mapM_append, singleton_mapM_gen]
      simp only [mem_support_bind_iff, support_map, Set.mem_image, support_pure,
        Set.mem_singleton_iff, exists_exists_and_eq_and]
      constructor
      · intro h
        rcases h with ⟨ys, hy, b, hb, hEq⟩
        have hpush : x.pop.push x.back = ys.push b := by
          simpa [Vector.append_singleton] using hEq
        rcases (Vector.push_eq_push.mp hpush) with ⟨hbEq, hysEq⟩
        subst hbEq hysEq
        intro i
        by_cases hi : (i : Nat) < n
        · simpa [Vector.getElem_append_left, hi] using
            (ih vec.pop x.pop).1 hy ⟨i, hi⟩
        · have hiVal : (i : Nat) = n := by omega
          simpa [hiVal, Vector.append_singleton] using hb
      · intro h
        refine ⟨x.pop, (ih vec.pop x.pop).2 ?_, x.back, ?_, ?_⟩
        · intro i
          simpa [Vector.getElem_append_left, i.2] using
            h (Fin.castLT i (by omega))
        · simpa [Vector.append_singleton] using h ⟨n, by omega⟩
        · simp [Vector.append_singleton]

@[simp]
lemma simulateQ_vector_mapM {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} {n : ℕ} (f : α → OracleComp spec β) (v : Vector α n) :
    simulateQ so (Vector.mapM f v) = Vector.mapM (fun x ↦ simulateQ so (f x)) v := by
  apply (Vector.map_toArray_inj (m := OracleComp superSpec)).mp
  rw [← simulateQ_map, Vector.toArray_mapM, Vector.toArray_mapM]
  exact simulateQ_array_mapM (so := so) (f := f) v.toArray

lemma mem_support_vector_mapM {n} {f : α → OracleComp spec β} {vec : Vector α n} {x : Vector β n} :
    x ∈ (Vector.mapM f vec).support ↔ ∀ i : Fin n, x[i] ∈ (f vec[i]).support := by
  exact support_vector_mapM_gen (m := OracleComp spec) (f := f) vec x

/-- `Vector.mapM` is failure-free if each element computation is failure-free. -/
@[simp]
lemma neverFail_vector_mapM
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {n : ℕ} {γ δ : Type} {f : γ → m δ} {vec : Vector γ n}
    (h : ∀ x ∈ vec.toList, NeverFail (f x)) :
    NeverFail (Vector.mapM f vec) := by
  have h_list : NeverFail (List.mapM f vec.toList) :=
    neverFail_list_mapM («as» := vec.toList) (f := f) h
  have h_array : NeverFail (Array.mapM f vec.toArray) := by
    rw [Array.mapM_eq_mapM_toList]
    exact
      (HasEvalSPMF.neverFail_map_iff (mx := List.mapM f vec.toList) (f := List.toArray)).2 h_list
  have h_vec_toArray : NeverFail (Vector.toArray <$> Vector.mapM f vec) := by
    rw [Vector.toArray_mapM]
    exact h_array
  exact (HasEvalSPMF.neverFail_map_iff (mx := Vector.mapM f vec) (f := Vector.toArray)).1
    h_vec_toArray

/-- `probFailure` form of `neverFail_vector_mapM`. -/
@[simp]
lemma probFailure_vector_mapM_eq_zero
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {n : ℕ} {γ δ : Type} {f : γ → m δ} {vec : Vector γ n}
    (h : ∀ x ∈ vec.toList, Pr[⊥ | f x] = 0) :
    Pr[⊥ | Vector.mapM f vec] = 0 := by
  have h_nf : NeverFail (Vector.mapM f vec) :=
    neverFail_vector_mapM (vec := vec) (f := f)
      (h := fun x hx => NeverFail.of_probFailure_eq_zero (f x) (h x hx))
  exact (HasEvalSPMF.neverFail_iff (Vector.mapM f vec)).1 h_nf

/-- OracleComp specialization of `probFailure_vector_mapM_eq_zero`. -/
@[simp]
lemma OracleComp.probFailure_vector_mapM_eq_zero
    {n : ℕ} {γ δ : Type} {f : γ → OracleComp spec δ} {vec : Vector γ n}
    (h : ∀ x ∈ vec.toList, Pr[⊥ | f x] = 0) :
    Pr[⊥ | Vector.mapM f vec] = 0 := by
  exact _root_.probFailure_vector_mapM_eq_zero
    (m := OracleComp spec) (vec := vec) (f := f) h

/-- OptionT specialization of `probFailure_vector_mapM_eq_zero`. -/
@[simp]
lemma OptionT.probFailure_vector_mapM_eq_zero
    {n : ℕ} {γ δ : Type} {f : γ → OptionT (OracleComp spec) δ} {vec : Vector γ n}
    (h : ∀ x ∈ vec.toList, Pr[⊥ | f x] = 0) :
    Pr[⊥ | Vector.mapM f vec] = 0 := by
  exact _root_.probFailure_vector_mapM_eq_zero
    (m := OptionT (OracleComp spec)) (vec := vec) (f := f) h

/-- OptionT version of `simulateQ_vector_mapM`.

This is the form needed when `Vector.mapM` is used in `OptionT (OracleComp spec)` code
(e.g. query batches that may short-circuit on `none`). -/
lemma OptionT.simulateQ_list_mapM {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (f : α → OptionT (OracleComp spec) β) :
    ∀ xs : List α, simulateQ so (xs.mapM f) = xs.mapM (fun x ↦ simulateQ so (f x)) := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.mapM_cons, ih]

lemma OptionT.simulateQ_array_mapM {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (f : α → OptionT (OracleComp spec) β) (xs : Array α) :
    simulateQ so (xs.mapM f) = xs.mapM (fun x ↦ simulateQ so (f x)) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  simp [OptionT.simulateQ_list_mapM]

lemma OptionT.simulateQ_list_mapM_eq {ι ι' : Type} {spec : OracleSpec ι}
    {superSpec : OracleSpec ι'} (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (f : α → OptionT (OracleComp spec) β) :
    ∀ xs : List α,
      (simulateQ so (xs.mapM (m := OptionT (OracleComp spec)) f) :
        OptionT (OracleComp superSpec) (List β)) =
      xs.mapM (m := OptionT (OracleComp superSpec)) (fun x ↦ simulateQ so (f x)) := by
  intro xs
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.mapM_cons, List.mapM_cons]
      change simulateQ so
          (OptionT.bind (f x) fun y ↦
            ((List.cons y <$> List.mapM (m := OptionT (OracleComp spec)) f xs) :
              OptionT (OracleComp spec) (List β))) = _
      calc
        simulateQ so
            (OptionT.bind (f x) fun y ↦
              ((List.cons y <$> List.mapM (m := OptionT (OracleComp spec)) f xs) :
                OptionT (OracleComp spec) (List β)))
            =
            OptionT.bind (simulateQ so (f x)) fun y ↦
              simulateQ so
                (((List.cons y <$> List.mapM (m := OptionT (OracleComp spec)) f xs) :
                  OptionT (OracleComp spec) (List β))) := by
              exact OptionT.simulateQ_bind (so := so) (mx := f x)
                (my := fun y ↦
                  ((List.cons y <$> List.mapM (m := OptionT (OracleComp spec)) f xs) :
                    OptionT (OracleComp spec) (List β)))
        _ =
            OptionT.bind (simulateQ so (f x)) fun y ↦
              ((List.cons y <$> simulateQ so
                (List.mapM (m := OptionT (OracleComp spec)) f xs)) :
                  OptionT (OracleComp superSpec) (List β)) := by
              congr
              funext y
              exact OptionT.simulateQ_map (so := so) (f := List.cons y)
                (mx := List.mapM (m := OptionT (OracleComp spec)) f xs)
        _ =
            OptionT.bind (simulateQ so (f x)) fun y ↦
              ((List.cons y <$>
                List.mapM (m := OptionT (OracleComp superSpec))
                  (fun z ↦ simulateQ so (f z)) xs) :
                    OptionT (OracleComp superSpec) (List β)) := by
              congr
              funext y
              rw [ih]

lemma OptionT.simulateQ_array_mapM_eq {ι ι' : Type} {spec : OracleSpec ι}
    {superSpec : OracleSpec ι'} (so : SimOracle.Stateless spec superSpec)
    {α β : Type} (f : α → OptionT (OracleComp spec) β) (xs : Array α) :
    (simulateQ so (xs.mapM (m := OptionT (OracleComp spec)) f) :
      OptionT (OracleComp superSpec) (Array β)) =
      xs.mapM (m := OptionT (OracleComp superSpec)) (fun x ↦ simulateQ so (f x)) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  simpa using OptionT.simulateQ_list_mapM_eq (so := so) (f := f) xs.toList

lemma OptionT.simulateQ_vector_mapM_eq {ι ι' : Type} {spec : OracleSpec ι}
    {superSpec : OracleSpec ι'} (so : SimOracle.Stateless spec superSpec)
    {α β : Type} {n : ℕ} (f : α → OptionT (OracleComp spec) β) (v : Vector α n) :
    (simulateQ so (Vector.mapM (m := OptionT (OracleComp spec)) f v) :
      OptionT (OracleComp superSpec) (Vector β n)) =
      Vector.mapM (m := OptionT (OracleComp superSpec)) (fun x ↦ simulateQ so (f x)) v := by
  apply (Vector.map_toArray_inj (m := OptionT (OracleComp superSpec))).mp
  calc
    (Vector.toArray <$> (simulateQ so (Vector.mapM (m := OptionT (OracleComp spec)) f v) :
      OptionT (OracleComp superSpec) (Vector β n)) :
        OptionT (OracleComp superSpec) (Array β)) =
        (simulateQ so
          ((Vector.toArray <$> Vector.mapM (m := OptionT (OracleComp spec)) f v :
            OptionT (OracleComp spec) (Array β))) :
              OptionT (OracleComp superSpec) (Array β)) := by
          symm
          exact OptionT.simulateQ_map (so := so) (f := Vector.toArray)
            (mx := Vector.mapM (m := OptionT (OracleComp spec)) f v)
    _ = (simulateQ so (Array.mapM (m := OptionT (OracleComp spec)) f v.toArray) :
          OptionT (OracleComp superSpec) (Array β)) := by
        rw [Vector.toArray_mapM]
    _ = (Array.mapM (m := OptionT (OracleComp superSpec))
          (fun x ↦ simulateQ so (f x)) v.toArray :
            OptionT (OracleComp superSpec) (Array β)) := by
        exact OptionT.simulateQ_array_mapM_eq (so := so) (f := f) v.toArray
    _ = (Vector.toArray <$> Vector.mapM (m := OptionT (OracleComp superSpec))
          (fun x ↦ simulateQ so (f x)) v :
            OptionT (OracleComp superSpec) (Array β)) := by
        rw [Vector.toArray_mapM]

@[simp]
lemma OptionT.simulateQ_vector_mapM {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} {n : ℕ} (f : α → OptionT (OracleComp spec) β) (v : Vector α n) :
    ((simulateQ so ((Vector.mapM f v).run)) : OracleComp superSpec (Option (Vector β n))) =
      ((OptionT.run (Vector.mapM (m := OptionT (OracleComp superSpec))
        (fun x ↦ (simulateQ so (f x) : OptionT (OracleComp superSpec) β)) v)) :
        OracleComp superSpec (Option (Vector β n))) := by
  simpa only [OptionT.run] using
    OptionT.simulateQ_vector_mapM_eq (so := so) (f := f) (v := v)

/-- OptionT support decomposition for `Vector.mapM`.

This mirrors `mem_support_vector_mapM` at the `OptionT` level. -/
lemma OptionT.mem_support_vector_mapM {ι : Type} {spec : OracleSpec ι}
    {α β : Type} {n : ℕ}
    {f : α → OptionT (OracleComp spec) β} {vec : Vector α n} {x : Vector β n} :
    x ∈ support (Vector.mapM f vec) ↔ ∀ i : Fin n, x[i] ∈ support (f vec[i]) := by
  exact support_vector_mapM_gen (m := OptionT (OracleComp spec)) (f := f) vec x

/-- Run-level `some` form of `OptionT.mem_support_vector_mapM`. -/
@[simp]
lemma OptionT.mem_support_run_vector_mapM_some {ι : Type} {spec : OracleSpec ι}
    {α β : Type} {n : ℕ}
    {f : α → OptionT (OracleComp spec) β} {vec : Vector α n} {x : Vector β n} :
    some x ∈ support (m := OracleComp spec) (α := Option (Vector β n))
      (OptionT.run (Vector.mapM f vec)) ↔
      ∀ i : Fin n, x[i] ∈ support (f vec[i]) := by
  simpa [OptionT.mem_support_iff] using
    (OptionT.mem_support_vector_mapM (f := f) (vec := vec) (x := x))

/-- When each computation in a `Vector.mapM` returns `pure (f x)`, membership in support means
equality to `Vector.map f v`. -/
@[simp]
lemma mem_support_vector_mapM_pure {α β : Type} {n : ℕ}
    {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    (f : α → β) (v : Vector α n) (x : Vector β n) :
    x ∈ (Vector.mapM (fun a ↦ pure (f a) : α → OracleComp spec β) v).support ↔
    x = Vector.map f v := by
  constructor
  · intro h
    ext i hi : 1
    have h_elem : x[i] ∈ (pure (f v[i]) : OracleComp spec β).support := by
      rw [mem_support_vector_mapM] at h
      exact h ⟨i, hi⟩
    simp only [support_pure, Set.mem_singleton_iff] at h_elem
    simp only [Vector.getElem_map, h_elem]
  · intro h
    rw [h, mem_support_vector_mapM]
    intro i
    simp only [Fin.getElem_fin, support_pure, Vector.getElem_map, Set.mem_singleton_iff]

end ForInLemmas


/-!
## Probability Notation Bridge Lemmas

This section contains lemmas to bridge between VCVio's `probEvent` notation `[p | oa]`
and ArkLib's `Pr_{...}[...]` PMF-based notation, enabling the use of probability
tools from `Instances.lean` (like Schwartz-Zippel) in security proofs.

### Key Strategy

Use `OracleComp.probEvent_bind_eq_tsum` to factor complex probability statements:
```lean
[q | oa >>= ob] = ∑' x : α, [= x | oa] * [q | ob x]
```
-/

section NestedSimulateQSupport
open OracleComp OracleSpec OracleQuery SimOracle

variable {ι : Type} {oSpec oSpec' : OracleSpec ι}
  [oSpec.Fintype] [oSpec'.Fintype]

omit [oSpec.Fintype] in
/-- **Support of simulateQ through bind with StateT**

For stateful oracle implementations, the support of `(simulateQ impl oa >>= f).run s` can be
related to the spec support by unfolding through the monadic structure.

This handles the case where we have a bind after simulateQ, which is common in verifier
executions that continue with additional stateful computations. -/
lemma support_simulateQ_bind_run_eq
    {σ α β : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) (f : α → StateT σ ProbComp β) (s : σ) :
    ((simulateQ impl oa >>= f).run s).support =
    (do let ⟨x, s'⟩ ← (simulateQ impl oa).run s; (f x).run s').support := by
  simp only [StateT.run]; rfl

-- OptionT (StateT σ ProbComp) PUnit.{1}
/-- **Support of StateT bind (run form)**
Membership in `support ((m >>= g).run s)` is equivalent to: there exists `out_forIn ∈ support (m.run s)`
such that `x` is in the support of continuing with `g` from that result (i.e. `(g out_forIn.1).run out_forIn.2`).
Useful to "peel" the outer bind and get an existential over the forIn (or first part) outcome. -/
lemma mem_support_StateT_bind_run {σ α β : Type}
    (ma : StateT σ ProbComp α) (f : α → StateT σ ProbComp β) (s : σ) (x : β × σ) :
    x ∈ ((ma >>= f).run s).support ↔
    ∃ (y : α) (s' : σ), (y, s') ∈ (ma.run s).support ∧ x ∈ ((f y).run s').support := by
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop, Prod.exists]

-- StateT σ ProbComp (Option (ForInStep PUnit.{1}))
lemma OptionT.mem_support_StateT_bind_run {σ α β : Type}
    (ma : StateT σ ProbComp α) (f : α → StateT σ ProbComp (Option β)) (s : σ) (x : Option (β) × σ) :
    x ∈ ((ma >>= f).run s).support ↔
    ∃ (y : α) (s' : σ), (y, s') ∈ (ma.run s).support ∧ x ∈ ((f y).run s').support := by
  simp only [StateT.run_bind, _root_.support_bind, Set.mem_iUnion, exists_prop, Prod.exists]

lemma support_StateT_ite_apply {σ α : Type}
    (ma ma' : StateT σ ProbComp α) (p : Prop) [Decidable p] (s : σ) :
    support ((ite p ma ma') s) = ite p (support (ma s)) (support (ma' s)) := by
  by_cases hp : p <;> simp [hp]

end NestedSimulateQSupport


section QueryImplSimplification

open ENNReal NNReal

open OracleSpec OracleComp ProtocolSpec ProbComp QueryImpl
open scoped ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype]
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
  {σ : Type}

/-- **Simplification: QueryImpl append for Sum.inr queries (challenge queries)**

When appending a `QueryImpl` with `challengeQueryImpl`, queries to `Sum.inr` (challenge queries)
are routed to `challengeQueryImpl`, which samples uniformly.

This lemma simplifies `(impl ++ₛₒ challengeQueryImpl).impl (query (Sum.inr i) ())` to
show it samples uniformly from the challenge space.

**Note**: The `++ₛₒ` operator implicitly lifts `challengeQueryImpl` from `ProbComp` to `StateT σ ProbComp`.
-/
theorem QueryImpl_append_impl_inr_stateful
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : pSpec.ChallengeIdx) (s : σ) :
    ((QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (.inr ⟨i, ()⟩)) s =
    (liftM (challengeQueryImpl ⟨i, ()⟩) : StateT σ ProbComp _).run s := by
  rfl

/-- **Simplification: QueryImpl append for Sum.inr queries (challenge queries) - run' version**

Same vec `QueryImpl_append_impl_inr_stateful` but using `run'` which discards the state.
-/
theorem QueryImpl_append_impl_inr_stateful_run'
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (i : pSpec.ChallengeIdx) (s : σ) :
    (((QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) (.inr ⟨i, ()⟩)).run') s =
    (liftM (challengeQueryImpl ⟨i, ()⟩) : StateT σ ProbComp _).run' s := by
  rfl

/-- For challenge queries, `monadLift` on `OracleQuery` lands in the `.inr` branch. -/
lemma addLift_challengeQueryImpl_input_run_eq_liftM_run
    {σ α : Type} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (q : OracleQuery [pSpec.Challenge]ₒ α)
    (s : σ) :
    ((impl + QueryImpl.liftTarget (StateT σ ProbComp) (challengeQueryImpl (pSpec := pSpec)))
      ((MonadLift.monadLift (query q.input) :
        OracleQuery ([]ₒ + [pSpec.Challenge]ₒ)
          ([pSpec.Challenge]ₒ.Range q.input)).input)).run s =
      ((liftM (challengeQueryImpl (pSpec := pSpec) q.input)) :
        StateT σ ProbComp ([pSpec.Challenge]ₒ.Range q.input)).run s := by rfl

end QueryImplSimplification

section MapLemmas

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Map over pure reduces to pure of the mapped value. -/
@[simp]
lemma map_pure (f : α → β) (a : α) :
    (f <$> pure a : OracleComp spec β) = pure (f a) := rfl

end MapLemmas

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.SimOracle
import ArkLib.ToVCVio.Lemmas
import ArkLib.OracleReduction.Execution
import VCVio.OracleComp.SimSemantics.Append
-- set_option linter.style.longFile 1600 AI, Don't ever write this shit
import VCVio.OracleComp.SimSemantics.SimulateQ
import Mathlib.Data.ENNReal.Basic
import VCVio.OracleComp.DistSemantics.EvalDist
import ArkLib.OracleReduction.OracleInterface

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

open OracleSpec OracleComp ProtocolSpec Sum

universe u v w

section NestedMonadLiftLemmas
-- The ground spec is T₁, we lift it to a superSpec

-- lift to left then lift to right
instance instMonadLift_left_right {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift T₁.OracleQuery (T₃ ++ₒ (T₁ ++ₒ T₂)).OracleQuery where
  monadLift q := liftM (liftM q : (T₁ ++ₒ T₂).OracleQuery _)

-- lift to right then lift to right
instance instMonadLift_right_right {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift T₁.OracleQuery (T₃ ++ₒ (T₂ ++ₒ T₁)).OracleQuery where
  monadLift q := liftM (liftM q : (T₂ ++ₒ T₁).OracleQuery _)

-- lift to left then lift to left
instance instMonadLift_left_left {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift T₁.OracleQuery ((T₁ ++ₒ T₂) ++ₒ T₃).OracleQuery where
  monadLift q := liftM (liftM q : (T₁ ++ₒ T₂).OracleQuery _)

instance instMonadLift_right_left {ι₁ ι₂ ι₃ : Type}
    {T₁ : OracleSpec ι₁} {T₂ : OracleSpec ι₂} {T₃ : OracleSpec ι₃} :
    MonadLift T₁.OracleQuery ((T₂ ++ₒ T₁) ++ₒ T₃).OracleQuery where
  monadLift q := liftM (liftM q : (T₂ ++ₒ T₁).OracleQuery _)

end NestedMonadLiftLemmas

section SimulationLemmas

variable {ι ι₁ ι₂ : Type*} {spec spec₁ spec₂ : OracleSpec ι}
  {m : Type u → Type v} [AlternativeMonad m] [LawfulMonad m] [LawfulAlternative m]
  {α β σ : Type u}

/-- Lift an implementation for `spec₂` to `spec₁` via `MonadLift`. -/
@[reducible]
def QueryImpl.lift {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)] (so : QueryImpl spec₂ m) :
    QueryImpl spec₁ m where
  impl q := so.impl (liftM q)

/-- If a computation is lifted from a sub-specification, we can commute the
  lifting and the simulation. -/
@[simp]
lemma simulateQ_liftComp {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [h : MonadLift (OracleQuery spec₁) (OracleQuery spec₂)] (so : QueryImpl spec₂ m)
    (oa : OracleComp spec₁ α) :
    simulateQ so (liftComp oa spec₂) = simulateQ (QueryImpl.lift so) oa :=
by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [QueryImpl.lift, OracleComp.simulateQ_pure]
  | query_bind i t oa ih => simp [ih, Function.comp_def, QueryImpl.lift]
  | failure => simp [QueryImpl.lift]

/--
**Step 2 Helper: Collapse Monadic Bind and Composition**
This lemma resolves the pattern `pure x >>= (simulateQ ∘ f)` that often appears
when simulating sequential code. It forces the function `f` to be applied to `x`
inside the simulation immediately.
-/
@[simp]
lemma bind_pure_simulateQ_comp
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : SimOracle.Stateless spec spec')
    {α β : Type v} (x : α) (f : α → OracleComp spec β) :
    (pure x >>= (simulateQ so ∘ f)) = simulateQ so (f x) := by rfl

end SimulationLemmas

section SimulationSafety

variable {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α β : Type}

/-- **Reverse Safety Preservation (Stateless)**

If the simulated computation is safe and the implementation has the **same support**
as the specification, then the original specification computation is safe.

**Why equality is required**: This lemma proves the reverse direction (simulateQ safe → spec safe).
When we have `x ∈ (liftM q).support` from the spec, we need to show `x ∈ (so.impl q).support`
for the implementation. This requires the reverse inclusion, hence we need equality.

**Note**: For the forward direction (spec safe → simulateQ safe), subset is sufficient.
See `simulateQ_preserves_safety` and `simulateQ_preserves_safety_stateful` which only
require `(so.impl q).support ⊆ (liftM q).support`. -/
lemma neverFails_of_simulateQ (so : QueryImpl spec ProbComp)
    (oa : OracleComp spec α)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support = (liftM q : OracleComp spec β).support)
    (h : [⊥|simulateQ so oa] = 0) : [⊥ | oa] = 0 := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih =>
    rw [simulateQ_query_bind] at h
    rw [probFailure_bind_eq_zero_iff] at h
    simp only [probFailure_bind_eq_zero_iff]
    constructor
    · simp only [probFailure_liftM]
    · intro x hx
      -- h.2 : ∀ x ∈ (so.impl (query i t)).support, [⊥ | (simulateQ so ∘ oa) x] = 0
      -- We have hx : x ∈ (liftM (query i t)).support
      -- By h_supp, these supports are equal
      have hx_sim : x ∈ (so.impl (query i t)).support := by rwa [h_supp]
      exact ih x (h.2 x hx_sim)
  | failure => simp at h

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
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥|(impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support ⊆ (q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ)
    (h_oa : [⊥|oa] = 0) :
    [⊥|(simulateQ impl oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | failure => simp at h_oa
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
    constructor
    · exact hImplSafe (query i t) s
    · intro ⟨result, newState⟩ h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      have h_result_in_spec : result ∈ ((query i t) : OracleComp oSpec _).support := by
        apply hImplSupp (query i t) s
        exact Set.mem_image_of_mem Prod.fst h_in_supp
      simp only [OracleComp.support_query, Set.mem_univ] at h_result_in_spec
      have h_result_in_query : result ∈ (query i t : OracleComp oSpec _).support := by
        simp only [OracleComp.support_query, Set.mem_univ]
      exact ih result newState (h_oa.2 result h_result_in_query)

/-- **Reverse Safety Preservation for Stateful Implementations**

If the simulated stateful computation is safe and the implementation has the same support
as the specification, then the original specification computation is safe.

This is the reverse direction of `simulateQ_preserves_safety_stateful`.

**Note**: This requires support **equality** rather than just subset (⊆) because we need
to extract witnesses: if a result is valid in the spec, we need to know that the implementation
can actually produce it (surjectivity).
-/
lemma neverFails_of_simulateQ_stateful
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ)
    (h : [⊥|(simulateQ impl oa).run s] = 0) :
    [⊥|oa] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | failure => simp at h
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff] at h
    simp only [probFailure_bind_eq_zero_iff]
    constructor
    · simp only [probFailure_liftM]
    · intro result h_result_in_spec
      -- h.2 : ∀ ⟨result, newState⟩ ∈ ((impl.impl (query i t)).run s).support,
      --       [⊥|(simulateQ impl (oa result)).run newState] = 0
      -- We need to show: [⊥|oa result] = 0
      simp only [OracleComp.support_query, Set.mem_univ] at h_result_in_spec
      -- By support equality, result is in the image of Prod.fst over impl's support
      have h_result_in_impl : result ∈ Prod.fst <$> ((impl.impl (query i t)).run s).support := by
        rw [hImplSupp]
        simp only [OracleComp.support_query, Set.mem_univ]
      -- Extract a witness: there exists a newState such that (result, newState) is in support
      obtain ⟨pair, h_in_supp, h_fst_eq⟩ := h_result_in_impl
      cases pair with | mk result' newState =>
      subst h_fst_eq
      exact ih result' newState (h.2 ⟨result', newState⟩ h_in_supp)

/-- **Stateful Safety Biconditional**

For stateful oracle implementations, the simulated computation is safe if and only if
the specification computation is safe. This requires:
1. The implementation itself never fails (hImplSafe).
2. The implementation has the same support as the specification (hImplSupp).

This is the stateful version of `probFailure_simulateQ_iff` and is useful for
simplifying completeness proofs where you need to establish equivalence between
simulated and specification safety.

**Note**: Unlike `simulateQ_preserves_safety_stateful` which only requires support subset (⊆),
this biconditional requires support **equality** (=) to enable the reverse direction.
-/
@[simp]
theorem probFailure_simulateQ_iff_stateful
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥|(impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    [⊥|(simulateQ impl oa).run s] = 0 ↔ [⊥|oa] = 0 := by
  constructor
  · intro h; exact neverFails_of_simulateQ_stateful impl hImplSupp oa s h
  · intro h
    apply simulateQ_preserves_safety_stateful impl hImplSafe _ oa s h
    intro β q s'
    rw [hImplSupp]

/-- **Stateful Safety Biconditional (run' version)**

This is the `run'` version of `probFailure_simulateQ_iff_stateful`. It works with
`StateT.run'` which projects out only the result (discarding the final state),
rather than `StateT.run` which returns the full `(result, state)` pair.

This lemma is useful when the goal involves `(simulateQ impl oa).run' s` instead of
`(simulateQ impl oa).run s`.
-/
@[simp]
theorem probFailure_simulateQ_iff_stateful_run'
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥|(impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    [⊥|(simulateQ impl oa).run' s] = 0 ↔ [⊥|oa] = 0 := by
  simp only [StateT.run', probFailure_map]
  exact probFailure_simulateQ_iff_stateful impl hImplSafe hImplSupp oa s

/-- **Safety Preservation Lemma for Stateless Implementations**

If an oracle implementation is safe and support-faithful, then simulation preserves safety
from the specification level to the implementation level (stateless version).

This is the stateless counterpart to `simulateQ_preserves_safety_stateful`.
-/
theorem simulateQ_preserves_safety
    {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    (so : QueryImpl oSpec ProbComp)
    (h_so : ∀ {β} (q : OracleQuery oSpec β), [⊥|so.impl q] = 0)
    (h_supp : ∀ {β} (q : OracleQuery oSpec β),
      (so.impl q).support ⊆ (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α)
    (h_oa : [⊥|oa] = 0) :
    [⊥|simulateQ so oa] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp at h_oa
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, probFailure_bind_eq_zero_iff]
    constructor
    · exact h_so (query i t)
    · intro result h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      have h_result_in_spec : result ∈ (query i t : OracleComp oSpec _).support := by
        exact h_supp (query i t) h_in_supp
      exact ih result (h_oa.2 result h_result_in_spec)

/--
Safety preservation: A simulated protocol is safe if and only if the original
protocol is safe. This requires:
1. The implementation itself never fails (h_so).
2. The implementation doesn't return "illegal" values outside the spec (h_supp).
-/
@[simp]
lemma probFailure_simulateQ_iff (so : QueryImpl spec ProbComp) (oa : OracleComp spec α)
    (h_so : ∀ {β} (q : OracleQuery spec β), [⊥|so.impl q] = 0)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support = (liftM q : OracleComp spec β).support) :
    [⊥|simulateQ so oa] = 0 ↔ [⊥|oa] = 0 := by
  constructor
  · intro h; exact neverFails_of_simulateQ so oa h_supp h
  · intro h_oa
    apply simulateQ_preserves_safety so h_so (h_supp := fun q ↦ (h_supp q).subset) oa h_oa

/-- Challenge query implementations have the same support as the specification.
    This is trivially true for uniform distributions. -/
@[simp]
lemma support_challengeQueryImpl_eq {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SelectableType (pSpec.Challenge i)] (i : pSpec.ChallengeIdx) :
    (challengeQueryImpl.impl (query i ())).support =
    (liftM (query i ()) : OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) _).support := by
  -- Both uniformOfFintype and liftM have full support over pSpec.Challenge i
  -- This should be provable using support_uniformOfFintype and support lemmas for liftM
-- 1. Expand the implementation of challengeQueryImpl
  unfold challengeQueryImpl
  -- 2. Simplify the implementation call
  -- 'challengeQueryImpl' is defined as mapping index 'i' to 'uniformOfFintype'
  simp only [ChallengeIdx, Challenge, support_query]
  -- ⊢ support ($ᵗpSpec.Type ↑i) = Set.univ
  rw [OracleComp.support_uniformOfFintype (α := pSpec.Type ↑i)]

/-- Challenge query implementations never fail (stateful version).
    Uniform sampling is always safe regardless of state. -/
@[simp]
lemma probFailure_challengeQueryImpl_run {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
    [∀ i, SelectableType (pSpec.Challenge i)]
    (q : ([pSpec.Challenge]ₒ'challengeOracleInterface).OracleQuery β) (s : σ) :
    [⊥|(liftM (challengeQueryImpl.impl q) : StateT σ ProbComp β).run s] = 0 := by
  cases q with | query i t =>
  cases t  -- t : Unit, so this eliminates the match
  unfold challengeQueryImpl
  simp only [StateT.run_liftM_lib, probFailure_bind_eq_zero_iff, probFailure_pure]
  -- now apply `probFailure_uniformOfFintype` for the form `[⊥|$ᵗα] = 0`
  exact ⟨@probFailure_uniformOfFintype (α := pSpec.Challenge i) _, fun _ _ => trivial⟩

/-- Challenge query implementations have full support (stateful version).
    The first component of the result has the same support as the spec. -/
@[simp]
lemma support_challengeQueryImpl_run_eq {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
    [∀ i, SelectableType (pSpec.Challenge i)]
    (q : ([pSpec.Challenge]ₒ'challengeOracleInterface).OracleQuery β) (s : σ) :
    Prod.fst <$> ((liftM (challengeQueryImpl.impl q) : StateT σ ProbComp β).run s).support =
    (liftM q : OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) β).support := by
  cases q with | query i t =>
  cases t  -- t : Unit, eliminate the match
  simp only [StateT.run_liftM_lib, support_bind, support_pure, liftM, support_query]
  ext x
  simp only [ChallengeIdx, support_challengeQueryImpl_eq, support_query, Set.mem_univ,
    Set.iUnion_true, Set.iUnion_singleton_eq_range, Set.fmap_eq_image, Set.mem_image, Set.mem_range,
    exists_exists_eq_and, exists_eq]

end SimulationSafety

section ProtocolUnrolling

variable {ι : Type} {n : ℕ} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- Simplification lemma for `processRound` when the direction is `P_to_V`. -/
@[simp]
lemma Prover.processRound_P_to_V (j : Fin n)
    (h : pSpec.dir j = .P_to_V)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
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
    (currentResult : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
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
  [∀ i, SelectableType (pSpec.Challenge i)]

omit [(i : pSpec.ChallengeIdx) → SelectableType (pSpec.Challenge i)] in
/-- Specifically handles the `Fin.induction` inside the `Prover.run` code. -/
@[simp]
lemma Prover.run_succ (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : Fin n) :
    prover.runToRound i.succ stmt wit =
      prover.processRound i (prover.runToRound i.castSucc stmt wit) :=
by simp [Prover.runToRound, Fin.induction_succ]

omit [(i : pSpec.ChallengeIdx) → SelectableType (pSpec.Challenge i)] in
/-- Simplifies `Reduction.run` by unfolding it into the prover's run and verifier's check. -/
@[simp]
lemma Reduction_run_def (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    reduction.run stmtIn witIn = (do
      let ⟨transcript, stmtOut, witOut⟩ ← reduction.prover.run stmtIn witIn
      let verifierStmtOut ← reduction.verifier.verify stmtIn transcript
      return ((transcript, stmtOut, witOut), verifierStmtOut)) :=
by rfl

alias Reduction.run_step := Reduction_run_def

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

variable {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α β : Type}
  {m : Type → Type} [AlternativeMonad m] [LawfulAlternative m]

omit [spec.FiniteRange] in
/-- The support of a lifted computation is the same as the original. -/
@[simp]
lemma support_liftComp {ι' : Type} {superSpec : OracleSpec ι'}
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : (liftComp oa superSpec).support = oa.support := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [ih]
  | failure => simp

omit [spec.FiniteRange] in
@[simp]
lemma support_simulateQ_eq (so : QueryImpl spec ProbComp) (oa : OracleComp spec α)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support = (liftM q : OracleComp spec β).support) :
    (simulateQ so oa).support = oa.support := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih =>
    simp [simulateQ_bind, ih, h_supp]
  | failure => simp

/-- **Helper: Support of run' for stateful simulateQ**

If a stateful oracle implementation is support-faithful, then for any state `s`,
the support of `(simulateQ impl oa).run' s` equals the support of `oa`.

This is the stateful version of `support_simulateQ_eq` and is used as a building
block for `support_bind_simulateQ_run'_eq`.

**Proof Strategy**: The proof requires careful handling of state transitions.
The key insight is that `run'` projects out the result component via `map Prod.fst`,
and `hImplSupp` ensures that the first component of the stateful implementation's
support matches the spec's support. The proof proceeds by induction on `oa`,
using the support-faithfulness at each query step.
-/
@[simp]
lemma support_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support) :
    ((simulateQ impl oa).run' s).support = oa.support := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run'_pure_lib, support_pure]
  | failure =>
    simp only [simulateQ_failure, StateT.run', support_map, support_failure, Set.image_eq_empty]
    rfl
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, StateT.run'_bind_lib, support_bind]
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro ⟨⟨x, s'⟩, h_pair, h_y⟩
      have h_x_spec : x ∈ (query i t : OracleComp oSpec _).support := by
        have h_supp_eq := hImplSupp (query i t) s
        rw [← h_supp_eq]
        exact Set.mem_image_of_mem Prod.fst h_pair
      have h_y_spec : y ∈ (oa x).support := by
        rw [← ih x s']
        exact h_y
      exact ⟨x, h_x_spec, h_y_spec⟩
    · intro ⟨x, h_x_spec, h_y_spec⟩
      have h_supp_eq := hImplSupp (query i t) s
      have h_x_in_image : x ∈ Prod.fst <$> ((impl.impl (query i t)).run s).support := by
        rw [h_supp_eq]
        exact h_x_spec
      simp only [Set.fmap_eq_image, Set.mem_image] at h_x_in_image
      obtain ⟨pair, h_pair, h_fst_eq⟩ := h_x_in_image
      cases pair with | mk x' s' =>
      have h_x'_eq_x : x' = x := h_fst_eq
      have h_y_sim : y ∈ ((simulateQ impl (oa x')).run' s').support := by
        rw [ih x' s']
        rw [h_x'_eq_x]
        exact h_y_spec
      have h_y_sim' : y ∈ support (((simulateQ impl ∘ oa) x').run' s') := by
        simp only [Function.comp_apply]
        exact h_y_sim
      exact ⟨(x', s'), h_pair, h_y_sim'⟩

/-- **Support Nonemptiness from Never-Fails**

If a computation never fails, then its support is nonempty. This is a fundamental
property: if `[⊥|oa] = 0`, then there must be at least one possible output value.

**Intuition**: If a computation never fails, the sum of probabilities over all outputs
equals 1. Since probabilities are non-negative and sum to 1, at least one output
must have positive probability, which means it's in the support.

**Application**: This lemma is useful in completeness proofs where we need to eliminate
quantifiers over support. If we have `∀ x ∈ oa.support, P x` and `oa.neverFails`,
we can instantiate the quantifier with a witness from the nonempty support.
-/
theorem support_nonempty_of_neverFails
    {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α : Type}
    (oa : OracleComp spec α) (h : oa.neverFails) :
    oa.support.Nonempty := by
  -- Convert neverFails to probFailure = 0
  have h_probFailure_eq_zero : [⊥|oa] = 0 := by
    rw [probFailure_eq_zero_iff]; exact h
  -- If probFailure = 0, then the sum of probOutput over all outputs is 1
  have h_sum_eq_one : ∑' x : α, [= x | oa] = 1 := by
    rw [tsum_probOutput_eq_sub, h_probFailure_eq_zero, tsub_zero]
  -- If the tsum is 1, then probEvent for True is positive
  have h_event_pos : 0 < [fun _ => True | oa] := by
    -- probEvent for True equals the tsum of probOutput
    rw [OracleComp.probEvent_eq_tsum_ite (p := fun _ => True)]
    -- Simplify: if True then [=x|oa] else 0 = [=x|oa]
    simp only [if_true]
    rw [h_sum_eq_one]
    -- The tsum is 1, which is positive
    norm_num
  -- Use probEvent_pos_iff to get that there exists x in support
  rw [probEvent_pos_iff] at h_event_pos
  obtain ⟨x, hx_mem, _⟩ := h_event_pos
  exact ⟨x, hx_mem⟩

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
(do let s ← init; (simulateQ impl oa).run' s).support = oa.support
```

**Application**: When proving completeness, we often need to show that the support
of the simulated execution matches the support of the specification. This lemma
bridges that gap for stateful implementations.

**Note**: The RHS is just `oa.support` (not bound with `init`) because `oa` is
a pure specification computation that doesn't depend on the oracle state.
-/
@[simp]
lemma support_bind_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ α : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α)
    (hInit : init.neverFails)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support) :
    (do let s ← init; (simulateQ impl oa).run' s).support = oa.support := by
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
    -- We need to show there exists s ∈ init.support such that
    -- x ∈ (simulateQ impl oa).run' s).support
    -- Since init.neverFails (or we can use init.support.Nonempty), we can pick any s
    -- Use the helper lemma
    have h_init_nonempty : init.support.Nonempty :=
      support_nonempty_of_neverFails init hInit
    obtain ⟨s, hs_init⟩ := h_init_nonempty
    have h_supp_eq := support_simulateQ_run'_eq impl oa s hImplSupp
    -- h_supp_eq: ((simulateQ impl oa).run' s).support = oa.support
    -- We have hx_spec: x ∈ oa.support
    -- Need: x ∈ ((simulateQ impl oa).run' s).support
    rw [← h_supp_eq] at hx_spec
    exact ⟨s, hs_init, hx_spec⟩

end SupportPreservation

section SimOracle2Lemmas
open OracleInterface OracleComp OracleSpec OracleQuery SimOracle

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
  {ι₁ : Type} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]

/-- simOracle2 is safe because it is a deterministic transcript lookup. -/
@[simp]
lemma probFailure_simOracle2 (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) :
    ∀ {β} (q : (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)).OracleQuery β),
    [⊥ | (simOracle2 oSpec t₁ t₂).impl q] = 0 := by
  intro β q
  rw [probFailure_eq_zero_iff]
  exact neverFails_simOracle2 oSpec t₁ t₂ q

/-- **Weak Safety Preservation for simOracle2** when `oa` is pure computation
  (no oracle queries). -/
@[simp]
lemma probFailure_simulateQ_simOracle2_eq_zero
    [OracleSpec.FiniteRange [T₁]ₒ] [OracleSpec.FiniteRange [T₂]ₒ]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α : Type} (oa : OracleComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) α)
    (h_oa : [⊥|oa] = 0) :
    [⊥ | simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) oa] = 0 := by
  -- simOracle2 returns QueryImpl spec (OracleComp specₜ), which is Stateless
  -- We prove this directly by induction, following the pattern of simulateQ_preserves_safety
  let so := OracleInterface.simOracle2 oSpec t₁ t₂
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp at h_oa
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, probFailure_bind_eq_zero_iff]
    constructor
    · -- The oracle implementation never fails
      exact probFailure_simOracle2 t₁ t₂ (query i t)
    · -- For each result in the support, the continuation is safe
      intro result h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      -- Show that result is in the spec support
      -- simOracle2: base queries pass through (idOracle), transcript queries return pure values
      have h_result_in_spec : result ∈
        (query i t : OracleComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) _).support := by
        cases i with
        | inl i_base =>
          -- Base queries: idOracle passes through, support is full range
          simp only [OracleComp.support_query, Set.mem_univ]
        | inr i_ext =>
          cases i_ext with
          | inl i_t1 =>
            -- T1 queries: fnOracle returns pure (answer (t₁ i_t1) t)
            -- The support is a singleton, and answer returns a value in the oracle range
            have h_supp : (so.impl (query (.inr (.inl i_t1)) t)).support
              = {OracleInterface.answer (t₁ i_t1) t} := by rfl
            have : result = OracleInterface.answer (t₁ i_t1) t := by
              rwa [h_supp, Set.mem_singleton_iff] at h_in_supp
            rw [this]
            simp only [OracleComp.support_query, Set.mem_univ]
          | inr i_t2 =>
            -- T2 queries: fnOracle returns pure (answer (t₂ i_t2) t)
            have h_supp : (so.impl (query (.inr (.inr i_t2)) t)).support
              = {OracleInterface.answer (t₂ i_t2) t} := by rfl
            have : result = OracleInterface.answer (t₂ i_t2) t := by
              rwa [h_supp, Set.mem_singleton_iff] at h_in_supp
            rw [this]
            -- answer (t₂ i_t2) t is in the range of the oracle for (.inr (.inr i_t2))
            simp only [OracleComp.support_query, Set.mem_univ]
      exact ih result (h_oa.2 result h_result_in_spec)

/--
**Generic Simulation Reduction**

This lemma reduces `simulateQ (simOracle2 ...) (liftM q)` to the
raw implementation `(simOracle2 ...).impl q`.

This allows you to eliminate `simulateQ` even if the specific query index
is generic or unknown at the moment.
-/
@[simp]
lemma simulateQ_simOracle2_liftM
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α : Type} (q : (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)).OracleQuery α) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (liftM q) =
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl q := by
  -- This follows directly from the definition of simulateQ on a single query
  simp only [simulateQ_query]

/-- Unfolds simOracle2 implementation for transcript 1. -/
@[simp]
lemma simOracle2_impl_inr_inl
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₁) (t : ([T₁]ₒ).domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (query (.inr (.inl i)) t) =
    pure (OracleInterface.answer (t₁ i) t) :=
by rfl

/-- Unfolds simOracle2 implementation for transcript 2. -/
@[simp]
lemma simOracle2_impl_inr_inr
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₂) (t : ([T₂]ₒ).domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (query (.inr (.inr i)) t) =
    pure (OracleInterface.answer (t₂ i) t) :=
by rfl

/-- Unfolds simOracle2 implementation for base queries. -/
@[simp]
lemma simOracle2_impl_inl
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι) (t : oSpec.domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (query (.inl i) t) =
    query i t :=
by rfl

/-- **Oracle query unfolding**: This is the main lemma that converts the OracleComp
lifted from oracle queries into an almost deterministic form -/
@[simp]
lemma simulateQ_simOracle2_lift_liftComp_query_T1
    {ι : Type} {oSpec : OracleSpec ι}
    {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (j : ι₁) (pt : [T₁]ₒ.domain j) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      ((OracleComp.lift (query j pt)).liftComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ))) =
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
    (j : ι₂) (pt : [T₂]ₒ.domain j) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      ((OracleComp.lift (query j pt)).liftComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ))) =
    pure (OracleInterface.answer (t₂ j) pt) := by
  rfl

end SimOracle2Lemmas

section ForInLemmas

variable {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange]
variable {α σ : Type}

/--
**Safety of forIn Loops (Sufficient Condition)**

If the loop body is safe for every element in the list and every possible state,
then the `forIn` loop is safe (never fails).

**Note:** The Right-Hand Side (`∀ s`) quantifies over *all* states `s`,
not just reachable ones. This makes the lemma useful for proving safety
"by inspection" without tracking complex state invariants.
For singleton states (like `PUnit`), this condition is both necessary and sufficient.

**Usage**: This is the key lemma for completeness proofs.
To show `[⊥|forIn l init f] = 0`, it suffices to show that each step
`[⊥|f x s] = 0` is safe for all elements and all states.
-/
lemma probFailure_forIn_eq_zero_of_body_safe
    (l : List α) (init : σ) (f : α → σ → OracleComp spec (ForInStep σ))
    (h : ∀ x ∈ l, ∀ s, [⊥|f x s] = 0) :
    [⊥|forIn l init f] = 0 := by
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

/-- Prove forIn safety using an invariant.
    P done s: Predicate meaning state 's' is correct after processing 'done'. -/
lemma probFailure_forIn_of_invariant {spec : OracleSpec ι} [spec.FiniteRange]
    {α σ : Type} (P : List α → σ → Prop)
    (l : List α) (init : σ) (f : α → σ → OracleComp spec (ForInStep σ))
    -- 1. Base: Invariant holds at start
    (h_start : P [] init)
    -- 2. Step: Preserves invariant and is safe
    (h_step : ∀ (done : List α) (x : α) (s : σ),
       x ∈ l → P done s →
       [⊥|f x s] = 0 ∧ ∀ s' ∈ (f x s).support,
         match s' with
         | .yield next => P (done ++ [x]) next
         | .done next => P (done ++ [x]) next) :
    [⊥|forIn l init f] = 0 := by
  -- We define a helper that iterates over a suffix 'xs' given a prefix 'done'
  let rec aux (xs : List α) (done : List α) (s : σ)
      (h_decomp : l = done ++ xs) (h_inv : P done s) :
      [⊥ | forIn xs s f] = 0 := by
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
lemma probFailure_forIn_of_relations {spec : OracleSpec ι} [spec.FiniteRange]
    {α σ : Type}
    (l : List α)
    (init : σ)
    (f : α → σ → OracleComp spec (ForInStep σ))
    -- The sequence of relations: rel i s
    (rel : Fin (l.length + 1) → σ → Prop)
    -- 1. Base Case: Relation 0 holds for initial state
    (h_start : rel 0 init)
    -- 2. Inductive Step: rel i -> step safe -> rel (i+1)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       -- Given the relation holds at step k
       rel (k.castSucc) s →
       -- Then the step using the k-th element of the list is safe
       [⊥|f (l.get k) s] = 0 ∧
       -- And the result satisfies the relation at step k+1
       ∀ s' ∈ (f (l.get k) s).support,
         match s' with
         | .yield next => rel (k.succ) next
         | .done next => rel (k.succ) next) :
    [⊥|forIn l init f] = 0 := by
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
      [⊥ | forIn xs s f] = 0 := by
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
lemma probFailure_forIn_of_relations_simplified {spec : OracleSpec ι} [spec.FiniteRange]
    {α σ : Type}
    (l : List α)
    (init : σ)
    (f : α → σ → OracleComp spec (ForInStep σ))
    (rel : Fin (l.length + 1) → σ → Prop)
    -- 1. Base Case
    (h_start : rel 0 init)
    -- 2. Inductive Step (Simplified)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       rel (k.castSucc) s →
       [⊥|f (l.get k) s] = 0 ∧
       -- Simplified: Just check the result state, no 'match' needed
       ∀ res ∈ (f (l.get k) s).support, rel (k.succ) res.state) :
    [⊥|forIn l init f] = 0 := by
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
lemma support_forIn_subset_rel {spec : OracleSpec ι} [spec.FiniteRange]
    {α σ : Type}
    (l : List α) (init : σ) (f : α → σ → OracleComp spec (ForInStep σ))
    (rel : Fin (l.length + 1) → σ → Prop)
    (h_start : rel 0 init)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       rel k.castSucc s →
       ∀ res ∈ (f (l.get k) s).support,
         match res with
         | .yield next => rel k.succ next
         | .done next => rel ⟨l.length, by omega⟩ next) :
    ∀ x ∈ (forIn l init f).support, rel ⟨l.length, by omega⟩ x := by
  -- Helper: Proves safety for a suffix `xs` starting at index `k`.
  let rec aux (k : ℕ) (xs : List α) (s : σ)
      (h_suffix : l.drop k = xs)
      (h_len : k + xs.length = l.length)
      (h_rel : rel ⟨k, by omega⟩ s) :
      ∀ x ∈ (forIn xs s f).support, rel ⟨l.length, by omega⟩ x := by
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
lemma support_forIn_subset_rel_yield_only {spec : OracleSpec ι} [spec.FiniteRange]
    {α σ : Type}
    (l : List α) (init : σ) (f : α → σ → OracleComp spec (ForInStep σ))
    (rel : Fin (l.length + 1) → σ → Prop)
    -- 1. Base Case
    (h_start : rel 0 init)
    -- 2. Inductive Step (Yield Only)
    (h_step : ∀ (k : Fin l.length) (s : σ),
       rel k.castSucc s →
       ∀ res ∈ (f (l.get k) s).support,
         res = .yield res.state ∧ rel k.succ res.state) :
    ∀ x ∈ (forIn l init f).support, rel ⟨l.length, by omega⟩ x := by
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
    [spec.FiniteRange] [superSpec.FiniteRange]
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
      simp only [forIn'_eq_forIn, Function.comp_apply, simulateQ_pure]
    · -- Yield: recurse (apply IH)
      apply ih

/-- Distributes `simulateQ` over `Vector.mapM`.

TODO: This proof is non-trivial because `Vector.mapM` is implemented via an auxiliary
`mapM.go` function that doesn't decompose cleanly. Attempted approaches:
- Vector induction produces `insertIdx` terms that don't match `mapM` structure
- toArray representation doesn't work since we're proving equality of `OracleComp` values
- Need either: (1) a lemma relating `simulateQ` to Array.mapM, or
  (2) a custom induction principle, or (3) direct reasoning about `mapM.go`. -/
@[simp]
lemma simulateQ_vector_mapM {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    (so : SimOracle.Stateless spec superSpec)
    {α β : Type} {n : ℕ} (f : α → OracleComp spec β) (v : Vector α n) :
    simulateQ so (Vector.mapM f v) = Vector.mapM (fun x ↦ simulateQ so (f x)) v := by
  sorry

/--
When each computation in a `Vector.mapM` returns `pure (f x)`, membership in support means
equality to `Vector.map f v`.

Note: This relies on `mem_support_vector_mapM` from VCVio which has a sorry.
-/
@[simp]
lemma mem_support_vector_mapM_pure {α β : Type} {n : ℕ} {ι : Type} {spec : OracleSpec ι}
    (f : α → β) (v : Vector α n) (x : Vector β n) :
    x ∈ (Vector.mapM (fun a ↦ pure (f a) : α → OracleComp spec β) v).support ↔
    x = Vector.map f v := by
  constructor
  · intro h
    ext i hi : 1
    have h_elem : x[i] ∈ (pure (f v[i]) : OracleComp spec β).support := by
      rw [OracleComp.mem_support_vector_mapM] at h
      exact h ⟨i, hi⟩
    simp only [OracleComp.support_pure, Set.mem_singleton_iff] at h_elem
    simp only [Vector.getElem_map, h_elem]
  · intro h
    rw [h, OracleComp.mem_support_vector_mapM]
    intro i
    simp only [Fin.getElem_fin, support_pure, Vector.getElem_map, Set.mem_singleton_iff]

end ForInLemmas

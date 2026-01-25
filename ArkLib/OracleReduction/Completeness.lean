/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic
import ArkLib.ToVCVio.Execution
import ArkLib.ToVCVio.Lemmas

/-!
# Completeness Proof Patterns for Oracle Reductions

This file contains reusable lemmas for proving perfect completeness of oracle reductions
with specific protocol structures. These lemmas handle the monadic unrolling and state
management automatically, reducing boilerplate in protocol-specific completeness proofs.

## Main Results

- `unroll_n_message_reduction_perfectCompleteness`: A generic lemma that bridges an n-message
  oracle reduction to its pure logic, handling induction unrolling, query implementation
  routing, and state peeling.
- `unroll_2_message_reduction_perfectCompleteness`: A specific lemma for 2-message protocols
  (e.g., P→V, V→P), deriving the explicit step-by-step form from the generic theorem.
- `unroll_1_message_reduction_perfectCompleteness_P_to_V`: A specific lemma for 1-message protocols
  (e.g., P→V only), useful for commitment rounds where the prover just submits data.
- `unroll_1_message_reduction_perfectCompleteness_V_to_P`: A specific lemma for 1-message protocols
  (e.g., V→P only), useful for query phase where the verifier just sends γ challenges.
## Usage

These lemmas are designed to be applied in protocol-specific completeness proofs. Instead of
manually unrolling the monadic execution, you can apply the appropriate lemma and then focus
on proving the pure logical properties of your protocol.

## Note

The parameter `n` in `ProtocolSpec n` represents the number of messages/steps in the protocol,
where each step can be either a prover message (P→V) or a verifier challenge (V→P).
-/

namespace OracleReduction

open OracleSpec OracleComp ProtocolSpec ProbComp

variable {ι : Type} {σ : Type}

/-! ## Supporting Lemmas for Safety Biconditionals

This section contains helper lemmas for proving safety equivalences between
simulated protocol executions and their pure specification counterparts.
-/

section SafetyLemmas

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.FiniteRange]

/-- `liftComp` preserves the never-fails property in both directions. -/
@[simp]
lemma probFailure_liftComp_iff
    {ι' : Type} {superSpec : OracleSpec ι'}
    [superSpec.FiniteRange]
    [MonadLift (OracleQuery oSpec) (OracleQuery superSpec)]
    {α : Type} (oa : OracleComp oSpec α) :
    [⊥|liftComp oa superSpec] = 0 ↔ [⊥|oa] = 0 := by
  simp only [probFailure_liftComp_eq]

/-- Safety of a bind can be decomposed into safety of each component. -/
@[simp]
lemma probFailure_bind_decompose
    {α β : Type} (oa : OracleComp oSpec α) (f : α → OracleComp oSpec β) :
    [⊥|oa >>= f] = 0 ↔ [⊥|oa] = 0 ∧ ∀ x ∈ oa.support, [⊥|f x] = 0 := by
  exact probFailure_bind_eq_zero_iff oa f

/-- Conjunction of safety conditions can be split. -/
lemma safety_and_split {P Q : Prop} :
    (P ∧ Q) ↔ P ∧ Q := by
  rfl

/-- Universal quantification over support with safety can be decomposed. -/
lemma forall_support_safety_decompose
    {α β : Type} (oa : OracleComp oSpec α) (f : α → OracleComp oSpec β) :
    (∀ x ∈ oa.support, [⊥|f x] = 0) ↔ (∀ x ∈ oa.support, [⊥|f x] = 0) := by
  rfl

end SafetyLemmas

/-! ## Generalized Bind Chain Safety Lemmas

This section provides reusable lemmas for proving safety of arbitrary nested do-blocks
by decomposing them into linear chains of dependent computations.

The core insight is that any do-block (regardless of nesting depth) can be unfolded
into a sequence of binds, each of which must be safe in the context of previously
computed values. These lemmas capture that pattern generically.
-/

section BindChainSafety

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.FiniteRange]

/-- **Two-step bind chain safety**
Decomposes safety of `oa₁ >>= λ x₁ => oa₂ x₁` into safety of both steps,
accounting for the dependency where oa₂ x₁ may depend on the value x₁ from oa₁.
-/
theorem probFailure_bind_chain_two_eq_zero
    {α₁ α₂ : Type}
    (oa₁ : OracleComp oSpec α₁)
    (oa₂ : α₁ → OracleComp oSpec α₂) :
    [⊥|oa₁ >>= oa₂] = 0 ↔
    [⊥|oa₁] = 0 ∧ ∀ x₁ ∈ oa₁.support, [⊥|oa₂ x₁] = 0 := by
  exact probFailure_bind_eq_zero_iff oa₁ oa₂

/-! **Generic composition principle: Decompose by peeling off two steps at a time**

This is the fundamental insight: to decompose an N-step chain, repeatedly apply the
2-step lemma. Each application reveals:
  [⊥|oa₁ >>= (λ x₁ => rest x₁)] = 0 ↔ [⊥|oa₁] = 0 ∧ (∀ x₁ ∈ oa₁.support, [⊥|rest x₁] = 0)

By recursively applying this, we can handle arbitrary depths without creating lemmas for each one.

**Example: 3-step decomposition**
  [⊥|oa₁ >>= oa₂ >>= oa₃] = 0
  ↔ [⊥|oa₁] = 0 ∧ (∀ x₁, [⊥|oa₂ x₁ >>= oa₃] = 0)     [apply 2-step lemma]
  ↔ [⊥|oa₁] = 0 ∧ (∀ x₁, [⊥|oa₂ x₁] = 0 ∧ (∀ x₂, [⊥|oa₃ x₂] = 0))  [apply 2-step again]

This compositionality means `probFailure_bind_chain_two_eq_zero` is sufficient for all depths!
-/

/-- **Three-step bind chain safety (derived from 2-step via composition)**
Provided as a convenience for direct use, but can always be reconstructed by
applying `probFailure_bind_chain_two_eq_zero` twice.
-/
theorem probFailure_bind_chain_three_eq_zero
    {α₁ α₂ α₃ : Type}
    (oa₁ : OracleComp oSpec α₁)
    (oa₂ : α₁ → OracleComp oSpec α₂)
    (oa₃ : α₂ → OracleComp oSpec α₃) :
    [⊥|oa₁ >>= fun x₁ => oa₂ x₁ >>= fun x₂ => oa₃ x₂] = 0 ↔
    [⊥|oa₁] = 0 ∧
    (∀ x₁ ∈ oa₁.support, [⊥|oa₂ x₁] = 0) ∧
    (∀ x₁ ∈ oa₁.support, ∀ x₂ ∈ (oa₂ x₁).support, [⊥|oa₃ x₂] = 0) := by
  simp only [probFailure_bind_eq_zero_iff]
  constructor
  · intro ⟨h₁, h₂₃⟩
    refine ⟨h₁, ?_, ?_⟩
    · intro x₁ h_x₁
      have := h₂₃ x₁ h_x₁
      exact this.1
    · intro x₁ h_x₁ x₂ h_x₂
      have := h₂₃ x₁ h_x₁
      exact this.2 x₂ h_x₂
  · intro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, fun x₁ h_x₁ => ?_⟩
    refine ⟨h₂ x₁ h_x₁, fun x₂ h_x₂ => ?_⟩
    exact h₃ x₁ h_x₁ x₂ h_x₂

/-- **Five-step bind chain safety (composing two-step lemma repeatedly)**
Rather than proving this directly, we compose the 2-step lemma three times.
This demonstrates the key principle: any N-step chain can be decomposed by
repeatedly applying the 2-step lemma.

Pattern for N steps:
  1. Apply 2-step to separate first step
  2. Recursively apply 2-step to remaining (N-1)-step chain
  3. Repeat until reaching base case

For this 5-step chain, we apply the pattern:
  [⊥|oa₁ >>= rest] = 0 ↔ [⊥|oa₁] = 0 ∧ (∀ x₁, [⊥|rest x₁] = 0)

where `rest = λ x₁ => oa₂ x₁ >>= oa₃ x₁ >>= oa₄ x₁ >>= oa₅ x₁`

This is the practical workhorse for protocols with 5 computational steps.
-/
theorem probFailure_bind_chain_five_eq_zero
    {α₁ α₂ α₃ α₄ α₅ : Type}
    (oa₁ : OracleComp oSpec α₁)
    (oa₂ : α₁ → OracleComp oSpec α₂)
    (oa₃ : α₂ → OracleComp oSpec α₃)
    (oa₄ : α₃ → OracleComp oSpec α₄)
    (oa₅ : α₄ → OracleComp oSpec α₅) :
    [⊥|oa₁ >>= fun x₁ => oa₂ x₁ >>= fun x₂ => oa₃ x₂ >>=
      fun x₃ => oa₄ x₃ >>= fun x₄ => oa₅ x₄] = 0 ↔
    [⊥|oa₁] = 0 ∧
    (∀ x₁ ∈ oa₁.support, [⊥|oa₂ x₁] = 0) ∧
    (∀ x₁ ∈ oa₁.support, ∀ x₂ ∈ (oa₂ x₁).support, [⊥|oa₃ x₂] = 0) ∧
    (∀ x₁ ∈ oa₁.support, ∀ x₂ ∈ (oa₂ x₁).support, ∀ x₃ ∈ (oa₃ x₂).support, [⊥|oa₄ x₃] = 0) ∧
    (∀ x₁ ∈ oa₁.support, ∀ x₂ ∈ (oa₂ x₁).support, ∀ x₃ ∈ (oa₃ x₂).support, ∀ x₄ ∈ (oa₄ x₃).support,
      [⊥|oa₅ x₄] = 0) := by
  simp only [probFailure_bind_eq_zero_iff]
  constructor
  · intro ⟨h₁, h₂₃₄₅⟩
    refine ⟨h₁, fun x₁ h_x₁ => ?_, fun x₁ h_x₁ x₂ h_x₂ => ?_,
      fun x₁ h_x₁ x₂ h_x₂ x₃ h_x₃ => ?_, fun x₁ h_x₁ x₂ h_x₂ x₃ h_x₃ x₄ h_x₄ => ?_⟩
    · exact (h₂₃₄₅ x₁ h_x₁).1
    · exact ((h₂₃₄₅ x₁ h_x₁).2 x₂ h_x₂).1
    · exact (((h₂₃₄₅ x₁ h_x₁).2 x₂ h_x₂).2 x₃ h_x₃).1
    · exact ((((h₂₃₄₅ x₁ h_x₁).2 x₂ h_x₂).2 x₃ h_x₃).2 x₄ h_x₄)
  · intro ⟨h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨h₁, fun x₁ h_x₁ => ?_⟩
    refine ⟨h₂ x₁ h_x₁, fun x₂ h_x₂ => ?_⟩
    refine ⟨h₃ x₁ h_x₁ x₂ h_x₂, fun x₃ h_x₃ => ?_⟩
    refine ⟨h₄ x₁ h_x₁ x₂ h_x₂ x₃ h_x₃, fun x₄ h_x₄ => ?_⟩
    exact h₅ x₁ h_x₁ x₂ h_x₂ x₃ h_x₃ x₄ h_x₄

end BindChainSafety

/-! ## Support Simplification for Do-Blocks

This section provides simp lemmas to simplify support expressions for common do-block patterns.
The key insight is that `support (do let x ← pure a; ...)` can be simplified by substituting `a`
directly into the continuation.
-/

section SupportSimplification

variable {ι : Type} {oSpec : OracleSpec ι}
  -- [oSpec.FiniteRange]

/-- Simplify support of: do let x ← pure a; let y ← f; pure (g x y) -/
@[simp]
lemma support_do_pure_bind_pure {α β γ : Type} (a : α) (f : OracleComp oSpec β) (g : α → β → γ) :
    (do
      let x ← pure a
      let y ← f
      pure (g x y)).support = (fun y => g a y) <$> f.support := by
  simp only [support_bind, support_pure]
  ext z
  simp [Set.mem_iUnion, Set.mem_image, eq_comm]

/-- Simplify support of: do let x ← pure a; let y ← f x; pure (g x y) -/
@[simp]
lemma support_do_pure_bind_dep_pure {α β γ : Type} (a : α)
  (f : α → OracleComp oSpec β) (g : α → β → γ) :
    (do
      let x ← pure a
      let y ← f x
      pure (g x y)).support = (fun y => g a y) <$> (f a).support := by
  simp only [support_bind, support_pure]
  ext z
  simp [Set.mem_iUnion, Set.mem_image, eq_comm]

/-- Simplify support of nested do-block: do let x ← (do let y ← pure a; f y); pure (g x) -/
@[simp]
lemma support_do_nested_pure {α β γ : Type} (a : α) (f : α → OracleComp oSpec β) (g : β → γ) :
    (do
      let x ← do
        let y ← pure a
        f y
      pure (g x)).support = g <$> (f a).support := by
  simp only [support_bind, support_pure]
  ext z
  simp [Set.mem_iUnion, Set.mem_image, eq_comm]


/-- Simplify support of triple-nested do-block -/
@[simp]
lemma support_do_triple_nested_pure {α β γ δ : Type}
    (a : α) (f : α → OracleComp oSpec β) (g : β → OracleComp oSpec γ) (h : γ → δ) :
    (do
      let x ← do
        let y ← do
          let z ← pure a
          f z
        g y
      pure (h x)).support = h <$> (do let y ← f a; g y).support := by
  simp only [support_bind, support_pure]
  ext w
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  aesop

/-- Simplify support when the final pure wraps a pair -/
@[simp]
lemma support_do_pure_pair {α β γ : Type} (a : α)
  (f : α → OracleComp oSpec β) (g : α → β → γ) :
    (do
      let x ← pure a
      let y ← f x
      pure (g x, y)).support = (fun y => (g a, y)) <$> (f a).support := by
  simp only [support_bind, support_pure]
  ext z
  simp [Set.mem_iUnion, Set.mem_image, eq_comm]

end SupportSimplification

/-! ## StateT-Specific Bind Chain Safety

This section lifts the bind chain lemmas to StateT computations, which are
fundamental for protocols that maintain mutable oracle state.
-/

/-! ## Protocol Chain Unfolding Tactics

This section provides tactical support for systematically unfolding arbitrary do-blocks
into their bind-chain equivalents, making nested protocol proofs more tractable.
-/

section DoBlockUnfolding

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.FiniteRange]

/-! **Systematic do-block unfolder**

This unfolds goals of the form `[⊥|do ... >>= ...] = 0` into a
conjunction of individual safety conditions by applying the appropriate bind chain lemma.

Usage:
  - Use `rw [probFailure_bind_chain_three_eq_zero]` to unfold 3-step chains
  - Use `rw [probFailure_bind_chain_five_eq_zero]` to unfold 5-step chains

For convenient systematic application, you can use `simp only [probFailure_bind_eq_zero_iff]`
which recursively decomposes nested binds into conjunctions.
-/

/-- **Systematic step-by-step unfolding: 3-step version**

For proofs that need to carefully reason about each step, this lemma provides
an explicit decomposition where each step can be proved independently.
-/
theorem unfold_do_block_three_steps
    {α₁ α₂ α₃ : Type}
    (step₁ : OracleComp oSpec α₁)
    (step₂ : α₁ → OracleComp oSpec α₂)
    (step₃ : α₂ → OracleComp oSpec α₃)
    (h₁ : [⊥|step₁] = 0)
    (h₂ : ∀ x₁ ∈ step₁.support, [⊥|step₂ x₁] = 0)
    (h₃ : ∀ x₁ ∈ step₁.support, ∀ x₂ ∈ (step₂ x₁).support, [⊥|step₃ x₂] = 0) :
    [⊥|step₁ >>= fun x₁ => step₂ x₁ >>= fun x₂ => step₃ x₂] = 0 := by
  rw [probFailure_bind_chain_three_eq_zero]
  exact ⟨h₁, h₂, h₃⟩

/-- **Systematic step-by-step unfolding: 5-step version**

Explicit decomposition for protocols with 5 computational steps:
  1. Prover sends message 0
  2. Verifier samples challenge 1
  3. Prover receives and responds to challenge 1
  4. Prover outputs final statement
  5. Verifier verifies the transcript

Each step's proof can be done independently.
-/
theorem unfold_do_block_five_steps
    {α₁ α₂ α₃ α₄ α₅ : Type}
    (step₁ : OracleComp oSpec α₁)
    (step₂ : α₁ → OracleComp oSpec α₂)
    (step₃ : α₂ → OracleComp oSpec α₃)
    (step₄ : α₃ → OracleComp oSpec α₄)
    (step₅ : α₄ → OracleComp oSpec α₅)
    (h₁ : [⊥|step₁] = 0)
    (h₂ : ∀ x₁ ∈ step₁.support, [⊥|step₂ x₁] = 0)
    (h₃ : ∀ x₁ ∈ step₁.support, ∀ x₂ ∈ (step₂ x₁).support, [⊥|step₃ x₂] = 0)
    (h₄ : ∀ x₁ ∈ step₁.support, ∀ x₂ ∈ (step₂ x₁).support, ∀ x₃ ∈ (step₃ x₂).support,
      [⊥|step₄ x₃] = 0)
    (h₅ : ∀ x₁ ∈ step₁.support, ∀ x₂ ∈ (step₂ x₁).support, ∀ x₃ ∈ (step₃ x₂).support,
      ∀ x₄ ∈ (step₄ x₃).support, [⊥|step₅ x₄] = 0) :
    [⊥|step₁ >>= fun x₁ => step₂ x₁ >>= fun x₂ => step₃ x₂ >>= fun x₃ =>
      step₄ x₃ >>= fun x₄ => step₅ x₄] = 0 := by
  rw [probFailure_bind_chain_five_eq_zero]
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

end DoBlockUnfolding

/-! ## Generic n-Message Protocol Completeness

This section provides a generic characterization of perfect completeness for protocols
with any number of messages. The key insight is to use `Prover.runToRound` abstractly
rather than unfolding it into explicit steps.

**Advantages over the 2-message specific version:**
- Works for any n (not just 2)
- Simpler RHS (3 steps instead of 4+)
- Leverages the inductive structure of `runToRound`
- Can be proven by induction on n

The 2-message version can be derived as a special case by instantiating n=2 and
unfolding `runToRound` using `Fin.induction`.
-/

section GenericProtocol

theorem forall_eq_bind_pure_iff {α β γ}
    (A : Set α) (B : α → Set β) (f : α → β → γ) (P : γ → Prop) :
    (∀ (x : γ), ∀ a ∈ A, ∀ b ∈ B a, x = f a b → P x) ↔
    (∀ a ∈ A, ∀ b ∈ B a, P (f a b)) := by
  constructor
  · -- Forward direction: Use the hypothesis with x := f a b
    intro h a ha b hb
    exact h (f a b) a ha b hb rfl
  · -- Backward direction: Substitute x with f a b
    intro h x a ha b hb hx
    rw [hx]
    exact h a ha b hb

-- 1. Basic version: ∀ y x, y = f x → P y x
theorem forall_eq_lift {α β} (f : α → β) (p : β → α → Prop) :
    (∀ (b : β) (a : α), b = f a → p b a) ↔ (∀ a : α, p (f a) a) := by
  constructor
  · intro h a; exact h (f a) a rfl
  · intro h b a heq; rw [heq]; exact h a

-- 2. Set membership version: ∀ y, ∀ x ∈ S, y = f x → P y x
theorem forall_eq_lift_mem {α β} {S : Set α} (f : α → β) (p : β → α → Prop) :
    (∀ (b : β), ∀ a ∈ S, b = f a → p b a) ↔ (∀ a ∈ S, p (f a) a) := by
  constructor
  · intro h a ha; exact h (f a) a ha rfl
  · intro h b a ha heq; rw [heq]; exact h a ha

-- 3. Nested Set version (Crucial for your goal): ∀ z, ∀ x ∈ S, ∀ y ∈ T, z = f x y → P z x y
theorem forall_eq_lift_mem_2 {α β γ} {S : Set α} {T : α → Set β}
    (f : α → β → γ) (p : γ → α → β → Prop) :
    (∀ (c : γ), ∀ a ∈ S, ∀ b ∈ T a, c = f a b → p c a b) ↔
    (∀ a ∈ S, ∀ b ∈ T a, p (f a b) a b) := by
  constructor
  · intro h a ha b hb; exact h (f a b) a ha b hb rfl
  · intro h c a ha b hb heq; rw [heq]; exact h a ha b hb

-- Allows swapping "∀ x" with "∀ a ∈ S"
theorem forall_mem_comm {α β} {S : Set α} {P : α → β → Prop} :
    (∀ (b : β), ∀ a ∈ S, P a b) ↔ (∀ a ∈ S, ∀ (b : β), P a b) := by
  constructor
  · intro h a ha b; exact h b a ha
  · intro h b a ha; exact h a ha b

-- Allows swapping "∀ x" with "∀ y" (Standard, but explicit helps simp)
theorem forall_comm_2 {α β} {P : α → β → Prop} :
    (∀ (a : α) (b : β), P a b) ↔ (∀ (b : β) (a : α), P a b) := forall_swap

-- A generic lemma: "If x equals a value 'a' found later, eliminate x"
theorem forall_eq_ghost {α : Sort*} {P : α → Prop} :
    (∀ (x : α) (a : α), x = a → P a) ↔ (∀ (a : α), P a) := by
  constructor
  · intro h a; exact h a a rfl
  · intro h x a heq; subst heq; exact h x

variable {oSpec : OracleSpec ι} [oSpec.FiniteRange] {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)] --[∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SelectableType (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

/-- Helper to lift a query object to a computation -/
def liftQuery {spec : OracleSpec ι} {α} (q : OracleQuery spec α) : OracleComp spec α :=
  match q with | query i t => query i t

/-- **Generic n-Message Protocol Completeness Theorem**

This theorem characterizes perfect completeness for interactive oracle reductions
with any number of messages. Unlike the 2-message specific version, this uses the
abstract `Prover.runToRound` function rather than explicitly unfolding all steps.

The RHS is much simpler: just run the prover to the last step, extract output,
and verify. The complexity of step-by-step execution is hidden in `runToRound`.

**Usage**: For specific protocols, instantiate this with the concrete number of messages.
For example, for a 2-message protocol, use `n := 2` and unfold `runToRound (Fin.last 2)`
if you need the explicit step-by-step form.
-/
theorem unroll_n_message_reduction_perfectCompleteness
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : init.neverFails)
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥|(impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftQuery q).support) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      [fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
      | do
          -- Run prover to the last step (abstractly, without unfolding)
          let ⟨transcript, state⟩ ← reduction.prover.runToRound (Fin.last n) (stmtIn, oStmtIn) witIn
          -- Extract prover's output
          let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp
            (reduction.prover.output state)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          -- Run verifier on the transcript
          let verifierStmtOut ← liftComp
            (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
      ] = 1 := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  simp only [OracleComp.probEvent_eq_one_iff]

  simp only [Prod.forall] at *

  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn

  simp only [Reduction_run_def, Prover.run, Prover.runToRound]
  have h_init_probFailure_eq_0 : [⊥|init] = 0 := by
    rw [probFailure_eq_zero_iff]; exact hInit

  conv_lhs =>
    simp only
    rw [probFailure_bind_eq_zero_iff]

  conv_lhs =>
    simp only [h_init_probFailure_eq_0, true_and]
    enter [1, x, 2]
    rw [probFailure_simulateQ_iff_stateful_run'
      (α := (pSpec.FullTranscript × (StmtOut × ((i : ιₛₒ) → OStmtOut i))
        × WitOut) × StmtOut × ((i : ιₛₒ) → OStmtOut i))
      (impl := (impl ++ₛₒ challengeQueryImpl)) (hImplSafe := by
      intro β q s
      cases q with | query i t =>
      cases i with
      | inl i => exact hImplSafe (query i t) s
      | inr i => exact probFailure_challengeQueryImpl_run (query i t) s
      ) (hImplSupp := by
      intro β q s
      cases q with | query i t =>
      cases i with
      | inl i => exact hImplSupp (query i t) s
      | inr i => exact support_challengeQueryImpl_run_eq (query i t) s
      )]
  conv_lhs =>
    enter [2];
    rw [support_bind_simulateQ_run'_eq (hInit := hInit) (hImplSupp := by
      intro β q s
      cases q with | query i t =>
      cases i with
      | inl i => exact hImplSupp (query i t) s
      | inr i => exact support_challengeQueryImpl_run_eq (query i t) s
    )]

  conv_lhs =>
    simp only [liftM_eq_liftComp]
  simp only [probFailure_bind_eq_zero_iff, probFailure_pure, implies_true, and_true,
    probFailure_liftComp]
  simp only [support_liftComp]
  simp only [OracleReduction.toReduction]

  have h_init_support_nonempty := support_nonempty_of_neverFails init hInit
  have elim_vacuous_quant : ∀ {α : Type} {S : Set α} {P : Prop},
      (∀ x ∈ S, P) ↔ (S.Nonempty → P) := by
    intro α S P
    constructor
    · intro h ⟨x, hx⟩; exact h x hx
    · intro h x hx; exact h ⟨x, hx⟩
  conv_lhs =>
    enter [1]
    rw [elim_vacuous_quant]
    simp only [h_init_support_nonempty, true_implies]
  rw [and_assoc, and_assoc, and_assoc]
  apply and_congr_right
  intro h_prover_execution_neverFails
  conv_rhs => simp only [forall_and]
  rw [and_assoc]
  apply and_congr_right
  intro h_prover_output_neverFails
  apply and_congr
  · conv_lhs =>
      simp only [
        OracleComp.support_bind,
        OracleComp.support_pure,
        OracleComp.support_map,
        support_liftComp,
        Set.mem_iUnion,
        Set.mem_singleton_iff,
        forall_exists_index,
        forall_apply_eq_imp_iff₂
      ]
    rw [forall_eq_bind_pure_iff]
  · simp only [
      OracleComp.support_bind,
      OracleComp.support_pure,
      support_liftComp,
      Set.mem_iUnion,
      Set.mem_singleton_iff,
      forall_exists_index,
      forall_and,
      forall_eq_lift_mem_2
    ]
    have imp_comm {P Q R : Prop} : (P → Q → R) ↔ (Q → P → R) := by
      constructor <;> intro h H1 H2 <;> exact h H2 H1
    simp only [and_imp, Prod.mk.injEq, Prod.forall]
    simp only [imp_comm]
    apply and_congr
    · constructor
      · intro hLeft
        intro x x_1 x_2 x_3 x_4 a b h_ab_in_support
        intro a_1 b_1 b_2 h_output_support
        intro a_2 b_verif
        intro h_x_eq h_x2_eq h_x4_eq h_x1_eq h_x3_eq h_verif_support
        rw [h_x2_eq, h_x3_eq, h_x4_eq]
        exact hLeft a x x_1 b_2 a_2 b_verif a b h_ab_in_support a_1 b_1 b_2 h_output_support
          a_2 b_verif h_x_eq rfl rfl h_x1_eq rfl h_verif_support rfl
      · intro hRight
        intro x x_1 x_2 x_3 x_4 x_5 a b h_ab_in_support
        intro a_2 b_1 b_2 h_output_support
        intro a_4 b_verif
        intro h_x1_eq h_x4_eq h_x3_eq h_x2_eq h_x5_eq h_verif_support h_x_eq
        rw [h_x4_eq, h_x5_eq, h_x3_eq]
        exact hRight a_2 b_1 a_4 b_verif b_2 a b h_ab_in_support a_2 b_1 b_2 h_output_support
          a_4 b_verif rfl rfl rfl rfl rfl h_verif_support
    · constructor
      · intro hLeft
        simp only [←forall_and]
        intro x x_1 x_2 x_3 x_4 a b h_ab_in_support
        intro a_1 b_1 b_2 h_output_support
        intro a_2 b_verif
        intro h_x_eq h_x2_eq h_x4_eq h_x1_eq h_x3_eq h_verif_support
        have := hLeft a x x_1 b_2 a_2 b_verif a b h_ab_in_support a_1 b_1 b_2 h_output_support
          a_2 b_verif h_x_eq rfl rfl h_x1_eq rfl h_verif_support rfl
        rw [h_x2_eq]
        constructor
        · simp only [this.1]
        · rw [this.2, h_x3_eq]
      · intro hRight
        intro x x_1 x_2 x_3 x_4 x_5 a b h_ab_in_support
        intro a_2 b_1 b_2 h_output_support
        intro a_4 b_verif
        intro h_x1_eq h_x4_eq h_x3_eq h_x2_eq h_x5_eq h_verif_support h_x_eq
        constructor
        · have result1 := hRight.1 x_1 x_2 x_4 x_5 x_3 a b h_ab_in_support a_2 b_1 b_2
            h_output_support a_4 b_verif h_x1_eq h_x4_eq h_x3_eq h_x2_eq h_x5_eq h_verif_support
          rw [result1, h_x4_eq]
        · have result2 := hRight.2 x_1 x_2 x_4 x_5 x_3 a b h_ab_in_support a_2 b_1 b_2
            h_output_support a_4 b_verif h_x1_eq h_x4_eq h_x3_eq h_x2_eq h_x5_eq h_verif_support
          rw [result2, h_x5_eq]

end GenericProtocol

section OneMessageProtocol

variable {oSpec : OracleSpec ι} [oSpec.FiniteRange] {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)] -- [∀ i, OracleInterface (OStmtOut i)]
  {pSpec : ProtocolSpec 1} [∀ i, SelectableType (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

/-- **Derive 1-message version from generic n-message theorem**

This theorem handles the case of a 1-message protocol where the prover sends a single
message to the verifier with no challenges. This is useful for protocols like commitment
rounds where the prover just submits data without any interaction.

The strategy is:
1. Apply the generic theorem with n := 1
2. Unfold `runToRound (Fin.last 1)` using `Prover.runToRound` definition
3. Simplify to get the explicit 2-step form (send message, output)
-/
theorem unroll_1_message_reduction_perfectCompleteness_P_to_V
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : init.neverFails)
    (hDir0 : pSpec.dir 0 = .P_to_V)
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥ | (impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftQuery q).support) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      [fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
      | do
          let ⟨msg0, state1⟩ ← liftComp
            (reduction.prover.sendMessage ⟨0, hDir0⟩
              (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state1)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let transcript : pSpec.FullTranscript := ProtocolSpec.FullTranscript.mk1 msg0
          let verifierStmtOut ← liftComp
            (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
      ] = 1 := by
-- 1. Apply the generic theorem for n = 1
  rw [unroll_n_message_reduction_perfectCompleteness (n := 1) (reduction := reduction)
    relIn relOut init impl hInit hImplSafe hImplSupp]
  -- 2. Peel off the quantifiers to get to the ProbComp execution
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  -- 3. Unfold Prover.runToRound
  simp only [Prover.runToRound]
  have h_last_eq_one : (Fin.last 1) = 1 := rfl
  -- 4. Set the limit to 1
  rw! (castMode := .all) [h_last_eq_one]
  -- 5. Focus on the LHS (Generic Execution)
  conv_lhs =>
    rw [Fin.induction_one'] -- Reduces induction 0 to pure init
    rw [Prover.processRound_P_to_V (h := hDir0)]
    simp only
  dsimp only [ChallengeIdx, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one, Message,
    liftM_eq_liftComp, Nat.reduceAdd, Fin.reduceLast]
  simp only [bind_assoc, pure_bind]
  congr!
  unfold FullTranscript.mk1
  funext i
  fin_cases i
  · rfl

/-- **Derive 1-message V→P version from generic n-message theorem**

This theorem is for 1-message protocols where the verifier sends a challenge to the prover
(e.g., query phase where V sends γ challenges).

The strategy is:
1. Apply the generic theorem for n = 1
2. Unfold `runToRound (Fin.last 1)` using `Prover.runToRound` definition
3. Simplify to get the explicit form (receive challenge, output)
-/
theorem unroll_1_message_reduction_perfectCompleteness_V_to_P
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : init.neverFails)
    (hDir0 : pSpec.dir 0 = .V_to_P)
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥ | (impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftQuery q).support) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      [fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
      | do
          let challenge ← liftComp (pSpec.getChallenge ⟨0, hDir0⟩) (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let receiveChallengeFn ← liftComp
            (reduction.prover.receiveChallenge ⟨0, hDir0⟩
              (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let state1 := receiveChallengeFn challenge
          let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state1)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let transcript : pSpec.FullTranscript := ProtocolSpec.FullTranscript.mk1 challenge
          let verifierStmtOut ← liftComp
            (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
      ] = 1 := by
  -- 1. Apply the generic theorem for n = 1
  rw [unroll_n_message_reduction_perfectCompleteness (n := 1) (reduction := reduction)
    relIn relOut init impl hInit hImplSafe hImplSupp]
  -- 2. Peel off the quantifiers to get to the ProbComp execution
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  -- 3. Unfold Prover.runToRound
  simp only [Prover.runToRound]
  have h_last_eq_one : (Fin.last 1) = 1 := rfl
  -- 4. Set the limit to 1
  rw! (castMode := .all) [h_last_eq_one]
  -- 5. Focus on the LHS (Generic Execution)
  conv_lhs =>
    rw [Fin.induction_one'] -- Reduces induction 0 to pure init
    rw [Prover.processRound_V_to_P (h := hDir0)]
    simp only
  dsimp only [ChallengeIdx, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one, Challenge,
    liftM_eq_liftComp, Nat.reduceAdd, Fin.reduceLast]
  simp only [bind_assoc, pure_bind]
  congr!
  unfold FullTranscript.mk1
  funext i
  fin_cases i
  · rfl

end OneMessageProtocol

section TwoMessageProtocol

variable {oSpec : OracleSpec ι} [oSpec.FiniteRange] {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)] -- [∀ i, OracleInterface (OStmtOut i)]
  {pSpec : ProtocolSpec 2} [∀ i, SelectableType (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

/-- **Derive 2-message version from generic n-message theorem**: [P->V, V->P]

This theorem tests whether `unroll_n_message_reduction_perfectCompleteness` is actually
useful by deriving the 2-message specific version from it. If this works, it validates
that the generic theorem can be instantiated for concrete protocols.

The strategy is:
1. Apply the generic theorem with n := 2
2. Unfold `runToRound (Fin.last 2)` using `Prover.runToRound` definition
3. Simplify using `Fin.induction` to get the explicit 4-step form
-/
theorem unroll_2_message_reduction_perfectCompleteness
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : init.neverFails)
    (hDir0 : pSpec.dir 0 = .P_to_V) (hDir1 : pSpec.dir 1 = .V_to_P)
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥ | (impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftQuery q).support) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      [fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
      | do
          let ⟨msg0, state1⟩ ← liftComp
            (reduction.prover.sendMessage ⟨0, hDir0⟩
              (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let r1 ← liftComp (pSpec.getChallenge ⟨1, hDir1⟩) (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let receiveChallengeFn ← liftComp (reduction.prover.receiveChallenge ⟨1, hDir1⟩ state1)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let state2 := receiveChallengeFn r1
          let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state2)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          let transcript := ProtocolSpec.FullTranscript.mk2 msg0 r1
          let verifierStmtOut ← liftComp
            (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
            (oSpec ++ₒ [pSpec.Challenge]ₒ)
          pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
      ] = 1 := by
  rw [unroll_n_message_reduction_perfectCompleteness (n := 2) (reduction := reduction)
    relIn relOut init impl hInit hImplSafe hImplSupp]
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Prover.runToRound]
  have h_last_eq_two : (Fin.last 2) = 2 := by rfl
  have h_init_probFailure_eq_0 : [⊥|init] = 0 := by
    rw [probFailure_eq_zero_iff]; exact hInit
  rw! (castMode := .all) [h_last_eq_two]
  simp only
  conv_lhs =>
    simp only [Fin.induction_two']
    rw [Prover.processRound_P_to_V (h := hDir0)]
    rw [Prover.processRound_V_to_P (h := hDir1)]
    simp only
  dsimp
  simp only [bind_assoc, pure_bind]
  unfold FullTranscript.mk2
  congr!
  rename_i msg0 r1 _ _ i
  fin_cases i
  · rfl
  · rfl

end TwoMessageProtocol

end OracleReduction

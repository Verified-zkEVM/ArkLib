/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.ToVCVio.Simulation.Basic
public import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Completeness Proof Patterns for Oracle Reductions

This file contains reusable lemmas for proving perfect completeness of oracle reductions
with specific protocol structures. These lemmas handle the monadic unrolling and state
management automatically, reducing boilerplate in protocol-specific completeness proofs.

## Main Results

- `unroll_n_message_reduction_perfectCompleteness`: A generic lemma that bridges an n-message
  oracle reduction to its pure logic, handling induction unrolling, query implementation
  routing, and state peeling.
- `unroll_0_message_reduction_perfectCompleteness`: A specific lemma for 0-message protocols
  (e.g., relay steps), deriving the explicit no-round form from the generic theorem.
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

@[expose] public section

namespace OracleReduction

open OracleSpec OracleComp ProtocolSpec ProbComp

variable {ι : Type} {σ : Type}

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
  · intro h a ha b hb
    exact h (f a b) a ha b hb rfl
  · intro h x a ha b hb hx
    rw [hx]
    exact h a ha b hb

theorem forall_eq_lift_mem_2 {α β γ} {S : Set α} {T : α → Set β}
    (f : α → β → γ) (p : γ → α → β → Prop) :
    (∀ (c : γ), ∀ a ∈ S, ∀ b ∈ T a, c = f a b → p c a b) ↔
    (∀ a ∈ S, ∀ b ∈ T a, p (f a b) a b) := by
  constructor
  · intro h a ha b hb; exact h (f a b) a ha b hb rfl
  · intro h c a ha b hb heq; rw [heq]; exact h a ha b hb

/-- Mapping an `Option` result before explicitly simulating an oracle computation maps
the successful event and leaves failure untouched. -/
theorem prEvent_simulateQ_option_map
    {ι σ α β : Type} {spec : OracleSpec ι}
    (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (computation : OracleComp spec (Option α)) (f : α → β) (P : β → Prop) :
    Pr{let result ← (OptionT.mk do
      let s ← init
      (simulateQ impl (Option.map f <$> computation)).run' s)}[P result] =
    Pr{let result ← (OptionT.mk do
      let s ← init
      (simulateQ impl computation).run' s)}[P (f result)] := by
  classical
  have hmap :
      (OptionT.mk do
        let s ← init
        (simulateQ impl (Option.map f <$> computation)).run' s) =
      f <$> (OptionT.mk do
        let s ← init
        (simulateQ impl computation).run' s) := by
    apply OptionT.ext
    rw [OptionT.run_map]
    change (do
      let s ← init
      (simulateQ impl (Option.map f <$> computation)).run' s) =
      (Option.map f <$> (do
        let s ← init
        (simulateQ impl computation).run' s) : ProbComp (Option β))
    simp only [simulateQ_map, StateT.run'_eq, map_bind, Functor.map_map, StateT.run_map]
  rw [hmap, prEvent_map]

variable {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

/-- Helper to lift a query object to a computation -/
def liftQuery {spec : OracleSpec ι} {α} (q : OracleQuery spec α) : OracleComp spec α :=
  OracleComp.lift q

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
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (_hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr{let ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          let computation : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
                (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) := do
            let ⟨transcript, state⟩ ←
              liftM (reduction.prover.runToRound (Fin.last n) (stmtIn, oStmtIn) witIn)
            let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp
              (reduction.prover.output state)
              (oSpec + [pSpec.Challenge]ₒ)
            let verifierStmtOut ← liftComp
              (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
              (oSpec + [pSpec.Challenge]ₒ)
            pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
          (simulateQ pImpl computation.run).run' s)}[
          ((verStmt, verOStmt), witOut) ∈ relOut ∧
            prvStmt = verStmt ∧ prvOStmt = verOStmt] = 1 := by
  classical
  rw [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness_eq_prob_one]
  constructor
  · intro h stmtIn oStmtIn witIn hmem
    specialize h (stmtIn, oStmtIn) witIn hmem
    let native := reduction.toReduction.run (stmtIn, oStmtIn) witIn
    let P : ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
        (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) → Prop :=
      fun ⟨(prvStmt, prvOStmt), (verStmt, verOStmt), witOut⟩ =>
        ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
    let f :
        ((pSpec.FullTranscript ×
          ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut)) ×
          (StmtOut × ((i : ιₛₒ) → OStmtOut i))) →
          ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
            (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) :=
      fun ⟨⟨_, ⟨prvStmt, prvOStmt⟩, witOut⟩, ⟨verStmt, verOStmt⟩⟩ =>
      ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut)
    let computation : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
          (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) := do
      let ⟨transcript, state⟩ ←
        liftM (reduction.prover.runToRound (Fin.last n) (stmtIn, oStmtIn) witIn)
      let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ←
        liftComp (reduction.prover.output state) (oSpec + [pSpec.Challenge]ₒ)
      let verifierStmtOut ←
        liftComp (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
          (oSpec + [pSpec.Challenge]ₒ)
      pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
    have hcomp : computation = f <$> native := by
      dsimp [computation, f, native]
      simp only [Reduction_run_def, Prover.run]
      simp only [liftM_bind, liftM_map, map_bind, bind_assoc,
        bind_map_left, bind_pure_comp, Functor.map_map]
      rfl
    have hbridge :
        Pr{let result ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          (simulateQ pImpl computation.run).run' s)}[P result] =
        Pr{let result ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          (simulateQ pImpl native.run).run' s)}[P (f result)] := by
      have hrun : computation.run = Option.map f <$> native.run := by
        rw [hcomp, OptionT.run_map]
      rw [hrun]
      exact prEvent_simulateQ_option_map init (QueryImpl.addLift impl challengeQueryImpl)
        native.run f P
    have hP :
        P ∘ f =
          fun ⟨⟨_, ⟨prvOut, witOut⟩⟩, verifierOut⟩ =>
            (verifierOut, witOut) ∈ relOut ∧ prvOut = verifierOut := by
      funext x
      rcases x with ⟨⟨transcript, prvOut⟩, verifierOut⟩
      rcases prvOut with ⟨prvOut, witOut⟩
      rcases prvOut with ⟨prvStmt, prvOStmt⟩
      rcases verifierOut with ⟨verStmt, verOStmt⟩
      simp only [Function.comp_apply, P, f]
      apply propext
      constructor
      · rintro ⟨hRel, hStmt, hOStmt⟩
        exact ⟨hRel, Prod.ext hStmt hOStmt⟩
      · rintro ⟨hRel, hEq⟩
        cases hEq
        exact ⟨hRel, rfl, rfl⟩
    have hP_apply := fun x => congrFun hP x
    simp only [Function.comp_apply] at hP_apply
    simp_rw [hP_apply] at hbridge
    exact hbridge.trans h
  · intro h stmtIn witIn hmem
    rcases stmtIn with ⟨stmtIn, oStmtIn⟩
    specialize h stmtIn oStmtIn witIn hmem
    let native := reduction.toReduction.run (stmtIn, oStmtIn) witIn
    let P : ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
        (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) → Prop :=
      fun ⟨(prvStmt, prvOStmt), (verStmt, verOStmt), witOut⟩ =>
        ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
    let f :
        ((pSpec.FullTranscript ×
          ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut)) ×
          (StmtOut × ((i : ιₛₒ) → OStmtOut i))) →
          ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
            (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) :=
      fun ⟨⟨_, ⟨prvStmt, prvOStmt⟩, witOut⟩, ⟨verStmt, verOStmt⟩⟩ =>
      ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut)
    let computation : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
          (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) := do
      let ⟨transcript, state⟩ ←
        liftM (reduction.prover.runToRound (Fin.last n) (stmtIn, oStmtIn) witIn)
      let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ←
        liftComp (reduction.prover.output state) (oSpec + [pSpec.Challenge]ₒ)
      let verifierStmtOut ←
        liftComp (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
          (oSpec + [pSpec.Challenge]ₒ)
      pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
    have hcomp : computation = f <$> native := by
      dsimp [computation, f, native]
      simp only [Reduction_run_def, Prover.run]
      simp only [liftM_bind, liftM_map, map_bind, bind_assoc,
        bind_map_left, bind_pure_comp, Functor.map_map]
      rfl
    have hbridge :
        Pr{let result ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          (simulateQ pImpl computation.run).run' s)}[P result] =
        Pr{let result ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          (simulateQ pImpl native.run).run' s)}[P (f result)] := by
      have hrun : computation.run = Option.map f <$> native.run := by
        rw [hcomp, OptionT.run_map]
      rw [hrun]
      exact prEvent_simulateQ_option_map init (QueryImpl.addLift impl challengeQueryImpl)
        native.run f P
    have hP :
        P ∘ f =
          fun ⟨⟨_, ⟨prvOut, witOut⟩⟩, verifierOut⟩ =>
            (verifierOut, witOut) ∈ relOut ∧ prvOut = verifierOut := by
      funext x
      rcases x with ⟨⟨transcript, prvOut⟩, verifierOut⟩
      rcases prvOut with ⟨prvOut, witOut⟩
      rcases prvOut with ⟨prvStmt, prvOStmt⟩
      rcases verifierOut with ⟨verStmt, verOStmt⟩
      simp only [Function.comp_apply, P, f]
      apply propext
      constructor
      · rintro ⟨hRel, hStmt, hOStmt⟩
        exact ⟨hRel, Prod.ext hStmt hOStmt⟩
      · rintro ⟨hRel, hEq⟩
        cases hEq
        exact ⟨hRel, rfl, rfl⟩
    have hP_apply := fun x => congrFun hP x
    simp only [Function.comp_apply] at hP_apply
    simp_rw [hP_apply] at hbridge
    exact hbridge.symm.trans h

end GenericProtocol

section ZeroMessageProtocol

variable {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {pSpec : ProtocolSpec 0} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

/-- **Derive 0-message version from generic n-message theorem**

This theorem handles protocols with no interaction rounds. It is useful for relay-style
steps (e.g., `pSpecRelay`) where the prover outputs immediately and the verifier checks
against the empty transcript.
-/
theorem unroll_0_message_reduction_perfectCompleteness
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr{let ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          let computation : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
                (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) := do
            let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ←
              liftComp
                (reduction.prover.output (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
                (oSpec + [pSpec.Challenge]ₒ)
            let verifierStmtOut ← liftComp
              (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) default)
              (oSpec + [pSpec.Challenge]ₒ)
            pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
          (simulateQ pImpl computation.run).run' s)}[
          ((verStmt, verOStmt), witOut) ∈ relOut ∧
            prvStmt = verStmt ∧ prvOStmt = verOStmt] = 1 := by
  rw [unroll_n_message_reduction_perfectCompleteness (n := 0) (reduction := reduction)
    relIn relOut init impl hImplSupp]
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Prover.runToRound]
  have h_last_eq_zero : (Fin.last 0) = 0 := rfl
  rw! (castMode := .all) [h_last_eq_zero]
  simp only [Fin.induction_zero]
  dsimp only [ChallengeIdx, Challenge, Fin.isValue, Fin.reduceLast, liftComp_eq_liftM]
  simp only [liftM_pure, bind_pure_comp, pure_bind, Prod.mk.eta]
  rfl

end ZeroMessageProtocol

section OneMessageProtocol

variable {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {pSpec : ProtocolSpec 1} [∀ i, SampleableType (pSpec.Challenge i)]
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
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (hDir0 : pSpec.dir 0 = .P_to_V)
  (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
    Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
  OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
  ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr{let ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          let computation : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
                (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) := do
            let ⟨msg0, state1⟩ ← liftComp
              (reduction.prover.sendMessage ⟨0, hDir0⟩
                (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
              (oSpec + [pSpec.Challenge]ₒ)
            let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state1)
              (oSpec + [pSpec.Challenge]ₒ)
            let transcript : pSpec.FullTranscript := ProtocolSpec.FullTranscript.mk1 msg0
            let verifierStmtOut ← liftComp
              (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
              (oSpec + [pSpec.Challenge]ₒ)
            pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
          (simulateQ pImpl computation.run).run' s)}[
          ((verStmt, verOStmt), witOut) ∈ relOut ∧
            prvStmt = verStmt ∧ prvOStmt = verOStmt] = 1 := by
  rw [unroll_n_message_reduction_perfectCompleteness (n := 1) (reduction := reduction)
    relIn relOut init impl hImplSupp]
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Prover.runToRound]
  have h_last_eq_one : (Fin.last 1) = 1 := rfl
  rw! (castMode := .all) [h_last_eq_one]
  conv_lhs =>
    rw [Fin.induction_one']
    rw [Prover.processRound_P_to_V (h := hDir0)]
    simp only
  dsimp only [ChallengeIdx, Challenge, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one,
    Message, liftComp_eq_liftM]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, liftM_map, Prod.mk.eta,
    bind_map_left]
  congr!
  rename_i _ prvState1 prvOut
  all_goals
    try rw [← ProtocolSpec.FullTranscript.mk1_eq_snoc]

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
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hDir0 : pSpec.dir 0 = .V_to_P)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr{let ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          let computation : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
                (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) := do
            let challenge ← liftComp (pSpec.getChallenge ⟨0, hDir0⟩) (oSpec + [pSpec.Challenge]ₒ)
            let receiveChallengeFn ← liftComp
              (reduction.prover.receiveChallenge ⟨0, hDir0⟩
                (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
              (oSpec + [pSpec.Challenge]ₒ)
            let state1 := receiveChallengeFn challenge
            let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state1)
              (oSpec + [pSpec.Challenge]ₒ)
            let transcript : pSpec.FullTranscript := ProtocolSpec.FullTranscript.mk1 challenge
            let verifierStmtOut ← liftComp
              (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
              (oSpec + [pSpec.Challenge]ₒ)
            pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
          (simulateQ pImpl computation.run).run' s)}[
          ((verStmt, verOStmt), witOut) ∈ relOut ∧
            prvStmt = verStmt ∧ prvOStmt = verOStmt] = 1 := by
  -- 1. Apply the generic theorem for n = 1
  rw [unroll_n_message_reduction_perfectCompleteness (n := 1) (reduction := reduction)
    relIn relOut init impl hImplSupp]
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
    liftComp_eq_liftM, Nat.reduceAdd, Fin.reduceLast]
  simp only [Fin.isValue, bind_pure_comp, pure_bind, liftM_bind, liftM_map, Prod.mk.eta, bind_assoc,
    bind_map_left]
  congr!
  all_goals
  · try rw [← ProtocolSpec.FullTranscript.mk1_eq_snoc]

end OneMessageProtocol

section TwoMessageProtocol

variable {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {pSpec : ProtocolSpec 2} [∀ i, SampleableType (pSpec.Challenge i)]
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
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hDir0 : pSpec.dir 0 = .P_to_V) (hDir1 : pSpec.dir 1 = .V_to_P)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr{let ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) ← (OptionT.mk do
          let s ← init
          let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
            QueryImpl.addLift impl challengeQueryImpl
          let computation : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
                (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut) := do
            let ⟨msg0, state1⟩ ← liftComp
              (reduction.prover.sendMessage ⟨0, hDir0⟩
                (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
              (oSpec + [pSpec.Challenge]ₒ)
            let r1 ← liftComp (pSpec.getChallenge ⟨1, hDir1⟩) (oSpec + [pSpec.Challenge]ₒ)
            let receiveChallengeFn ← liftComp (reduction.prover.receiveChallenge ⟨1, hDir1⟩ state1)
              (oSpec + [pSpec.Challenge]ₒ)
            let state2 := receiveChallengeFn r1
            let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp (reduction.prover.output state2)
              (oSpec + [pSpec.Challenge]ₒ)
            let transcript := ProtocolSpec.FullTranscript.mk2 msg0 r1
            let verifierStmtOut ← liftComp
              (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
              (oSpec + [pSpec.Challenge]ₒ)
            pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
          (simulateQ pImpl computation.run).run' s)}[
          ((verStmt, verOStmt), witOut) ∈ relOut ∧
            prvStmt = verStmt ∧ prvOStmt = verOStmt] = 1 := by
  rw [unroll_n_message_reduction_perfectCompleteness (n := 2) (reduction := reduction)
    relIn relOut init impl hImplSupp]
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Prover.runToRound]
  have h_last_eq_two : (Fin.last 2) = 2 := by rfl
  rw! (castMode := .all) [h_last_eq_two]
  conv_lhs =>
    simp only [Fin.induction_two']
    rw [Prover.processRound_P_to_V (h := hDir0)]
    rw [Prover.processRound_V_to_P (h := hDir1)]
    simp only
  dsimp
  simp only [Fin.isValue, bind_pure_comp, pure_bind, bind_map_left, liftM_bind, liftM_map,
    Prod.mk.eta, bind_assoc]
  congr!
  all_goals
  · try rw [← ProtocolSpec.FullTranscript.mk2_eq_snoc_snoc]

end TwoMessageProtocol

/-! ## Round-by-round knowledge-soundness reducers

These compatibility theorems retain the PR's protocol-shape API while delegating the
mixture argument to the maintained worst-case round-by-round interface. -/
section RbrKSReducers

open ProbabilityTheory
open scoped ProbabilityTheory NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {σ : Type}

theorem rbrKnowledgeSoundness_of_2msg_PtoV_uniformChallenge
    {pSpec : ProtocolSpec 2}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (hDir0 : pSpec.dir 0 = .P_to_V) (hDir1 : pSpec.dir 1 = .V_to_P)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
    (WitMid : Fin 3 → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (hbound : ∀ (stmtIn : StmtIn) (msg₀ : pSpec.Message ⟨0, hDir0⟩),
      Pr{let y ← $ᵗ (pSpec.Challenge (⟨1, hDir1⟩ : pSpec.ChallengeIdx))}[rbrExtractionFailureEvent
        kSF extractor (⟨1, hDir1⟩ : pSpec.ChallengeIdx) stmtIn
          (FullTranscript.mk1 msg₀) y] ≤ rbrKnowledgeError ⟨1, hDir1⟩) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError := by
  classical
  apply Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
  refine ⟨WitMid, extractor, kSF, ?_⟩
  intro stmtIn j transcript
  have h_j_eq_1 : j = ⟨1, hDir1⟩ := by
    obtain ⟨i, hj⟩ := j
    fin_cases i
    · exact absurd (hDir0.symm.trans hj) (by decide)
    · rfl
  subst j
  have htr : transcript = FullTranscript.mk1 (transcript ⟨0, by change 0 < 1; omega⟩) := by
    funext k
    fin_cases k
    rfl
  rw [htr]
  exact hbound stmtIn _

theorem rbrKnowledgeSoundness_of_1msg_VtoP_uniformChallenge
    {pSpec : ProtocolSpec 1}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    (hDir0 : pSpec.dir 0 = .V_to_P)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
    (WitMid : Fin 2 → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (hbound : ∀ (stmtIn : StmtIn)
        (transcript : pSpec.Transcript (⟨0, hDir0⟩ : pSpec.ChallengeIdx).1.castSucc),
      Pr{let y ← $ᵗ (pSpec.Challenge (⟨0, hDir0⟩ : pSpec.ChallengeIdx))}[rbrExtractionFailureEvent
        kSF extractor (⟨0, hDir0⟩ : pSpec.ChallengeIdx) stmtIn
          transcript y] ≤ rbrKnowledgeError ⟨0, hDir0⟩) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError := by
  classical
  apply Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
  refine ⟨WitMid, extractor, kSF, ?_⟩
  intro stmtIn j transcript
  have h_j_eq_0 : j = ⟨0, hDir0⟩ := by
    obtain ⟨i, hj⟩ := j
    fin_cases i
    rfl
  subst j
  exact hbound stmtIn transcript

end RbrKSReducers

end OracleReduction

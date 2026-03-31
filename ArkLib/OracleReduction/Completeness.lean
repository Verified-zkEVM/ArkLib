/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Security.RoundByRound
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

namespace OracleReduction

open OracleSpec OracleComp ProtocolSpec ProbComp

variable {ι : Type} {σ : Type}

/-! ## Supporting Lemmas for Safety Biconditionals

This section contains helper lemmas for proving safety equivalences between
simulated protocol executions and their pure specification counterparts.
-/

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

variable {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [[pSpec.Challenge]ₒ.Fintype] [[pSpec.Challenge]ₒ.Inhabited]
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
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
            let ⟨transcript, state⟩ ←
              liftM (reduction.prover.runToRound (Fin.last n) (stmtIn, oStmtIn) witIn)
            let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp
              (reduction.prover.output state)
              (oSpec + [pSpec.Challenge]ₒ)
            let verifierStmtOut ← liftComp
              (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
              (oSpec + [pSpec.Challenge]ₒ)
            pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
          ) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
                (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
        ] = 1 := by
  unfold OracleReduction.perfectCompleteness
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  simp only [probEvent_eq_one_iff]
  simp only [Prod.forall] at *
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Reduction_run_def, Prover.run, Prover.runToRound]
  have h_init_probFailure_eq_0 : Pr[⊥ | init] = 0 := by
    rw [probFailure_eq_zero_iff]; exact hInit
  conv_lhs =>
    simp only
    rw [OptionT.probFailure_mk_bind_eq_zero_iff]
  conv_lhs =>
    simp only [h_init_probFailure_eq_0, true_and]
    enter [1, x, 2]
    rw [probFailure_simulateQ_iff_stateful_run'_mk
      (α := (pSpec.FullTranscript × (StmtOut × ((i : ιₛₒ) → OStmtOut i))
        × WitOut) × StmtOut × ((i : ιₛₒ) → OStmtOut i))
      (impl := QueryImpl.addLift impl challengeQueryImpl) (hImplSupp := by
      intro β q s
      cases q with | mk t f =>
      cases t with
      | inl i => exact hImplSupp (OracleQuery.mk i f) s
      | inr i =>
        simp only [QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
          QueryImpl.addLift_def, QueryImpl.add_apply_inr]
        have hq := support_challengeQueryImpl_run_eq (q := OracleQuery.mk i f) s
        simpa only [ChallengeIdx, Challenge, add_apply_inr, QueryImpl.liftTarget_apply,
          StateT.run_map, StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map,
          support_map, Set.fmap_eq_image, toPFunctor_add, ofPFunctor_add, ofPFunctor_toPFunctor,
          support_liftM, QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
          liftM_map] using hq
      )]
  conv_lhs =>
    enter [2];
    rw [support_bind_simulateQ_run'_eq_mk (hInit := hInit) (hImplSupp := by
      intro β q s
      cases q with | mk t f =>
      cases t with
      | inl i => exact hImplSupp (OracleQuery.mk i f) s
      | inr i =>
        simp only [QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
          QueryImpl.addLift_def, QueryImpl.add_apply_inr]
        have hq := support_challengeQueryImpl_run_eq (q := OracleQuery.mk i f) s
        simpa only [ChallengeIdx, Challenge, add_apply_inr, QueryImpl.liftTarget_apply,
          StateT.run_map, StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map,
          support_map, Set.fmap_eq_image, toPFunctor_add, ofPFunctor_add, ofPFunctor_toPFunctor,
          support_liftM, QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
          liftM_map] using hq
      )]
  simp only [liftM_bind]
  simp only [ChallengeIdx, Challenge, liftM_pure, bind_pure_comp, liftM_OptionT_eq, Prod.mk.eta,
    bind_assoc, bind_map_left, OptionT.support_mk, Set.mem_setOf_eq, Prod.mk.injEq,
    liftComp_eq_liftM, probFailure_bind_eq_zero_iff, OptionT.mem_support_iff, probFailure_map,
    Prod.forall, support_bind, support_map, Set.mem_iUnion, Set.mem_image, toPFunctor_add,
    Prod.exists, ↓existsAndEq, and_true, true_and, exists_and_left, exists_prop,
    forall_exists_index, and_imp]
  rw [OptionT.probFailure_mk_do_bind_bindT_eq_zero_iff]
  simp only [OptionT.probFailure_mk_do_bindT_eq_zero_iff]
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
  conv_lhs =>
    enter [1, 1]
  simp only [and_assoc]
  apply and_congr_right
  intro h_prover_execution_neverFails
  simp_rw [forall_and]
  rw [and_assoc, and_assoc]
  conv => -- Key block to split the Prod support membership
    dsimp only [Functor.map, OptionT.instMonad]
    simp only [OptionT.mem_support_OptionT_bind_run_some_iff, Challenge,
      Function.comp_apply, Prod.exists]
  apply and_congr
  · constructor
    · intro h tr lastPrvState h_mem_prvRun
      exact h ⟨tr, lastPrvState⟩ h_mem_prvRun
    · intro h ⟨tr, lastPrvState⟩ h_mem_prvRun
      exact h tr lastPrvState h_mem_prvRun
  · apply and_congr
    · constructor
      · intro h tr lastPrvState h_mem_prvRun stmtOut oStmtOut witOut h_mem_prvOutput_support
        have h_res := h ⟨tr, lastPrvState⟩ (by simpa using h_mem_prvRun)
          ⟨⟨stmtOut, oStmtOut⟩, witOut⟩ (by simpa only using h_mem_prvOutput_support)
        simp only [OptionT.probFailure_bind_pure_comp_eq_zero_iff] at h_res
        exact h_res
      · intro h ⟨tr, lastPrvState⟩ h_mem_prvRun ⟨⟨stmtOut, oStmtOut⟩, witOut⟩
          h_mem_prvOutput_support
        simp only
        have h_res := h tr lastPrvState (by simpa only using h_mem_prvRun)
          stmtOut oStmtOut witOut (by simpa only using h_mem_prvOutput_support)
        simp only [OptionT.probFailure_bind_pure_comp_eq_zero_iff]
        exact h_res
    · apply and_congr
      · constructor
        · intro h pStmtOut pOStmtOut vStmtOut vOstmtOut witOut tr h_vOut
            lastPrvState h_mem_prvRun h_pOut
          have h_res := h tr pStmtOut pOStmtOut witOut vStmtOut vOstmtOut (by
            use tr, lastPrvState
            constructor
            · exact h_mem_prvRun
            · use pStmtOut, pOStmtOut, witOut
              refine ⟨?_, ?_⟩
              · exact h_pOut
              · use vStmtOut, vOstmtOut
                constructor
                · exact h_vOut
                · simp only [OptionT.support_OptionT_pure_run, Set.mem_singleton_iff]
          )
          exact h_res
        · intro h tr pStmtOut pOStmtOut witOut vStmtOut vOstmtOut h_exists_tr_lastPrvState
          rcases h_exists_tr_lastPrvState with
            ⟨a, b, h_prv, a_1, b_1, b_2, h_out, a_2, b_ver, h_ver, h_pure⟩
          simp only [OptionT.support_OptionT_pure_run, Set.mem_singleton_iff, Option.some.injEq,
            Prod.mk.injEq] at h_pure
          rcases h_pure with ⟨⟨rfl, ⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
          exact
            SetRel.mem_inv.mp
              (h pStmtOut pOStmtOut vStmtOut vOstmtOut (witOut, vStmtOut, vOstmtOut).1 tr h_ver b
                h_prv h_out)
      · apply and_congr
        · constructor
          · intro hLeft pStmtOut pOStmtOut vStmtOut vOStmtOut witOut
              tr h_ver lastPrvState h_mem_prvRun h_pOut
            apply hLeft tr pStmtOut pOStmtOut witOut vStmtOut vOStmtOut
            use tr, lastPrvState
            refine ⟨h_mem_prvRun, ?_⟩
            use pStmtOut, pOStmtOut, witOut
            refine ⟨h_pOut, ?_⟩
            use vStmtOut, vOStmtOut
            refine ⟨?_, rfl⟩
            dsimp only [OptionT.run] at h_ver
            simp only [OptionT.mem_support_simulateQ_liftQuery_iff, liftM_OptionT_eq]
            exact h_ver
          · intro hRight tr pStmtOut pOStmtOut pWitOut vStmtOut vOStmtOut h_exists_tr_lastPrvState
            rcases h_exists_tr_lastPrvState with
              ⟨a, b, h_prv, a_1, b_1, b_2, h_out, a_2, b_ver, h_ver, h_pure⟩
            simp only [OptionT.support_OptionT_pure_run, Set.mem_singleton_iff, Option.some.injEq,
              Prod.mk.injEq] at h_pure
            rcases h_pure with ⟨⟨rfl, ⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
            exact (hRight pStmtOut pOStmtOut vStmtOut vOStmtOut pWitOut tr h_ver b h_prv h_out)
        · constructor
          · intro hLeft pStmtOut pOstmtOut vStmtOut vOstmtOut pWitOut
              tr h_vOut lastPrvState h_mem_prvRun h_pOut
            have h_res := hLeft tr pStmtOut pOstmtOut pWitOut vStmtOut vOstmtOut (by
              use tr, lastPrvState
              refine ⟨?_, ?_⟩
              · exact h_mem_prvRun
              · use pStmtOut, pOstmtOut, pWitOut
                refine ⟨?_, ?_⟩
                · exact h_pOut
                · use vStmtOut, vOstmtOut
                  refine ⟨?_, rfl⟩
                  · exact h_vOut
            )
            exact h_res
          · intro hRight tr pStmtOut pOstmtOut pWitOut vStmtOut vOstmtOut h_exists_tr_lastPrvState
            rcases h_exists_tr_lastPrvState with
              ⟨a, b, h_prv, a_1, b_1, b_2, h_out, a_2, b_ver, h_ver, h_pure⟩
            simp only [OptionT.support_OptionT_pure_run, Set.mem_singleton_iff, Option.some.injEq,
              Prod.mk.injEq] at h_pure
            rcases h_pure with ⟨⟨rfl, ⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
            exact (hRight pStmtOut pOstmtOut vStmtOut vOstmtOut pWitOut tr h_ver b h_prv h_out)


end GenericProtocol

section ZeroMessageProtocol

variable {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
{StmtIn WitIn StmtOut WitOut : Type}
{ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
[∀ i, OracleInterface (OStmtIn i)]
{pSpec : ProtocolSpec 0} [∀ i, SampleableType (pSpec.Challenge i)]
[[pSpec.Challenge]ₒ.Fintype] [[pSpec.Challenge]ₒ.Inhabited]
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
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
          let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ←
            liftComp
              (reduction.prover.output (reduction.prover.input ((stmtIn, oStmtIn), witIn)))
              (oSpec + [pSpec.Challenge]ₒ)
          let verifierStmtOut ← liftComp
            (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) default)
            (oSpec + [pSpec.Challenge]ₒ)
          pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
        ) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
            ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) ×
              (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
      ] = 1 := by
  rw [unroll_n_message_reduction_perfectCompleteness (n := 0) (reduction := reduction)
    relIn relOut init impl hInit hImplSupp]
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

end ZeroMessageProtocol

section OneMessageProtocol

variable {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
{StmtIn WitIn StmtOut WitOut : Type}
{ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
[∀ i, OracleInterface (OStmtIn i)]
{pSpec : ProtocolSpec 1} [∀ i, SampleableType (pSpec.Challenge i)]
[[pSpec.Challenge]ₒ.Fintype] [[pSpec.Challenge]ₒ.Inhabited]
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
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : NeverFail init)
  (hDir0 : pSpec.dir 0 = .P_to_V)
  (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
    Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
  OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
  ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
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
      ) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
    ] = 1 := by
  rw [unroll_n_message_reduction_perfectCompleteness (n := 1) (reduction := reduction)
    relIn relOut init impl hInit hImplSupp]
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
    funext i
    fin_cases i <;> rfl

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
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : NeverFail init)
    (hDir0 : pSpec.dir 0 = .V_to_P)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
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
        ) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
            ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
      ] = 1 := by
  -- 1. Apply the generic theorem for n = 1
  rw [unroll_n_message_reduction_perfectCompleteness (n := 1) (reduction := reduction)
    relIn relOut init impl hInit hImplSupp]
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
  · funext i
    fin_cases i
    · rfl

end OneMessageProtocol

section TwoMessageProtocol

variable {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  {pSpec : ProtocolSpec 2} [∀ i, SampleableType (pSpec.Challenge i)]
  [[pSpec.Challenge]ₒ.Fintype] [[pSpec.Challenge]ₒ.Inhabited]
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
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hInit : NeverFail init)
    (hDir0 : pSpec.dir 0 = .P_to_V) (hDir1 : pSpec.dir 1 = .V_to_P)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftQuery q)) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
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
        ) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
            ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
      ] = 1 := by
  rw [unroll_n_message_reduction_perfectCompleteness (n := 2) (reduction := reduction)
    relIn relOut init impl hInit hImplSupp]
  apply forall_congr'; intro stmtIn
  apply forall_congr'; intro oStmtIn
  apply forall_congr'; intro witIn
  apply imp_congr_right; intro h_relIn
  simp only [Prover.runToRound]
  have h_last_eq_two : (Fin.last 2) = 2 := by rfl
  have h_init_probFailure_eq_0 : Pr[⊥|init] = 0 := by
    rw [probFailure_eq_zero_iff]; exact hInit
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
  · funext i
    fin_cases i
    · rfl
    · rfl

end TwoMessageProtocol

/-! ## Round-by-Round Knowledge Soundness Unroll Lemmas

This section provides unroll lemmas for `rbrKnowledgeSoundness` that mirror the structure
of the completeness unroll lemmas. These lemmas convert the probabilistic soundness bounds
into factored tsum forms that are easier to work with for probability reasoning.

**Key differences from completeness:**
- Completeness: `probEvent = 1` → pure logic/support statements
- Soundness: `probEvent ≤ error` → tsum factorization → probability bounds

**Main Results:**
- `unroll_rbrKnowledgeSoundness`: Generic lemma that factors the probEvent bound into a tsum
  over initial states, enabling uniform bounds on the inner computation.
- Future: Specific versions for 1-message and 2-message protocols (similar to completeness)
-/

section RoundByRoundKnowledgeSoundness

open NNReal ENNReal

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype]
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

lemma tsum_mul_le_of_le_of_sum_le_one_nnreal {α : Type*}
    {f g : α → ℝ≥0} {ε : ℝ≥0}
    (hf_summable : Summable f) -- Required for NNReal tsum arithmetic
    (hg : ∀ x, g x ≤ ε)
    (hf : ∑' x, f x ≤ 1) :
    ∑' x, f x * g x ≤ ε := by
  -- 1. Establish that the upper bound series (f x * ε) is summable
  have h_mul_summable : Summable (fun x ↦ f x * ε) :=
    hf_summable.mul_right ε
  -- 2. Establish that the target series (f x * g x) is summable by comparison
  have h_fg_summable : Summable (fun x ↦ f x * g x) := by
    refine NNReal.summable_of_le (fun x ↦ ?_) h_mul_summable
    exact mul_le_mul_of_nonneg_left (hg x) (zero_le (f x))
  -- 3. The calculation
  calc ∑' x, f x * g x
    _ ≤ ∑' x, f x * ε := by
      apply Summable.tsum_le_tsum _ h_fg_summable h_mul_summable
      intro x
      exact mul_le_mul_of_nonneg_left (hg x) (zero_le _)
    _ = (∑' x, f x) * ε := tsum_mul_right f ε
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hf (zero_le _)
    _ = ε := one_mul ε

lemma ENNReal.tsum_mul_le_of_le_of_sum_le_one {α : Type*} {f g : α → ℝ≥0∞} {ε : ℝ≥0∞}
    (hg : ∀ x, g x ≤ ε) -- The conditional probability is bounded
    (hf : ∑' x, f x ≤ 1) :    -- The weights sum to at most 1
    ∑' x, f x * g x ≤ ε := by
  calc ∑' x, f x * g x
    _ ≤ ∑' x, f x * ε :=
      ENNReal.tsum_le_tsum (fun x ↦ mul_le_mul_left' (hg x) _)
    _ = (∑' x, f x) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul_right' hf ε
    _ = ε := one_mul ε

omit [oSpec.Fintype] in
/-- **Unroll lemma for round-by-round knowledge soundness (uniform bound form)**

This is the preferred formulation for proving round-by-round knowledge soundness.
Instead of proving the tsum bound directly, we prove a **uniform bound for all states**:

```
∀ (s : σ), [doom_event | (simulateQ ...).run s] ≤ rbrKnowledgeError i
```

This implies `rbrKnowledgeSoundness` because:
- `∑' s, [= s | init] * [doom_event | ...run s] ≤ ∑' s, [= s | init] * ε`
- `= ε * ∑' s, [= s | init]`
- `≤ ε * 1 = ε`  (since `∑' s, [= s | init] ≤ 1` for any probability distribution)

This form is convenient because:
1. The initial state `s` is fixed, simplifying the probability reasoning
2. The bound holds uniformly regardless of `init`, making proofs more modular
3. It aligns with how we typically apply tools like Schwartz-Zippel
-/
theorem unroll_rbrKnowledgeSoundness
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (h_single_bound : ∀ stmtIn : StmtIn,
    ∀ witIn : WitIn,
    ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
    ∀ i : pSpec.ChallengeIdx,
    ∀ s : σ,
      (Pr[fun ⟨⟨transcript, challenge, _proveQueryLog⟩, _initState⟩ =>
        ∃ witMid,
          ¬ kSF i.1.castSucc stmtIn transcript
            (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
            kSF i.1.succ stmtIn (transcript.concat challenge) witMid
      | (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩
              ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run s] ≤
      rbrKnowledgeError i)) :
    (verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError) := by
  -- Provide the witnesses from hypotheses
  use WitMid, extractor, kSF
  intro stmtIn witIn prover i
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_mul_le_of_le_of_sum_le_one (α := σ) (f := fun s => Pr[= s | init])
  · intro s
    simp only [StateT.run']
    rw [probEvent_map]
    let res := h_single_bound stmtIn witIn prover i s
    exact res
  · apply tsum_probOutput_le_one

end RoundByRoundKnowledgeSoundness

/-! ## Probability Event Simplification Lemmas for Soundness Proofs

This section provides lemmas for simplifying `probEvent` expressions when the predicate
ignores certain parts of the output (like query logs or final states). These are essential
for reducing complex soundness goals to cleaner forms suitable for Schwartz-Zippel-style bounds.

### Key Patterns Addressed

1. **State marginalization**: When predicate ignores the final state from `StateT`
2. **Query log elimination**: When predicate ignores the query log from `runWithLogToRound`
3. **Combined patterns**: Full simplification for the common soundness proof shape

### Usage

Apply these lemmas (or use them as `simp` lemmas) to transform goals of the form:
```lean
[fun ⟨⟨transcript, challenge, _log⟩, _state⟩ => P transcript challenge |
  (simulateQ impl (do ... runWithLogToRound ... getChallenge ...)).run s]
```
into cleaner forms:
```lean
[fun ⟨transcript, challenge⟩ => P transcript challenge |
  simulateQ impl (do ... runToRound ... getChallenge ...)]
```
-/

section ProbEventSimplification

open NNReal ENNReal

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype]
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

/-! ### Lemma 1: State Marginalization

When the predicate ignores the final state, we can use `run'` instead of `run`. -/

/-- When the predicate ignores the final state from a stateful computation,
    the probability event can be computed using `run'` (which discards state). -/
theorem probEvent_StateT_run_ignore_state {α : Type}
    (comp : StateT σ ProbComp α) (s : σ)
    (P : α → Prop) [DecidablePred P] [DecidablePred (fun x : α × σ => P x.1)] :
    Pr[fun x : α × σ => P x.1 | comp.run s] = Pr[P | comp.run' s] := by
  simp only [StateT.run'_eq, probEvent_map]
  congr 1

omit [oSpec.Fintype] in
/-- Version for `simulateQ` with stateful implementation. -/
theorem probEvent_simulateQ_run_ignore_state {α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) (s : σ)
    (P : α → Prop) [DecidablePred P] [DecidablePred (fun x : α × σ => P x.1)] :
    Pr[fun x : α × σ => P x.1 | (simulateQ impl oa).run s] =
    Pr[P | (simulateQ impl oa).run' s] := by
  simp only [StateT.run'_eq, probEvent_map]
  congr 1

/-! ### Lemma 2: Query Log Elimination

When the predicate ignores the query log from `runWithLogToRound`, we can
eliminate the logging layer entirely using `runToRound`. -/

omit [oSpec.Fintype] [(i : pSpec.ChallengeIdx) → SampleableType (pSpec.Challenge i)] in
/-- When the predicate ignores the query log, `runWithLogToRound` can be replaced
    with `runToRound`. This is the fundamental query log elimination lemma. -/
theorem probEvent_runWithLogToRound_ignore_log
    [(oSpec + [pSpec.Challenge]ₒ).Fintype]
    [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : Fin (n + 1)) (stmt : StmtIn) (wit : WitIn)
    (P : pSpec.Transcript i × prover.PrvState i → Prop)
    [DecidablePred P]
    [DecidablePred (fun x : (pSpec.Transcript i × prover.PrvState i) ×
        QueryLog (oSpec + [pSpec.Challenge]ₒ) => P x.1)] :
    Pr[fun x => P x.1 | prover.runWithLogToRound i stmt wit] =
    Pr[P | prover.runToRound i stmt wit] := by
  rw [← Prover.runWithLogToRound_discard_log_eq_runToRound, probEvent_map]
  congr 1

/-! ### Lemma 3: Combined Transcript-Challenge Pattern

These lemmas handle the common pattern in soundness proofs where we compute
`(transcript, challenge, queryLog)` but only care about `(transcript, challenge)`. -/

/-- Projection function that extracts `(transcript, challenge)` from the full tuple
    `((transcript, challenge, queryLog), state)`. -/
@[reducible]
def projTranscriptChallenge {T C L S : Type} : ((T × C × L) × S) → T × C :=
  fun ⟨⟨t, c, _⟩, _⟩ => (t, c)

/-- Projection function that extracts `(transcript, challenge)` from the inner tuple
    `(transcript, challenge, queryLog)`. -/
@[reducible]
def projTranscriptChallengeInner {T C L : Type} : (T × C × L) → T × C :=
  fun ⟨t, c, _⟩ => (t, c)

/-- When computing `(transcript, challenge, queryLog)` inside a stateful simulation,
    but the predicate only uses `(transcript, challenge)`, we can eliminate both
    the query log and the state tracking.
    This transforms:
    ```
    Pr[fun ⟨⟨tr, chal, _log⟩, _state⟩ => P tr chal | (simulateQ impl computation).run s]
    ```
    into a cleaner form suitable for probability analysis. -/
theorem probEvent_proj_transcript_challenge
    {T C L : Type}
    (comp : StateT σ ProbComp (T × C × L))
    (s : σ) (P : T × C → Prop)
    [DecidablePred P]
    [DecidablePred (P ∘ projTranscriptChallenge (T := T) (C := C) (L := L) (S := σ))] :
    Pr[P ∘ projTranscriptChallenge | comp.run s] =
    Pr[P ∘ projTranscriptChallengeInner | comp.run' s] := by
  simp only [StateT.run'_eq, probEvent_map, Function.comp_def, projTranscriptChallenge,
    projTranscriptChallengeInner]

/-! ### Lemma 4: Master Log Unrolling for Soundness Goals

The ultimate lemmas that handle the full pattern appearing in `unroll_rbrKnowledgeSoundness`,
eliminating both the query log and state when the predicate doesn't use them. -/

omit [oSpec.Fintype] in
/-- **Master log unrolling lemma for soundness bounds.**

This transforms the complex goal shape from `unroll_rbrKnowledgeSoundness`:
```lean
Pr[fun ⟨⟨transcript, challenge, _log⟩, _state⟩ => P transcript challenge |
  (simulateQ (impl ++ₛₒ challengeQueryImpl)
    (do
      let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← runWithLogToRound ...
      let challenge ← getChallenge.liftComp ...
      pure (transcript, challenge, proveQueryLog))).run s]
```

into the cleaner form without logging:
```lean
Pr[fun ⟨transcript, challenge⟩ => P transcript challenge |
  (simulateQ (impl ++ₛₒ challengeQueryImpl)
    (do
      let ⟨transcript, _⟩ ← runToRound ...
      let challenge ← getChallenge.liftComp ...
      pure (transcript, challenge))).run' s]
```

This cleaner form is suitable for applying `probEvent_bind_eq_tsum` to factor
out the challenge for Schwartz-Zippel-style probability bounds.
-/
theorem probEvent_soundness_goal_unroll_log
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
    [(oSpec + [pSpec.Challenge]ₒ).Fintype]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (wit : WitIn) (s : σ)
    (P : pSpec.Transcript i.1.castSucc × pSpec.Challenge i → Prop)
    [DecidablePred P]
    [DecidablePred (fun x : (pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
      QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ => P (projTranscriptChallenge x))] :
    Pr[fun x => P (projTranscriptChallenge x) |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmt wit
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return (transcript, challenge, proveQueryLog))).run s] =
    Pr[fun x => P x |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmt wit
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return (transcript, challenge))).run' s] := by
  simp only  at *
  have h_eq : (fun x => P (projTranscriptChallenge (T := pSpec.Transcript i.1.castSucc)
      (C := pSpec.Challenge i) (L := QueryLog (oSpec + [pSpec.Challenge]ₒ)) (S := σ) x)) =
      P ∘ projTranscriptChallenge (T := pSpec.Transcript i.1.castSucc)
      (C := pSpec.Challenge i) (L := QueryLog (oSpec + [pSpec.Challenge]ₒ)) (S := σ) := by
    ext x
    simp only [Function.comp_apply]
  rw [h_eq]
  rw [← probEvent_map (f := projTranscriptChallenge (T := pSpec.Transcript i.1.castSucc)
      (C := pSpec.Challenge i) (L := QueryLog (oSpec + [pSpec.Challenge]ₒ)) (S := σ))]
  congr 1
  simp only [StateT.run'_eq]
  simp only [← Prover.runWithLogToRound_discard_log_eq_runToRound]
  simp only [simulateQ_bind, liftComp_query, bind_pure_comp, StateT.run_bind, Function.comp_apply,
    simulateQ_map,
    simulateQ_query, StateT.run_map, map_bind, Functor.map_map]
  rw [bind_map_left]

omit [oSpec.Fintype] in
/-- Variant of `probEvent_soundness_goal_unroll_log` with explicit predicate matching
    the exact shape in `unroll_rbrKnowledgeSoundness`. -/
theorem probEvent_soundness_goal_unroll_log'
    [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
    [(oSpec + [pSpec.Challenge]ₒ).Fintype]
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (wit : WitIn) (s : σ)
    (P : pSpec.Transcript i.1.castSucc → pSpec.Challenge i → Prop)
    [DecidablePred (fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i => P x.1 x.2)]
    [DecidablePred (fun x : (pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
      QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ => P x.1.1 x.1.2.1)] :
    Pr[fun x : (pSpec.Transcript i.1.castSucc × pSpec.Challenge i ×
        QueryLog (oSpec + [pSpec.Challenge]ₒ)) × σ => P x.1.1 x.1.2.1 |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmt wit
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return (transcript, challenge, proveQueryLog))).run s] =
    Pr[fun x : pSpec.Transcript i.1.castSucc × pSpec.Challenge i => P x.1 x.2 |
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmt wit
          let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
          return (transcript, challenge))).run' s] := by
  have h := probEvent_soundness_goal_unroll_log (ι := ι) (oSpec := oSpec)
    (StmtIn := StmtIn) (WitIn := WitIn) (StmtOut := StmtOut) (WitOut := WitOut)
    (n := n) (pSpec := pSpec) (σ := σ) (impl := impl) (prover := prover)
    (i := i) (stmt := stmt) (wit := wit) (s := s) (P := fun x => P x.1 x.2)
  exact h

end ProbEventSimplification

section SoundnessUnrolling

open OracleSpec OracleComp ProtocolSpec ProbComp

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]
  {σ : Type}

/-- **Unroll Soundness Computation: 1 Round (P → V)**

Unrolls `runToRound 1` when dir 0 = P_to_V (one prover message at index 0). For pSpecBatching
the challenge is at index 1; use `soundness_unroll_runToRound_2_pSpec_2` to unroll through it.

**Usage:** `rw [soundness_unroll_runToRound_1_P_to_V_pSpec_2]` -/
theorem soundness_unroll_runToRound_1_P_to_V_pSpec_2
    {pSpec : ProtocolSpec 2}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (hDir0 : pSpec.dir 0 = .P_to_V) :
    prover.runToRound 1 stmtIn witIn =
    do
      let msg0_state1 ← prover.sendMessage ⟨0, hDir0⟩ (prover.input (stmtIn, witIn))
      let transcript := ProtocolSpec.FullTranscript.mk1 msg0_state1.1
      return (transcript, msg0_state1.2) := by
  simp only [Prover.runToRound]
  have h_one_eq : (1 : Fin 3) = (1 : Fin 2).castSucc := rfl
  rw! (castMode := .all) [h_one_eq, Fin.induction_init]
  conv_lhs =>
    rw [Fin.induction_one']
    simp only [Fin.castSucc_zero]
    rw [Prover.processRound_P_to_V (h := hDir0)]
    simp only
  dsimp only [ChallengeIdx, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one, Challenge,
    Nat.reduceAdd, Fin.reduceLast]
  simp only [pure_bind]
  congr 1
  unfold FullTranscript.mk1
  funext i
  unfold Transcript.concat
  congr 1; congr 1
  funext x
  fin_cases x
  rfl

/-- **Unroll Soundness Computation: 1 Round (V → P)**

Variant when the first message (index 0) is verifier-to-prover: unrolls `runToRound 1` into
explicit `getChallenge` and `receiveChallenge` calls. Useful for ProtocolSpec 2 where dir 0 = V_to_P.

**Usage:** `rw [soundness_unroll_runToRound_1_V_to_P_pSpec_2]` -/
theorem soundness_unroll_runToRound_1_V_to_P_pSpec_2
    {pSpec : ProtocolSpec 2}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (hDir0 : pSpec.dir 0 = .V_to_P) :
    prover.runToRound 1 stmtIn witIn =
    do
      let challenge ← pSpec.getChallenge ⟨0, hDir0⟩
      let receiveChallengeFn ← prover.receiveChallenge ⟨0, hDir0⟩ (prover.input (stmtIn, witIn))
      let state1 := receiveChallengeFn challenge
      let transcript := ProtocolSpec.FullTranscript.mk1 challenge
      return (transcript, state1) := by
  simp only [Prover.runToRound]
  have h_one_eq : (1 : Fin 3) = (1 : Fin 2).castSucc := rfl
  rw! (castMode := .all) [h_one_eq, Fin.induction_init]
  conv_lhs =>
    rw [Fin.induction_one']
    simp only [Fin.castSucc_zero]
    rw [Prover.processRound_V_to_P (h := hDir0)]
    simp only
  dsimp only [ChallengeIdx, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one, Challenge,
    Nat.reduceAdd, Fin.reduceLast]
  simp only [pure_bind]
  congr 1
  unfold FullTranscript.mk1
  funext i
  unfold Transcript.concat
  congr 1;
  funext receiveChallengeFn
  congr 1; congr 1;
  funext x
  fin_cases x
  rfl

theorem soundness_unroll_runToRound_0_pSpec_1_V_to_P
    {pSpec : ProtocolSpec 1}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    prover.runToRound 0 stmtIn witIn =
    pure (default, prover.input (stmtIn, witIn)) := by
  simp only [Prover.runToRound]
  rfl

/-- **Unroll Soundness Computation: 2 Rounds (P → V, V → P)**

Unrolls the computation leading up to the second challenge (Index 2).
Useful for 5-move protocols or 2-round reductions.
-/
theorem soundness_unroll_runToRound_2_pSpec_2
    {pSpec : ProtocolSpec 2} -- Restrict to n=2 context or generally n >= 2
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn)
    (hDir0 : pSpec.dir 0 = .P_to_V) (hDir1 : pSpec.dir 1 = .V_to_P) :
    prover.runToRound 2 stmtIn witIn =
    do
      let ⟨msg0, state1⟩ ← prover.sendMessage ⟨0, hDir0⟩ (prover.input (stmtIn, witIn))
      let r1 ← pSpec.getChallenge ⟨1, hDir1⟩
      let receiveChallengeFn ← prover.receiveChallenge ⟨1, hDir1⟩ state1
      let state2 := receiveChallengeFn r1
      let transcript := ProtocolSpec.FullTranscript.mk2 msg0 r1
      return (transcript, state2) := by
  simp [Prover.runToRound, Fin.induction_two', Prover.processRound_P_to_V (h := hDir0),
    Prover.processRound_V_to_P (h := hDir1), ProtocolSpec.FullTranscript.mk2_eq_snoc_snoc]

end SoundnessUnrolling

section ProbEventToPrNotation

open ProbabilityTheory
open scoped ProbabilityTheory

/-- **Convert probEvent notation to Pr notation for PMF**

Converts `[P | pmf]` (where `pmf : PMF α`) to `Pr_{ let x ← pmf }[P x]`.

This bridges VCVio's `probEvent` notation with ArkLib's `Pr_` notation,
enabling the use of probability tools like Schwartz-Zippel.

**Note**: `[P | pmf]` where `pmf : PMF α` is interpreted as `pmf.toOuterMeasure {x | P x}`.
-/
theorem probEvent_PMF_eq_Pr {α : Type} (pmf : PMF α) (P : α → Prop) [DecidablePred P] :
    (pmf.toOuterMeasure {x | P x}) = Pr_{ let x ← pmf }[P x] := by
  -- Both sides compute the probability that P holds
  -- LHS: pmf.toOuterMeasure {x | P x} = ∑' x, if P x then pmf x else 0
  -- RHS: Pr_{ let x ← pmf }[P x] = (do let x ← pmf; return P x).val True
  --     = ∑' x, pmf x * (if P x then 1 else 0)
  simp only [PMF.toOuterMeasure_apply]
  rw [prob_tsum_form_singleton]
  congr 1
  funext x
  simp only [Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero]

/-- **Convert probOutput on OracleComp to PMF value**

If `evalDist oa = OptionT.lift pmf` for some `pmf : PMF α`, then `[= x | oa] = pmf x`.

This is useful when an `OracleComp` evaluates to a pure `PMF` (no failure probability).
-/
theorem probOutput_eq_PMF_apply
    {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    {α : Type} (oa : OracleComp spec α) (pmf : PMF α) (x : α)
    (h : evalDist oa = OptionT.lift pmf) :
    Pr[= x | oa] = pmf x := by
  have h' : evalDist oa = liftM pmf := by
    exact (show evalDist oa = liftM pmf from by
      simpa [OptionT.liftM_def] using h)
  exact (evalDist_eq_liftM_iff (mx := oa) (p := pmf)).1 h' x

open Classical in
/-- **Convert probOutput on uniform OracleComp to Pr_ notation**

If an `OracleComp` evaluates to uniform sampling from a finite type `L`,
then `[= x | oa]` equals the uniform probability `1/|L|` for any `x : L`.

This can be converted to `Pr_` notation: `[= x | oa] = Pr_{ let y ← $ᵖ L }[y = x]`.
-/
theorem probOutput_uniform_eq_Pr
    {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
    {L : Type} [Fintype L] [Nonempty L] [DecidableEq L]
    (oa : OracleComp spec L) (x : L)
    (h : evalDist oa = OptionT.lift (PMF.uniformOfFintype L)) :
    Pr[= x | oa] = Pr_{ let y ← $ᵖ L }[y = x] := by
  classical
  rw [probOutput_eq_PMF_apply oa (PMF.uniformOfFintype L) x h]
  simp

/-- **Convert probOutput on uniform OracleComp to Pr_ notation (using $ᵗ notation)**

If `oa = $ᵗ L` (uniform sampling from a finite type `L`),
then `[= x | oa]` equals the uniform probability `1/|L|` for any `x : L`.

This can be converted to `Pr_` notation: `[= x | $ᵗ L] = Pr_{ let y ← $ᵖ L }[y = x]`.

This version uses the existing `evalDist_uniformOfFintype` lemma to derive the hypothesis.

**Note**: The `[Inhabited L]` requirement is necessary because `evalDist_uniformOfFintype` requires it.
For field types `L`, this is automatically satisfied since `Field L` implies `Inhabited L` (via `Zero`).
-/
theorem probOutput_uniformOfFintype_eq_Pr
    {L : Type} [Fintype L] [Nonempty L] [DecidableEq L] [SampleableType L] [Inhabited L]
    (x : L) :
    Pr[= x | $ᵗ L] = Pr_{ let y ← $ᵖ L }[y = x] := by
  refine probOutput_uniform_eq_Pr ($ᵗ L) x ?_
  simpa [OptionT.liftM_def] using (evalDist_uniformSample (α := L))

open Classical in
/-- **Convert sum of uniform probabilities back to Pr_ notation**

If we have a sum over `x` where each term is `Pr_{ let y ← $ᵖ L }[y = x]` when `P x` holds,
this equals `Pr_{ let y ← $ᵖ L }[P y]`.

This is the inverse of expanding `Pr_` notation into a sum.
-/
theorem tsum_uniform_Pr_eq_Pr
    {L : Type} [Fintype L] [Nonempty L] [DecidableEq L]
    (P : L → Prop) [DecidablePred P] :
    (∑' x : L, if P x then Pr_{ let y ← $ᵖ L }[y = x] else 0) = Pr_{ let y ← $ᵖ L }[P y] := by
  classical
  simp

/-- **Convert probEvent on StateT.run' to tsum form**

Converts `[P | (comp : StateT σ ProbComp α).run' s]` to a sum form using `probEvent_eq_tsum_ite`.

**Note**: `ProbComp = OracleComp unifSpec`. The `probEvent` notation measures `Option.some '' {x | P x}`
in `PMF (Option α)`, which is equivalent to summing `[= x | comp.run' s]` over `α` where `P x` holds.

This is useful for further manipulation, e.g., applying probability bounds. Note that we cannot
directly convert to `Pr_` notation because `evalDist` returns `PMF (Option α)`, not `PMF α`.
-/
theorem probEvent_StateT_run'_eq_tsum
    {σ α : Type} (comp : StateT σ ProbComp α) (s : σ) (P : α → Prop) [DecidablePred P] :
    Pr[P | comp.run' s] = ∑' x : α, if P x then Pr[= x | comp.run' s] else 0 := by
  simpa using (probEvent_eq_tsum_ite (mx := comp.run' s) (p := P))

end ProbEventToPrNotation

end OracleReduction

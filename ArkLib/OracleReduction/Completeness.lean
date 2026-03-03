/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic
import ArkLib.ToVCVio.Simulation
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

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]

end SafetyLemmas

section BindChainSafety

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]

end BindChainSafety



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

-- 3. Nested Set version (Crucial for your goal): ∀ z, ∀ x ∈ S, ∀ y ∈ T, z = f x y → P z x y
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
  [∀ i, OracleInterface (OStmtIn i)] --[∀ i, OracleInterface (OStmtOut i)]
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
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
      Prod.fst <$> ((QueryImpl.mapQuery impl q).run s).support = (liftQuery q).support) :
    OracleReduction.perfectCompleteness init impl relIn relOut reduction ↔
    ∀ (stmtIn : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (witIn : WitIn),
      ((stmtIn, oStmtIn), witIn) ∈ relIn →
      Pr[fun ((prvStmt, prvOStmt), (verStmt, verOStmt), witOut) =>
          ((verStmt, verOStmt), witOut) ∈ relOut ∧ prvStmt = verStmt ∧ prvOStmt = verOStmt
        | ((do
            -- Run prover to the last step (abstractly, without unfolding)
            let ⟨transcript, state⟩ ←
              liftM (reduction.prover.runToRound (Fin.last n) (stmtIn, oStmtIn) witIn)
            -- Extract prover's output
            let ⟨⟨prvStmtOut, prvOStmtOut⟩, witOut⟩ ← liftComp
              (reduction.prover.output state)
              (oSpec + [pSpec.Challenge]ₒ)
            -- Run verifier on the transcript
            let verifierStmtOut ← liftComp
              (reduction.verifier.toVerifier.verify (stmtIn, oStmtIn) transcript)
              (oSpec + [pSpec.Challenge]ₒ)
            pure ((prvStmtOut, prvOStmtOut), verifierStmtOut, witOut)
          ) : OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
              ((StmtOut × ((i : ιₛₒ) → OStmtOut i)) × (StmtOut × ((i : ιₛₒ) → OStmtOut i)) × WitOut))
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
    -- dsimp only [OptionT.mk]
    rw [OptionT.probFailure_mk_bind_eq_zero_iff]
    -- rw [probFailure_bind_eq_zero_iff]

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
    liftComp_eq_liftM, probFailure_bind_eq_zero_iff, OptionT.mem_support_iff, -- OptionT.run_monadLift,
    support_map, Set.mem_image, Option.some.injEq, exists_eq_right, probFailure_map, Prod.forall,
    support_bind, Set.mem_iUnion, toPFunctor_add, exists_eq_right_right, exists_and_left,
    exists_prop, ↓existsAndEq, and_true, Prod.exists, true_and, and_imp, forall_exists_index]
  rw [OptionT.probFailure_mk_do_bind_bindT_eq_zero_iff]
  -- conv_lhs =>
    -- simp only [liftComp_eq_liftM]
  -- rw [OptionT.probFailure_mk_do_bind_bindT_eq_zero_iff]
  simp only [probFailure_bind_eq_zero_iff, probFailure_pure, implies_true, and_true,
    probFailure_liftM, probFailure_liftComp, support_liftComp, support_liftM,
    OptionT.probFailure_mk_do_bindT_eq_zero_iff, OptionT.probFailure_liftM, OptionT.support_liftM]
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
    -- simp only [liftM_bind]
    -- rw [probFailure_bind_eq_zero_iff]
  -- simp only [probFailure_bind_eq_zero_iff, probFailure_pure, implies_true, and_true,
  -- simp only [OptionT.probFailure_liftM, HasEvalPMF.probFailure_eq_zero]
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
        -- exact h ⟨tr, lastPrvState⟩ h_mem_prvRun
        have h_res := h ⟨tr, lastPrvState⟩ (by simpa using h_mem_prvRun)
          ⟨⟨stmtOut, oStmtOut⟩, witOut⟩ (by simpa only using h_mem_prvOutput_support)
        simp only [OptionT.probFailure_bind_pure_comp_eq_zero_iff] at h_res
        exact h_res
      · intro h ⟨tr, lastPrvState⟩ h_mem_prvRun ⟨⟨stmtOut, oStmtOut⟩, witOut⟩ h_mem_prvOutput_support
        simp only
        have h_res := h tr lastPrvState (by simpa only using h_mem_prvRun)
          stmtOut oStmtOut witOut (by simpa only using h_mem_prvOutput_support)
        simp only [OptionT.probFailure_bind_pure_comp_eq_zero_iff]
        exact h_res
    · apply and_congr
      ·
        constructor
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
            -- (by simpa using h_vOut) (by simpa using h_mem_prvRun) (by simpa using h_pOut)
          exact h_res
        · intro h tr pStmtOut pOStmtOut witOut vStmtOut vOstmtOut h_exists_tr_lastPrvState
          --   h_mem_prvOutput_support h_mem_ver
          -- exact h tr lastPrvState h_mem_prvRun stmtOut oStmtOut witOut h_mem_prvOutput_support
          --   verifierStmtOut h_mem_ver
          -- 1. Extract the individual states and execution proofs from the chain
          rcases h_exists_tr_lastPrvState with ⟨a, b, h_prv, a_1, b_1, b_2, h_out, a_2, b_ver, h_ver, h_pure⟩
          -- 2. The innermost proposition is a pure support membership. Simplify it into equalities.
          simp only [OptionT.support_OptionT_pure_run, Set.mem_singleton_iff, Option.some.injEq,
            Prod.mk.injEq] at h_pure
          -- 3. Destruct the nested tuple equalities to align the variables.
          -- This forces Lean to substitute `a` with `tr`, `b_2` with `witOut`, `a_2` with `vStmtOut`, etc.
          rcases h_pure with ⟨⟨rfl, ⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
          exact
            SetRel.mem_inv.mp
              (h pStmtOut pOStmtOut vStmtOut vOstmtOut (witOut, vStmtOut, vOstmtOut).1 tr h_ver b
                h_prv h_out)
      · apply and_congr
        · constructor
          ·
            -- 1. Introduce the hypotheses, renaming the variables for sanity
            intro hLeft pStmtOut pOStmtOut vStmtOut vOStmtOut witOut tr h_ver lastPrvState h_mem_prvRun h_pOut

            -- 2. Apply the master hypothesis to the specific variables we just introduced
            apply hLeft tr pStmtOut pOStmtOut witOut vStmtOut vOStmtOut

            -- 3. The goal is now the massive existential chain. We provide the witnesses sequentially.

            -- Prover Rounds
            use tr, lastPrvState
            refine ⟨h_mem_prvRun, ?_⟩

            -- Prover Output
            use pStmtOut, pOStmtOut, witOut
            refine ⟨h_pOut, ?_⟩

            -- Verifier Output
            use vStmtOut, vOStmtOut

            -- 4. Split into the verifier execution and the pure tuple assembly
            refine ⟨?_, rfl⟩
            dsimp only [OptionT.run] at h_ver
            simp only [OptionT.mem_support_simulateQ_liftQuery_iff, liftM_OptionT_eq]
            exact h_ver
          · -- 1. Introduce hypotheses. Lean auto-generated x, x_1, etc., so we keep them for the intro
            -- and rename the existential block to h_mem.
            intro hRight tr pStmtOut pOStmtOut pWitOut vStmtOut vOStmtOut h_exists_tr_lastPrvState
            -- 1. Extract the individual states, outputs, and execution proofs from the chain
            rcases h_exists_tr_lastPrvState with ⟨a, b, h_prv, a_1, b_1, b_2, h_out, a_2, b_ver, h_ver, h_pure⟩

            -- 2. Simplify the innermost pure support membership into raw equalities
            simp only [OptionT.support_OptionT_pure_run, Set.mem_singleton_iff, Option.some.injEq,
              Prod.mk.injEq] at h_pure

            -- 3. Destruct the nested tuple equalities.
            -- This forces Lean to substitute `a` with `tr`, `a_1` with `pStmtOut`, `a_2` with `vStmtOut`, etc.
            rcases h_pure with ⟨⟨rfl, ⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
            exact (hRight pStmtOut pOStmtOut vStmtOut vOStmtOut pWitOut tr h_ver b h_prv h_out)
        · constructor
          · -- mp: combined support membership → x_2 = x_5
            intro hLeft pStmtOut pOstmtOut vStmtOut vOstmtOut pWitOut tr h_vOut lastPrvState h_mem_prvRun h_pOut
            have h_res := hLeft tr pStmtOut pOstmtOut pWitOut vStmtOut vOstmtOut (by
            -- 1. Provide witnesses for the Prover Rounds
              use tr, lastPrvState

              -- Split the `∧` into the Prover Rounds subgoal and the rest of the chain
              refine ⟨?_, ?_⟩

              · -- Subgoal 1: Prove the Prover Rounds execution
                -- `liftM (...).support` is definitionally equivalent to `(...).run.support` here.
                exact h_mem_prvRun

              -- 2. Provide witnesses for the Prover Output
              · use pStmtOut, pOstmtOut, pWitOut
                refine ⟨?_, ?_⟩

                · -- Subgoal 2: Prove the Prover Output execution
                  exact h_pOut
                · use vStmtOut, vOstmtOut
                  refine ⟨?_, rfl⟩
                  · -- Subgoal 3: Prove the Verifier Output execution
                    exact h_vOut
            )
            exact h_res
          · -- mpr: decomposed witnesses → x_2 = x_5
            intro hRight tr pStmtOut pOstmtOut pWitOut vStmtOut vOstmtOut h_exists_tr_lastPrvState
             --   h_mem_prvOutput_support h_mem_ver
            -- exact h tr lastPrvState h_mem_prvRun stmtOut oStmtOut witOut h_mem_prvOutput_support
            --   verifierStmtOut h_mem_ver
            -- 1. Extract the individual states and execution proofs from the chain
            rcases h_exists_tr_lastPrvState with ⟨a, b, h_prv, a_1, b_1, b_2, h_out, a_2, b_ver, h_ver, h_pure⟩
            -- 2. The innermost proposition is a pure support membership. Simplify it into equalities.
            simp only [OptionT.support_OptionT_pure_run, Set.mem_singleton_iff, Option.some.injEq,
              Prod.mk.injEq] at h_pure
            -- 3. Destruct the nested tuple equalities to align the variables.
            -- This forces Lean to substitute `a` with `tr`, `b_2` with `witOut`, `a_2` with `vStmtOut`, etc.
            rcases h_pure with ⟨⟨rfl, ⟨rfl, rfl⟩, rfl⟩, rfl, rfl⟩
            exact (hRight pStmtOut pOstmtOut vStmtOut vOstmtOut pWitOut tr h_ver b h_prv h_out)


end GenericProtocol

section OneMessageProtocol

variable {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
{StmtIn WitIn StmtOut WitOut : Type}
{ιₛᵢ ιₛₒ : Type} {OStmtIn : ιₛᵢ → Type} {OStmtOut : ιₛₒ → Type}
[∀ i, OracleInterface (OStmtIn i)] -- [∀ i, OracleInterface (OStmtOut i)]
{pSpec : ProtocolSpec 1} [∀ i, SampleableType (pSpec.Challenge i)]
[∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
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
    Prod.fst <$> ((QueryImpl.mapQuery impl q).run s).support = (liftQuery q).support) :
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
  rw [Prover.processRound_P_to_V (h := hDir0)]
  simp only
dsimp only [ChallengeIdx, Challenge, Fin.isValue, Fin.castSucc_zero, Fin.succ_zero_eq_one, Message,
  liftComp_eq_liftM]
simp only [Challenge, Fin.isValue, bind_pure_comp, pure_bind, liftM_map, Prod.mk.eta,
  bind_map_left]
congr!
rename_i _ prvState1 prvOut
all_goals
  -- unfold FullTranscript.mk1 Transcript.concat Fin.snoc
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
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s,
      Pr[⊥ | (QueryImpl.mapQuery impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((QueryImpl.mapQuery impl q).run s).support = (liftQuery q).support) :
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
  [∀ i, OracleInterface (OStmtIn i)] -- [∀ i, OracleInterface (OStmtOut i)]
  {pSpec : ProtocolSpec 2} [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, Inhabited (pSpec.Challenge i)]
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
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, Pr[⊥|(QueryImpl.mapQuery impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((QueryImpl.mapQuery impl q).run s).support = (liftQuery q).support) :
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

end OracleReduction

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.StateRestoration
public import VCVio.OracleComp.QueryTracking.CostModel
public import ArkLib.Interaction.Core.Security.MeasuredResources

/-!
# Per-round errors in the state-restoration experiment

Each round of the protocol has its own local error. A challenge node's error is the error of its
round (`roundEps`, through `nodeRound`), and a key is charged the error of its round (`keyError`),
which is the error of its challenge node (`keyError_eq_roundEps`). An adaptive adversary with at
most `Q` queries pays at most `Q` times the largest round error on every branch, and completion pays
the sum of the round errors, so the restored execution has worst-case charge at most
`Q * max + sum` (`restoredExecution_round_cost`).
-/

@[expose] public section

universe uK uW uO wI wJ uS uI

namespace Interaction.Core.StateRestoration
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec Oracle

/-- Local errors indexed by round, in protocol order. -/
abbrev RoundErrors (rounds : List Round) := Fin rounds.length → ENNReal

/-- The round of a challenge node. -/
def nodeRound : (rounds : List Round) → ChallengeNode oracleSig (protocol rounds) →
    Fin rounds.length
  | [], ⟨n, _⟩ => n.elim
  | _ :: _, ⟨.inl _, h⟩ => nomatch h
  | _ :: _, ⟨.inr ⟨_, .inl _⟩, _⟩ => 0
  | _ :: rounds, ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, h⟩ => (nodeRound rounds ⟨n, h⟩).succ

/-- The error of a challenge node is the error of its round. -/
def roundEps {rounds : List Round} (errors : RoundErrors rounds) :
    ChallengeNode oracleSig (protocol rounds) → ENNReal :=
  errors ∘ nodeRound rounds

/-- A key is charged the error of its round. -/
def keyError {Input Salt : Type} : {rounds : List Round} → RoundErrors rounds →
    Key Input Salt rounds → ENNReal
  | [], _, key => nomatch key
  | _ :: _, errors, .inl _ => errors 0
  | _ :: _, errors, .inr (_, _, key) => keyError (fun j => errors j.succ) key

/-- A key's charge is the error of its challenge node. -/
theorem keyError_eq_roundEps {Input Salt : Type} : {rounds : List Round} →
    (errors : RoundErrors rounds) → (key : Key Input Salt rounds) →
    keyError errors key = roundEps errors (keyNode key)
  | [], _, key => key.elim
  | _ :: _, _, .inl _ => rfl
  | _ :: _, errors, .inr (_, _, key) => keyError_eq_roundEps (fun j => errors j.succ) key

/-- Every key's charge is at most the largest round error. -/
theorem keyError_le_max {Input Salt : Type} {rounds : List Round}
    (errors : RoundErrors rounds) (key : Key Input Salt rounds) :
    keyError errors key ≤ Finset.univ.sup errors := by
  induction rounds with
  | nil => exact key.elim
  | cons round rounds ih =>
      cases key with
      | inl _ => exact Finset.le_sup (Finset.mem_univ (0 : Fin (rounds.length + 1)))
      | inr data =>
          apply (ih (fun j => errors j.succ) data.2.2).trans
          apply Finset.sup_le
          intro j _
          exact Finset.le_sup (Finset.mem_univ j.succ)

/-- Routing a key of the remaining rounds keeps its round's charge on every execution. -/
theorem costDist_prependQuery {Input Salt A : Type} {round : Round} {rounds : List Round}
    (errors : RoundErrors (round :: rounds)) (message : round.Message) (salt : Salt)
    (program : OracleComp (oracleSpec Input Salt rounds) A) :
    costDist (simulateQ (prependQuery message salt) program)
        (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) =
      simulateQ (prependQuery message salt)
        (costDist program (⟨keyError (fun j => errors j.succ)⟩ :
          CostModel (oracleSpec Input Salt rounds) ENNReal)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [costDist, instrumentedRun]
  | query_bind key next ih =>
      simp only [costDist, instrumentedRun, QueryImpl.withAddCost, QueryImpl.ofLift_eq_id'] at ih
      simp [costDist, instrumentedRun, QueryImpl.withAddCost, prependQuery, OracleSpec.query,
        WriterT.run_bind, simulateQ_bind, simulateQ_query, bind_assoc, keyError, ih]

/-- A `Q`-query program pays at most `Q` times the largest round error on every branch. -/
theorem queryBound_round_cost {Input Salt A : Type} {rounds : List Round}
    (errors : RoundErrors rounds) (program : OracleComp (oracleSpec Input Salt rounds) A)
    (Q : Nat) (bounded : IsTotalQueryBound program Q) :
    WorstCaseCostBound program (⟨keyError errors⟩ :
      CostModel (oracleSpec Input Salt rounds) ENNReal) (Q * Finset.univ.sup errors) := by
  induction program using OracleComp.inductionOn generalizing Q with
  | pure value => simp
  | query_bind key next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro response result supported
      have tail := ih response (Q - 1) (bounded.2 response) result supported
      calc
        keyError errors key + Multiplicative.toAdd result.2 ≤
            Finset.univ.sup errors + (Q - 1 : Nat) * Finset.univ.sup errors :=
          add_le_add (keyError_le_max errors key) tail
        _ = Q * Finset.univ.sup errors := by
          have hQ : Q = (Q - 1) + 1 := by omega
          conv_rhs => rw [hQ]
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- Routing keys of the remaining rounds preserves a worst-case charge bound. -/
theorem roundCost_prependQuery {Input Salt A : Type} {round : Round} {rounds : List Round}
    (errors : RoundErrors (round :: rounds)) (message : round.Message) (salt : Salt)
    (program : OracleComp (oracleSpec Input Salt rounds) A) (budget : ENNReal)
    (bounded : WorstCaseCostBound program (⟨keyError (fun j => errors j.succ)⟩ :
      CostModel (oracleSpec Input Salt rounds) ENNReal) budget) :
    WorstCaseCostBound (simulateQ (prependQuery message salt) program)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) budget := by
  intro result supported
  change result ∈ support (costDist _ _) at supported
  rw [costDist_prependQuery] at supported
  exact bounded result (support_simulateQ_subset _ _ supported)

/-- Completion pays one round error per round, hence the sum of the round errors. -/
theorem complete_round_cost {Input Salt : Type} (rounds : List Round) (errors : RoundErrors rounds)
    (z : Input) (messages : Messages Salt rounds) :
    WorstCaseCostBound (complete rounds z messages)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal) (∑ j, errors j) := by
  induction rounds with
  | nil => exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      simp only [complete, List.length_cons]
      rw [Fin.sum_univ_succ]
      apply (worstCaseCostBound_query_bind_iff _ _ _ _).mpr
      intro challenge result supported
      have tail := roundCost_prependQuery errors message salt (complete rounds z messages) _
        (ih (fun j => errors j.succ) messages)
      have combined := tail.bind (fun tr => show WorstCaseCostBound
        (pure (⟨message, ⟨challenge, tr⟩⟩ : PathAlong oracleSig (protocol (round :: rounds))))
          (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) 0 from
            by simp)
      have hcost := combined result supported
      simpa only [keyError, add_zero, zero_add, add_comm] using add_le_add_left hcost (errors 0)

/-- The adversary's and completion's charges add in the restored execution. -/
theorem restoredExecution_round_cost {Input Salt W : Type} (rounds : List Round)
    (errors : RoundErrors rounds)
    (adversary : OracleComp (oracleSpec Input Salt rounds) (Input × Messages Salt rounds × W))
    (Q : Nat) (bounded : IsTotalQueryBound adversary Q) :
    WorstCaseCostBound (restoredExecution rounds adversary)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal)
      (Q * Finset.univ.sup errors + ∑ j, errors j) := by
  apply (queryBound_round_cost errors adversary Q bounded).bind
  rintro ⟨z, messages, witness⟩
  have completed := (complete_round_cost rounds errors z messages).bind
    (fun tr => show WorstCaseCostBound (pure (z, tr, witness))
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt rounds) ENNReal) 0 from by simp)
  simpa only [add_zero] using completed

/-! ### Knowledge soundness with per-round errors -/

section Knowledge

variable {S W Salt : Type} {Win : S → Type uW} {rounds : List Round} {admissible : S → Prop}
  {relIn : (stmt : S) → Win stmt → Prop}
  {Wout : S → PathAlong oracleSig (protocol rounds) → Type uO}
  {validOutput : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) → Wout stmt tr → Prop}

/-- Knowledge soundness of the restored execution with per-round errors: for every adversary with
at most `Q` queries, the probability that the selected input is admissible, the output read at the
completed transcript is valid and extraction fails is at most `Q * max_j errors j + ∑ j, errors j`.
-/
theorem restoredExecution_knowledge_soundness_nonuniform [DecidableEq (Key S Salt rounds)]
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput)
    (errors : RoundErrors rounds)
    (bounded : F.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    (readOut : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) → W → Wout stmt tr)
    (adversary : OracleComp (oracleSpec S Salt rounds) (S × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (restoredExecution rounds adversary)).run' ∅}[
      admissible result.1 ∧
        validOutput result.1 result.2.1 (readOut result.1 result.2.1 result.2.2) ∧
        ¬ relIn result.1
          (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2))] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j :=
  prEvent_randomOracle_le_of_bad_queries_weighted _ (keyError errors) _
    (restoredExecution_round_cost rounds errors adversary Q queryBound) _ (badKey F)
    (fun key table => (keyError_eq_roundEps errors key).symm ▸
      badKey_resample_bound bounded key table)
    (restored_bad_trace F readOut adversary)

end Knowledge

section Games

variable {rounds : List Round} {I S Salt W : Type} {A : I → Type}
  {T : Path (protocol rounds) → Type} {J : Path (protocol rounds) → Type}
  {B : (p : Path (protocol rounds)) → J p → Type}
  {Win : S × (∀ i, A i) → Type uW}
  {inputs : OracleFamily.{0, 0, wI} I A}
  {outputs : (p : Path (protocol rounds)) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {admissible : S × (∀ i, A i) → Prop} {relIn : (stmt : S × (∀ i, A i)) → Win stmt → Prop}
  {Wout : (S × (∀ i, A i)) → PathAlong oracleSig (protocol rounds) → Type uO}
  {validOutput : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) →
    Wout stmt tr → Prop}

/-- State-restoration knowledge soundness of a verifier with per-round errors. -/
theorem stateRestoration_knowledge_soundness_nonuniform
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : PathAlong oracleSig (protocol rounds)) →
      T (projectPathAlong oracleSig _ tr) → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr t w, terminalObservation V stmt tr = some t → relOut stmt tr t w →
      validOutput stmt tr (readOut stmt tr w))
    (errors : RoundErrors rounds)
    (bounded : F.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (verificationGame V adversary)).run' ∅}[
      admissible result.1 ∧
      (∃ t, result.2.2.1 = some t ∧ relOut result.1 result.2.1 t result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  rw [verificationGame_eq, simulateQ_map, StateT.run'_map', prEvent_map]
  refine le_trans (prEvent_mono _ _ _ ?_)
    (restoredExecution_knowledge_soundness_nonuniform F errors bounded readOut adversary Q
      queryBound)
  rintro ⟨stmt, tr, w⟩ ⟨hadm, ⟨t, ht, hrel⟩, hfail⟩
  exact ⟨hadm, outputLaw stmt tr t w ht hrel, hfail⟩

/-- State-restoration knowledge soundness with output oracle data and per-round errors. -/
theorem stateRestoration_oracle_knowledge_soundness_nonuniform
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : PathAlong oracleSig (protocol rounds)) →
      OracleVerifier.Output T B (projectPathAlong oracleSig _ tr) → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr claim w, closedTerminalObservation V stmt tr = some claim →
      relOut stmt tr claim w → validOutput stmt tr (readOut stmt tr w))
    (errors : RoundErrors rounds)
    (bounded : F.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame V adversary)).run' ∅}[
      admissible result.1 ∧
      (∃ claim, result.2.2.1 = some claim ∧ relOut result.1 result.2.1 claim result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  rw [closedVerificationGame_eq, simulateQ_map, StateT.run'_map', prEvent_map]
  refine le_trans (prEvent_mono _ _ _ ?_)
    (restoredExecution_knowledge_soundness_nonuniform F errors bounded readOut adversary Q
      queryBound)
  rintro ⟨stmt, tr, w⟩ ⟨hadm, ⟨claim, hc, hrel⟩, hfail⟩
  exact ⟨hadm, outputLaw stmt tr claim w hc hrel, hfail⟩

end Games

end Interaction.Core.StateRestoration

/-! ### Measured extraction along the rounds -/

namespace Interaction.Core.KnowledgeStateFunction.MeasuredStages
open PFunctor FreeM TwoParty.Lens OracleComp
open Interaction.Core.StateRestoration

variable {s : OracleProtocol} {S : Type uS} {Win : S → Type} {W : S → PathAlong oracleSig s → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : PathAlong oracleSig s) → W stmt tr → Prop}
  {F : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig s S W Win admissible relIn validOutput}
  {ω : Type}

variable [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]

/-- Under a per-node-kind bound, the budget from a cursor whose remaining protocol is `rounds` is
at most the leaf bound plus, for each remaining round, the message and challenge bounds. -/
theorem programFrom_budget_le_rounds (stages : MeasuredStages F ω) {stmt : S}
    {rootBound messageBound challengeBound leafBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt rootBound messageBound challengeBound leafBound) :
    (rounds : List Round) → (sp : Cursor.Spine s (protocol rounds)) →
    (history : PrefixMoves oracleSig sp) → (tr : PathAlong oracleSig (protocol rounds)) →
    (stages.programFrom stmt sp history tr).budget ≤
      leafBound + rounds.length • (messageBound + challengeBound)
  | [], sp, history, _ => le_of_le_of_eq (h.leaf sp history) (by simp)
  | round :: rounds, sp, history, ⟨message, ⟨challenge, tr⟩⟩ => by
    change (stages.programFrom stmt _ (PrefixMoves.snoc oracleSig _
        (PrefixMoves.snoc oracleSig sp history message) challenge) tr).budget +
      (stages.step stmt _ (PrefixMoves.snoc oracleSig sp history message)).budget +
      (stages.step stmt sp history).budget ≤ _
    calc
      _ ≤ leafBound + rounds.length • (messageBound + challengeBound) + challengeBound +
          messageBound :=
        add_le_add (add_le_add (programFrom_budget_le_rounds stages h rounds _ _ tr)
          (h.step _ _)) (h.step sp history)
      _ = leafBound + (round :: rounds).length • (messageBound + challengeBound) := by
        rw [List.length_cons, succ_nsmul]
        ac_rfl

/-- Under a per-node-kind bound, the budget along a transcript of `protocol rounds` is at most the
leaf bound, plus `rounds.length` times the sum of the message and challenge bounds, plus the root
bound. -/
theorem programAlong_budget_le_protocol {rounds : List Round}
    {Wout : S → PathAlong oracleSig (protocol rounds) → Type}
    {valid : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) → Wout stmt tr → Prop}
    {G : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn valid}
    (stages : MeasuredStages G ω) {stmt : S}
    {rootBound messageBound challengeBound leafBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt rootBound messageBound challengeBound leafBound)
    (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong stmt tr).budget ≤
      leafBound + rounds.length • (messageBound + challengeBound) + rootBound :=
  add_le_add (programFrom_budget_le_rounds stages h rounds (.root _) ⟨⟩ tr) h.root

/-- Zero root and leaf budgets recover the bound that counts only the two stages per round. -/
theorem programAlong_budget_le_protocol_zero {rounds : List Round}
    {Wout : S → PathAlong oracleSig (protocol rounds) → Type}
    {valid : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) → Wout stmt tr → Prop}
    {G : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn valid}
    (stages : MeasuredStages G ω) {stmt : S} {messageBound challengeBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt 0 messageBound challengeBound 0)
    (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong stmt tr).budget ≤ rounds.length • (messageBound + challengeBound) := by
  simpa only [zero_add, add_zero] using programAlong_budget_le_protocol stages h tr

/-- Every execution path of the composed program along a transcript of `protocol rounds` costs at
most the protocol budget. -/
theorem programAlong_costAtMost_protocol {rounds : List Round}
    {Wout : S → PathAlong oracleSig (protocol rounds) → Type}
    {valid : (stmt : S) → (tr : PathAlong oracleSig (protocol rounds)) → Wout stmt tr → Prop}
    {G : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn valid}
    (stages : MeasuredStages G ω) {stmt : S}
    {rootBound messageBound challengeBound leafBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt rootBound messageBound challengeBound leafBound)
    (tr : PathAlong oracleSig (protocol rounds)) :
    (stages.programAlong stmt tr).program.CostAtMost
      (leafBound + rounds.length • (messageBound + challengeBound) + rootBound) :=
  (stages.programAlong stmt tr).costAtMost.mono (programAlong_budget_le_protocol stages h tr)

end Interaction.Core.KnowledgeStateFunction.MeasuredStages

namespace Interaction.Core.MeasuredKnowledgeStateFunction
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec Oracle
open Interaction.Core.StateRestoration

variable {rounds : List Round} {I S Salt W Kind : Type} [Finite Kind]
  {A : I → Type} {T : Path (protocol rounds) → Type}
  {J : Path (protocol rounds) → Type} {B : (p : Path (protocol rounds)) → J p → Type}
    {Win : S × (∀ i, A i) → Type}
  {inputs : OracleFamily.{0, 0, wI} I A}
  {outputs : (p : Path (protocol rounds)) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {admissible : S × (∀ i, A i) → Prop} {relIn : (stmt : S × (∀ i, A i)) → Win stmt → Prop}
  {Wout : (S × (∀ i, A i)) → PathAlong oracleSig (protocol rounds) → Type}
  {validOutput : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) →
    Wout stmt tr → Prop}

/-- A measured knowledge state function with per-round errors and per-node-kind stage bounds. The
closed verification game has knowledge error at most `Q * max_j errors j + ∑ j, errors j`, and
for every admissible input and transcript the composed stage program returns the extracted input
witness and costs at most the protocol budget on every execution path. -/
theorem stateRestoration_oracle_knowledge_soundness_nonuniform
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : PathAlong oracleSig (protocol rounds)) →
      OracleVerifier.Output T B (projectPathAlong oracleSig _ tr) → W → Prop)
    (M : MeasuredKnowledgeStateFunction Kind oracleSig (protocol rounds) (S × (∀ i, A i)) Wout
      Win admissible relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr claim w, closedTerminalObservation V stmt tr = some claim →
      relOut stmt tr claim w → validOutput stmt tr (readOut stmt tr w))
    (errors : RoundErrors rounds)
    (bounded : M.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    (rootBound messageBound challengeBound leafBound : S × (∀ i, A i) → Kind → ℕ)
    (budget : ∀ z, admissible z → M.stages.ProtocolBudgetAtMost z (rootBound z)
      (messageBound z) (challengeBound z) (leafBound z))
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame V adversary)).run' ∅}[
      admissible result.1 ∧
      (∃ claim, result.2.2.1 = some claim ∧ relOut result.1 result.2.1 claim result.2.2.2) ∧
      ¬ relIn result.1
        (M.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j ∧
    ∀ z, admissible z → ∀ tr,
      (∀ w, (M.stages.programAlong z tr).program.run w = M.extractAlong z tr w) ∧
      (M.stages.programAlong z tr).program.CostAtMost
        (leafBound z + rounds.length • (messageBound z + challengeBound z) + rootBound z) :=
  ⟨StateRestoration.stateRestoration_oracle_knowledge_soundness_nonuniform V relOut
      M.toKnowledgeStateFunction readOut outputLaw errors bounded adversary Q queryBound,
    fun z hz tr => ⟨M.stages.run_programAlong z tr,
      KnowledgeStateFunction.MeasuredStages.programAlong_costAtMost_protocol M.stages
        (budget z hz) tr⟩⟩

end Interaction.Core.MeasuredKnowledgeStateFunction

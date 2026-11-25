/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Security.StateRestoration
public import VCVio.OracleComp.QueryTracking.CostModel.Simulation
public import ArkLib.Interaction.Security.MeasuredExtraction

/-!
# Per-round errors in the state-restoration experiment

Each round of the protocol has its own local error. A challenge node's error is the error of its
round (`roundEps`, through `nodeRound`), and a key is charged the error of its round (`keyError`),
which is the error of its challenge node (`keyError_eq_roundEps`). An adaptive adversary with at
most `Q` queries pays at most `Q` times the largest round error on every branch, and completion pays
the sum of the round errors, so the restored execution has worst-case charge at most
`Q * max + sum` (`restoredExecution_round_cost`).

The verification games therefore have knowledge error at most `Q * max + sum` for a fixed
adversary program with at most `Q` queries (`stateRestoration_knowledge_soundness_nonuniform`,
`stateRestoration_oracle_knowledge_soundness_nonuniform`). The `_privateCoins` forms average this
bound over private coins whose sampler may fail; every fixed-coin adversary has the same query
bound `Q`. The uniform theorems in `StateRestoration` give `(Q + rounds.length) * error` instead.

## Measured extraction

`MeasuredKnowledgeStateFunction.stateRestoration_oracle_knowledge_soundness_nonuniform` bounds the
stage programs along the completed transcript on the witness that `readOut` has already converted.
It does not charge `readOut`. `MeasuredKnowledgeStateFunction.extractionProgram` runs a program
realizing `readOut` before the stage programs, and
`stateRestoration_oracle_knowledge_soundness_nonuniform_withReadOut` states the failure event on
that composite program and charges both. Budgets are per statement and count declared stage
instructions only.

## References

Chiesa and Yogev's Theorem 31.3.1 and WARP's Theorem B.4 give the uniform error bound, which this
module refines by round. The port record
(`docs/design/interaction-layer/state-restoration-disposition.md`) gives the detailed
correspondence.

* [Chiesa, A., and Yogev, E., *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
* [Bünz, B., Chiesa, A., Fenzi, G., and Wang, W., *Linear time accumulation
    schemes*][BCFW25]
-/
@[expose] public section

universe uK uW uO wI wJ uS uI

namespace Interaction.StateRestoration
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
      have tail := (worstCaseCostBound_iff_support_bound ..).1 (ih _ _ (bounded.2 _)) _ supported
      calc
        keyError errors key + Multiplicative.toAdd result.2 ≤
            Finset.univ.sup errors + (Q - 1 : Nat) * Finset.univ.sup errors :=
          add_le_add (keyError_le_max errors key) tail
        _ = Q * Finset.univ.sup errors := by
          have hQ : Q = (Q - 1) + 1 := by omega
          conv_rhs => rw [hQ]
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- Routing keys of the remaining rounds preserves a worst-case charge bound. The handler issues
one query at the charge of the routed key, so VCVio's `WorstCaseCostBound.simulateQ` transfers the
bound. -/
theorem roundCost_prependQuery {Input Salt A : Type} {round : Round} {rounds : List Round}
    (errors : RoundErrors (round :: rounds)) (message : round.Message) (salt : Salt)
    (program : OracleComp (oracleSpec Input Salt rounds) A) (budget : ENNReal)
    (bounded : WorstCaseCostBound program (⟨keyError (fun j => errors j.succ)⟩ :
      CostModel (oracleSpec Input Salt rounds) ENNReal) budget) :
    WorstCaseCostBound (simulateQ (prependQuery message salt) program)
      (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) budget :=
  bounded.simulateQ (prependQuery message salt) fun key =>
    worstCaseCostBound_query (spec := oracleSpec Input Salt (round :: rounds))
      (Key.later message salt key) _

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
        (pure (⟨message, ⟨challenge, tr⟩⟩ : Transcript oracleSig (protocol (round :: rounds))))
          (⟨keyError errors⟩ : CostModel (oracleSpec Input Salt (round :: rounds)) ENNReal) 0 from
            by simp)
      have hcost := (worstCaseCostBound_iff_support_bound _ _ _).mp combined result supported
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
  {Wout : S → Transcript oracleSig (protocol rounds) → Type uO}
  {validOutput : (stmt : S) → (tr : Transcript oracleSig (protocol rounds)) → Wout stmt tr → Prop}

/-- Knowledge soundness of the restored execution with per-round errors: for every adversary with
at most `Q` queries, the probability that the selected input is admissible, the output read at the
completed transcript is valid and extraction fails is at most `Q * max_j errors j + ∑ j, errors j`.
-/
theorem restoredExecution_knowledge_soundness_nonuniform [DecidableEq (Key S Salt rounds)]
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn validOutput)
    (errors : RoundErrors rounds)
    (bounded : F.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    (readOut : (stmt : S) → (tr : Transcript oracleSig (protocol rounds)) → W → Wout stmt tr)
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
  {Wout : (S × (∀ i, A i)) → Transcript oracleSig (protocol rounds) → Type uO}
  {validOutput : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) →
    Wout stmt tr → Prop}

/-- State-restoration knowledge soundness of a verifier with per-round errors. -/
theorem stateRestoration_knowledge_soundness_nonuniform
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : Transcript oracleSig (protocol rounds)) →
      T tr.path → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr t w, verdict V stmt tr = some t → relOut stmt tr t w →
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
    (relOut : S × (∀ i, A i) → (tr : Transcript oracleSig (protocol rounds)) →
      OracleVerifier.Output T B tr.path → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
    (S × (∀ i, A i)) Wout Win admissible
      relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr claim w, closedVerdict V stmt tr = some claim →
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

/-- State-restoration knowledge soundness with per-round errors, averaged over the adversary's
private coins. The coin sampler may fail; failed coins contribute missing mass. Every fixed-coin
adversary has the same query bound `Q`, so averaging the fixed-coin bound gives
`Q * max_j errors j + ∑ j, errors j`. -/
theorem stateRestoration_knowledge_soundness_nonuniform_privateCoins
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : Transcript oracleSig (protocol rounds)) →
      T tr.path → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      (S × (∀ i, A i)) Wout Win admissible relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr t w, verdict V stmt tr = some t → relOut stmt tr t w →
      validOutput stmt tr (readOut stmt tr w))
    (errors : RoundErrors rounds)
    (bounded : F.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    {Coins : Type} (coins : OptionT ProbComp Coins)
    (adversary : Coins → OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : ∀ c, IsTotalQueryBound (adversary c) Q) :
    Pr{let result ← (coins >>= fun c => OptionT.lift
        ((simulateQ randomOracle (verificationGame V (adversary c))).run' ∅))}[
      admissible result.1 ∧
      (∃ t, result.2.2.1 = some t ∧ relOut result.1 result.2.1 t result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  apply prEvent_bind_le_of_forall_le
  intro c
  rw [OptionT.prEvent_lift]
  exact stateRestoration_knowledge_soundness_nonuniform V relOut F readOut outputLaw errors
    bounded (adversary c) Q (queryBound c)

/-- The private-coins form of `stateRestoration_oracle_knowledge_soundness_nonuniform`. The coin
sampler may fail, and every fixed-coin adversary has the same query bound `Q`. -/
theorem stateRestoration_oracle_knowledge_soundness_nonuniform_privateCoins
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : Transcript oracleSig (protocol rounds)) →
      OracleVerifier.Output T B tr.path → W → Prop)
    (F : KnowledgeStateFunction.{0, uW, uK, uO, 1, 0} oracleSig (protocol rounds)
      (S × (∀ i, A i)) Wout Win admissible relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr claim w, closedVerdict V stmt tr = some claim →
      relOut stmt tr claim w → validOutput stmt tr (readOut stmt tr w))
    (errors : RoundErrors rounds)
    (bounded : F.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    {Coins : Type} (coins : OptionT ProbComp Coins)
    (adversary : Coins → OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : ∀ c, IsTotalQueryBound (adversary c) Q) :
    Pr{let result ← (coins >>= fun c => OptionT.lift
        ((simulateQ randomOracle (closedVerificationGame V (adversary c))).run' ∅))}[
      admissible result.1 ∧
      (∃ claim, result.2.2.1 = some claim ∧ relOut result.1 result.2.1 claim result.2.2.2) ∧
      ¬ relIn result.1
        (F.extractAlong result.1 result.2.1 (readOut result.1 result.2.1 result.2.2.2))] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j := by
  apply prEvent_bind_le_of_forall_le
  intro c
  rw [OptionT.prEvent_lift]
  exact stateRestoration_oracle_knowledge_soundness_nonuniform V relOut F readOut outputLaw errors
    bounded (adversary c) Q (queryBound c)

end Games

end Interaction.StateRestoration

/-! ### Measured extraction along the rounds -/

namespace Interaction.KnowledgeStateFunction.MeasuredStages
open PFunctor FreeM TwoParty.Lens OracleComp
open Interaction.StateRestoration

variable {s : OracleProtocol} {S : Type uS} {Win : S → Type} {W : S → Transcript oracleSig s → Type}
  {admissible : S → Prop} {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : Transcript oracleSig s) → W stmt tr → Prop}
  {F : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig s S W Win admissible relIn validOutput}
  {ω : Type}

variable [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω]

/-- Under a per-node-kind bound, the budget from a cursor whose remaining protocol is `rounds` is
at most the leaf bound plus, for each remaining round, the message and challenge bounds. -/
theorem programFrom_budget_le_rounds (stages : MeasuredStages F ω) {stmt : S}
    {rootBound messageBound challengeBound leafBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt rootBound messageBound challengeBound leafBound) :
    (rounds : List Round) → (sp : Cursor.Spine s (protocol rounds)) →
    (history : PartialTranscriptAt oracleSig sp) → (tr : Transcript oracleSig (protocol rounds)) →
    (stages.programFrom stmt sp history tr).budget ≤
      leafBound + rounds.length • (messageBound + challengeBound)
  | [], sp, history, _ => le_of_le_of_eq (h.leaf sp history) (by simp)
  | round :: rounds, sp, history, ⟨message, ⟨challenge, tr⟩⟩ => by
    change (stages.programFrom stmt _ (PartialTranscriptAt.snoc oracleSig _
        (PartialTranscriptAt.snoc oracleSig sp history message) challenge) tr).budget +
      (stages.step stmt _ (PartialTranscriptAt.snoc oracleSig sp history message)).budget +
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
    {Wout : S → Transcript oracleSig (protocol rounds) → Type}
    {valid : (stmt : S) → (tr : Transcript oracleSig (protocol rounds)) → Wout stmt tr → Prop}
    {G : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn valid}
    (stages : MeasuredStages G ω) {stmt : S}
    {rootBound messageBound challengeBound leafBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt rootBound messageBound challengeBound leafBound)
    (tr : Transcript oracleSig (protocol rounds)) :
    (stages.programAlong stmt tr).budget ≤
      leafBound + rounds.length • (messageBound + challengeBound) + rootBound :=
  add_le_add (programFrom_budget_le_rounds stages h rounds (.root _) ⟨⟩ tr) h.root

/-- Zero root and leaf budgets recover the bound that counts only the two stages per round. -/
theorem programAlong_budget_le_protocol_zero {rounds : List Round}
    {Wout : S → Transcript oracleSig (protocol rounds) → Type}
    {valid : (stmt : S) → (tr : Transcript oracleSig (protocol rounds)) → Wout stmt tr → Prop}
    {G : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn valid}
    (stages : MeasuredStages G ω) {stmt : S} {messageBound challengeBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt 0 messageBound challengeBound 0)
    (tr : Transcript oracleSig (protocol rounds)) :
    (stages.programAlong stmt tr).budget ≤ rounds.length • (messageBound + challengeBound) := by
  simpa only [zero_add, add_zero] using programAlong_budget_le_protocol stages h tr

/-- Every execution path of the composed program along a transcript of `protocol rounds` costs at
most the protocol budget. -/
theorem programAlong_costAtMost_protocol {rounds : List Round}
    {Wout : S → Transcript oracleSig (protocol rounds) → Type}
    {valid : (stmt : S) → (tr : Transcript oracleSig (protocol rounds)) → Wout stmt tr → Prop}
    {G : KnowledgeStateFunction.{uS, 0, 0, 0, 1, 0} oracleSig (protocol rounds)
      S Wout Win admissible relIn valid}
    (stages : MeasuredStages G ω) {stmt : S}
    {rootBound messageBound challengeBound leafBound : ω}
    (h : stages.ProtocolBudgetAtMost stmt rootBound messageBound challengeBound leafBound)
    (tr : Transcript oracleSig (protocol rounds)) :
    (stages.programAlong stmt tr).program.CostAtMost
      (leafBound + rounds.length • (messageBound + challengeBound) + rootBound) :=
  (stages.programAlong stmt tr).costAtMost.mono (programAlong_budget_le_protocol stages h tr)

end Interaction.KnowledgeStateFunction.MeasuredStages

namespace Interaction.MeasuredKnowledgeStateFunction
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec Oracle
open Interaction.StateRestoration

section ReadOut

variable {Kind : Type} [Finite Kind] {s : OracleProtocol} {S : Type uS} {W : Type}
  {Win : S → Type} {Wout : S → Transcript oracleSig s → Type} {admissible : S → Prop}
  {relIn : (stmt : S) → Win stmt → Prop}
  {validOutput : (stmt : S) → (tr : Transcript oracleSig s) → Wout stmt tr → Prop}

/-- The full extraction program at a statement and completed transcript: a program realizing the
conversion `readOut` of the adversary's witness, then the stage programs along the transcript.
Its budget is the conversion budget plus the stage budgets (`extractionProgram_budget`). -/
def extractionProgram
    (M : MeasuredKnowledgeStateFunction Kind oracleSig s S Wout Win admissible relIn validOutput)
    {readOut : (stmt : S) → (tr : Transcript oracleSig s) → W → Wout stmt tr}
    (readOutProgram : ∀ stmt tr, BudgetedProgram (readOut stmt tr) (Kind → ℕ))
    (stmt : S) (tr : Transcript oracleSig s) :
    BudgetedProgram (M.extractAlong stmt tr ∘ readOut stmt tr) (Kind → ℕ) :=
  (M.stages.programAlong stmt tr).comp (readOutProgram stmt tr)

/-- The full extraction program returns the extracted input witness at the converted witness. -/
theorem run_extractionProgram
    (M : MeasuredKnowledgeStateFunction Kind oracleSig s S Wout Win admissible relIn validOutput)
    {readOut : (stmt : S) → (tr : Transcript oracleSig s) → W → Wout stmt tr}
    (readOutProgram : ∀ stmt tr, BudgetedProgram (readOut stmt tr) (Kind → ℕ))
    (stmt : S) (tr : Transcript oracleSig s) (w : W) :
    (M.extractionProgram readOutProgram stmt tr).program.run w =
      M.extractAlong stmt tr (readOut stmt tr w) :=
  ((M.extractionProgram readOutProgram stmt tr).realizes w).symm

/-- The full extraction budget is the conversion budget plus the stage budgets. -/
theorem extractionProgram_budget
    (M : MeasuredKnowledgeStateFunction Kind oracleSig s S Wout Win admissible relIn validOutput)
    {readOut : (stmt : S) → (tr : Transcript oracleSig s) → W → Wout stmt tr}
    (readOutProgram : ∀ stmt tr, BudgetedProgram (readOut stmt tr) (Kind → ℕ))
    (stmt : S) (tr : Transcript oracleSig s) :
    (M.extractionProgram readOutProgram stmt tr).budget =
      (readOutProgram stmt tr).budget + (M.stages.programAlong stmt tr).budget := rfl

end ReadOut

variable {rounds : List Round} {I S Salt W Kind : Type} [Finite Kind]
  {A : I → Type} {T : Path (protocol rounds) → Type}
  {J : Path (protocol rounds) → Type} {B : (p : Path (protocol rounds)) → J p → Type}
    {Win : S × (∀ i, A i) → Type}
  {inputs : OracleFamily.{0, 0, wI} I A}
  {outputs : (p : Path (protocol rounds)) → OracleFamily.{0, 0, wJ} (J p) (B p)}
  {admissible : S × (∀ i, A i) → Prop} {relIn : (stmt : S × (∀ i, A i)) → Win stmt → Prop}
  {Wout : (S × (∀ i, A i)) → Transcript oracleSig (protocol rounds) → Type}
  {validOutput : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) →
    Wout stmt tr → Prop}

/-- A measured knowledge state function with per-round errors and per-node-kind stage bounds. The
closed verification game has knowledge error at most `Q * max_j errors j + ∑ j, errors j`, and
for every admissible input and transcript the composed stage program returns the extracted input
witness and costs at most the protocol budget on every execution path.

The measured budget begins after `readOut`. The failure event applies `M.extractAlong` to
`readOut stmt tr w`, and the realization equality lets the event use the stage program
`M.stages.programAlong stmt tr` on that converted witness. `readOut` is an arbitrary function of
the input, the completed transcript and the adversary's witness, and this theorem does not charge
it. The budget also assumes that the statement, the transcript and the stage programs are
supplied. The bounds `rootBound`, `messageBound`, `challengeBound` and `leafBound` are per
statement, so the theorem gives a uniform size-based budget only if the caller bounds them
separately. `stateRestoration_oracle_knowledge_soundness_nonuniform_withReadOut` also charges a
program realizing `readOut`. -/
theorem stateRestoration_oracle_knowledge_soundness_nonuniform
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : Transcript oracleSig (protocol rounds)) →
      OracleVerifier.Output T B tr.path → W → Prop)
    (M : MeasuredKnowledgeStateFunction Kind oracleSig (protocol rounds) (S × (∀ i, A i)) Wout
      Win admissible relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (outputLaw : ∀ stmt tr claim w, closedVerdict V stmt tr = some claim →
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

/-- The full extractor contract. A budgeted program realizes `readOut` at every statement and
transcript, and `extractionProgram` runs it before the stage programs. The failure event runs
this composite program on the adversary's witness, so the knowledge error
`Q * max_j errors j + ∑ j, errors j` bounds failure of the program whose cost is bounded. For every
admissible input and transcript the composite program returns the extracted input witness at the
converted witness, and every execution path costs at most the conversion bound plus the protocol
budget. All bounds are per statement; the statement, the transcript and the programs are
supplied. -/
theorem stateRestoration_oracle_knowledge_soundness_nonuniform_withReadOut
    [DecidableEq (Key (S × (∀ i, A i)) Salt rounds)]
    (V : OracleVerifier []ₒ (protocol rounds) S T inputs outputs)
    (relOut : S × (∀ i, A i) → (tr : Transcript oracleSig (protocol rounds)) →
      OracleVerifier.Output T B tr.path → W → Prop)
    (M : MeasuredKnowledgeStateFunction Kind oracleSig (protocol rounds) (S × (∀ i, A i)) Wout
      Win admissible relIn validOutput)
    (readOut : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig (protocol rounds)) → W →
      Wout stmt tr)
    (readOutProgram : ∀ stmt tr, BudgetedProgram (readOut stmt tr) (Kind → ℕ))
    (outputLaw : ∀ stmt tr claim w, closedVerdict V stmt tr = some claim →
      relOut stmt tr claim w → validOutput stmt tr (readOut stmt tr w))
    (errors : RoundErrors rounds)
    (bounded : M.LocallyBoundedOfNodes (uniformDraw rounds) (roundEps errors))
    (readOutBound rootBound messageBound challengeBound leafBound : S × (∀ i, A i) → Kind → ℕ)
    (readOutBudget : ∀ z, admissible z → ∀ tr, (readOutProgram z tr).budget ≤ readOutBound z)
    (budget : ∀ z, admissible z → M.stages.ProtocolBudgetAtMost z (rootBound z)
      (messageBound z) (challengeBound z) (leafBound z))
    (adversary : OracleComp (oracleSpec (S × (∀ i, A i)) Salt rounds)
      ((S × (∀ i, A i)) × Messages Salt rounds × W))
    (Q : ℕ) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (closedVerificationGame V adversary)).run' ∅}[
      admissible result.1 ∧
      (∃ claim, result.2.2.1 = some claim ∧ relOut result.1 result.2.1 claim result.2.2.2) ∧
      ¬ relIn result.1
        ((M.extractionProgram readOutProgram result.1 result.2.1).program.run result.2.2.2)] ≤
      Q * Finset.univ.sup errors + ∑ j, errors j ∧
    ∀ z, admissible z → ∀ tr,
      (∀ w, (M.extractionProgram readOutProgram z tr).program.run w =
        M.extractAlong z tr (readOut z tr w)) ∧
      (M.extractionProgram readOutProgram z tr).program.CostAtMost
        (readOutBound z +
          (leafBound z + rounds.length • (messageBound z + challengeBound z) + rootBound z)) := by
  obtain ⟨bound, laws⟩ := stateRestoration_oracle_knowledge_soundness_nonuniform V relOut M
    readOut outputLaw errors bounded rootBound messageBound challengeBound leafBound budget
    adversary Q queryBound
  refine ⟨?_, fun z hz tr => ⟨run_extractionProgram M readOutProgram z tr, ?_⟩⟩
  · simpa only [run_extractionProgram] using bound
  · exact MeasuredProgram.CostAtMost.comp (laws z hz tr).2
      ((readOutProgram z tr).costAtMost.mono (readOutBudget z hz tr))

end Interaction.MeasuredKnowledgeStateFunction

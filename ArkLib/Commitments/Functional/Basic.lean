/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Tobias Rothmann
-/

import VCVio
import ArkLib.OracleReduction.Security.Basic
import ArkLib.Data.Fin.Fold

/-!
  # Functional Commitment Schemes (with Oracle Openings)

  A commitment scheme, relative to an oracle `oSpec : OracleSpec ι`, and for a given
  function `oracle : Data → Query → Response` transforming underlying data `Data` into an
  oracle `Query → Response`, is a tuple of three operations:

  - KeyGen, which is a function `keygen : OracleComp oSpec (ComKey × VerifKey)` that samples keys
    for the committer and the verifier.
  - Commit, which is a function `commit : Data → OracleComp oSpec (Commitment × Decommitment)`.
    The `Decommitment` value captures any auxiliary information (e.g. blinding randomness) produced
    during the commit phase that is needed to open the commitment later.
  - Open, which is (roughly) an interactive proof (relative to `oSpec`) for the following relation:
    - `StmtIn := (cm : Commitment) × (x : Query) × (y : Response)`
    - `WitIn := Data × Decommitment`
    - `rel : StmtIn → WitIn → Prop :=
        fun ⟨cm, x, y⟩ ⟨d, dc⟩ ↦ commit d ⇝ (cm, dc) ∧ oracle d x = y`

  For deterministic schemes (e.g. KZG), `Decommitment` is `Unit`.
  For randomized schemes (e.g. Pedersen, RO-based), `Decommitment` carries the blinding factor.

  There is one inaccuracy about the relation above: `commit` is an oracle computation, and not a
  deterministic function; hence the relation is not literally true as described. This is why
  security definitions for commitment schemes have to be stated differently than those for IOPs.

  ## References

  * [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z., *On the Fiat-Shamir Security of
      Succinct Arguments from Functional Commitments*][CGKY25]
-/

namespace Commitment

open OracleSpec OracleComp SubSpec ProtocolSpec

variable {ι : Type} (oSpec : OracleSpec ι) (Data Commitment Decommitment ComKey VerifKey : Type)

/-- Key generation for a commitment scheme, producing a committer key and a verifier key. -/
structure KeyGen where
  keygen : OracleComp oSpec (ComKey × VerifKey)

/-- The commitment algorithm, parameterized by the committer key and the data to commit. -/
structure Commit where
  commit : ComKey → Data → OracleComp oSpec (Commitment × Decommitment)

variable [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n)

/-- The opening protocol used to prove a claimed oracle response for committed data. -/
structure Opening where
  opening : (ComKey × VerifKey) →
    Proof oSpec (Commitment × (q : O.Query) × O.Response q) (Data × Decommitment) pSpec

/-- A commitment scheme with key generation, commitment, and opening algorithms. -/
structure Scheme extends
    KeyGen oSpec ComKey VerifKey,
    Commit oSpec Data Commitment Decommitment ComKey,
    Opening oSpec Data Commitment Decommitment ComKey VerifKey pSpec

section Security

noncomputable section

open scoped NNReal ENNReal

variable [DecidableEq ι]
  {oSpec : OracleSpec ι} {Data : Type} [O : OracleInterface Data]
  {Commitment Decommitment ComKey VerifKey : Type} [oSpec.Fintype] {n : ℕ}
  {pSpec : ProtocolSpec n} [[pSpec.Challenge]ₒ.Inhabited] [[pSpec.Challenge]ₒ.Fintype]
  [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A commitment scheme satisfies **correctness** with error `correctnessError` if for all
  `data : Data` and `query : O.Query`, the probability of accepting upon executing the commitment
  and opening procedures honestly is at least `1 - correctnessError`. Any randomness used by the
  committer is sampled inside the `OracleComp` in `scheme.commit`.
-/
def correctness (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (correctnessError : ℝ≥0) : Prop :=
  ∀ data : Data,
  ∀ query : O.Query,
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl challengeQueryImpl
  Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ ↦
    (stmtOut, witOut) ∈ acceptRejectRel ∧ prvStmtOut = stmtOut
  | OptionT.mk do
      (simulateQ pImpl (do
        let (ck, vk) ← liftComp scheme.keygen _
        let (cm, decomm) ← liftComp (scheme.commit ck data) _
        let proof := scheme.opening (ck, vk)
        let stmt : Commitment × (q : O.Query) × O.Response q :=
          (cm, ⟨query, O.answer data query⟩)
        let wit : Data × Decommitment := (data, decomm)
        (proof.run stmt wit).run
      )).run' (← init)] ≥ 1 - correctnessError

/-- A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
-/
def perfectCorrectness
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec) : Prop :=
  correctness init impl scheme 0

/-- An adversary in the (evaluation) binding game returns a commitment `cm`, a query `q`, two
  purported responses `r₁, r₂` to the query, and an auxiliary private state (to be passed to the
  malicious prover in the opening procedure). -/
structure BindingAdversary (oSpec : OracleSpec ι) (Data Commitment AuxState : Type)
  [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n) (ComKey : Type)
where
  claim : (ComKey →
    OracleComp oSpec
      (Commitment × (q : O.Query) × O.Response q × O.Response q × AuxState × AuxState))
  prover : (ComKey →
    Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec)

/-- Evaluation binding condition for an adversary to win the binding game. -/
abbrev bindingCondition :
    ((query : O.Query) × O.Response query × O.Response query × Bool × Bool) → Prop :=
  fun ⟨_, resp₁, resp₂, accept₁, accept₂⟩ ↦
    resp₁ ≠ resp₂ ∧ accept₁ ∧ accept₂

/-- The evaluation-binding game for a specific adversary. -/
abbrev bindingGame (AuxState : Type)
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey) :
    OptionT ProbComp ((query : O.Query) × O.Response query × O.Response query × Bool × Bool) :=
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl (challengeQueryImpl (pSpec := pSpec))
  OptionT.mk do
    let s ← init
    let (ck, vk) ← (simulateQ impl scheme.keygen).run' s
    (simulateQ pImpl <| (show OracleComp _ _ from do
      let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim ck) _
      let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
      let accept₁ := (← (reduction.verdict
        (cm, (⟨query, resp₁⟩ : (q : O.Query) × O.Response q)) st₁).run).getD false
      let accept₂ := (← (reduction.verdict
        (cm, (⟨query, resp₂⟩ : (q : O.Query) × O.Response q)) st₂).run).getD false
      pure (some ((⟨query, resp₁, resp₂, accept₁, accept₂⟩ :
        (query : O.Query) × O.Response query × O.Response query × Bool × Bool)))
    )).run' s

/-- The probability of breaking evaluation binding for a specific adversary. -/
def bindingExperiment (AuxState : Type)
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey) : ℝ≥0∞ :=
  Pr[bindingCondition (Data := Data) | bindingGame init impl AuxState scheme adversary]

/-- A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all
    adversaries that output a commitment `cm`, query `q`, two responses `resp₁, resp₂`, and
    auxiliary state `st`, and for all malicious provers in the opening procedure taking in `st`, the
    probability that:

  1. The responses are different (`resp₁ ≠ resp₂`);
  2. The verifier accepts both openings

  is at most `bindingError`.

  Informally, evaluation binding says that it's computationally infeasible to open a commitment to
  two different responses for the same query. -/
def binding (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (bindingError : ℝ≥0) : Prop :=
  ∀ AuxState : Type,
  ∀ adversary : BindingAdversary oSpec Data Commitment AuxState pSpec ComKey,
    bindingExperiment init impl AuxState scheme adversary ≤ bindingError

/-- A **straightline extractor** for a commitment scheme takes in the commitment, the log of queries
    made during the commitment phase, and returns the underlying data for the commitment. -/
abbrev StraightlineExtractor (oSpec : OracleSpec ι) (Data Commitment : Type) :=
  Commitment → QueryLog oSpec → Data

/-- An adversary in the extractability game is an oracle computation that returns a commitment, a
  query, a response value, and some auxiliary state (to be used in the opening procedure). -/
abbrev ExtractabilityAdversary (oSpec : OracleSpec ι) (Data Commitment AuxState : Type)
    [O : OracleInterface Data] :=
  OracleComp oSpec (Commitment × (q : O.Query) × O.Response q × AuxState)

set_option linter.unusedVariables false

/-- A commitment scheme satisfies **extractability** with error `extractabilityError` if there
    exists a straightline extractor `E` such that for all adversaries that output a commitment `cm`,
    a query `q`, a response `r`, and some auxiliary state `st`, and for all malicious provers in the
    opening procedure that takes in `st`, the probability that:

  1. The verifier accepts in the opening procedure given `cm, q, r`
  2. The extracted data `d` is inconsistent with the claimed response (i.e., `O.answer d q ≠ r`)

  is at most `extractabilityError`.

  Informally, extractability says that if an adversary can convince the verifier to accept an
  opening, then the extractor must be able to recover some underlying data that is consistent with
  the evaluation query. -/
def extractability (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey pSpec)
    (extractabilityError : ℝ≥0) : Prop :=
  ∃ extractor : StraightlineExtractor oSpec Data Commitment,
  ∀ AuxState : Type,
  ∀ adversary : ExtractabilityAdversary oSpec Data Commitment AuxState,
  ∀ prover : Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec,
    False
    -- [ fun ⟨b, d, q, r⟩ ↦ b ∧ O.answer d q = r | do
    --     let result ← liftM (simulate loggingOracle ∅ adversary)
    --     let ⟨⟨cm, query, response, st⟩, queryLog⟩ := result
    --     let proof : Proof pSpec oSpec (Commitment × O.Query × O.Response) AuxState :=
    --       ⟨prover, scheme.opening.verifier⟩
    --     let ⟨accept, _⟩ ← proof.run ⟨cm, query, response⟩ st
    --     letI data := extractor cm queryLog
    --     return (accept, data, query, response)] ≤ extractabilityError

set_option linter.unusedVariables true

-- TODO: version where the query is chosen according to some public coin?

-- TODO: multi-instance versions?

/-- An adversary in the function binding game returns a commitment `cm`, and for each index in
  `Fin L`, a query, a claimed response to the query, and an auxiliary private state (to be passed
  to the malicious prover in the opening procedure). -/
structure FunctionBindingAdversary (oSpec : OracleSpec ι) (Data Commitment AuxState : Type)
  [O : OracleInterface Data] (L : ℕ) {n : ℕ} (pSpec : ProtocolSpec n) (ComKey : Type)
where
  claim : (ComKey →
    OracleComp oSpec (Commitment ×
      (queryOf : Fin L → O.Query) ×
      ((i : Fin L) → O.Response (queryOf i)) ×
      (Fin L → AuxState)))
  prover : (ComKey →
    Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec)

/-- Function binding condition for an adversary to win the function-binding game. -/
abbrev functionBindingCondition {L : ℕ} :
    ((queryOf : Fin L → O.Query) ×
      ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)) → Prop :=
  fun ⟨queryOf, responseOf, acceptedOf⟩ ↦
    let S : Finset (Fin L) := Finset.univ
    (∀ i ∈ S, acceptedOf i = true)
    ∧ (¬ ∃ (d : Data), ∀ i ∈ S, O.answer d (queryOf i) = responseOf i)

/-- The function-binding game for a specific adversary. -/
abbrev functionBindingGame {L : ℕ} (hn : n = 1)
    (AuxState : Type)
    [∀ i, VCVCompatible ((hn ▸ pSpec).Challenge i)]
    [∀ i, SampleableType ((hn ▸ pSpec).Challenge i)]
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey (hn ▸ pSpec))
    (adversary :
      FunctionBindingAdversary oSpec Data Commitment AuxState L (hn ▸ pSpec)
        ComKey) :
    OptionT ProbComp ((queryOf : Fin L → O.Query) ×
      ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)) :=
    let pImpl : QueryImpl (oSpec + [(hn ▸ pSpec).Challenge]ₒ) (StateT σ ProbComp) :=
      QueryImpl.addLift impl (challengeQueryImpl (pSpec := hn ▸ pSpec))
    OptionT.mk do
      let s ← init
      let (ck, vk) ← (simulateQ impl scheme.keygen).run' s
      (simulateQ pImpl <| (show OracleComp _ _ from do
        let ⟨cm, queryOf, responseOf, stateOf⟩ ← liftComp (adversary.claim ck) _
        let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
        let (accepts : Option (Fin L → Bool)) ← reduction.allVerdicts
          (fun i ↦
            (cm, (⟨queryOf i, responseOf i⟩ : (q : O.Query) × O.Response q)))
          stateOf
        pure (accepts.map fun accepts ↦ (⟨queryOf, responseOf, accepts⟩ :
          (queryOf : Fin L → O.Query) ×
            ((i : Fin L) → O.Response (queryOf i)) × (Fin L → Bool)))
      )).run' s

/-- The probability of breaking function binding for a specific adversary. -/
def functionBindingExperiment {L : ℕ} (hn : n = 1)
    (AuxState : Type)
    [∀ i, VCVCompatible ((hn ▸ pSpec).Challenge i)]
    [∀ i, SampleableType ((hn ▸ pSpec).Challenge i)]
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey (hn ▸ pSpec))
    (adversary :
      FunctionBindingAdversary oSpec Data Commitment AuxState L (hn ▸ pSpec)
        ComKey) : ℝ≥0∞ :=
    Pr[functionBindingCondition (Data := Data) |
      functionBindingGame init impl hn AuxState scheme adversary]

/-- A commitment scheme satisfies **function binding** with error `functionBindingError` if for all
adversaries that output a commitment `cm`, and a vector of length `L` of queries `q_i`, claimed
responses `r_i` to the queries, and auxiliary private states `st_i` (to be passed to the adversary
prover in the opening procedure), and for all malicious provers in the opening procedure taking in
`st_i`, the probability that:

  1. The verifier accepts all `r_i` to the respective `q_i` in the opening procedure for `cm`
  2. There exists no data `d` that is consistent with the claimed responses
    (i.e. for all data `d`, for some `i`, `O.answer d q_i ≠ r_i`)

  is at most `functionBindingError`.

  Informally, function binding says it's computationally infeasible to convince the
  verifier to accept responses for which no consistent (source) data exists.

  Note: This is an adaptation of the function binding property introduced in [CGKY25]. -/
def functionBinding {L : ℕ} (hn : n = 1)
    [∀ i, VCVCompatible ((hn ▸ pSpec).Challenge i)]
    [∀ i, SampleableType ((hn ▸ pSpec).Challenge i)]
    (scheme : Scheme oSpec Data Commitment Decommitment ComKey VerifKey (hn ▸ pSpec))
    (functionBindingError : ℝ≥0) : Prop :=
  ∀ AuxState : Type,
  ∀ adversary : FunctionBindingAdversary oSpec Data Commitment AuxState L (hn ▸ pSpec) ComKey,
    functionBindingExperiment init impl hn AuxState scheme adversary ≤
      functionBindingError

end

end Security

end Commitment

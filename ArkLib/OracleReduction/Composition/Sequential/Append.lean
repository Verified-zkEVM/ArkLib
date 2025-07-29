/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.ProtocolSpec
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Sequential Composition of Two (Oracle) Reductions

  This file gives the definition & properties of the sequential composition of two (oracle)
  reductions. For composition to be valid, we need that the output context (statement + oracle
  statement + witness) for the first (oracle) reduction is the same as the input context for the
  second (oracle) reduction.

  We have refactored the composition logic for `ProtocolSpec` and its associated structures into
  `ProtocolSpec.lean`, and we will use the definitions from there.

  We will prove that the composition of reductions preserve all completeness & soundness properties
  of the reductions being composed (with extra conditions on the extractor).
-/

open OracleComp OracleSpec SubSpec

section find_home

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

@[simp]
lemma evalDist_cast (h : α = β) [spec.FiniteRange] :
    evalDist (cast (congrArg (OracleComp spec) h) oa) =
      cast (congrArg (PMF ∘ Option) h) (evalDist oa) := by
  induction h; rfl

end find_home

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

section Instances

/-- If two protocols have sampleable challenges, then their concatenation also has sampleable
  challenges. -/
instance [h₁ : ∀ i, SelectableType (pSpec₁.Challenge i)]
    [h₂ : ∀ i, SelectableType (pSpec₂.Challenge i)] :
    ∀ i, SelectableType ((pSpec₁ ++ₚ pSpec₂).Challenge i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  by_cases h' : i < m <;> simp [h'] at h ⊢
  · exact h₁ ⟨⟨i, by omega⟩, h⟩
  · exact h₂ ⟨⟨i - m, by omega⟩, h⟩

/-- If two protocols' messages have oracle representations, then their concatenation's messages also
    have oracle representations. -/
instance [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)] :
    ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir, Fin.append, Fin.addCases,
    Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  by_cases h' : i < m <;> simp [h'] at h ⊢
  · exact O₁ ⟨⟨i, by omega⟩, h⟩
  · exact O₂ ⟨⟨i - m, by omega⟩, h⟩

variable [∀ i, SelectableType (pSpec₁.Challenge i)] [∀ i, SelectableType (pSpec₂.Challenge i)]

instance instSubSpecOfProtocolSpecAppendChallenge :
    SubSpec ([pSpec₁.Challenge]ₒ ++ₒ [pSpec₂.Challenge]ₒ) ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => match i with
    | Sum.inl j => by
      simpa [OracleSpec.append, OracleSpec.range, OracleInterface.toOracleSpec, ChallengeIdx.inl,
        instChallengeOracleInterface] using
      query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) j.inl ()
    | Sum.inr j => by
      simpa [OracleSpec.append, OracleSpec.range, OracleInterface.toOracleSpec, ChallengeIdx.inr,
        instChallengeOracleInterface] using
      query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) j.inr ()
  -- evalDist_toFun' := fun i q => by
  --   cases i with
  --   | inl j =>
  --     simp only [eq_mp_eq_cast, id_eq]
  --     have : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.range j.inl =
  --       ([pSpec₁.Challenge]ₒ ++ₒ [pSpec₂.Challenge]ₒ).range (Sum.inl j) := by
  --       simp [OracleSpec.append, ChallengeIdx.inl, instChallengeOracleInterface]
  --     rw [evalDist_cast _ this, evalDist_query, evalDist_query]
  --     simp [OracleSpec.append, ChallengeIdx.inl, instChallengeOracleInterface]
  --     refine cast_eq_iff_heq.mpr ((PMF.heq_iff (by simp [this])).mpr ?_)
  --     intro x
  --     simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fin.append_left]
  --     refine tsum_cast (by simp) (fun a => ?_)
  --     congr <;> try { simp only [Fin.append_left] } <;> symm <;> simp only [cast_heq]
  --   | inr j =>
  --     simp only [eq_mp_eq_cast, id_eq]
  --     have : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.range j.inr =
  --       ([pSpec₁.Challenge]ₒ ++ₒ [pSpec₂.Challenge]ₒ).range (Sum.inr j) := by
  --       simp [OracleSpec.append, ChallengeIdx.inr, instChallengeOracleInterface]
  --     rw [evalDist_cast _ this, evalDist_query, evalDist_query]
  --     simp [OracleSpec.append, ChallengeIdx.inr, instChallengeOracleInterface]
  --     refine cast_eq_iff_heq.mpr ((PMF.heq_iff (by simp [this])).mpr ?_)
  --     intro x
  --     simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fin.append_right]
  --     refine tsum_cast (by simp) (fun a => ?_)
  --     congr <;> try { simp only [Fin.append_right] } <;> symm <;> simp only [cast_heq]

instance : SubSpec [pSpec₁.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inl i) t)

instance : SubSpec [pSpec₂.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inr i) t)

end Instances

/--
Appending two provers corresponding to two reductions, where the output statement & witness type for
the first prover is equal to the input statement & witness type for the second prover. We also
require a verifier for the first protocol in order to derive the intermediate statement for the
second prover.

This is defined by combining the two provers' private states and functions, with the exception that
the last private state of the first prover is "merged" into the first private state of the second
prover (via outputting the new statement and witness, and then inputting these into the second
prover). -/
def Prover.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where

  /- The combined prover's states are the concatenation of the first prover's states, except the
  last one, and the second prover's states. -/
  PrvState := Fin.append (m := m) (Fin.init P₁.PrvState) P₂.PrvState

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun ctxIn => by
    by_cases h : m > 0
    · simp [Fin.append, Fin.addCases, Fin.init, Fin.castLT, h]
      exact P₁.input ctxIn
    · simp [Fin.append, Fin.addCases, h, Fin.subNat]
      exact (
        letI state := P₁.input ctxIn
        haveI : 0 = Fin.last m := by aesop
        haveI state : P₁.PrvState (Fin.last m) := by simpa [this] using state
        P₂.input (P₁.output state))

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m - 1`, then it sends the message & updates the state as the first prover
  - if `i = m - 1`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. -/
  sendMessage := fun ⟨⟨i, hLt⟩, h⟩ state => by
    by_cases hi : i < m
    · dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
      by_cases hi' : i + 1 < m
      · simp [hi, hi'] at h state ⊢
        exact P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
      · haveI : i + 1 = m := by omega
        simp [hi, this] at h state ⊢
        exact (do
          let ⟨msg, state⟩ ← P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
          haveI state : P₁.PrvState (Fin.last m) := by
            simpa only [Fin.last, Fin.succ_mk, this] using state
          return ⟨msg, P₂.input (P₁.output state)⟩)
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi, this, Fin.cast, Fin.castLT, Fin.succ,
        Fin.castSucc] at h state ⊢
      exact (do
        let ⟨msg, newState⟩ ← P₂.sendMessage ⟨⟨i - m, by omega⟩, h⟩ state
        haveI newState : P₂.PrvState ⟨i + 1 - m, by omega⟩ := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa only [this, Fin.succ] using newState
        return ⟨msg, newState⟩)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨⟨i, hLt⟩, h⟩ state chal => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state chal ⊢
      by_cases hi' : i + 1 < m
      · simp [hi']
        exact P₁.receiveChallenge ⟨⟨i, hi⟩, h⟩ state chal
      · haveI : i + 1 = m := by omega
        simp [this]
        exact (
          letI newState := P₁.receiveChallenge ⟨⟨i, hi⟩, h⟩ state chal
          haveI newState : P₁.PrvState (Fin.last m) := by
            simpa [Fin.last, this] using newState
          P₂.input (P₁.output newState))
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi, this, Fin.cast, Fin.castLT, Fin.succ,
        Fin.castSucc] at h state chal ⊢
      exact (
        letI newState := P₂.receiveChallenge ⟨⟨i - m, by omega⟩, h⟩ state chal
        haveI newState := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa [Fin.succ, this] using newState
        newState)

  /- The combined prover's output function is simply the second prover's output function. -/
  output := fun state => by
    simp [Fin.append, Fin.addCases, Fin.last] at state
    exact P₂.output state

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
      Verifier oSpec Stmt₁ Stmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Composition of reductions boils down to composing the provers and verifiers. -/
def Reduction.append (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Reduction oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

open Function Embedding in
def OracleVerifier.append (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt challenges => by
    -- First, invoke the first oracle verifier, handling queries as necessary
    have := V₁.verify stmt (fun chal => sorry)
    simp at this
    -- Then, invoke the second oracle verifier, handling queries as necessary
    -- Return the final output statement
    sorry

  -- Need to provide an embedding `ιₛ₃ ↪ ιₛ₁ ⊕ (pSpec₁ ++ₚ pSpec₂).MessageIdx`
  embed :=
    -- `ιₛ₃ ↪ ιₛ₂ ⊕ pSpec₂.MessageIdx`
    .trans V₂.embed <|
    -- `ιₛ₂ ⊕ pSpec₂.MessageIdx ↪ (ιₛ₁ ⊕ pSpec₁.MessageIdx) ⊕ pSpec₂.MessageIdx`
    .trans (.sumMap V₁.embed (.refl _)) <|
    -- re-associate the sum `_ ↪ ιₛ₁ ⊕ (pSpec₁.MessageIdx ⊕ pSpec₂.MessageIdx)`
    .trans (Equiv.sumAssoc _ _ _).toEmbedding <|
    -- use the equivalence `pSpec₁.MessageIdx ⊕ pSpec₂.MessageIdx ≃ (pSpec₁ ++ₚ pSpec₂).MessageIdx`
    .sumMap (.refl _) MessageIdx.sumEquiv.toEmbedding

  hEq := fun i => by
    rcases h : V₂.embed i with j | j
    · rcases h' : V₁.embed j with k | k
      · have h1 := V₁.hEq j
        have h2 := V₂.hEq i
        simp [h, h'] at h1 h2 ⊢
        exact h2.trans h1
      · have h1 := V₁.hEq j
        have h2 := V₂.hEq i
        simp [h, h', MessageIdx.inl] at h1 h2 ⊢
        exact h2.trans h1
    · have := V₂.hEq i
      simp [h] at this ⊢
      simp [this, MessageIdx.inr]

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

namespace Verifier

/-! Sequential composition of extractors and state functions

These have the following form: they needs to know the first verifier, and derive the intermediate
statement from running the first verifier on the first statement.

This leads to complications: the verifier is assumed to be a general `OracleComp oSpec`, and so
we also need to have the extractors and state functions to be similarly `OracleComp`s.

The alternative is to consider a fully deterministic (and non-failing) verifier. The non-failing
part is somewhat problematic as we write our verifiers to be able to fail (i.e. implicit failing
via `guard` statements).

As such, the definitions below are temporary until further development. -/

/-- The sequential composition of two straightline extractors.

TODO: state a monotone condition on the extractor, namely that if extraction succeeds on a given
query log, then it also succeeds on any extension of that query log -/
def Extractor.Straightline.append (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) :
      Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) :=
  fun stmt₁ wit₃ transcript proveQueryLog verifyQueryLog => do
    let stmt₂ ← V₁.verify stmt₁ transcript.fst
    let wit₂ ← E₂ stmt₂ wit₃ transcript.snd proveQueryLog verifyQueryLog
    let wit₁ ← E₁ stmt₁ wit₂ transcript.fst proveQueryLog verifyQueryLog
    return wit₁

/-- The round-by-round extractor for the sequential composition of two (oracle) reductions -/
def Extractor.RoundByRound.append
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂) :
      Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂)
        (Fin.append (m := m + 1) WitMid₁ (Fin.init WitMid₂) ∘ Fin.cast (by omega)) where
  eqIn := by
    simp [Fin.append, Fin.addCases, Fin.castLT]
    exact E₁.eqIn
  extractMid := fun idx stmt₁ tr h => by
    simp at h ⊢
    -- do casing
    sorry
  extractOut := fun stmt₁ tr wit₃ => by
    simp [Fin.cast]
    sorry

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

example {a b : ℕ} (h : a < b) : min b a = a := by exact min_eq_right_of_lt h

/-- The sequential composition of two state functions. -/
def StateFunction.append
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    -- Assume the first verifier is deterministic for now
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) :
      (V₁.append V₂).StateFunction init impl lang₁ lang₃ where
  toFun := fun roundIdx stmt₁ transcript =>
    if h : roundIdx.val ≤ m then
    -- If the round index falls in the first protocol, then we simply invokes the first state fn
      S₁ ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst)
    else
    -- If the round index falls in the second protocol, then we returns the conjunction of
    -- the first state fn on the first protocol's transcript, and the second state fn on the
    -- remaining transcript.
      S₁ ⟨m, by omega⟩ stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst) ∧
      S₂ ⟨roundIdx - m, by omega⟩ (verify stmt₁
        (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst))
        (by simpa [h] using transcript.snd)
  toFun_empty := sorry
  toFun_next := sorry
  toFun_full := sorry

end Verifier

section Execution

variable [∀ i, SelectableType (pSpec₁.Challenge i)] [∀ i, SelectableType (pSpec₂.Challenge i)]

/--
States that running an appended prover `P₁.append P₂` with an initial statement `stmt₁` and
witness `wit₁` behaves as expected: it first runs `P₁` to obtain an intermediate statement
`stmt₂`, witness `wit₂`, and transcript `transcript₁`. Then, it runs `P₂` on `stmt₂` and `wit₂`
to produce the final statement `stmt₃`, witness `wit₃`, and transcript `transcript₂`.
The overall output is `stmt₃`, `wit₃`, and the combined transcript `transcript₁ ++ₜ transcript₂`.
-/
theorem Prover.append_run (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) (stmt : Stmt₁) (wit : Wit₁) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨⟨stmt₂, wit₂⟩, transcript₁⟩ ← liftM (P₁.run stmt wit)
        let ⟨⟨stmt₃, wit₃⟩, transcript₂⟩ ← liftM (P₂.run stmt₂ wit₂)
        -- TODO: should we refactor the prover to take in a running query log?
        return ⟨⟨stmt₃, wit₃⟩, transcript₁ ++ₜ transcript₂⟩) :=
  sorry

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Execution

section Security

open scoped NNReal

section Append

open OracleComp

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SelectableType (pSpec₁.Challenge i)]
    [∀ i, SelectableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

namespace Reduction

/-- If two reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for `R₁` and
    `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
    `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies
    completeness with respect to `rel₁` and `rel₃`.
    The completeness error of the appended reduction is the sum of the individual errors
    (`completenessError₁ + completenessError₂`). -/
theorem completeness_append (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := sorry

/-- If two reductions satisfy perfect completeness with compatible relations, then their
  concatenation also satisfies perfect completeness. -/
theorem perfectCompleteness_append (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  dsimp [perfectCompleteness] at h₁ h₂ ⊢
  convert Reduction.completeness_append R₁ R₂ h₁ h₂
  simp only [add_zero]

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

-- Synthesization issues...
-- So maybe no synthesization but simp is fine? Maybe not...
-- instance [R₁.IsComplete rel₁ rel₂] [R₂.IsComplete rel₂ rel₃] :
--     (R₁.append R₂).IsComplete rel₁ rel₃ := by sorry

end Reduction

namespace Verifier

/-- If two verifiers satisfy soundness with compatible languages and respective soundness errors,
    then their sequential composition also satisfies soundness.
    The soundness error of the appended verifier is the sum of the individual errors. -/
theorem append_soundness (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (langIn₁ : Set Stmt₁) (langOut₁ : Set Stmt₂)
    (langIn₂ : Set Stmt₂) (langOut₂ : Set Stmt₃)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl langIn₁ langOut₁ soundnessError₁)
    (h₂ : V₂.soundness init impl langIn₂ langOut₂ soundnessError₂) :
      (V₁.append V₂).soundness init impl langIn₁ langOut₂ (soundnessError₁ + soundnessError₂) := by
  sorry

/-- If two verifiers satisfy knowledge soundness with compatible relations and respective knowledge
    errors, then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the appended verifier is the sum of the individual errors. -/
theorem append_knowledgeSoundness (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (relIn₁ : Set (Stmt₁ × Wit₁)) (relOut₁ : Set (Stmt₂ × Wit₂))
    (relIn₂ : Set (Stmt₂ × Wit₂)) (relOut₂ : Set (Stmt₃ × Wit₃))
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl relIn₁ relOut₁ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl relIn₂ relOut₂ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl
        relIn₁ relOut₂ (knowledgeError₁ + knowledgeError₂) := by
  sorry

/-- If two verifiers satisfy round-by-round soundness with compatible languages and respective RBR
    soundness errors, then their sequential composition also satisfies round-by-round soundness.
    The RBR soundness error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrSoundness (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (langIn₁ : Set Stmt₁) (langOut₁ : Set Stmt₂)
    (langIn₂ : Set Stmt₂) (langOut₂ : Set Stmt₃)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl langIn₁ langOut₁ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl langIn₂ langOut₂ rbrSoundnessError₂)
    -- Deterministic verifier condition for state function composition (placeholder for now)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify₁ : V₁ = ⟨fun stmt tr => pure (verify₁ stmt tr)⟩) :
      (V₁.append V₂).rbrSoundness init impl langIn₁ langOut₂
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

/-- If two verifiers satisfy round-by-round knowledge soundness with compatible relations and
    respective RBR knowledge errors, then their sequential composition also satisfies
    round-by-round knowledge soundness.
    The RBR knowledge error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrKnowledgeSoundness (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (relIn₁ : Set (Stmt₁ × Wit₁)) (relOut₁ : Set (Stmt₂ × Wit₂))
    (relIn₂ : Set (Stmt₂ × Wit₂)) (relOut₂ : Set (Stmt₃ × Wit₃))
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl relIn₁ relOut₁ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl relIn₂ relOut₂ rbrKnowledgeError₂)
    -- Deterministic verifier condition for state function composition (placeholder for now)
    (verify₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify₁ : V₁ = ⟨fun stmt tr => pure (verify₁ stmt tr)⟩) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl relIn₁ relOut₂
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

end Verifier

end Append

end Security

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.ProtocolSpec
import ArkLib.OracleReduction.Security.Basic

/-!
  # Sequential Composition of Oracle Reductions

  We define the composition of two or more interactive (oracle) reductions, where the output
  statement & witness types for one reduction is the same as the input statement & witness types for
  the next.

  This is defined in two steps:
  1. First, we define the concatenation of two reductions, one from R1 => R2 and the other from R2
     => R3.
  2. Then, we define the general composition of `m + 1` reductions, indexed by `i : Fin (m + 1)`, by
     iterating the concatenation of two reductions.

  For the definitions of composition for `ProtocolSpec` and their associated functions, see
  `ProtocolSpec.lean`.

  We also prove that the composition of reductions preserve all completeness & soundness properties
  of the reductions being composed.
-/

section find_home

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

open OracleComp

@[simp]
lemma evalDist_cast (h : α = β) [spec.FiniteRange] :
    evalDist (cast (congrArg (OracleComp spec) h) oa) =
      cast (congrArg (PMF ∘ Option) h) (evalDist oa) := by
  induction h; rfl

end find_home

open ProtocolSpec

section Cast

-- Dependent casts across `ProtocolSpec`s for the `(Oracle)Prover`, `(Oracle)Verifier`, and
-- `(Oracle)Reduction` types

/-- To cast the verifier, we only need to cast the transcript. -/
def Verifier.cast {m n : ℕ} {pSpec : ProtocolSpec m} {pSpec' : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    (h : m = n) (hSpec : dcast h pSpec = pSpec')
    (V : Verifier pSpec oSpec StmtIn StmtOut) :
    Verifier pSpec' oSpec StmtIn StmtOut where
  verify := fun stmt transcript => V.verify stmt (dcast₂ h.symm (dcast_symm h hSpec) transcript)

@[simp]
def Verifier.cast_id {n} {pSpec : ProtocolSpec n}
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    (V : Verifier pSpec oSpec StmtIn StmtOut) :
      V.cast rfl rfl = V := by
  ext; simp [Verifier.cast]

instance instDepCast₂Verifier {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type} :
    DepCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier pSpec oSpec StmtIn StmtOut) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp

end Cast

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} {ι : Type} [DecidableEq ι]
    {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}

section Instances

/-- If two protocols have sampleable challenges, then their concatenation also has sampleable
  challenges. -/
instance [h₁ : ∀ i, Sampleable (pSpec₁.Challenge i)] [h₂ : ∀ i, Sampleable (pSpec₂.Challenge i)] :
    ∀ i, Sampleable ((pSpec₁ ++ₚ pSpec₂).Challenge i) := fun ⟨⟨i, isLt⟩, h⟩ => by
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

open OracleComp OracleSpec SubSpec

variable [∀ i, Sampleable (pSpec₁.Challenge i)] [∀ i, Sampleable (pSpec₂.Challenge i)]

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
def Prover.append (P₁ : Prover pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (P₂ : Prover pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) :
      Prover (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ where

  /- The combined prover's states are the concatenation of the first prover's states, except the
  last one, and the second prover's states. -/
  PrvState := Fin.append (m := m) (Fin.init P₁.PrvState) P₂.PrvState ∘ Fin.cast (by omega)

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun stmt wit => by
    by_cases h : m > 0
    · simp [Fin.append, Fin.addCases, Fin.init, Fin.castLT, h]
      exact P₁.input stmt wit
    · simp [Fin.append, Fin.addCases, h, Fin.subNat]
      exact (
        letI state := P₁.input stmt wit
        haveI : 0 = Fin.last m := by aesop
        haveI state : P₁.PrvState (Fin.last m) := by simpa [this] using state
        P₂.input.uncurry (P₁.output state))

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m - 1`, then it sends the message & updates the state as the first prover
  - if `i = m - 1`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. It needs to
    provide a `stmt₂` for the second prover, which it derives from running the verifier on the first
    transcript. -/
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
          return ⟨msg, P₂.input.uncurry (P₁.output state)⟩)
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
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
          P₂.input.uncurry (P₁.output newState))
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state chal ⊢
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
def Verifier.append (V₁ : Verifier pSpec₁ oSpec Stmt₁ Stmt₂)
    (V₂ : Verifier pSpec₂ oSpec Stmt₂ Stmt₃) :
      Verifier (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Stmt₃ where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Composition of reductions boils down to composing the provers and verifiers. -/
def Reduction.append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) :
      Reduction (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

open Function Embedding in
def OracleVerifier.append (V₁ : OracleVerifier pSpec₁ oSpec Stmt₁ Stmt₂ OStmt₁ OStmt₂)
    (V₂ : OracleVerifier pSpec₂ oSpec Stmt₂ Stmt₃ OStmt₂ OStmt₃) :
      OracleVerifier (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Stmt₃ OStmt₁ OStmt₃ where
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
    · rcases h' : V₁.embed j with k | k <;>
      simp [h, h', V₁.hEq j, V₂.hEq i, MessageIdx.inl]
    · simp [h, V₂.hEq i, MessageIdx.inr]

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ OStmt₁ OStmt₂)
    (R₂ : OracleReduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ OStmt₂ OStmt₃) :
      OracleReduction (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ OStmt₁ OStmt₃ where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

section GeneralComposition

section Instances

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

/-- If all protocols have sampleable challenges, then the challenges of their sequential
  composition also have sampleable challenges. -/
instance [h : ∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)] :
    ∀ j, Sampleable ((compose m n pSpec).Challenge j) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.compose, Fin.append, Fin.addCases, Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  sorry
  -- by_cases h' : i < m <;> simp [h'] at h ⊢
  -- · exact h₁ ⟨⟨i, by omega⟩, h⟩
  -- · exact h₂ ⟨⟨i - m, by omega⟩, h⟩

/-- If all protocols' messages have oracle interfaces, then the messages of their sequential
  composition also have oracle interfaces. -/
instance [O : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)] :
    ∀ i, OracleInterface ((compose m n pSpec).Message i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.compose, ProtocolSpec.getDir, Fin.append, Fin.addCases,
    Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  sorry
  -- by_cases h' : i < m <;> simp [h'] at h ⊢
  -- · exact O₁ ⟨⟨i, by omega⟩, h⟩
  -- · exact O₂ ⟨⟨i - m, by omega⟩, h⟩

-- open OracleComp OracleSpec SubSpec

-- variable [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]

-- instance : SubSpec (challengeOracle pSpec₁ ++ₒ challengeOracle pSpec₂)
--     (challengeOracle (compose m n pSpec)) := sorry

end Instances

def Prover.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    (P : (i : Fin (m + 1)) → Prover (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ)) :
      Prover (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
        (Wit (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Prover
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ))
    (fun i Pacc => by
      convert Prover.append Pacc (P i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using P 0)

def Verifier.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type)
    (V : (i : Fin (m + 1)) → Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ)) :
      Verifier (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Stmt (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Verifier
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Stmt i.succ))
    (fun i Vacc => by
      refine dcast₂ (self := instDepCast₂Verifier) ?_ ?_ (Vacc.append (V i.succ))
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using V 0)

def Reduction.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    (R : (i : Fin (m + 1)) → Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ)) :
      Reduction (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
        (Wit (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Reduction
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ))
    (fun i Racc => by
      convert Reduction.append Racc (R i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using R 0)

end GeneralComposition

section Execution

open OracleComp OracleSpec SubSpec

variable [∀ i, Sampleable (pSpec₁.Challenge i)] [∀ i, Sampleable (pSpec₂.Challenge i)]
  [oSpec.DecidableEq]

/--
States that running an appended prover `P₁.append P₂` with an initial statement `stmt₁` and
witness `wit₁` behaves as expected: it first runs `P₁` to obtain an intermediate statement
`stmt₂`, witness `wit₂`, and transcript `transcript₁`. Then, it runs `P₂` on `stmt₂` and `wit₂`
to produce the final statement `stmt₃`, witness `wit₃`, and transcript `transcript₂`.
The overall output is `stmt₃`, `wit₃`, and the combined transcript `transcript₁ ++ₜ transcript₂`.
-/
theorem Prover.append_run (P₁ : Prover pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (P₂ : Prover pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) (stmt : Stmt₁) (wit : Wit₁) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨stmt₂, wit₂, transcript₁⟩ ← liftM (P₁.run stmt wit)
        let ⟨stmt₃, wit₃, transcript₂⟩ ← liftM (P₂.run stmt₂ wit₂)
        -- TODO: should we refactor the prover to take in a running query log?
        return ⟨stmt₃, wit₃, transcript₁ ++ₜ transcript₂⟩) :=
  sorry

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Execution

section Security

open scoped NNReal

namespace Reduction

section Append

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} [∀ i, Sampleable (pSpec₁.Challenge i)]
    [∀ i, Sampleable (pSpec₂.Challenge i)] {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {rel₁ : Stmt₁ → Wit₁ → Prop} {rel₂ : Stmt₂ → Wit₂ → Prop} {rel₃ : Stmt₃ → Wit₃ → Prop}
    [oSpec.DecidableEq] [oSpec.FiniteRange]

/-- If two reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for `R₁` and
    `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
    `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies
    completeness with respect to `rel₁` and `rel₃`.
    The completeness error of the appended reduction is the sum of the individual errors
    (`completenessError₁ + completenessError₂`). -/
theorem completeness_append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness rel₁ rel₃ (completenessError₁ + completenessError₂) := sorry

/-- If two reductions satisfy perfect completeness with compatible relations, then their
  concatenation also satisfies perfect completeness. -/
theorem perfectCompleteness_append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃)
    (h₁ : R₁.perfectCompleteness rel₁ rel₂) (h₂ : R₂.perfectCompleteness rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness rel₁ rel₃ := by
  dsimp [perfectCompleteness] at h₁ h₂ ⊢
  convert Reduction.completeness_append R₁ R₂ h₁ h₂
  simp only [add_zero]

end Append

section GeneralComposition

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]
    {Stmt : Fin (m + 2) → Type} {Wit : Fin (m + 2) → Type} {rel : ∀ i, Stmt i → Wit i → Prop}
    [oSpec.DecidableEq] [oSpec.FiniteRange]

theorem completeness_compose
    (R : ∀ i, Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ))
    (completenessError : Fin (m + 1) → ℝ≥0)
    (h : ∀ i, (R i).completeness (rel i.castSucc) (rel i.succ) (completenessError i)) :
      (Reduction.compose m n pSpec Stmt Wit R).completeness (rel 0) (rel (Fin.last (m + 1)))
        (∑ i, completenessError i) := by
  induction m with
  | zero =>
    simp_all; convert h 0; sorry
  | succ m ih =>
    sorry


end GeneralComposition

end Reduction

end Security

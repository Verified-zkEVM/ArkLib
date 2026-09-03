/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
import ArkLib.OracleReduction.Security.RoundByRound
import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
  # Sequential Composition of Two (Oracle) Reductions

  This file gives the definition & properties of the sequential composition of two (oracle)
  reductions. For composition to be valid, we need that the output context (statement + oracle
  statement + witness) for the first (oracle) reduction is the same as the input context for the
  second (oracle) reduction.

  The composition logic for `ProtocolSpec` and its associated structures lives in
  `ProtocolSpec/SeqCompose.lean`; we use the definitions from there.

  We will prove that the composition of reductions preserve all completeness & soundness properties
  of the reductions being composed (with extra conditions on the extractor).
-/

open OracleComp OracleSpec SubSpec

universe u v

section find_home

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

end find_home

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

private theorem heqFunApply {A A' : Sort u} {B B' : Sort v}
    (hA : A = A') (hB : B = B') {f : A → B} {f' : A' → B'}
    (hf : HEq f f') {a : A} {a' : A'} (ha : HEq a a') : HEq (f a) (f' a') := by
  subst hA
  subst hB
  exact heq_of_eq (by rw [eq_of_heq hf, eq_of_heq ha])

private theorem simulateQueryAlongHEq {A B : Type}
    (OA : OracleInterface A) (OB : OracleInterface B)
    (hType : A = B) (hInterface : HEq OA OB)
    {ι' : Type} {spec : OracleSpec ι'}
    (impl : (q : OB.Query) → OracleComp spec (OB.Response q))
    (q : OA.Query) {ι'' : Type} {targetSpec : OracleSpec ι''}
    (sim : QueryImpl spec (OracleComp targetSpec))
    (a : A) (b : B) (hab : HEq a b)
    (hImpl : ∀ q, simulateQ sim (impl q) = pure (OB.answer b q)) :
    simulateQ sim (OracleVerifier.queryAlongHEq OA OB hType hInterface impl q) =
      pure (OA.answer a q) := by
  cases hType
  cases eq_of_heq hInterface
  cases eq_of_heq hab
  exact hImpl q

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

  /- The combined prover's states are the concatenation of the first prover's states and the second
  prover's states (except the first one). -/
  PrvState := Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState) ∘ Fin.cast (by omega)

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun ctxIn => by
    simp only [Function.comp_apply, Fin.cast_zero, Fin.append_zero_of_succ_left]
    exact P₁.input ctxIn

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m`, then it sends the message & updates the state as the first prover
  - if `i = m`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. -/
  sendMessage := fun ⟨i, hDir⟩ state => by
    dsimp [Fin.vappend_eq_append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp only [hi, Fin.vappend_left_of_lt, Order.lt_add_one_iff, Order.add_one_le_iff,
        ↓reduceDIte] at hDir ⊢
      simp only [this, ↓reduceDIte] at state
      exact P₁.sendMessage ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp only [hi', lt_self_iff_false, not_false_eq_true,
          Fin.vappend_right_of_not_lt, tsub_self,
          lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceDIte, zero_add,
          eq_rec_constant] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.sendMessage ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp only [hi, not_false_eq_true, Fin.vappend_right_of_not_lt,
          Order.lt_add_one_iff, Order.add_one_le_iff, ↓reduceDIte,
          Nat.reduceSubDiff, eq_rec_constant] at hDir ⊢
        simp only [hi1, ↓reduceDIte, eq_rec_constant] at state
        exact P₂.sendMessage ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨i, hDir⟩ state => by
    dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp only [hi, Fin.vappend_left_of_lt, Order.lt_add_one_iff, Order.add_one_le_iff,
        ↓reduceDIte] at hDir ⊢
      simp only [this, ↓reduceDIte] at state
      exact P₁.receiveChallenge ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp only [hi', lt_self_iff_false, not_false_eq_true,
          Fin.vappend_right_of_not_lt, tsub_self,
          lt_add_iff_pos_right, Order.lt_one_iff, ↓reduceDIte, zero_add,
          eq_rec_constant] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.receiveChallenge ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp only [hi, not_false_eq_true, Fin.vappend_right_of_not_lt,
          Order.lt_add_one_iff, Order.add_one_le_iff, ↓reduceDIte,
          Nat.reduceSubDiff, eq_rec_constant] at hDir ⊢
        simp only [hi1, ↓reduceDIte, eq_rec_constant] at state
        exact P₂.receiveChallenge ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- The combined prover's output function has two cases:
  - if the second protocol is empty, then it is the composition of the first prover's output
    function, the second prover's input function, and the second prover's output function.
  - if the second protocol is non-empty, then it is the second prover's output function. -/
  output := fun state => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.cast, Fin.last, Fin.subNat] at state
    by_cases hn : n = 0
    · simp only [hn, add_zero, lt_add_iff_pos_right, Order.lt_one_iff,
        ↓reduceDIte] at state
      exact (do
        let ctxIn₂ ← P₁.output state
        letI state₂ := P₂.input ctxIn₂
        P₂.output (dcast (by simp [hn]) state₂))
    · haveI : m + n - (m + 1) + 1 = n := by omega
      simp only [Order.lt_add_one_iff, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, hn, ↓reduceDIte, eq_rec_constant] at state
      exact P₂.output (dcast (by simp [this, Fin.last]) state)

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

/-! ## Challenge-sampling transport across `++ₚ`

The security definitions draw challenges by `uniformSample`-ing the protocol's challenge type at a
given index, using the `SampleableType` instance found there. For an appended protocol that
instance is built by `Fin.fappend₂`, so it is not *syntactically* the component's instance — it is
the component's instance transported along `challenge_append_inl` / `challenge_append_inr`.

Every distributional comparison between an appended protocol and its components needs to know that
this transport is the identity on distributions. That is what the lemmas below establish. They are
the `SampleableType` analogue of `messageInterfaceInl` / `messageInterfaceInr` below, and are
proved the same way, by computing the `Fin.fappend₂` with `Fin.fappend₂_left` / `_right`. -/

section ChallengeSampling

variable [inst₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
    [inst₂ : ∀ i, SampleableType (pSpec₂.Challenge i)]

/-- Transporting a uniform sample along an equality of types, when the two `SampleableType`
instances correspond across that equality, leaves the distribution unchanged. -/
private theorem uniformSample_cast {α β : Type} (h : α = β)
    (instα : SampleableType α) (instβ : SampleableType β) (hI : HEq instα instβ) :
    cast h <$> (@uniformSample α instα) = (@uniformSample β instβ) := by
  subst h
  cases hI
  have hc : (cast (rfl : α = α)) = id := rfl
  rw [hc, id_map]

/-- The appended protocol's `SampleableType` instance at a left-injected challenge index is the
first component's instance, transported along `challenge_append_inl`. -/
private theorem challengeSampleableInl (i : pSpec₁.ChallengeIdx) : HEq (inst₁ i)
    (inferInstance : SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))) := by
  rcases i with ⟨i, hi⟩
  let u : (i : Fin m) →
      (h : pSpec₁.dir i = .V_to_P) → SampleableType (pSpec₁.«Type» i) :=
    fun i h => inst₁ ⟨i, h⟩
  let v : (i : Fin n) →
      (h : pSpec₂.dir i = .V_to_P) → SampleableType (pSpec₂.«Type» i) :=
    fun i h => inst₂ ⟨i, h⟩
  have hf : HEq
      (Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
        (_ : dir = Direction.V_to_P) → SampleableType type)
        u v (Fin.castAdd n i))
      (u i) := by
    rw [Fin.fappend₂_left]
    exact cast_heq _ _
  have hDomain : (pSpec₁.dir i = Direction.V_to_P) =
      ((Fin.vappend pSpec₁.dir pSpec₂.dir) (Fin.castAdd n i) = Direction.V_to_P) :=
    congrArg (· = Direction.V_to_P) (Fin.vappend_left pSpec₁.dir pSpec₂.dir i).symm
  have ha : HEq hi (ChallengeIdx.inl ⟨i, hi⟩).property :=
    (cast_heq hDomain hi).symm.trans (heq_of_eq (Subsingleton.elim _ _))
  change HEq (inst₁ ⟨i, hi⟩)
    ((Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
      (_ : dir = Direction.V_to_P) → SampleableType type)
      u v (Fin.castAdd n i)) (ChallengeIdx.inl ⟨i, hi⟩).property)
  exact heqFunApply hDomain
    (congrArg SampleableType (Fin.vappend_left pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

/-- The appended protocol's `SampleableType` instance at a right-injected challenge index is the
second component's instance, transported along `challenge_append_inr`. -/
private theorem challengeSampleableInr (i : pSpec₂.ChallengeIdx) : HEq (inst₂ i)
    (inferInstance : SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))) := by
  rcases i with ⟨i, hi⟩
  let u : (i : Fin m) →
      (h : pSpec₁.dir i = .V_to_P) → SampleableType (pSpec₁.«Type» i) :=
    fun i h => inst₁ ⟨i, h⟩
  let v : (i : Fin n) →
      (h : pSpec₂.dir i = .V_to_P) → SampleableType (pSpec₂.«Type» i) :=
    fun i h => inst₂ ⟨i, h⟩
  have hf : HEq
      (Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
        (_ : dir = Direction.V_to_P) → SampleableType type)
        u v (Fin.natAdd m i))
      (v i) := by
    rw [Fin.fappend₂_right]
    exact cast_heq _ _
  have hDomain : (pSpec₂.dir i = Direction.V_to_P) =
      ((Fin.vappend pSpec₁.dir pSpec₂.dir) (Fin.natAdd m i) = Direction.V_to_P) :=
    congrArg (· = Direction.V_to_P) (Fin.vappend_right pSpec₁.dir pSpec₂.dir i).symm
  have ha : HEq hi (ChallengeIdx.inr ⟨i, hi⟩).property :=
    (cast_heq hDomain hi).symm.trans (heq_of_eq (Subsingleton.elim _ _))
  change HEq (inst₂ ⟨i, hi⟩)
    ((Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
      (_ : dir = Direction.V_to_P) → SampleableType type)
      u v (Fin.natAdd m i)) (ChallengeIdx.inr ⟨i, hi⟩).property)
  exact heqFunApply hDomain
    (congrArg SampleableType (Fin.vappend_right pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

/-- **Challenge transport, left.** Sampling the appended protocol's challenge at a left-injected
index and casting back along `challenge_append_inl` is exactly sampling the first component's
challenge. -/
theorem uniformSample_challenge_append_inl (i : pSpec₁.ChallengeIdx) :
    cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
        ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i)))
      = ($ᵗ (pSpec₁.Challenge i)) :=
  uniformSample_cast _ _ _ (challengeSampleableInl (pSpec₂ := pSpec₂) i).symm

/-- **Challenge transport, right.** The `challenge_append_inr` analogue of
`uniformSample_challenge_append_inl`. -/
theorem uniformSample_challenge_append_inr (i : pSpec₂.ChallengeIdx) :
    cast (challenge_append_inr (pSpec₁ := pSpec₁) i) <$>
        ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i)))
      = ($ᵗ (pSpec₂.Challenge i)) :=
  uniformSample_cast _ _ _ (challengeSampleableInr (pSpec₁ := pSpec₁) i).symm

end ChallengeSampling

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

private theorem messageInterfaceInl (i : pSpec₁.MessageIdx) : HEq (Oₘ₁ i)
    (inferInstance : OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl i))) := by
  rcases i with ⟨i, hi⟩
  let u : (i : Fin m) →
      (h : pSpec₁.dir i = .P_to_V) → OracleInterface (pSpec₁.«Type» i) :=
    fun i h => Oₘ₁ ⟨i, h⟩
  let v : (i : Fin n) →
      (h : pSpec₂.dir i = .P_to_V) → OracleInterface (pSpec₂.«Type» i) :=
    fun i h => Oₘ₂ ⟨i, h⟩
  have hf : HEq
      (Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
        (_ : dir = Direction.P_to_V) → OracleInterface type)
        u v (Fin.castAdd n i))
      (u i) := by
    rw [Fin.fappend₂_left]
    exact cast_heq _ _
  have hDomain : (pSpec₁.dir i = Direction.P_to_V) =
      ((Fin.vappend pSpec₁.dir pSpec₂.dir) (Fin.castAdd n i) = Direction.P_to_V) :=
    congrArg (· = Direction.P_to_V) (Fin.vappend_left pSpec₁.dir pSpec₂.dir i).symm
  have ha : HEq hi (MessageIdx.inl ⟨i, hi⟩).property :=
    (cast_heq hDomain hi).symm.trans (heq_of_eq (Subsingleton.elim _ _))
  change HEq (Oₘ₁ ⟨i, hi⟩)
    ((Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
      (_ : dir = Direction.P_to_V) → OracleInterface type)
      u v (Fin.castAdd n i)) (MessageIdx.inl ⟨i, hi⟩).property)
  exact heqFunApply hDomain
    (congrArg OracleInterface (Fin.vappend_left pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

private theorem messageInterfaceInr (i : pSpec₂.MessageIdx) : HEq (Oₘ₂ i)
    (inferInstance : OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr i))) := by
  rcases i with ⟨i, hi⟩
  let u : (i : Fin m) →
      (h : pSpec₁.dir i = .P_to_V) → OracleInterface (pSpec₁.«Type» i) :=
    fun i h => Oₘ₁ ⟨i, h⟩
  let v : (i : Fin n) →
      (h : pSpec₂.dir i = .P_to_V) → OracleInterface (pSpec₂.«Type» i) :=
    fun i h => Oₘ₂ ⟨i, h⟩
  have hf : HEq
      (Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
        (_ : dir = Direction.P_to_V) → OracleInterface type)
        u v (Fin.natAdd m i))
      (v i) := by
    rw [Fin.fappend₂_right]
    exact cast_heq _ _
  have hDomain : (pSpec₂.dir i = Direction.P_to_V) =
      ((Fin.vappend pSpec₁.dir pSpec₂.dir) (Fin.natAdd m i) = Direction.P_to_V) :=
    congrArg (· = Direction.P_to_V) (Fin.vappend_right pSpec₁.dir pSpec₂.dir i).symm
  have ha : HEq hi (MessageIdx.inr ⟨i, hi⟩).property :=
    (cast_heq hDomain hi).symm.trans (heq_of_eq (Subsingleton.elim _ _))
  change HEq (Oₘ₂ ⟨i, hi⟩)
    ((Fin.fappend₂ (F := fun (dir : Direction) (type : Type) =>
      (_ : dir = Direction.P_to_V) → OracleInterface type)
      u v (Fin.natAdd m i)) (MessageIdx.inr ⟨i, hi⟩).property)
  exact heqFunApply hDomain
    (congrArg OracleInterface (Fin.vappend_right pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

private abbrev AppendSpec :=
  oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)

private def messageQueryInl : QueryImpl [pSpec₁.Message]ₒ (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  fun q => by
    rcases q with ⟨i, q⟩
    have hType : pSpec₁.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl i) := by
      simp [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
    exact OracleVerifier.queryAlongHEq (Oₘ₁ i) inferInstance hType (messageInterfaceInl i)
      (fun t => ((QueryImpl.id' [(pSpec₁ ++ₚ pSpec₂).Message]ₒ).liftTarget
        (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁))))
          ⟨MessageIdx.inl i, t⟩) q

private def messageQueryInr : QueryImpl [pSpec₂.Message]ₒ (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  fun q => by
    rcases q with ⟨i, q⟩
    have hType : pSpec₂.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr i) := by
      simp [MessageIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right]
    exact OracleVerifier.queryAlongHEq (Oₘ₂ i) inferInstance hType (messageInterfaceInr i)
      (fun t => ((QueryImpl.id' [(pSpec₁ ++ₚ pSpec₂).Message]ₒ).liftTarget
        (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁))))
          ⟨MessageIdx.inr i, t⟩) q

private theorem simulateMessageQueryInl
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    (q : [pSpec₁.Message]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (messageQueryInl (oSpec := oSpec) (OStmt₁ := OStmt₁) q) =
      pure ((Oₘ₁ q.1).answer (messages.fst q.1) q.2) := by
  rcases q with ⟨i, q⟩
  have hType : pSpec₁.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl i) := by
    simp [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
  have hab : HEq (messages.fst i) (messages (MessageIdx.inl i)) := by
    unfold Messages.fst
    exact cast_heq _ _
  unfold messageQueryInl
  apply simulateQueryAlongHEq (Oₘ₁ i) inferInstance hType (messageInterfaceInl i)
    _ q _ (messages.fst i) (messages (MessageIdx.inl i)) hab
  intro t
  refine Eq.trans (QueryImpl.simulateQ_addLift_add_liftM_right (QueryImpl.id oSpec)
    (OracleInterface.simOracle0 OStmt₁ oStmt)
    (OracleInterface.simOracle0 _ messages)
    (([(pSpec₁ ++ₚ pSpec₂).Message]ₒ).query ⟨MessageIdx.inl i, t⟩)) ?_
  rfl

private theorem simulateMessageQueryInr
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    (q : [pSpec₂.Message]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (messageQueryInr (oSpec := oSpec) (OStmt₁ := OStmt₁) q) =
      pure ((Oₘ₂ q.1).answer (messages.snd q.1) q.2) := by
  rcases q with ⟨i, q⟩
  have hType : pSpec₂.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr i) := by
    simp [MessageIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right]
  have hab : HEq (messages.snd i) (messages (MessageIdx.inr i)) := by
    unfold Messages.snd
    exact cast_heq _ _
  unfold messageQueryInr
  apply simulateQueryAlongHEq (Oₘ₂ i) inferInstance hType (messageInterfaceInr i)
    _ q _ (messages.snd i) (messages (MessageIdx.inr i)) hab
  intro t
  refine Eq.trans (QueryImpl.simulateQ_addLift_add_liftM_right (QueryImpl.id oSpec)
    (OracleInterface.simOracle0 OStmt₁ oStmt)
    (OracleInterface.simOracle0 _ messages)
    (([(pSpec₁ ++ₚ pSpec₂).Message]ₒ).query ⟨MessageIdx.inr i, t⟩)) ?_
  rfl

private def firstQueryImpl : QueryImpl (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ))
    (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  ((QueryImpl.id' oSpec).liftTarget (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)))) +
    (((QueryImpl.id' [OStmt₁]ₒ).liftTarget (OracleComp
      (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)))) +
      messageQueryInl (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))

private theorem simulateFirstQueryImpl
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    (q : (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ)).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁) q) =
      OracleInterface.simOracle2 oSpec oStmt messages.fst q := by
  rcases q with q | q
  · simp [firstQueryImpl, OracleInterface.simOracle2]
  · rcases q with q | q
    · rcases q with ⟨i, q⟩
      rfl
    · exact simulateMessageQueryInl oStmt messages q

private theorem simulateFirstQueryImplComp
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    {α : Type} (oa : OracleComp (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ)) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁)) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec oStmt messages.fst) oa := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl => simulateQ impl oa)
  apply QueryImpl.ext
  exact simulateFirstQueryImpl oStmt messages

private theorem simulateFirstQueryImplOptionTComp
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    {α : Type} (oa : OptionT
      (OracleComp (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ))) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁)) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec oStmt messages.fst) oa := by
  apply OptionT.ext
  exact simulateFirstQueryImplComp oStmt messages oa.run

private theorem simulateOutputQueryEq
    (V : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) (oStmt : ∀ i, OStmt₁ i)
    (messages : pSpec₁.Messages) (q : [OStmt₂]ₒ.Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (V.simulateOutputQuery challenges q) =
      pure ((Oₛ₂ q.1).answer (V.materializeOutput challenges oStmt messages q.1) q.2) := by
  exact V.simulateOutputQuery_eq challenges oStmt messages q

private def secondQueryImpl
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) :
    QueryImpl (oSpec + ([OStmt₂]ₒ + [pSpec₂.Message]ₒ))
      (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  ((QueryImpl.id' oSpec).liftTarget (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁)
      (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)))) +
    ((fun q => simulateQ
      (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))
      (V₁.simulateOutputQuery challenges q)) +
      messageQueryInr (oSpec := oSpec) (OStmt₁ := OStmt₁)
        (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))

private theorem simulateSecondQueryImpl
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) (oStmt : ∀ i, OStmt₁ i)
    (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    (q : (oSpec + ([OStmt₂]ₒ + [pSpec₂.Message]ₒ)).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (secondQueryImpl V₁ challenges q) =
      OracleInterface.simOracle2 oSpec
        (V₁.materializeOutput challenges oStmt messages.fst) messages.snd q := by
  rcases q with q | q
  · simp [secondQueryImpl, OracleInterface.simOracle2]
  · rcases q with q | q
    · rcases q with ⟨i, q⟩
      change simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
          (simulateQ (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁))
            (V₁.simulateOutputQuery challenges ⟨i, q⟩)) =
        pure ((Oₛ₂ i).answer
          (V₁.materializeOutput challenges oStmt messages.fst i) q)
      rw [simulateFirstQueryImplComp]
      exact simulateOutputQueryEq V₁ challenges oStmt messages.fst ⟨i, q⟩
    · exact simulateMessageQueryInr oStmt messages q

private theorem simulateSecondQueryImplComp
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) (oStmt : ∀ i, OStmt₁ i)
    (messages : (pSpec₁ ++ₚ pSpec₂).Messages) {α : Type}
    (oa : OracleComp (oSpec + ([OStmt₂]ₒ + [pSpec₂.Message]ₒ)) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (secondQueryImpl V₁ challenges) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec
        (V₁.materializeOutput challenges oStmt messages.fst) messages.snd) oa := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl => simulateQ impl oa)
  apply QueryImpl.ext
  exact simulateSecondQueryImpl V₁ challenges oStmt messages

private theorem simulateSecondQueryImplOptionTComp
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) (oStmt : ∀ i, OStmt₁ i)
    (messages : (pSpec₁ ++ₚ pSpec₂).Messages) {α : Type}
    (oa : OptionT (OracleComp (oSpec + ([OStmt₂]ₒ + [pSpec₂.Message]ₒ))) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (secondQueryImpl V₁ challenges) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec
        (V₁.materializeOutput challenges oStmt messages.fst) messages.snd) oa := by
  apply OptionT.ext
  exact simulateSecondQueryImplComp V₁ challenges oStmt messages oa.run

private def appendOutputSimulation
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
    OracleOutputSimulation oSpec OStmt₁ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  materializeOutput := fun challenges oStmt messages =>
    V₂.materializeOutput challenges.snd
      (V₁.materializeOutput challenges.fst oStmt messages.fst) messages.snd
  simulateOutputQuery := fun challenges q =>
    simulateQ (secondQueryImpl V₁ challenges.fst)
      (V₂.simulateOutputQuery challenges.snd q)
  simulateOutputQuery_eq := by
    intro challenges oStmt messages q
    rw [simulateSecondQueryImplComp]
    exact simulateOutputQueryEq V₂ challenges.snd
      (V₁.materializeOutput challenges.fst oStmt
        (Messages.fst (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) messages))
      (Messages.snd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) messages) q

def OracleVerifier.append (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt challenges => do
    let stmt₂ ← simulateQ
      (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁))
      (V₁.verify stmt challenges.fst)
    simulateQ (secondQueryImpl V₁ challenges.fst)
      (V₂.verify stmt₂ challenges.snd)

  outputOracle := .inr (appendOutputSimulation V₁ V₂)

private theorem append_materializeOutput
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (challenges : (pSpec₁ ++ₚ pSpec₂).Challenges) (oStmt : ∀ i, OStmt₁ i)
    (messages : (pSpec₁ ++ₚ pSpec₂).Messages) :
    (OracleVerifier.append V₁ V₂).materializeOutput challenges oStmt messages =
      V₂.materializeOutput challenges.snd
        (V₁.materializeOutput challenges.fst oStmt messages.fst) messages.snd := by
  rfl

private theorem append_verify_simulate
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (stmt : Stmt₁) (challenges : (pSpec₁ ++ₚ pSpec₂).Challenges)
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        ((OracleVerifier.append V₁ V₂).verify stmt challenges) = ((do
      let stmt₂ ← simulateQ (OracleInterface.simOracle2 oSpec oStmt messages.fst)
        (V₁.verify stmt challenges.fst)
      simulateQ (OracleInterface.simOracle2 oSpec
        (V₁.materializeOutput challenges.fst oStmt messages.fst) messages.snd)
        (V₂.verify stmt₂ challenges.snd)) : OptionT (OracleComp oSpec) Stmt₃) := by
  unfold OracleVerifier.append
  rw [simulateQ_optionT_bind, simulateFirstQueryImplOptionTComp]
  simp_rw [simulateSecondQueryImplOptionTComp]

@[simp]
lemma OracleVerifier.append_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      (OracleVerifier.append V₁ V₂).toVerifier =
        Verifier.append V₁.toVerifier V₂.toVerifier := by
  ext ⟨stmt, oStmt⟩ transcript
  simp only [OracleVerifier.toVerifier, Verifier.append]
  rw [show
    simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.messages)
        ((OracleVerifier.append V₁ V₂).verify stmt transcript.challenges).run =
      ((do
        let stmt₂ ← simulateQ
          (OracleInterface.simOracle2 oSpec oStmt (Messages.fst transcript.messages))
          (V₁.verify stmt (Challenges.fst transcript.challenges))
        simulateQ (OracleInterface.simOracle2 oSpec
          (V₁.materializeOutput (Challenges.fst transcript.challenges) oStmt
            (Messages.fst transcript.messages))
          (Messages.snd transcript.messages))
          (V₂.verify stmt₂ (Challenges.snd transcript.challenges))) :
            OptionT (OracleComp oSpec) Stmt₃).run from
      congrArg OptionT.run (append_verify_simulate V₁ V₂ stmt
        transcript.challenges oStmt transcript.messages),
    append_materializeOutput]
  rw [show Challenges.fst transcript.challenges = transcript.fst.challenges from rfl,
    show Challenges.snd transcript.challenges = transcript.snd.challenges from rfl,
    show Messages.fst transcript.messages = transcript.fst.messages from rfl,
    show Messages.snd transcript.messages = transcript.snd.messages from rfl]
  simp only [MessageIdx, Message, OptionT.run_bind, Option.elimM, map_bind,
    OptionT.mk_bind, OptionT.run_monadLift, monadLift_self, OptionT.run_mk,
    bind_map_left, Option.elim_some, Option.elim_map, Function.comp_def]
  rw [show
    OptionT.run (simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.fst.messages)
      (V₁.verify stmt transcript.fst.challenges) :
        OptionT (OracleComp oSpec) Stmt₂) =
      simulateQ (OracleInterface.simOracle2 oSpec oStmt transcript.fst.messages)
        (V₁.verify stmt transcript.fst.challenges).run from rfl]
  simp_rw [show ∀ stmt₂,
    OptionT.run (simulateQ (OracleInterface.simOracle2 oSpec
      (V₁.materializeOutput transcript.fst.challenges oStmt transcript.fst.messages)
      transcript.snd.messages) (V₂.verify stmt₂ transcript.snd.challenges) :
        OptionT (OracleComp oSpec) Stmt₃) =
      simulateQ (OracleInterface.simOracle2 oSpec
        (V₁.materializeOutput transcript.fst.challenges oStmt transcript.fst.messages)
        transcript.snd.messages) (V₂.verify stmt₂ transcript.snd.challenges).run from
    fun _ => rfl]
  apply bind_congr
  intro result
  cases result <;> simp

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

@[simp]
lemma OracleReduction.append_toReduction
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      (OracleReduction.append R₁ R₂).toReduction =
        Reduction.append R₁.toReduction R₂.toReduction := by
  ext : 1 <;> simp [toReduction, OracleReduction.append, Reduction.append]

end OracleProtocol

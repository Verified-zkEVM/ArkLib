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

/-! Sequential composition of extractors and state functions

These have the following form: they needs to know the first verifier, and derive the intermediate
statement from running the first verifier on the first statement.

This leads to complications: the verifier is assumed to be a general `OracleComp oSpec`, and so
we also need to have the extractors and state functions to be similarly `OracleComp`s.

The alternative is to consider a fully deterministic (and non-failing) verifier. The non-failing
part is somewhat problematic as we write our verifiers to be able to fail (i.e. implicit failing
via `guard` statements).

As such, the definitions below are temporary until further development. -/

namespace Extractor

/-- The sequential composition of two straightline extractors.

TODO: state a monotone condition on the extractor, namely that if extraction succeeds on a given
query log, then it also succeeds on any extension of that query log -/
def Straightline.append (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) :
      Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) :=
  fun stmt₁ wit₃ transcript proveQueryLog verifyQueryLog => do
    let stmt₂ ← V₁.verify stmt₁ transcript.fst
    let wit₂ ← E₂ stmt₂ wit₃ transcript.snd proveQueryLog verifyQueryLog
    let wit₁ ← E₁ stmt₁ wit₂ transcript.fst proveQueryLog verifyQueryLog
    return wit₁

/-- The composed round-by-round witness motive of `Extractor.RoundByRound.append`, evaluated at an
index lying in the first protocol's range, is the first extractor's witness type. -/
private lemma witMid_append_left {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (i : Fin (m + n + 1)) (j : Fin (m + 1)) (hij : i.val = j.val) :
    (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) i = WitMid₁ j := by
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) i = Fin.castAdd n j := by
    ext; simpa using hij
  simp only [Function.comp_apply, hcast, Fin.append_left]

/-- The composed round-by-round witness motive of `Extractor.RoundByRound.append`, evaluated at an
index lying in the second protocol's range, is the second extractor's witness type. -/
private lemma witMid_append_right {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (i : Fin (m + n + 1)) (j : Fin (n + 1)) (hij : i.val = m + j.val) (hj : 0 < j.val) :
    (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) i = WitMid₂ j := by
  have hjn := j.isLt
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) i
      = Fin.natAdd (m + 1) ⟨j.val - 1, by omega⟩ := by
    ext; simp; omega
  rw [Function.comp_apply, hcast, Fin.append_right]
  show Fin.tail WitMid₂ _ = _
  unfold Fin.tail
  congr 1
  ext; simp; omega

/-- The round-by-round extractor for the sequential composition of two (oracle) reductions.

`verify` is the first verifier's *deterministic* next-statement function. It is needed because the
second extractor `E₂` runs on the intermediate statement `Stmt₂`, and an appended extractor is only
handed the *initial* statement `Stmt₁`: without `verify` there is no way to produce the `Stmt₂`
that every call into `E₂` requires, and the definition cannot be written at all.

This mirrors `Extractor.Straightline.append`, which takes the first verifier for the same reason,
and `Verifier.StateFunction.append`, which takes this same deterministic `verify` function. A plain
`Verifier` cannot be used here: `Verifier.verify` returns an `OptionT (OracleComp oSpec) Stmt₂`,
whereas `extractMid` and `extractOut` are pure functions and so cannot run an oracle computation. -/
def RoundByRound.append
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) :
      Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂)
        (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) where
  eqIn := by
    simp only [Fin.append, Function.comp_apply, Fin.addCases, Fin.cast_zero,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, lt_add_iff_pos_left,
      Order.lt_add_one_iff, zero_le, ↓reduceDIte, Fin.castLT, Fin.zero_eta]
    exact E₁.eqIn
  extractMid := fun idx stmt₁ tr h => by
    have hidx := idx.isLt
    -- Re-expose the transcript with a transparent round bound, so that `omega` can discharge
    -- the index side conditions below.
    have tr' : (i : Fin (idx.val + 1)) →
        (pSpec₁ ++ₚ pSpec₂).«Type» ⟨i.val, by have := i.isLt; omega⟩ := tr
    by_cases hlt : idx.val < m
    · exact cast (witMid_append_left (WitMid₂ := WitMid₂) idx.castSucc ⟨idx.val, by omega⟩ rfl).symm
        (E₁.extractMid ⟨idx.val, hlt⟩ stmt₁
          (show pSpec₁.Transcript ⟨idx.val + 1, by omega⟩ from fun i =>
            cast (ProtocolSpec.append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
              ⟨i.val, by have := i.isLt; omega⟩) (tr' ⟨i.val, by have := i.isLt; omega⟩))
          (cast (witMid_append_left (WitMid₂ := WitMid₂) idx.succ ⟨idx.val + 1, by omega⟩ rfl) h))
    · have hm : m ≤ idx.val := by omega
      have tr₁ : pSpec₁.FullTranscript := fun i =>
        cast (ProtocolSpec.append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i)
          (tr' ⟨i.val, by have := i.isLt; omega⟩)
      by_cases heq : idx.val = m
      · have hn : 0 < n := by omega
        exact cast (witMid_append_left (WitMid₂ := WitMid₂) idx.castSucc (Fin.last m)
            (by simp [heq])).symm
          (E₁.extractOut stmt₁ tr₁
            (cast (show WitMid₂ (⟨0, hn⟩ : Fin n).castSucc = Wit₂ by
                rw [show ((⟨0, hn⟩ : Fin n).castSucc) = 0 from by ext; simp]; exact E₂.eqIn)
              (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ tr₁)
                (show pSpec₂.Transcript ⟨1, by omega⟩ from fun i =>
                  cast (ProtocolSpec.append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                    ⟨i.val, by have : i.val < 1 := i.isLt; omega⟩)
                    (tr' ⟨m + i.val, by have : i.val < 1 := i.isLt; omega⟩))
                (cast (witMid_append_right (WitMid₁ := WitMid₁) idx.succ (⟨0, hn⟩ : Fin n).succ
                  (by simp [heq]) (by simp)) h))))
      · have hk : idx.val - m < n := by omega
        exact cast (witMid_append_right (WitMid₁ := WitMid₁) idx.castSucc
            (⟨idx.val - m, hk⟩ : Fin n).castSucc (by simp; omega) (by simp; omega)).symm
          (E₂.extractMid ⟨idx.val - m, hk⟩ (verify stmt₁ tr₁)
            (show pSpec₂.Transcript ⟨idx.val - m + 1, by omega⟩ from fun i =>
              cast (ProtocolSpec.append_Type_natAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
                ⟨i.val, by have : i.val < idx.val - m + 1 := i.isLt; omega⟩)
                (tr' ⟨m + i.val, by have : i.val < idx.val - m + 1 := i.isLt; omega⟩))
            (cast (witMid_append_right (WitMid₁ := WitMid₁) idx.succ
              (⟨idx.val - m, hk⟩ : Fin n).succ (by simp; omega) (by simp)) h))
  extractOut := fun stmt₁ tr wit₃ => by
    by_cases hn : 0 < n
    · exact cast (witMid_append_right (WitMid₁ := WitMid₁) (Fin.last (m + n)) (Fin.last n)
          (by simp) (by simpa using hn)).symm
        (E₂.extractOut (verify stmt₁ tr.fst) tr.snd wit₃)
    · exact cast (witMid_append_left (WitMid₂ := WitMid₂) (Fin.last (m + n)) (Fin.last m)
          (by simp; omega)).symm
        (E₁.extractOut stmt₁ tr.fst
          (cast (show WitMid₂ (Fin.last n) = Wit₂ by
              rw [show (Fin.last n) = 0 from by ext; simp; omega]; exact E₂.eqIn)
            (E₂.extractOut (verify stmt₁ tr.fst) tr.snd wit₃)))

end Extractor

section StateFunctionAppend

/-! ### Helpers for `Verifier.StateFunction.append`

These are index-bookkeeping lemmas for partial transcripts of an appended protocol. They are all
stated with `HEq` because the round indices involved (`min k m`, `k - m`, ...) are only
*propositionally* equal to the ones appearing in the goals. -/

/-- Transporting along a type equality is the identity up to `HEq`. Used to peel off the
coercions that `Verifier.StateFunction.append`'s `toFun` inserts when it re-indexes a partial
transcript. -/
private lemma heq_eqMp {α β : Sort u} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  rw [eq_mp_eq_cast]; exact cast_heq _ _

/-- Extensionality for partial transcripts sitting at propositionally equal round indices. -/
private lemma transcript_heq_ext {N : ℕ} {pSpec : ProtocolSpec N} {k k' : Fin (N + 1)}
    {T : pSpec.Transcript k} {T' : pSpec.Transcript k'} (hk : k.val = k'.val)
    (h : ∀ (i : ℕ) (hi : i < k.val) (hi' : i < k'.val), HEq (T ⟨i, hi⟩) (T' ⟨i, hi'⟩)) :
    HEq T T' := by
  obtain rfl : k = k' := Fin.ext hk
  exact heq_of_eq (funext fun i => eq_of_heq (h i.val i.isLt i.isLt))

/-- Pointwise computation rule for `Transcript.fst`. -/
private lemma transcript_fst_apply {k : Fin (m + n + 1)}
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (i : ℕ) (hi : i < min k.val m) (hi' : i < k.val) :
    HEq (T.fst ⟨i, hi⟩) (T ⟨i, hi'⟩) := cast_heq _ _

/-- Pointwise computation rule for `Transcript.snd`. -/
private lemma transcript_snd_apply {k : Fin (m + n + 1)}
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (i : ℕ) (hi : i < k.val - m) (hi' : m + i < k.val) :
    HEq (T.snd ⟨i, hi⟩) (T ⟨m + i, hi'⟩) := cast_heq _ _

/-- Below the last round, `Transcript.concat` agrees with the transcript it extends. -/
private lemma transcript_concat_apply_lt {N : ℕ} {pSpec : ProtocolSpec N} {k : Fin N}
    (T : pSpec.Transcript k.castSucc) (msg : pSpec.«Type» k) (i : ℕ) (hi : i < k.val)
    (hi' : i < (k.succ : Fin (N + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) (T ⟨i, hi⟩) := by
  unfold Transcript.concat Fin.snoc
  rw [dif_pos hi]
  exact cast_heq _ _

/-- At the last round, `Transcript.concat` returns the newly appended message. -/
private lemma transcript_concat_apply_last {N : ℕ} {pSpec : ProtocolSpec N} {k : Fin N}
    (T : pSpec.Transcript k.castSucc) (msg : pSpec.«Type» k) (i : ℕ) (hik : i = k.val)
    (hi' : i < (k.succ : Fin (N + 1)).val) :
    HEq (T.concat msg ⟨i, hi'⟩) msg := by
  subst hik
  unfold Transcript.concat Fin.snoc
  rw [dif_neg (Nat.lt_irrefl k.val)]
  exact cast_heq _ _

/-- A state function's value only depends on the round index, statement, and transcript up to
(heterogeneous) equality. -/
private lemma stateFunction_toFun_heq {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
    {N : ℕ} {pSpec : ProtocolSpec N} {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {langIn : Set StmtIn} {langOut : Set StmtOut}
    {V : Verifier oSpec StmtIn StmtOut pSpec} (S : V.StateFunction init impl langIn langOut)
    {k k' : Fin (N + 1)} (hk : k = k') {stmt stmt' : StmtIn} (hstmt : stmt = stmt')
    {T : pSpec.Transcript k} {T' : pSpec.Transcript k'} (h : HEq T T')
    (hS : S.toFun k stmt T) : S.toFun k' stmt' T' := by
  subst hk
  subst hstmt
  obtain rfl := eq_of_heq h
  exact hS

/-- Pointwise computation rule for `FullTranscript.fst`. -/
private lemma fullTranscript_fst_apply (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (i : Fin m) :
    HEq (FullTranscript.fst T i) (T (Fin.castAdd n i)) := by
  unfold FullTranscript.fst; exact cast_heq _ _

/-- Pointwise computation rule for `FullTranscript.snd`. -/
private lemma fullTranscript_snd_apply (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (i : Fin n) :
    HEq (FullTranscript.snd T i) (T (Fin.natAdd m i)) := by
  unfold FullTranscript.snd; exact cast_heq _ _

/-- At the last round, the partial projection `Transcript.fst` is the full projection
`FullTranscript.fst`, up to the index rewriting `min (m + n) m = m`. -/
private lemma transcript_fst_eq_full (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (fun i : Fin m => (Transcript.fst (k := Fin.last (m + n)) T)
      ⟨i.val, by have := i.isLt; change i.val < min (m + n) m; omega⟩) =
      FullTranscript.fst T := by
  funext i
  have hi := i.isLt
  exact eq_of_heq ((transcript_fst_apply (k := Fin.last (m + n)) T i.val
    (show i.val < min (m + n) m by omega) (show i.val < m + n by omega)).trans
      (fullTranscript_fst_apply T i).symm)

/-- Heterogeneous form of `transcript_fst_eq_full`. -/
private lemma transcript_fst_heq_full (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    HEq (Transcript.fst (k := Fin.last (m + n)) T) (FullTranscript.fst T) := by
  refine transcript_heq_ext (k := ⟨min (m + n) m, by omega⟩) (k' := Fin.last m)
    (show min (m + n) m = m by omega) ?_
  intro i hi hi'
  exact (transcript_fst_apply (k := Fin.last (m + n)) T i hi (show i < m + n by omega)).trans
    (fullTranscript_fst_apply T ⟨i, hi'⟩).symm

/-- At the last round, the partial projection `Transcript.snd` is the full projection
`FullTranscript.snd`, up to the index rewriting `(m + n) - m = n`. -/
private lemma transcript_snd_heq_full (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    HEq (Transcript.snd (k := Fin.last (m + n)) T) (FullTranscript.snd T) := by
  refine transcript_heq_ext (k := ⟨(m + n) - m, by omega⟩) (k' := Fin.last n)
    (show (m + n) - m = n by omega) ?_
  intro i hi hi'
  exact (transcript_snd_apply (k := Fin.last (m + n)) T i (show i < (m + n) - m by omega)
    (show m + i < m + n by omega)).trans (fullTranscript_snd_apply T ⟨i, hi'⟩).symm

/-- If the first verifier is deterministic (`hVerify`), running the appended verifier is the same
as running the second verifier on the second half of the transcript, started from the first
verifier's output on the first half. -/
private lemma append_run_of_deterministic
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (V₁.append V₂).run stmt tr = V₂.run (verify stmt tr.fst) tr.snd := by
  subst hVerify
  simp [Verifier.run, Verifier.append]

/-- The output of a deterministic verifier is reachable as soon as the initial-state computation
`init` can succeed. -/
private lemma mem_support_of_pure_run {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {x : Stmt₂} {s : σ} (hs : s ∈ support init) :
    x ∈ support (OptionT.mk do
      (simulateQ impl (pure x : OptionT (OracleComp oSpec) Stmt₂)).run' (← init)) := by
  rw [OptionT.mem_support_iff]
  simp only [OptionT.run_mk, StateT.run'_eq, mem_support_bind_iff]
  refine ⟨s, hs, ?_⟩
  change some x ∈ support ((fun p => p.1) <$> (pure (some x, s) : ProbComp (Option Stmt₂ × σ)))
  simp

/-- Every `ProbComp` has at least one possible outcome: `OracleComp` is a free monad with no
failure constructor, and every `unifSpec` query has an answer. (A general fact about `ProbComp`,
kept here only because it has no other home yet.) -/
private lemma probComp_support_nonempty {σ : Type} (init : ProbComp σ) :
    (support init).Nonempty := by
  induction init using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    obtain ⟨u⟩ : Nonempty (unifSpec.Range t) := by infer_instance
    obtain ⟨x, hx⟩ := ih u
    exact ⟨x, by simp only [support_bind, support_query, Set.mem_iUnion]; exact ⟨u, trivial, hx⟩⟩

/-- A deterministic verifier's run is a `pure` computation. -/
private lemma run_of_deterministic
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) :
    V₁.run stmt tr = (pure (verify stmt tr) : OptionT (OracleComp oSpec) Stmt₂) := by
  subst hVerify; rfl

/-- If a deterministic first verifier's state function rejects the completed first-half transcript,
then the statement it hands to the second verifier lies outside the intermediate language.

This step needs `init` to have at least one possible outcome, since a `StateFunction`'s
`toFun_full` field only constrains a *probability*. That is automatic for `ProbComp`
(`probComp_support_nonempty`), so no side condition is needed. -/
private lemma verify_notMem_of_not_toFun {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂}
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript) (h : ¬ S₁.toFun (Fin.last m) stmt tr) :
    verify stmt tr ∉ lang₂ := by
  obtain ⟨s, hs⟩ := probComp_support_nonempty init
  have h₁ := S₁.toFun_full stmt tr h
  rw [run_of_deterministic hVerify, probEvent_eq_zero_iff] at h₁
  exact h₁ _ (mem_support_of_pure_run hs)

end StateFunctionAppend

namespace Verifier

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- The sequential composition of two state functions.

Rounds `0, …, m` of the appended protocol are scored by `S₁`, and rounds `m+1, …, m+n` are scored
by `S₂`, started at the statement `verify` produces from the first half of the transcript. In
particular the second half is scored by `S₂` **alone**: the first half's verdict is not carried
along as a conjunct.

The reason is that the *only* thing a `StateFunction` promises about a "bad" state is
`toFun_full`, and at a full transcript of the appended protocol it is `V₂` that produces the
output statement. Conjoining `S₁` would let the composite be bad on account of its first half
while `S₂` — the half that actually decides — is good and `V₂` accepts, contradicting
`toFun_full`. Handing the verdict to whichever half owns the last round is what makes the
composite honest.

The hand-off at round `m` uses `hVerify`: `V₁` is deterministic, so there is a single
intermediate statement `verify stmt tr₁` to start `S₂` from, and `S₁` rejecting the first half
forces that statement out of `lang₂`. -/
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
    -- If the round index falls in the second protocol, then we hand the first protocol's
    -- transcript to `verify` and score the remaining transcript with the second state fn.
      have hm : min roundIdx.val m = m := min_eq_right_of_lt (by omega)
      let transcript₁ : pSpec₁.FullTranscript := fun i => transcript.fst ⟨i, by simp [hm]⟩
      S₂ ⟨roundIdx - m, by omega⟩ (verify stmt₁ transcript₁)
        (by simpa [h] using transcript.snd)
  toFun_empty := by
    intro stmt
    split
    · constructor <;> intro h
      · have h' := (S₁.toFun_empty stmt).mp h
        convert h' using 2
        · rfl
        · apply heq_of_eq
          funext i
          exact Fin.elim0 i
      · exact (S₁.toFun_empty stmt).mpr
          (by
            convert h using 2
            · rfl
            · apply heq_of_eq
              funext i
              exact Fin.elim0 i)
    · exact absurd (Nat.zero_le m) ‹_›
  toFun_next := by
    intro j hDir stmt tr hnot msg
    have hj := j.isLt
    have hcs : ((j.castSucc : Fin (m + n + 1)) : ℕ) = j.val := rfl
    have hsc : ((j.succ : Fin (m + n + 1)) : ℕ) = j.val + 1 := rfl
    rcases lt_trichotomy j.val m with hlt | heq | hgt
    · -- Case 1: the new round lies strictly inside the first protocol, so both sides of the
      -- implication take the `then` branch and we may appeal to `S₁.toFun_next`.
      have hDir' : Fin.vappend pSpec₁.dir pSpec₂.dir j = Direction.P_to_V := hDir
      rw [Fin.vappend_left_of_lt _ _ j hlt] at hDir'
      have htype : (pSpec₁ ++ₚ pSpec₂).«Type» j = pSpec₁.«Type» ⟨j.val, hlt⟩ := by
        have h0 : (pSpec₁ ++ₚ pSpec₂).«Type» j = Fin.vappend pSpec₁.«Type» pSpec₂.«Type» j := rfl
        rw [h0, Fin.vappend_left_of_lt _ _ j hlt]
      let T₁ : pSpec₁.Transcript ⟨j.val, by omega⟩ := fun i =>
        cast (append_Type_castAdd (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
          ⟨i.val, by have hi : i.val < j.val := i.isLt; omega⟩)
          (tr ⟨i.val, by have hi : i.val < j.val := i.isLt; omega⟩)
      have hnot₁ : ¬ S₁.toFun ⟨j.val, by omega⟩ stmt T₁ := by
        intro hc
        apply hnot
        rw [dif_pos (show ((j.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)]
        convert hc using 2
        exact (heq_eqMp _ _).trans (transcript_heq_ext (by simp; omega) (fun i hi hi' => HEq.rfl))
      have key := S₁.toFun_next ⟨j.val, hlt⟩ hDir' stmt T₁ hnot₁ (cast htype msg)
      intro hgoal
      rw [dif_pos (show ((j.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hgoal
      refine key ?_
      convert hgoal using 2
      · rfl
      refine HEq.symm ((heq_eqMp _ _).trans (transcript_heq_ext
        (show min ((j.succ : Fin (m + n + 1)) : ℕ) m = j.val + 1 by omega) ?_))
      intro i hi hi'
      have hi'' : i < j.val + 1 := hi'
      rcases Nat.lt_or_ge i j.val with hij | hij
      · exact ((transcript_fst_apply _ i hi hi').trans
          (transcript_concat_apply_lt tr msg i hij hi')).trans
            ((transcript_concat_apply_lt T₁ (cast htype msg) i hij hi').trans (cast_heq _ _)).symm
      · obtain rfl : i = j.val := le_antisymm (by omega) hij
        exact ((transcript_fst_apply _ j.val hi hi').trans
          (transcript_concat_apply_last tr msg j.val rfl hi')).trans
            ((transcript_concat_apply_last T₁ (cast htype msg) j.val rfl hi').trans
              (cast_heq _ _)).symm
    · -- Case 2: the boundary round `j.val = m`. The hypothesis is the `then` branch (`S₁` at its
      -- last round) and the goal is the `else` branch (`S₂` at its round `1`). The appended
      -- protocol's direction at index `m` *is* `pSpec₂.dir 0`, so this is `S₂.toFun_next` at
      -- round `0`; its hypothesis `¬ S₂.toFun 0 _ default` is `S₂.toFun_empty` applied to
      -- `verify stmt _ ∉ lang₂`, which `S₁`'s rejection yields via determinism of `V₁`.
      have hn : 0 < n := by omega
      have hzm : (⟨j.val - m, by omega⟩ : Fin n) = ⟨0, hn⟩ :=
        Fin.ext (show j.val - m = 0 by omega)
      have hDir₂ : pSpec₂.dir ⟨0, hn⟩ = Direction.P_to_V := by
        have hDir' : Fin.vappend pSpec₁.dir pSpec₂.dir j = Direction.P_to_V := hDir
        rw [Fin.vappend_right_of_not_lt _ _ j (by omega)] at hDir'
        rwa [hzm] at hDir'
      have htype₂ : (pSpec₁ ++ₚ pSpec₂).«Type» j = pSpec₂.«Type» ⟨0, hn⟩ := by
        have h0 : (pSpec₁ ++ₚ pSpec₂).«Type» j = Fin.vappend pSpec₁.«Type» pSpec₂.«Type» j := rfl
        rw [h0, Fin.vappend_right_of_not_lt _ _ j (by omega), hzm]
      -- The first protocol's half of the transcript is unchanged by the new message.
      have hTr : ∀ (i : Fin m) (h1 : i.val < min ((j.succ : Fin (m + n + 1)) : ℕ) m)
          (h2 : i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m),
          HEq ((Transcript.concat msg tr).fst ⟨i.val, h1⟩) (tr.fst ⟨i.val, h2⟩) := by
        intro i h1 h2
        exact ((transcript_fst_apply _ i.val h1 (by omega)).trans
          (transcript_concat_apply_lt tr msg i.val (by omega) (by omega))).trans
            (transcript_fst_apply tr i.val h2 (by omega)).symm
      rw [dif_pos (show ((j.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hnot
      intro hgoal
      rw [dif_neg (show ¬ ((j.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hgoal
      -- `S₁` rejects the completed first half, so `V₁`'s output misses `lang₂`, so `S₂` is false
      -- at its round `0` on that output.
      have h0 : ¬ S₂.toFun (⟨0, hn⟩ : Fin n).castSucc
          (verify stmt fun i => tr.fst ⟨i.val,
            show i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by have := i.isLt; omega⟩)
          (fun i => Fin.elim0 i) := by
        intro hc
        refine verify_notMem_of_not_toFun S₁ hVerify stmt _ ?_
          ((S₂.toFun_empty _).mpr (stateFunction_toFun_heq S₂ (Fin.ext (by simp)) rfl
            (heq_of_eq (funext fun i => Fin.elim0 i)) hc))
        intro hc₁
        refine hnot (stateFunction_toFun_heq S₁
          (Fin.ext (show m = ((j.castSucc : Fin (m + n + 1)) : ℕ) by omega)) rfl ?_ hc₁)
        refine HEq.trans ?_ (heq_eqMp _ _).symm
        exact transcript_heq_ext (k := ⟨m, by omega⟩)
          (k' := ⟨min ((j.castSucc : Fin (m + n + 1)) : ℕ) m, by omega⟩)
          (show m = min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by omega)
          (fun i hi hi' => HEq.rfl)
      -- The second protocol's half of the new transcript is exactly its single new message.
      have hSnd : HEq ((Transcript.concat msg tr).snd)
          (Transcript.concat (cast htype₂ msg) (fun i => Fin.elim0 i)) := by
        refine transcript_heq_ext (k := ⟨((j.succ : Fin (m + n + 1)) : ℕ) - m, by omega⟩)
          (k' := (⟨0, hn⟩ : Fin n).succ)
          (show ((j.succ : Fin (m + n + 1)) : ℕ) - m = 0 + 1 by omega) ?_
        intro i hi hi'
        obtain rfl : i = 0 := by have : i < 0 + 1 := hi'; omega
        exact ((transcript_snd_apply (Transcript.concat msg tr) 0 hi (by omega)).trans
          (transcript_concat_apply_last tr msg (m + 0) (by omega) (by omega))).trans
            ((transcript_concat_apply_last _ (cast htype₂ msg) 0 rfl hi').trans
              (cast_heq _ _)).symm
      refine S₂.toFun_next ⟨0, hn⟩ hDir₂ _ _ h0 (cast htype₂ msg)
        (stateFunction_toFun_heq S₂
          (Fin.ext (show ((j.succ : Fin (m + n + 1)) : ℕ) - m = 0 + 1 by omega))
          ?_ hSnd hgoal)
      exact congrArg (verify stmt) (funext fun i => eq_of_heq (hTr i _ _))
    · -- Case 3: the new round lies strictly inside the second protocol, so both sides take the
      -- `else` branch. The `S₁` conjunct carries over verbatim and the `S₂` conjunct is the
      -- contrapositive of `S₂.toFun_next` at round `⟨j.val - m, _⟩`.
      have hkn : j.val - m < n := by omega
      have hDir₂ : pSpec₂.dir ⟨j.val - m, hkn⟩ = Direction.P_to_V := by
        have hDir' : Fin.vappend pSpec₁.dir pSpec₂.dir j = Direction.P_to_V := hDir
        rw [Fin.vappend_right_of_not_lt _ _ j (by omega)] at hDir'
        exact hDir'
      have htype₂ : (pSpec₁ ++ₚ pSpec₂).«Type» j = pSpec₂.«Type» ⟨j.val - m, hkn⟩ := by
        have h0 : (pSpec₁ ++ₚ pSpec₂).«Type» j = Fin.vappend pSpec₁.«Type» pSpec₂.«Type» j := rfl
        rw [h0, Fin.vappend_right_of_not_lt _ _ j (by omega)]
      -- The first protocol's half of the transcript is unchanged by the new message.
      have hTr : ∀ (i : Fin m) (h1 : i.val < min ((j.succ : Fin (m + n + 1)) : ℕ) m)
          (h2 : i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m),
          HEq ((Transcript.concat msg tr).fst ⟨i.val, h1⟩) (tr.fst ⟨i.val, h2⟩) := by
        intro i h1 h2
        exact ((transcript_fst_apply _ i.val h1 (by omega)).trans
          (transcript_concat_apply_lt tr msg i.val (by omega) (by omega))).trans
            (transcript_fst_apply tr i.val h2 (by omega)).symm
      rw [dif_neg (show ¬ ((j.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hnot
      intro hgoal
      rw [dif_neg (show ¬ ((j.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at hgoal
      -- The second protocol's half gains exactly the new message at its last position.
      have hSnd : HEq ((Transcript.concat msg tr).snd)
          (Transcript.concat (cast htype₂ msg) tr.snd) := by
        refine transcript_heq_ext (k := ⟨((j.succ : Fin (m + n + 1)) : ℕ) - m, by omega⟩)
          (k' := (⟨j.val - m, hkn⟩ : Fin n).succ) ?_ ?_
        · show ((j.succ : Fin (m + n + 1)) : ℕ) - m = j.val - m + 1
          omega
        intro i hi hi'
        have hi2 : i < j.val - m + 1 := hi'
        rcases Nat.lt_or_ge i (j.val - m) with hij | hij
        · exact ((transcript_snd_apply (Transcript.concat msg tr) i hi (by omega)).trans
            (transcript_concat_apply_lt tr msg (m + i) (by omega) (by omega))).trans
              ((transcript_concat_apply_lt tr.snd (cast htype₂ msg) i hij hi').trans
                (transcript_snd_apply tr i hij (by omega))).symm
        · exact ((transcript_snd_apply (Transcript.concat msg tr) i hi (by omega)).trans
            (transcript_concat_apply_last tr msg (m + i) (by omega) (by omega))).trans
              ((transcript_concat_apply_last tr.snd (cast htype₂ msg) i
                (by show i = j.val - m; omega) hi').trans (cast_heq _ _)).symm
      have hnot₂ : ¬ S₂.toFun (⟨j.val - m, hkn⟩ : Fin n).castSucc
          (verify stmt fun i => tr.fst ⟨i.val,
            show i.val < min ((j.castSucc : Fin (m + n + 1)) : ℕ) m by have := i.isLt; omega⟩)
          tr.snd := by
        intro hc
        refine hnot (stateFunction_toFun_heq S₂
          (Fin.ext (show j.val - m = ((j.castSucc : Fin (m + n + 1)) : ℕ) - m by omega)) rfl ?_ hc)
        exact HEq.rfl
      refine absurd (stateFunction_toFun_heq S₂
        (Fin.ext (show ((j.succ : Fin (m + n + 1)) : ℕ) - m = j.val - m + 1 by omega))
        (congrArg (verify stmt) (funext fun i => eq_of_heq (hTr i _ _))) hSnd hgoal)
        (S₂.toFun_next ⟨j.val - m, hkn⟩ hDir₂ _ _ hnot₂ (cast htype₂ msg))
  toFun_full := by
    intro stmt tr hnot
    rw [append_run_of_deterministic hVerify stmt tr]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `pSpec₂` is empty, so the appended protocol's last round is `m` and `hnot` is about `S₁`.
      -- Determinism of `V₁` turns that into `verify stmt tr.fst ∉ lang₂`, which is `¬ S₂.toFun 0`
      -- by `S₂.toFun_empty`; and with `n = 0`, round `0` *is* `S₂`'s last round.
      subst hn
      rw [dif_pos (show (((Fin.last (m + 0)) : Fin (m + 0 + 1)) : ℕ) ≤ m by
        simp only [Fin.val_last]; omega)] at hnot
      have hS₁ : ¬ S₁.toFun (Fin.last m) stmt (FullTranscript.fst tr) := fun hc =>
        hnot (stateFunction_toFun_heq S₁ (Fin.ext (by simp)) rfl
          ((transcript_fst_heq_full tr).symm.trans (heq_eqMp _ _).symm) hc)
      refine S₂.toFun_full _ _ fun hc => ?_
      exact verify_notMem_of_not_toFun S₁ hVerify stmt (FullTranscript.fst tr) hS₁
        ((S₂.toFun_empty _).mpr (stateFunction_toFun_heq S₂ (Fin.ext (by simp)) rfl
          (heq_of_eq (funext fun i => Fin.elim0 i)) hc))
    · -- `pSpec₂` is non-empty, so the appended protocol's last round lies in the `else` branch and
      -- `hnot` is literally the hypothesis of `S₂`'s own `toFun_full`.
      rw [dif_neg (show ¬ (((Fin.last (m + n)) : Fin (m + n + 1)) : ℕ) ≤ m by
        simp only [Fin.val_last]; omega)] at hnot
      refine S₂.toFun_full _ _ fun hc => hnot ?_
      exact stateFunction_toFun_heq S₂ (Fin.ext (by simp))
        (congrArg (verify stmt) (transcript_fst_eq_full tr).symm)
        (transcript_snd_heq_full tr).symm hc

end Verifier

section Execution

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

-- #print Prover.processRound

-- theorem append_processRound (roundIdx : Fin (m + n)) (stmt : Stmt₁) (wit : Wit₁)
--     (transcript : pSpec₁.FullTranscript) (proveQueryLog : Set (Stmt₁ × Wit₁))
--     (verifyQueryLog : Set (Stmt₂ × Wit₂)) :
--       (P₁.append P₂).processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog =
--         (P₁.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) ∧
--         (P₂.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) := sorry

-- theorem append_runToRound

-- The challenge-oracle inclusions that `append_run`'s statement lifts along are provided
-- (proved) by `ProtocolSpec.subSpec_challenge_append_left` / `..._right` in
-- `ProtocolSpec/SeqCompose.lean`, with their `LawfulSubSpec` instances and the `@[simp]` lemmas
-- `liftM_getChallenge_append_inl` / `_inr` that compute the lifted challenge query.
--
-- Scope of what lawfulness buys: `support_liftComp` / `mem_support_liftComp_iff` apply directly.
-- `evalDist_liftComp` / `probEvent_liftComp` do NOT apply at this shape — they additionally
-- require `IsUniformSpec` on both specs, and `oSpec` here is arbitrary. The security definitions
-- below measure after `simulateQ pImpl`, so relating the two sides at the distribution level will
-- need `simulateQ_liftM_eq_of_query` plus the fact that `challengeQueryImpl` for the appended
-- protocol, precomposed with the lift, agrees with `challengeQueryImpl` for the component — a
-- `SampleableType`-compatibility fact across the transport that is not yet proved.

/--
States that running an appended prover `P₁.append P₂` with an initial statement `stmt₁` and
witness `wit₁` behaves as expected: it first runs `P₁` to obtain an intermediate statement
`stmt₂`, witness `wit₂`, and transcript `transcript₁`. Then, it runs `P₂` on `stmt₂` and `wit₂`
to produce the final statement `stmt₃`, witness `wit₃`, and transcript `transcript₂`.
The overall output is `stmt₃`, `wit₃`, and the combined transcript `transcript₁ ++ₜ transcript₂`.
-/
theorem append_run (stmt : Stmt₁) (wit : Wit₁) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftAppendRight pSpec₁ (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) := by
  unfold run runToRound
  sorry

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Prover

namespace Verifier

variable {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {stmt : Stmt₁}

/-- Running the sequential composition of two verifiers on a transcript of the combined protocol
  is equivalent to running the first verifier on the first part of the transcript, and the second
  verifier on the second part of the transcript, and returning the final statement. -/
theorem append_run (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    (V₁.append V₂).run stmt tr =
        (do
          let stmt₂ ← V₁.run stmt tr.fst
          let stmt₃ ← V₂.run stmt₂ tr.snd
          return stmt₃) := rfl

end Verifier

namespace Reduction

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/- Unfortunately this is not true due to sequencing: `(R₁.append R₂).run` runs the two provers
first, then the two verifiers, whereas `R₁.run` and then `R₂.run` runs the first prover and
verifier, then the second prover and verifier.

We need justification to be able to swap the first verifier with the second prover, which would be
true if we interpret / maps this oracle computation (a priori a term of the free monad) into a
commutative monad (such as `Id`, i.e. all oracle queries are answered deterministically, `PMF`, i.e.
all oracle queries are answered probabilistically, `Option`, `ReaderT ρ`, `Set`, `WriterT` into a
commutative monoid, etc.). -/

-- TODO: prove this after VCVio refactor
-- theorem append_run_interp {m : Type → Type} [Monad m] [m.IsCommutative]
--     {interp : OracleImpl oSpec m} : ((R₁.append R₂).run stmt wit).runM interp =
--         (do
--           let ⟨ctx₁, stmt₂, transcript₁⟩ ← liftM (R₁.run stmt wit)
--           let ⟨ctx₂, stmt₃, transcript₂⟩ ← liftM (R₂.run stmt₂ ctx₁.2)
--           return ⟨ctx₂, stmt₃, transcript₁ ++ₜ transcript₂⟩).runM interp := by
--   unfold run append
--   simp [Prover.append_run, Verifier.append_run]
--   sorry

end Reduction

end Execution

section Security

open scoped NNReal

/-! ### Admitted security-composition boundary

The virtual-output execution semantics and the `append_toVerifier` commutation theorem above are
proved. The generic completeness and security theorems below remain admitted because appended
execution orders both prover phases before both verifier phases, while sequential execution
interleaves each prover with its verifier. Their unrestricted `StateT` statements must therefore
not be treated as established composition security. Standalone protocol theorems that do not invoke
these declarations are outside this inherited trust boundary. -/

section Protocol

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-
TODO: when do these theorems hold? The answer may be that when oracle queries are answered according
to a _commutative_ monad, which are then interpreted into a probability distribution.

Unfortunately, this means that `StateT` is out; this works for `ReaderT` and `WriterT` into a
commutative monoid. If we still want composition to work for `StateT`, then we need to have extra
conditions (what are they?)
-/

namespace Reduction

/-- Sequential composition preserves completeness

  Namely, two reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for `R₁` and
  `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
  `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies
  completeness with respect to `rel₁` and `rel₃`.

  The completeness error of the appended reduction is the sum of the individual errors
  (`completenessError₁ + completenessError₂`). -/
theorem append_completeness
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  unfold completeness at h₁ h₂ ⊢
  intro stmtIn witIn hRelIn
  have h₁' := h₁ stmtIn witIn hRelIn
  clear h₁
  unfold Reduction.append Reduction.run
  simp [Prover.append_run, Verifier.append_run]
  sorry

/-- If two reductions satisfy perfect completeness with compatible relations, then their
  concatenation also satisfies perfect completeness. -/
theorem append_perfectCompleteness (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  dsimp [perfectCompleteness] at h₁ h₂ ⊢
  convert Reduction.append_completeness R₁ R₂ h₁ h₂
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
theorem append_soundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  sorry

/-- If two verifiers satisfy knowledge soundness with compatible relations and respective knowledge
    errors, then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the appended verifier is the sum of the individual errors. -/
theorem append_knowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl
        rel₁ rel₃ (knowledgeError₁ + knowledgeError₂) := by
  sorry

/-- If two verifiers satisfy round-by-round soundness with compatible languages and respective RBR
    soundness errors, then their sequential composition also satisfies round-by-round soundness.
    The RBR soundness error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrSoundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

/-- If two verifiers satisfy round-by-round knowledge soundness with compatible relations and
    respective RBR knowledge errors, then their sequential composition also satisfies
    round-by-round knowledge soundness.
    The RBR knowledge error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrKnowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

end Verifier

end Protocol

section OracleProtocol

variable {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

namespace OracleReduction

/-- Sequential composition preserves completeness

  Namely, two oracle reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for
  `R₁` and `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
  `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies completeness
  with respect to `rel₁` and `rel₃`.

  The completeness error of the appended reduction is the sum of the individual errors
  (`completenessError₁ + completenessError₂`). -/
theorem append_completeness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  unfold completeness
  convert Reduction.append_completeness R₁.toReduction R₂.toReduction h₁ h₂
  simp only [append_toReduction]

/-- If two oracle reductions satisfy perfect completeness with compatible relations, then their
  sequential composition also satisfies perfect completeness. -/
theorem append_perfectCompleteness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change (R₁.append R₂).completeness init impl rel₁ rel₃ 0
  simpa only [zero_add] using OracleReduction.append_completeness R₁ R₂ h₁ h₂

end OracleReduction

namespace OracleVerifier

variable {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))} {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

/-- If two oracle verifiers satisfy soundness with compatible languages and respective soundness
    errors, then their sequential composition also satisfies soundness.
    The soundness error of the appended verifier is the sum of the individual errors. -/
theorem append_soundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold soundness
  convert Verifier.append_soundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy knowledge soundness with compatible relations and respective
    knowledge errors, then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the appended verifier is the sum of the individual errors. -/
theorem append_knowledgeSoundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃
        (knowledgeError₁ + knowledgeError₂) := by
  unfold knowledgeSoundness
  convert Verifier.append_knowledgeSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy round-by-round soundness with compatible languages and
  respective RBR soundness errors, then their sequential composition also satisfies
  round-by-round soundness. The RBR soundness error of the appended verifier extends the
  individual errors appropriately. -/
theorem append_rbrSoundness (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrSoundness
  convert Verifier.append_rbrSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy round-by-round knowledge soundness with compatible relations
    and respective RBR knowledge errors, then their sequential composition also satisfies
    round-by-round knowledge soundness.
    The RBR knowledge error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrKnowledgeSoundness (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrKnowledgeSoundness
  convert Verifier.append_rbrKnowledgeSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

end OracleVerifier

end OracleProtocol

end Security

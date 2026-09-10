/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, scaraven
-/
module

public import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
public import ArkLib.ToMathlib.Logic.HEq
public import ArkLib.OracleReduction.Security.RoundByRound
public import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Sequential composition of provers and verifiers

Binary composition feeds the first reduction's output statement and witness into the second.
The component context types must agree. This module defines the append operations and proves
challenge-sampling transport and oracle-verifier conversion equalities.

Protocol specifications and transcript operations are defined in `ProtocolSpec/SeqCompose.lean`.
`Composition/Sequential/Append.lean` exports execution and security results.
-/

@[expose] public section

open OracleComp OracleSpec SubSpec

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

private theorem simulateQ_queryAlongHEq {A B : Type}
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

/-- Arity bookkeeping for `Prover.append`'s state family. Stated as a standalone lemma
rather than an inline `by omega`: under the module system a tactic proof inside a public
definition is elaborated lazily, which would leave a metavariable in the type of
`sendMessage`'s `state`. -/
theorem Prover.append_state_arity (m n : ℕ) : m + n + 1 = m + 1 + n := by omega

/-- Compose two provers by feeding the first prover's output into the second prover's input.
The first prover's final state is retained until the second protocol's first round; for an empty
second protocol, the transfer occurs during output. -/
def Prover.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where

  /- The combined prover's states are the concatenation of the first prover's states and the second
  prover's states (except the first one). -/
  PrvState := Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState) ∘
    Fin.cast (Prover.append_state_arity m n)

  /- The combined prover always starts with the first prover's input function, including when the
  first protocol is empty. The second prover is initialized when the seam is processed. -/
  input := fun ctxIn => by
    simp only [Function.comp_apply, Fin.cast_zero, Fin.append_zero_of_succ_left]
    exact P₁.input ctxIn

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m`, then it sends the message & updates the state as the first prover
  - if `i = m`, then it runs the first prover's output, initializes the second prover from that
    output, and sends the second prover's first message
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

/-! ### Computation rules for `Prover.append`

`Prover.append` defines `PrvState` by a `Fin.append` and `output` by a `dif` on whether the second
protocol is empty, so both fields only reduce once the round index has been placed relative to the
seam. The four lemmas below do that placement once, and are what every proof about an appended
prover — `Prover.OutputIsPure.append` just below, and the `runToRound` ladder in
`Append/Execution.lean` — starts from. -/

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- Below the seam, the appended prover's state family is the first prover's. -/
theorem append_prvState_left (k : Fin (m + n + 1)) (j : Fin (m + 1)) (hkj : k.val = j.val) :
    (P₁.append P₂).PrvState k = P₁.PrvState j := by
  change (Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState)
    ∘ Fin.cast (by omega)) k = P₁.PrvState j
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) k = Fin.castAdd n j := by
    ext; simpa using hkj
  simp only [Function.comp_apply, hcast, Fin.append_left]

/-- Past the seam, the appended prover's state family is the second prover's. -/
theorem append_prvState_right (k : Fin (m + n + 1)) (j : Fin (n + 1)) (hk : m < k.val)
    (hkj : k.val = m + j.val) :
    (P₁.append P₂).PrvState k = P₂.PrvState j := by
  change (Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState)
    ∘ Fin.cast (by omega)) k = P₂.PrvState j
  have hcast : Fin.cast (show m + n + 1 = m + 1 + n by omega) k
      = Fin.natAdd (m + 1) ⟨j.val - 1, by omega⟩ := by
    ext; simp; omega
  simp only [Function.comp_apply, hcast, Fin.append_right, Fin.tail]
  congr 1
  ext; simp; omega

/-- When the second protocol has rounds, the appended prover's output step is the second prover's,
on the transported final state. -/
theorem append_output_pos (hn : n ≠ 0)
    (state : (P₁.append P₂).PrvState (Fin.last (m + n)))
    (state₂ : P₂.PrvState (Fin.last n)) (hst : HEq state state₂) :
    (P₁.append P₂).output state = P₂.output state₂ := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_neg hn]
  exact congrArg P₂.output
    (eq_of_heq ((heq_dcast _ _).trans ((cast_heq _ _).trans hst)))

/-- When the second protocol is empty, the seam collapses into the output step: the appended
prover's output runs `P₁.output`, feeds the result through `P₂.input`, then runs `P₂.output`. -/
theorem append_output_zero (hn : n = 0)
    (state : (P₁.append P₂).PrvState (Fin.last (m + n)))
    (state₁ : P₁.PrvState (Fin.last m)) (hst : HEq state state₁) :
    (P₁.append P₂).output state
      = (do let ctx ← P₁.output state₁
            P₂.output (dcast (by simp [hn]) (P₂.input ctx))) := by
  conv_lhs => unfold Prover.append
  dsimp only
  rw [dif_pos hn]
  congr 1
  exact congrArg P₁.output (eq_of_heq ((cast_heq _ _).trans hst))

/-- Sequential composition preserves pure prover output, including empty components. -/
theorem OutputIsPure.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : P₁.OutputIsPure) (h₂ : P₂.OutputIsPure) :
    (P₁.append P₂).OutputIsPure := by
  obtain ⟨f₁, hf₁⟩ := h₁.output_is_pure
  obtain ⟨f₂, hf₂⟩ := h₂.output_is_pure
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun st =>
      f₂ (dcast (by simp) (P₂.input (f₁ (cast (append_prvState_left _ _ (by simp)) st)))),
      fun st => ?_⟩
    rw [append_output_zero rfl st _ (cast_heq _ st).symm, hf₁, pure_bind, hf₂]
  · refine ⟨fun st =>
      f₂ (cast (append_prvState_right _ _ (by simp; omega) (by simp)) st), fun st => ?_⟩
    rw [append_output_pos hn st _ (cast_heq _ st).symm, hf₂]

/-- Sequential composition of provers with pure output has pure output. -/
instance instOutputIsPureAppend [h₁ : P₁.OutputIsPure] [h₂ : P₂.OutputIsPure] :
    (P₁.append P₂).OutputIsPure := OutputIsPure.append P₁ P₂ h₁ h₂

end Prover

/-- Run the first verifier on the transcript prefix, then pass its output statement to the
second verifier on the transcript suffix. Failure in either verifier propagates. -/
def Verifier.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
      Verifier oSpec Stmt₁ Stmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Compose the component provers and verifiers of two reductions. -/
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
the `SampleableType` analogue of `message_interface_inl` / `message_interface_inr` below, and are
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
  exact id_map _

/-- The appended protocol's `SampleableType` instance at a left-injected challenge index is the
first component's instance, transported along `challenge_append_inl`. -/
private theorem challenge_sampleable_inl (i : pSpec₁.ChallengeIdx) : HEq (inst₁ i)
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
  exact heq_apply hDomain
    (congrArg SampleableType (Fin.vappend_left pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

/-- The appended protocol's `SampleableType` instance at a right-injected challenge index is the
second component's instance, transported along `challenge_append_inr`. -/
private theorem challenge_sampleable_inr (i : pSpec₂.ChallengeIdx) : HEq (inst₂ i)
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
  exact heq_apply hDomain
    (congrArg SampleableType (Fin.vappend_right pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

/-- **Challenge transport, left.** Sampling the appended protocol's challenge at a left-injected
index and casting back along `challenge_append_inl` is exactly sampling the first component's
challenge. -/
theorem uniformSample_challenge_append_inl (i : pSpec₁.ChallengeIdx) :
    cast (challenge_append_inl (pSpec₂ := pSpec₂) i) <$>
        ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i)))
      = ($ᵗ (pSpec₁.Challenge i)) :=
  uniformSample_cast _ _ _ (challenge_sampleable_inl (pSpec₂ := pSpec₂) i).symm

/-- **Challenge transport, right.** The `challenge_append_inr` analogue of
`uniformSample_challenge_append_inl`. -/
theorem uniformSample_challenge_append_inr (i : pSpec₂.ChallengeIdx) :
    cast (challenge_append_inr (pSpec₁ := pSpec₁) i) <$>
        ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i)))
      = ($ᵗ (pSpec₂.Challenge i)) :=
  uniformSample_cast _ _ _ (challenge_sampleable_inr (pSpec₁ := pSpec₁) i).symm

end ChallengeSampling

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

theorem message_interface_inl (i : pSpec₁.MessageIdx) : HEq (Oₘ₁ i)
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
  exact heq_apply hDomain
    (congrArg OracleInterface (Fin.vappend_left pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

theorem message_interface_inr (i : pSpec₂.MessageIdx) : HEq (Oₘ₂ i)
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
  exact heq_apply hDomain
    (congrArg OracleInterface (Fin.vappend_right pSpec₁.«Type» pSpec₂.«Type» i).symm)
    hf.symm ha

abbrev AppendSpec :=
  oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)

def messageQueryInl : QueryImpl [pSpec₁.Message]ₒ (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  fun q => by
    rcases q with ⟨i, q⟩
    have hType : pSpec₁.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl i) := by
      simp [MessageIdx.inl, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_left]
    exact OracleVerifier.queryAlongHEq (Oₘ₁ i) inferInstance hType (message_interface_inl i)
      (fun t => ((QueryImpl.id' [(pSpec₁ ++ₚ pSpec₂).Message]ₒ).liftTarget
        (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁))))
          ⟨MessageIdx.inl i, t⟩) q

def messageQueryInr : QueryImpl [pSpec₂.Message]ₒ (OracleComp
    (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁) (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))) :=
  fun q => by
    rcases q with ⟨i, q⟩
    have hType : pSpec₂.Message i = (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr i) := by
      simp [MessageIdx.inr, ProtocolSpec.append, Fin.vappend_eq_append, Fin.append_right]
    exact OracleVerifier.queryAlongHEq (Oₘ₂ i) inferInstance hType (message_interface_inr i)
      (fun t => ((QueryImpl.id' [(pSpec₁ ++ₚ pSpec₂).Message]ₒ).liftTarget
        (OracleComp (AppendSpec (oSpec := oSpec) (OStmt₁ := OStmt₁))))
          ⟨MessageIdx.inr i, t⟩) q

private theorem simulateQ_messageQueryInl
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
  apply simulateQ_queryAlongHEq (Oₘ₁ i) inferInstance hType (message_interface_inl i)
    _ q _ (messages.fst i) (messages (MessageIdx.inl i)) hab
  intro t
  refine Eq.trans (QueryImpl.simulateQ_addLift_add_liftM_right (QueryImpl.id oSpec)
    (OracleInterface.simOracle0 OStmt₁ oStmt)
    (OracleInterface.simOracle0 _ messages)
    (([(pSpec₁ ++ₚ pSpec₂).Message]ₒ).query ⟨MessageIdx.inl i, t⟩)) ?_
  rfl

private theorem simulateQ_messageQueryInr
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
  apply simulateQ_queryAlongHEq (Oₘ₂ i) inferInstance hType (message_interface_inr i)
    _ q _ (messages.snd i) (messages (MessageIdx.inr i)) hab
  intro t
  refine Eq.trans (QueryImpl.simulateQ_addLift_add_liftM_right (QueryImpl.id oSpec)
    (OracleInterface.simOracle0 OStmt₁ oStmt)
    (OracleInterface.simOracle0 _ messages)
    (([(pSpec₁ ++ₚ pSpec₂).Message]ₒ).query ⟨MessageIdx.inr i, t⟩)) ?_
  rfl

def firstQueryImpl : QueryImpl (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ))
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

private theorem simulateQ_firstQueryImpl
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
    · exact simulateQ_messageQueryInl oStmt messages q

private theorem simulateQ_simulateQ_firstQueryImpl
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    {α : Type} (oa : OracleComp (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ)) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁)) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec oStmt messages.fst) oa := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl => simulateQ impl oa)
  apply QueryImpl.ext
  exact simulateQ_firstQueryImpl oStmt messages

private theorem simulateQ_simulateQ_firstQueryImpl_optionT
    (oStmt : ∀ i, OStmt₁ i) (messages : (pSpec₁ ++ₚ pSpec₂).Messages)
    {α : Type} (oa : OptionT
      (OracleComp (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ))) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (firstQueryImpl (oSpec := oSpec) (OStmt₁ := OStmt₁)) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec oStmt messages.fst) oa := by
  apply OptionT.ext
  exact simulateQ_simulateQ_firstQueryImpl oStmt messages oa.run

def secondQueryImpl
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

private theorem simulateQ_secondQueryImpl
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
      rw [simulateQ_simulateQ_firstQueryImpl]
      exact V₁.simulateOutputQuery_eq challenges oStmt messages.fst ⟨i, q⟩
    · exact simulateQ_messageQueryInr oStmt messages q

private theorem simulateQ_simulateQ_secondQueryImpl
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
  exact simulateQ_secondQueryImpl V₁ challenges oStmt messages

private theorem simulateQ_simulateQ_secondQueryImpl_optionT
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (challenges : pSpec₁.Challenges) (oStmt : ∀ i, OStmt₁ i)
    (messages : (pSpec₁ ++ₚ pSpec₂).Messages) {α : Type}
    (oa : OptionT (OracleComp (oSpec + ([OStmt₂]ₒ + [pSpec₂.Message]ₒ))) α) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        (simulateQ (secondQueryImpl V₁ challenges) oa) =
      simulateQ (OracleInterface.simOracle2 oSpec
        (V₁.materializeOutput challenges oStmt messages.fst) messages.snd) oa := by
  apply OptionT.ext
  exact simulateQ_simulateQ_secondQueryImpl V₁ challenges oStmt messages oa.run

def appendOutputSimulation
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
    rw [simulateQ_simulateQ_secondQueryImpl]
    exact V₂.simulateOutputQuery_eq challenges.snd
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
  rw [simulateQ_optionT_bind, simulateQ_simulateQ_firstQueryImpl_optionT]
  simp_rw [simulateQ_simulateQ_secondQueryImpl_optionT]

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

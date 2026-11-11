/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.Execution

/-!
# Execution of embedded legacy oracle reductions

The oracle tree and the plain tree of a legacy protocol have the same rounds, owners and runtime
moves; they differ only in how a prover message is recorded. This file relates runs of the
embedded oracle verifier on the oracle tree to legacy oracle reduction runs.

* Transport. `toPlainFrom` sends an oracle-tree strategy of either participant to the plain
  tree. The runner commutes with it (`runWith_toPlainFrom`), as do `Prover.simulate`, the
  sampler and the embedded honest prover (`toPlainFrom_embedOracleProver`). `toOraclePath`
  reads a plain runtime path back on the oracle tree.
* Transcript. On the runtime path of an actual run, the verifier's challenges
  (`viewChallenges_toView`) and the message oracles' data (`pathMessages_payloads`) are the
  components of the decoded legacy transcript.
* Decision. Routing the legacy decision to the input and path oracles and answering them from
  the run's data is legacy `simOracle2` on the input data and decoded messages
  (`simulateQ_decisionImpl`, `simulateQ_embedOracleVerifier_decide`); the output data are the
  legacy materialization (`embedOracleVerifier_outputMap_f`).
* Observation. `oracleObserveWith` is the run of an oracle verifier with legacy-indexed
  challenges, under a chosen schedule. The run of `embedOracleVerifier V` is the plain run of
  `V.toVerifier` against the transported prover (`oracleObserveWith_embed`,
  `simulateQ_embedOracleVerifier_run`, `experiment_embedOracleVerifier_run`).
* Result. `oracleFinalize` decodes an accepted oracle observation into the legacy result,
  keeping the prover's output statement, output oracle data and witness, and the verifier's
  output statement and output oracle data. The counterpart-first program equality
  (`oracleFinalize_observeWith_counterpartFirst`) holds for every legacy oracle reduction; the
  default-schedule form assumes pure challenge slots (`simulateQ_oracleFinalize_run`); the
  distributional and measure forms hold for every reduction
  (`experiment_oracleFinalize_run_evalDistEq`, `evalDist_experiment_oracleFinalize_run`).
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec Oracle

variable {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface.{0, 0} (pSpec.Message i)]

/-! ### Transport from the oracle tree to the plain tree -/

/-- A plain round's runtime move as the oracle round's runtime move. -/
def toOracleMove (j : Fin n) : (D : Direction) → (hD : pSpec.dir j = D) →
    Move plainSig (plainPos D (pSpec.«Type» j)) → Move oracleSig (oraclePos pSpec j D hD)
  | .P_to_V, _, x => x
  | .V_to_P, _, x => x

/-- A runtime path of the plain tree from round `k` as a runtime path of the oracle tree. -/
def toOraclePath : (k m : ℕ) → (h : k + m = n) → PathAlong plainSig (suffix pSpec k m h) →
    PathAlong oracleSig (oracleSuffix pSpec k m h)
  | _, 0, _, _ => ⟨⟩
  | k, m + 1, _, ⟨x, tr⟩ => ⟨toOracleMove ⟨k, by omega⟩ _ rfl x, toOraclePath (k + 1) m _ tr⟩

/-- Transport a slot payload at an oracle round to the plain round of the same direction. -/
def toPlainChoice (agent : Participant) (j : Fin n) : (D : Direction) → (hD : pSpec.dir j = D) →
    {A : Move oracleSig (oraclePos pSpec j D hD) → Type} →
    {B : Move plainSig (plainPos D (pSpec.«Type» j)) → Type} →
    (∀ x, A (toOracleMove j D hD x) → B x) →
    Choice agent (owner oracleSig (oraclePos pSpec j D hD))
      (Move oracleSig (oraclePos pSpec j D hD)) A →
    Choice agent (owner plainSig (plainPos D (pSpec.«Type» j)))
      (Move plainSig (plainPos D (pSpec.«Type» j))) B
  | .P_to_V, _, _, _, f => Choice.map agent .sender f
  | .V_to_P, _, _, _, f => Choice.map agent .receiver f

/-- Transport a participant's strategy on the oracle tree from round `k` to the plain tree. -/
def toPlainFrom {M : Type → Type} [Functor M] (agent : Participant) :
    (k m : ℕ) → (h : k + m = n) → {Out : PathAlong oracleSig (oracleSuffix pSpec k m h) → Type} →
    PureEnd oracleSig M agent (oracleSuffix pSpec k m h) Out →
    PureEnd plainSig M agent (suffix pSpec k m h) (fun tr => Out (toOraclePath k m h tr))
  | _, 0, _, _, p => p
  | k, m + 1, h, _, p =>
    toPlainChoice agent ⟨k, by omega⟩ _ rfl
      (fun _ q => toPlainFrom agent (k + 1) m (by omega) q) <$> p

theorem toPlainFrom_succ {M : Type → Type} [Functor M] (agent : Participant) (k m : ℕ)
    (h : k + (m + 1) = n) {Out : PathAlong oracleSig (oracleSuffix pSpec k (m + 1) h) → Type}
    (p : PureEnd oracleSig M agent (oracleSuffix pSpec k (m + 1) h) Out) :
    toPlainFrom agent k (m + 1) h p =
      toPlainChoice agent ⟨k, by omega⟩ _ rfl
        (fun _ q => toPlainFrom agent (k + 1) m (by omega) q) <$> p := rfl

/-- Mapping the result of a local exchange moves inside the exchange. -/
theorem map_step {M : Type → Type} [Monad M] [LawfulMonad M] {X : Type} {A B : X → Type}
    {R R' : Type} (role : TwoParty.Role) (order : Schedule) (p : M (Choice .focal role X A))
    (c : M (Choice .counterpart role X B)) (k : ∀ x, A x → B x → M R) (f : R → R') :
    f <$> step role order p c k = step role order p c (fun x a b => f <$> k x a b) := by
  simp only [map_eq_bind_pure_comp, step_bind]

/-- Mapping the result of a sequenced pair of slots moves inside the continuation. -/
theorem map_seq {M : Type → Type} [Monad M] [LawfulMonad M] (order : Schedule) {A B R R' : Type}
    (p : M A) (c : M B) (k : A → B → M R) (f : R → R') :
    f <$> order.seq p c k = order.seq p c (fun a b => f <$> k a b) := by
  cases order <;> simp [Schedule.seq]

/-- A pure post-processing step followed by a pure continuation is a single map. -/
theorem bind_pure_bind_pure {M : Type → Type} [Monad M] [LawfulMonad M] {α β γ δ : Type}
    (x : M α) (f : α → β) (k : β → γ) (F : δ → γ) (k' : α → δ) (h : ∀ a, k (f a) = F (k' a)) :
    (x >>= fun a => (pure (f a) : M β) >>= fun b => pure (k b)) =
      F <$> (x >>= fun a => pure (k' a)) := by
  simp [h]

/-- One node of the runner commutes with the transport, given that the rest of the tree does. -/
theorem runWith_node_toPlain {M : Type → Type} [Monad M] [LawfulMonad M] (order : Schedule)
    (j : Fin n) (D : Direction) (hD : pSpec.dir j = D) (restO : OracleProtocol.{0})
    (restP : Protocol.{0}) (g : PathAlong plainSig restP → PathAlong oracleSig restO)
    {OutP OutC : PathAlong oracleSig (.liftBind (oraclePos pSpec j D hD) fun _ => restO) → Type}
    (p : Focal oracleSig M (.liftBind (oraclePos pSpec j D hD) fun _ => restO) OutP)
    (c : Counterpart oracleSig M (.liftBind (oraclePos pSpec j D hD) fun _ => restO) OutC)
    (TP : ∀ x, Focal oracleSig M restO (fun tr => OutP ⟨toOracleMove j D hD x, tr⟩) →
      Focal plainSig M restP (fun tr => OutP ⟨toOracleMove j D hD x, g tr⟩))
    (TC : ∀ x, Counterpart oracleSig M restO (fun tr => OutC ⟨toOracleMove j D hD x, tr⟩) →
      Counterpart plainSig M restP (fun tr => OutC ⟨toOracleMove j D hD x, g tr⟩))
    (ih : ∀ x pn cn, runWith order restO pn cn =
      (fun r => (⟨g r.1, r.2.1, r.2.2⟩ : (tr : PathAlong oracleSig restO) ×
        OutP ⟨toOracleMove j D hD x, tr⟩ × OutC ⟨toOracleMove j D hD x, tr⟩)) <$>
        runWith order restP (TP x pn) (TC x cn)) :
    runWith order (.liftBind (oraclePos pSpec j D hD) fun _ => restO) p c =
      (fun r : (tr : PathAlong plainSig (.liftBind (plainPos D (pSpec.«Type» j)) fun _ => restP)) ×
          OutP ⟨toOracleMove j D hD tr.1, g tr.2⟩ × OutC ⟨toOracleMove j D hD tr.1, g tr.2⟩ =>
        (⟨⟨toOracleMove j D hD r.1.1, g r.1.2⟩, r.2.1, r.2.2⟩ :
          (tr : PathAlong oracleSig (.liftBind (oraclePos pSpec j D hD) fun _ => restO)) ×
            OutP tr × OutC tr)) <$>
        runWith order (.liftBind (plainPos D (pSpec.«Type» j)) fun _ => restP)
          (toPlainChoice .focal j D hD TP <$> p) (toPlainChoice .counterpart j D hD TC <$> c) := by
  cases D with
  | P_to_V =>
    rw [runWith_liftBind, runWith_liftBind]
    change step .sender order p c _ = _ <$> step .sender order
      (Choice.map .focal .sender TP <$> p) (Choice.map .counterpart .sender TC <$> c) _
    erw [step_map_left, step_map_right, map_step]
    refine congrArg _ (funext fun x => funext fun a => funext fun b => ?_)
    erw [ih x a b, map_eq_bind_pure_comp, bind_assoc]
    exact bind_pure_bind_pure _ _ _ _ _ fun _ => rfl
  | V_to_P =>
    rw [runWith_liftBind, runWith_liftBind]
    change step .receiver order p c _ = _ <$> step .receiver order
      (Choice.map .focal .receiver TP <$> p) (Choice.map .counterpart .receiver TC <$> c) _
    erw [step_map_left, step_map_right, map_step]
    refine congrArg _ (funext fun x => funext fun a => funext fun b => ?_)
    erw [ih x a b, map_eq_bind_pure_comp, bind_assoc]
    exact bind_pure_bind_pure _ _ _ _ _ fun _ => rfl

/-- **The runner commutes with the transport.** Running two strategies on the oracle tree is
running their transports on the plain tree, with the runtime path read back on the oracle
tree. -/
theorem runWith_toPlainFrom {M : Type → Type} [Monad M] [LawfulMonad M] (order : Schedule) :
    (k m : ℕ) → (h : k + m = n) →
    {OutP OutC : PathAlong oracleSig (oracleSuffix pSpec k m h) → Type} →
    (p : Focal oracleSig M (oracleSuffix pSpec k m h) OutP) →
    (c : Counterpart oracleSig M (oracleSuffix pSpec k m h) OutC) →
    runWith order (oracleSuffix pSpec k m h) p c =
      (fun r => (⟨toOraclePath k m h r.1, r.2.1, r.2.2⟩ :
        (tr : PathAlong oracleSig (oracleSuffix pSpec k m h)) × OutP tr × OutC tr)) <$>
        runWith order (suffix pSpec k m h) (toPlainFrom .focal k m h p)
          (toPlainFrom .counterpart k m h c)
  | k, 0, h, _, _, p, c => by
    erw [runWith_done, runWith_done, map_seq]
    exact congrArg (order.seq p c) (funext fun _ => funext fun _ => by
      erw [LawfulApplicative.map_pure]; rfl)
  | k, m + 1, h, _, _, p, c =>
    runWith_node_toPlain order ⟨k, by omega⟩ _ rfl _ _ (toOraclePath (k + 1) m (by omega)) p c
      (fun _ q => toPlainFrom .focal (k + 1) m (by omega) q)
      (fun _ q => toPlainFrom .counterpart (k + 1) m (by omega) q)
      (fun _ pn cn => runWith_toPlainFrom order (k + 1) m (by omega) pn cn)

theorem toPlainChoice_map (agent : Participant) (j : Fin n) (D : Direction)
    (hD : pSpec.dir j = D) {A A' : Move oracleSig (oraclePos pSpec j D hD) → Type}
    {B : Move plainSig (plainPos D (pSpec.«Type» j)) → Type}
    (f : ∀ x, A' (toOracleMove j D hD x) → B x) (g : ∀ x, A x → A' x)
    (v : Choice agent (owner oracleSig (oraclePos pSpec j D hD))
      (Move oracleSig (oraclePos pSpec j D hD)) A) :
    toPlainChoice agent j D hD f (Choice.map agent _ g v) =
      toPlainChoice agent j D hD (fun x a => f x (g _ a)) v := by
  cases D <;> cases agent <;> rfl

theorem map_toPlainChoice (agent : Participant) (j : Fin n) (D : Direction)
    (hD : pSpec.dir j = D) {A : Move oracleSig (oraclePos pSpec j D hD) → Type}
    {B B' : Move plainSig (plainPos D (pSpec.«Type» j)) → Type}
    (f : ∀ x, A (toOracleMove j D hD x) → B x) (g : ∀ x, B x → B' x)
    (v : Choice agent (owner oracleSig (oraclePos pSpec j D hD))
      (Move oracleSig (oraclePos pSpec j D hD)) A) :
    Choice.map agent _ g (toPlainChoice agent j D hD f v) =
      toPlainChoice agent j D hD (fun x a => g x (f x a)) v := by
  cases D <;> cases agent <;> rfl

/-- **Simulation commutes with the transport.** -/
theorem toPlainFrom_simulate {κ κ' : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'}
    (F : QueryImpl spec (OracleComp spec')) :
    (k m : ℕ) → (h : k + m = n) → {Out : PathAlong oracleSig (oracleSuffix pSpec k m h) → Type} →
    (p : Core.Prover oracleSig spec (oracleSuffix pSpec k m h) Out) →
    toPlainFrom .focal k m h (Prover.simulate F p) =
      Prover.simulate F (toPlainFrom .focal k m h p)
  | _, 0, _, _, _ => rfl
  | k, m + 1, h, _, p => by
    erw [Prover.simulate_node, Prover.simulate_node, toPlainFrom_succ, toPlainFrom_succ,
      simulateQ_map, Functor.map_map, Functor.map_map]
    refine congrArg (· <$> simulateQ F p) (funext fun v => ?_)
    erw [toPlainChoice_map, map_toPlainChoice]
    congr 1
    funext _ q
    exact toPlainFrom_simulate F (k + 1) m _ q

/-! ### Challenge nodes -/

/-- The branch of an oracle round: oracle payloads and challenges have a single branch. -/
def oracleBranch (j : Fin n) : (D : Direction) → (hD : pSpec.dir j = D) →
    OraclePoly.B (oraclePos pSpec j D hD)
  | .P_to_V, _ => ⟨⟩
  | .V_to_P, _ => ⟨⟩

/-- An oracle round's runtime move as the plain round's runtime move. -/
def toPlainMove (j : Fin n) : (D : Direction) → (hD : pSpec.dir j = D) →
    Move oracleSig (oraclePos pSpec j D hD) → Move plainSig (plainPos D (pSpec.«Type» j))
  | .P_to_V, _, x => x
  | .V_to_P, _, x => x

theorem toPlainMove_symm (j : Fin n) : (D : Direction) → (hD : pSpec.dir j = D) →
    (y : pSpec.«Type» j) →
    toPlainMove j D hD ((oracleMoveEquiv pSpec j D hD).symm y) = (plainMoveEquiv D _).symm y
  | .P_to_V, _, _ => rfl
  | .V_to_P, _, _ => rfl

/-- The oracle-tree challenge node of a plain-tree challenge node from round `k`. -/
def toOracleNode : (k m : ℕ) → (h : k + m = n) → ChallengeNode plainSig (suffix pSpec k m h) →
    ChallengeNode oracleSig (oracleSuffix pSpec k m h)
  | _, 0, _, c => c.val.elim
  | _, _ + 1, _, ⟨.inl u, hc⟩ => ⟨.inl u, oracle_owner_of_dir (dir_eq_of_owner hc)⟩
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩ =>
    ⟨.inr ⟨oracleBranch ⟨k, by omega⟩ _ rfl, (toOracleNode (k + 1) m _ ⟨c, hc⟩).val⟩,
      (toOracleNode (k + 1) m _ ⟨c, hc⟩).property⟩

/-- The move at an oracle-tree challenge node as the move at its plain-tree node. -/
def nodeMove : (k m : ℕ) → (h : k + m = n) → (c : ChallengeNode plainSig (suffix pSpec k m h)) →
    challengeSpec oracleSig (oracleSuffix pSpec k m h) (toOracleNode k m h c) →
      challengeSpec plainSig (suffix pSpec k m h) c
  | _, 0, _, c => c.val.elim
  | k, _ + 1, _, ⟨.inl _, _⟩ => toPlainMove ⟨k, by omega⟩ _ rfl
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩ => nodeMove (k + 1) m _ ⟨c, hc⟩

/-- Reading a legacy challenge at the oracle node is reading it at the plain node. -/
theorem map_oracleLegacyDraw {M : Type → Type} [Functor M] [LawfulFunctor M]
    (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) :
    (k m : ℕ) → (h : k + m = n) → (c : ChallengeNode plainSig (suffix pSpec k m h)) →
    nodeMove k m h c <$> oracleLegacyDraw src k m h (toOracleNode k m h c) =
      legacyDraw src k m h c
  | _, 0, _, c => c.val.elim
  | k, _ + 1, _, ⟨.inl _, _⟩ => by
    simp only [oracleLegacyDraw, legacyDraw, Layout.draw, Functor.map_map]
    exact congrArg (· <$> _) (funext fun y => toPlainMove_symm ⟨k, by omega⟩ _ rfl y)
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩ => map_oracleLegacyDraw src (k + 1) m _ ⟨c, hc⟩

/-! ### The sampler -/

theorem oracle_sampler_payload {M : Type → Type} [Monad M] [LawfulMonad M] (j : Fin n)
    (hD : pSpec.dir j = .P_to_V) (rest : OracleProtocol.{0})
    (draw : (c : ChallengeNode oracleSig
        (.liftBind (oraclePos pSpec j .P_to_V hD) fun _ => rest)) →
      M (challengeSpec oracleSig (.liftBind (oraclePos pSpec j .P_to_V hD) fun _ => rest) c)) :
    sampler oracleSig (.liftBind (oraclePos pSpec j .P_to_V hD) fun _ => rest) draw =
      pure (fun _ => sampler oracleSig rest (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)) := by
  change Choice.map .counterpart .sender _ <$> pure _ = _
  erw [LawfulApplicative.map_pure]
  rfl

theorem oracle_sampler_challenge {M : Type → Type} [Monad M] [LawfulMonad M] (j : Fin n)
    (hD : pSpec.dir j = .V_to_P) (rest : OracleProtocol.{0})
    (draw : (c : ChallengeNode oracleSig
        (.liftBind (oraclePos pSpec j .V_to_P hD) fun _ => rest)) →
      M (challengeSpec oracleSig (.liftBind (oraclePos pSpec j .V_to_P hD) fun _ => rest) c)) :
    sampler oracleSig (.liftBind (oraclePos pSpec j .V_to_P hD) fun _ => rest) draw =
      (fun x => ⟨x, sampler oracleSig rest (fun c => draw ⟨.inr ⟨⟨⟩, c.val⟩, c.property⟩)⟩) <$>
        draw ⟨.inl ⟨⟩, rfl⟩ := by
  change Choice.map .counterpart .receiver _ <$> (_ <$> _) = _
  erw [Functor.map_map]
  rfl

/-- One node of the sampler commutes with the transport. -/
theorem sampler_node_toPlain {M : Type → Type} [Monad M] [LawfulMonad M] (j : Fin n)
    (D : Direction) (hD : pSpec.dir j = D) (restO : OracleProtocol.{0}) (restP : Protocol.{0})
    (drawO : (c : ChallengeNode oracleSig (.liftBind (oraclePos pSpec j D hD) fun _ => restO)) →
      M (challengeSpec oracleSig (.liftBind (oraclePos pSpec j D hD) fun _ => restO) c))
    (drawP : (c : ChallengeNode plainSig
        (.liftBind (plainPos D (pSpec.«Type» j)) fun _ => restP)) →
      M (challengeSpec plainSig (.liftBind (plainPos D (pSpec.«Type» j)) fun _ => restP) c))
    (T : Move plainSig (plainPos D (pSpec.«Type» j)) →
      Counterpart oracleSig M restO (fun _ => PUnit) →
        Counterpart plainSig M restP (fun _ => PUnit))
    (hroot : ∀ hc hc', drawP ⟨.inl ⟨⟩, hc⟩ = toPlainMove j D hD <$> drawO ⟨.inl ⟨⟩, hc'⟩)
    (hrest : ∀ x, T x (sampler oracleSig restO
        (fun c => drawO ⟨.inr ⟨oracleBranch j D hD, c.val⟩, c.property⟩)) =
      sampler plainSig restP (fun c => drawP ⟨.inr ⟨plainSig.toFunB _ x, c.val⟩, c.property⟩)) :
    toPlainChoice .counterpart j D hD (fun x q => T x q) <$>
        sampler oracleSig (.liftBind (oraclePos pSpec j D hD) fun _ => restO) drawO =
      sampler plainSig (.liftBind (plainPos D (pSpec.«Type» j)) fun _ => restP) drawP := by
  cases D with
  | P_to_V =>
    rw [oracle_sampler_payload]
    erw [sampler_message]
    erw [LawfulApplicative.map_pure]
    exact congrArg pure (funext fun x => hrest x)
  | V_to_P =>
    rw [oracle_sampler_challenge]
    erw [sampler_challenge, hroot _ rfl, Functor.map_map, Functor.map_map]
    exact congrArg (· <$> _) (funext fun x => congrArg (Sigma.mk x) (hrest x))

/-- **The sampler commutes with the transport.** The transported oracle sampler is the plain
sampler that draws at each plain node what the oracle sampler draws at its oracle node. -/
theorem toPlainFrom_sampler {M : Type → Type} [Monad M] [LawfulMonad M] :
    (k m : ℕ) → (h : k + m = n) →
    (drawO : (c : ChallengeNode oracleSig (oracleSuffix pSpec k m h)) →
      M (challengeSpec oracleSig (oracleSuffix pSpec k m h) c)) →
    toPlainFrom .counterpart k m h (sampler oracleSig (oracleSuffix pSpec k m h) drawO) =
      sampler plainSig (suffix pSpec k m h)
        (fun c => nodeMove k m h c <$> drawO (toOracleNode k m h c))
  | _, 0, _, _ => rfl
  | k, m + 1, h, drawO => by
    rw [toPlainFrom_succ]
    exact sampler_node_toPlain ⟨k, by omega⟩ _ rfl (oracleSuffix pSpec (k + 1) m (by omega))
      (suffix pSpec (k + 1) m (by omega)) drawO
      (fun c => nodeMove k (m + 1) h c <$> drawO (toOracleNode k (m + 1) h c))
      (fun _ q => toPlainFrom .counterpart (k + 1) m (by omega) q) (fun _ _ => rfl)
      (fun _ => toPlainFrom_sampler (k + 1) m (by omega) _)

/-- The transported legacy sampler of the oracle tree is the legacy sampler of the plain tree. -/
theorem toPlainFrom_oracleLegacySampler {M : Type → Type} [Monad M] [LawfulMonad M]
    (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) :
    toPlainFrom .counterpart 0 n (Nat.zero_add n) (oracleLegacySampler pSpec src) =
      legacySampler pSpec src := by
  rw [toPlainFrom_sampler]
  exact congrArg _ (funext fun c => map_oracleLegacyDraw src 0 n _ c)

/-! ### The honest prover -/

section Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}

/-- The plain round slot is the transported oracle round slot. -/
theorem roundSlot_eq_map (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n) :
    (D : Direction) → (hD : pSpec.dir j = D) → (st : P.PrvState j.castSucc) →
    roundSlot P j D hD st =
      toPlainChoice .focal j D hD (fun _ s => s) <$> oracleRoundSlot P j D hD st
  | .P_to_V, _, _ => by
    simp only [roundSlot, oracleRoundSlot]
    erw [Functor.map_map]
    rfl
  | .V_to_P, _, _ => (id_map _).symm

/-- The transported embedded oracle prover is the embedded plain prover. -/
theorem toPlainFrom_embedOracleFrom (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (k m : ℕ) → (h : k + m = n) → (st : P.PrvState ⟨k, by omega⟩) →
    toPlainFrom .focal k m h (embedOracleFrom P k m h st) = embedFrom P k m h st
  | _, 0, _, _ => rfl
  | k, m + 1, h, st => by
    have hk : k < n := by omega
    have hk' : k + 1 + m = n := by omega
    change toPlainChoice .focal ⟨k, hk⟩ _ rfl
        (fun _ q => toPlainFrom .focal (k + 1) m hk' q) <$>
          (Choice.map .focal _ (fun _ st' => embedOracleFrom P (k + 1) m hk' st') <$>
            oracleRoundSlot P ⟨k, hk⟩ (pSpec.dir ⟨k, hk⟩) rfl st) =
        Choice.map .focal _ (fun _ st' => embedFrom P (k + 1) m hk' st') <$>
          roundSlot P ⟨k, hk⟩ (pSpec.dir ⟨k, hk⟩) rfl st
    rw [Functor.map_map, roundSlot_eq_map, Functor.map_map]
    refine congrArg (· <$> _) (funext fun v => ?_)
    erw [toPlainChoice_map, map_toPlainChoice]
    exact congrArg (fun f => toPlainChoice .focal ⟨k, hk⟩ _ rfl f v)
      (funext fun _ => funext fun st' => toPlainFrom_embedOracleFrom P (k + 1) m hk' st')

end Prover

/-! ### The legacy transcript of an oracle run -/

section Transcript

omit Oₘ in
theorem decodeFrom_succ {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly.{0})
    (pos : Fin n → P.A) (e : (j : Fin n) → Move l (pos j) ≃ pSpec.«Type» j) (k m : ℕ)
    (h : k + (m + 1) = n) (pre : Transcript ⟨k, by omega⟩ pSpec) (d : Move l (pos ⟨k, by omega⟩))
    (rest : PathAlong l (chain pos (k + 1) m (by omega))) :
    decodeFrom l pos e k (m + 1) h pre ⟨d, rest⟩ =
      decodeFrom l pos e (k + 1) m (by omega)
        (Transcript.concat (m := ⟨k, by omega⟩) (e ⟨k, by omega⟩ d) pre) rest := rfl

omit Oₘ in
/-- The round read at a node is its move. -/
theorem decodeFrom_succ_self {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly.{0})
    (pos : Fin n → P.A) (e : (j : Fin n) → Move l (pos j) ≃ pSpec.«Type» j) (k m : ℕ)
    (h : k + (m + 1) = n) (pre : Transcript ⟨k, by omega⟩ pSpec) (d : Move l (pos ⟨k, by omega⟩))
    (rest : PathAlong l (chain pos (k + 1) m (by omega))) :
    decodeFrom l pos e k (m + 1) h pre ⟨d, rest⟩ ⟨k, by omega⟩ = e ⟨k, by omega⟩ d := by
  rw [decodeFrom_succ, decodeFrom_lt l pos e (k + 1) m (by omega) _ rest ⟨k, by omega⟩ (by simp)]
  exact eq_of_heq (Transcript.concat_apply_last (m := ⟨k, by omega⟩) pre _ k rfl _)

theorem toOracleMove_symm (j : Fin n) : (D : Direction) → (hD : pSpec.dir j = D) →
    (y : pSpec.«Type» j) →
    toOracleMove j D hD ((plainMoveEquiv D _).symm y) = (oracleMoveEquiv pSpec j D hD).symm y
  | .P_to_V, _, _ => rfl
  | .V_to_P, _, _ => rfl

theorem toOraclePath_encodeFrom (T : FullTranscript pSpec) : (k m : ℕ) → (h : k + m = n) →
    toOraclePath k m h
        (encodeFrom plainSig (plainRound pSpec) (fun _ => plainMoveEquiv _ _) T k m h) =
      encodeFrom oracleSig (oracleRound pSpec) (fun j => oracleMoveEquiv pSpec j _ rfl) T k m h
  | _, 0, _ => rfl
  | k, m + 1, h => by
    simp only [encodeFrom, toOraclePath]
    rw [toOracleMove_symm, toOraclePath_encodeFrom T (k + 1) m]

/-- **The oracle path of a plain run decodes to the same legacy transcript.** -/
theorem oracleDecode_toOraclePath (tr : PathAlong plainSig (protocol pSpec)) :
    oracleDecode pSpec (toOraclePath 0 n (Nat.zero_add n) tr) = decode pSpec tr := by
  have htr : tr = encodeFrom plainSig (plainRound pSpec) (fun _ => plainMoveEquiv _ _)
      (decode pSpec tr) 0 n (Nat.zero_add n) := ((transcriptEquiv pSpec).left_inv tr).symm
  conv_lhs => rw [htr]
  rw [toOraclePath_encodeFrom]
  exact (oracleTranscriptEquiv pSpec).right_inv _

theorem viewChallenge_eraseOracle (j : Fin n) : (D : Direction) → (hD : pSpec.dir j = D) →
    (hV : D = .V_to_P) → (d : Move oracleSig (oraclePos pSpec j D hD)) →
    viewChallenge j D hD hV (eraseOracle.map _ d) = oracleMoveEquiv pSpec j D hD d
  | .V_to_P, _, _, _ => rfl

omit Oₘ in
theorem mapMoves_chain_succ {P : PFunctor.{1, 0}} {l l' : PFunctor.Lens P rolePoly.{0}}
    (g : PathAlong.MoveMap l l') (pos : Fin n → P.A) (k m : ℕ) (h : k + (m + 1) = n)
    (d : Move l (pos ⟨k, by omega⟩)) (rest : PathAlong l (chain pos (k + 1) m (by omega))) :
    PathAlong.mapMoves g (chain pos k (m + 1) h) ⟨d, rest⟩ =
      ⟨g.map _ d, PathAlong.mapMoves g (chain pos (k + 1) m (by omega)) rest⟩ := rfl

/-- The challenges of the verifier's view of a path from round `k` are the decoded ones. -/
theorem viewChallenge_decodeFrom : (k m : ℕ) → (h : k + m = n) →
    (preV : Transcript ⟨k, by omega⟩ (viewSpec pSpec)) → (pre : Transcript ⟨k, by omega⟩ pSpec) →
    (tr : PathAlong oracleSig (oracleSuffix pSpec k m h)) → (i : pSpec.ChallengeIdx) →
    k ≤ i.1.val →
    viewChallenge i.1 _ rfl i.2 (decodeFrom viewSig (oracleRound pSpec) (fun _ => Equiv.refl _)
        k m h preV (PathAlong.mapMoves eraseOracle _ tr) i.1) =
      decodeFrom oracleSig (oracleRound pSpec) (fun j => oracleMoveEquiv pSpec j _ rfl)
        k m h pre tr i.1
  | k, 0, h, _, _, _, i, hi => absurd i.1.isLt (by omega)
  | k, m + 1, h, preV, pre, ⟨d, tr⟩, i, hi => by
    rw [mapMoves_chain_succ]
    by_cases hik : i.1.val = k
    · obtain ⟨⟨iv, hiv⟩, hdir⟩ := i
      simp only at hik
      subst hik
      rw [decodeFrom_succ_self, decodeFrom_succ_self]
      exact viewChallenge_eraseOracle _ _ rfl hdir d
    · rw [decodeFrom_succ, decodeFrom_succ]
      exact viewChallenge_decodeFrom (k + 1) m (by omega) _ _ tr i (by omega)

/-- **The verifier's view of an oracle run carries its legacy challenges.** -/
theorem viewChallenges_toView (tr : PathAlong oracleSig (oracleProtocol pSpec)) :
    viewChallenges (toView _ tr).val = (oracleDecode pSpec tr).challenges :=
  funext fun i => viewChallenge_decodeFrom 0 n _ default default tr i (Nat.zero_le _)

/-- One node of the message reader reads the decoded transcript. -/
theorem readMsgNode_decode (j : Fin n) (D : Direction) (hD : pSpec.dir j = D)
    (rest : OracleProtocol.{0})
    (recur : (p : Path rest) → (∀ o, OracleData rest p o) → (i : pSpec.MessageIdx) →
      j.val < i.1.val → pSpec.Message i)
    (x : Move oracleSig (oraclePos pSpec j D hD)) (tr : PathAlong oracleSig rest)
    (T : FullTranscript pSpec) (hhead : T j = oracleMoveEquiv pSpec j D hD x)
    (hrec : ∀ i hi, recur (projectPathAlong oracleSig rest tr) (payloads rest tr) i hi = T i.1) :
    ∀ i hi, readMsgNode j rest recur D hD
        (projectPathAlong oracleSig (.liftBind (oraclePos pSpec j D hD) fun _ => rest) ⟨x, tr⟩)
        (payloads (.liftBind (oraclePos pSpec j D hD) fun _ => rest) ⟨x, tr⟩) i hi = T i.1 := by
  cases D with
  | P_to_V =>
    intro i hi
    by_cases hij : i.1.val = j.val
    · obtain ⟨⟨iv, hiv⟩, hdir⟩ := i
      obtain ⟨jv, hjv⟩ := j
      simp only at hij
      subst hij
      exact (dite_eq_left (rfl : iv = iv)).trans hhead.symm
    · exact (dite_eq_right hij).trans (hrec i _)
  | V_to_P => exact fun i _ => hrec i _

/-- The messages held by the oracle data of a path from round `k` are the decoded ones. -/
theorem readMsg_decodeFrom : (k m : ℕ) → (h : k + m = n) → (pre : Transcript ⟨k, by omega⟩ pSpec) →
    (tr : PathAlong oracleSig (oracleSuffix pSpec k m h)) → (i : pSpec.MessageIdx) →
    (hi : k ≤ i.1.val) →
    readMsg k m h (projectPathAlong oracleSig _ tr) (payloads _ tr) i hi =
      decodeFrom oracleSig (oracleRound pSpec) (fun j => oracleMoveEquiv pSpec j _ rfl)
        k m h pre tr i.1
  | k, 0, h, _, _, i, hi => absurd i.1.isLt (by omega)
  | k, m + 1, h, pre, ⟨x, tr⟩, i, hi =>
    readMsgNode_decode ⟨k, by omega⟩ _ rfl _ _ x tr _
      (decodeFrom_succ_self oracleSig (oracleRound pSpec) _ k m h pre x tr)
      (fun i hi => readMsg_decodeFrom (k + 1) m (by omega) _ tr i hi) i hi

/-- **The oracle data of an oracle run carries its legacy messages.** -/
theorem pathMessages_payloads (tr : PathAlong oracleSig (oracleProtocol pSpec)) :
    pathMessages (projectPathAlong oracleSig _ tr) (payloads _ tr) =
      (oracleDecode pSpec tr).messages :=
  funext fun i => readMsg_decodeFrom 0 n _ default tr i (Nat.zero_le _)

end Transcript

/-! ### The decision of an embedded oracle verifier -/

section Decision

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface.{0, 0} (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface.{0, 0} (OStmtOut i)]

/-- Routing the legacy decision's queries to the oracle family of a path and answering them from
concrete data is legacy `simOracle2` on the input data and the path's messages. The ambient
queries go to any implementation `amb`: plain, stateful or logging. -/
theorem simulateQ_decisionImpl {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl oSpec m) (p : Path (oracleProtocol pSpec))
    (r : (pathResources (family OStmtIn) (oracleProtocol pSpec) p).Data) {α : Type}
    (x : OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ)) α) :
    simulateQ (QueryImpl.addLift amb
        ((pathResources (family OStmtIn) (oracleProtocol pSpec) p).answer r))
        (simulateQ (decisionImpl p) x) =
      simulateQ amb (simulateQ (OracleInterface.simOracle2 (T₁ := OStmtIn) (T₂ := pSpec.Message)
        oSpec r.1 (pathMessages p r.2)) x) := by
  have key : ∀ t, simulateQ (QueryImpl.addLift amb
        ((pathResources (family OStmtIn) (oracleProtocol pSpec) p).answer r))
        (decisionImpl p t) =
      simulateQ amb (OracleInterface.simOracle2 (T₁ := OStmtIn) (T₂ := pSpec.Message)
        oSpec r.1 (pathMessages p r.2) t) := by
    rintro (q | q)
    · simp only [decisionImpl, QueryImpl.addLift_def, QueryImpl.add_apply_inl,
        OracleInterface.simOracle2, QueryImpl.liftTarget_apply, QueryImpl.id_apply,
        QueryImpl.liftTarget_self]
      refine (QueryImpl.simulateQ_add_query_left amb (QueryImpl.liftTarget m
        ((pathResources (family OStmtIn) (oracleProtocol pSpec) p).answer r)) q).trans ?_
      rw [simulateQ_spec_query]
    · simp only [QueryImpl.addLift_def, OracleInterface.simOracle2, QueryImpl.liftTarget_self]
      change simulateQ _ (simulateQ (fun t => liftM
          ((oSpec + (pathResources (family OStmtIn) (oracleProtocol pSpec) p).spec).query
            (.inr t))) (resourceImpl p q)) = _
      rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
        (impl := ((pathResources (family OStmtIn) (oracleProtocol pSpec) p).answer r).liftTarget m)
          (fun t => QueryImpl.simulateQ_add_query_right _ _ t),
        simulateQ_liftTarget, resourceImpl_law]
      change pure _ = simulateQ amb (pure _)
      rw [simulateQ_pure]
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply key x]
  exact (QueryImpl.simulateQ_simulateQ_eq_of_apply (fun _ => rfl) x).symm

end Decision

/-! ### Running the oracle tree -/

section Run

variable {ι : Type} {oSpec : OracleSpec ι}

/-- Answer the challenge queries of the oracle tree with the legacy challenge oracle. -/
abbrev oracleChallengeReindex (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface.{0, 0} (pSpec.Message i)] :
    QueryImpl (oSpec + challengeSpec oracleSig (oracleProtocol pSpec))
      (OracleComp (oSpec + [pSpec.Challenge]ₒ)) :=
  (oracleLayout pSpec).challengeReindex oSpec

/-- The challenge implementation of the oracle tree induced by a legacy challenge
implementation. -/
abbrev oracleChallengeImpl (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp) :
    QueryImpl (challengeSpec oracleSig (oracleProtocol pSpec)) ProbComp :=
  (oracleLayout pSpec).challengeImpl chImpl

/-- Read an observation of the plain tree as an observation of the oracle tree. -/
def toOracleObservation {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type} {T : Type}
    (r : Observation plainSig (protocol pSpec) (fun tr => Out (toOraclePath 0 n _ tr))
      (fun _ => T)) :
    Observation oracleSig (oracleProtocol pSpec) Out (fun _ => T) :=
  ⟨toOraclePath 0 n (Nat.zero_add n) r.1, r.2.1, r.2.2⟩

/-- **A run of the oracle tree is a run of the plain tree.** Against the legacy sampler, the
run of a simulated prover on the oracle tree is the run of its transport on the plain tree,
with the runtime path read back on the oracle tree. -/
theorem runWith_oracleLegacySampler {κ : Type} {spec : OracleSpec κ}
    (F : QueryImpl oSpec (OracleComp spec)) (order : Schedule)
    {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out)
    (src : (i : pSpec.ChallengeIdx) → OracleComp spec (pSpec.Challenge i)) :
    runWith order (oracleProtocol pSpec) (p.simulate F) (oracleLegacySampler pSpec src) =
      (fun r : (tr : PathAlong plainSig (protocol pSpec)) × Out (toOraclePath 0 n _ tr) × PUnit =>
        (⟨toOraclePath 0 n _ r.1, r.2.1, r.2.2⟩ :
          (tr : PathAlong oracleSig (oracleProtocol pSpec)) × Out tr × PUnit)) <$>
        runWith order (protocol pSpec) (Prover.simulate F (toPlainFrom .focal 0 n _ p))
          (legacySampler pSpec src) := by
  rw [runWith_toPlainFrom, toPlainFrom_simulate, toPlainFrom_oracleLegacySampler]

/-- The prover-sampler run of the oracle tree, with its queries reindexed, is the focal-first
run against the legacy sampler. -/
theorem simulateQ_oracleChallengeReindex_run
    {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) :
    simulateQ (oracleChallengeReindex oSpec pSpec) (TwoParty.Lens.run (oracleProtocol pSpec)
      (p.simulate (fun q => liftM
        ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query (.inl q))))
      (sampler oracleSig (oracleProtocol pSpec) (fun c =>
        liftM ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query (.inr c))))) =
      runWith .focalFirst (oracleProtocol pSpec) (p.simulate (liftShared oSpec pSpec))
        (oracleLegacySampler pSpec (challengeOracle oSpec pSpec)) := by
  have hl : (fun q => simulateQ (oracleChallengeReindex oSpec pSpec)
      (liftM ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query (.inl q)))) =
      liftShared oSpec pSpec :=
    funext fun q => QueryImpl.simulateQ_add_liftM_query_left _ _ q
  have hr : (fun c => simulateQ (oracleChallengeReindex oSpec pSpec)
      (nodeMove 0 n _ c <$> liftM ((oSpec + challengeSpec oracleSig (oracleProtocol pSpec)).query
        (.inr (toOracleNode 0 n _ c))))) =
      legacyDraw (challengeOracle oSpec pSpec) 0 n (Nat.zero_add n) := by
    refine funext fun c => ?_
    rw [simulateQ_map]
    erw [QueryImpl.simulateQ_add_liftM_query_right]
    exact map_oracleLegacyDraw _ 0 n _ c
  rw [TwoParty.Lens.run, runWith_toPlainFrom, simulateQ_map, toPlainFrom_simulate,
    toPlainFrom_sampler, simulateQ_runWith, simulate_simulate, hl, hr,
    runWith_oracleLegacySampler]
  rfl

variable {I S : Type} {T : Path (oracleProtocol pSpec) → Type} {A : I → Type}
  {J : Path (oracleProtocol pSpec) → Type} {B : (p : Path (oracleProtocol pSpec)) → J p → Type}
  {inputs : OracleFamily I A}
  {outputs : (p : Path (oracleProtocol pSpec)) → OracleFamily (J p) (B p)}

/-- Run an oracle verifier on the oracle tree of a legacy protocol under `order`, in the legacy
query monad. The prover runs against the legacy sampler; the decision and the output map read
the input data and the payloads of the actual run, as in `Core.OracleVerifier.run`. -/
def oracleObserveWith (order : Schedule)
    (V : Core.OracleVerifier oSpec (oracleProtocol pSpec) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) :
    OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (Observation oracleSig (oracleProtocol pSpec) Out (Core.OracleVerifier.Output T B)) := do
  let r ← runWith order (oracleProtocol pSpec) (p.simulate (liftShared oSpec pSpec))
    (oracleLegacySampler pSpec (challengeOracle oSpec pSpec))
  let pp := projectPathAlong oracleSig (oracleProtocol pSpec) r.1
  let view := toView (oracleProtocol pSpec) r.1
  let resources : (pathResources inputs (oracleProtocol pSpec) pp).Data :=
    (data, payloads (oracleProtocol pSpec) r.1)
  let verdict ← simulateQ (QueryImpl.addLift (liftShared oSpec pSpec)
    ((pathResources inputs (oracleProtocol pSpec) pp).answer resources))
    (V.decide stmt pp view).run
  pure ⟨r.1, r.2.1, verdict.map fun t => (t, (V.outputMap stmt pp view).f resources)⟩

/-- **Challenge reindexing of an oracle run.** The run of an oracle verifier on a legacy
protocol's oracle tree, with its challenges answered by the legacy challenge oracle, is the
focal-first oracle observation. -/
theorem simulateQ_oracleVerifier_run
    (V : Core.OracleVerifier oSpec (oracleProtocol pSpec) S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) :
    simulateQ (oracleChallengeReindex oSpec pSpec) (V.run stmt data p) =
      oracleObserveWith .focalFirst V stmt data p := by
  rw [Core.OracleVerifier.run, oracleObserveWith, simulateQ_bind,
    simulateQ_oracleChallengeReindex_run]
  refine bind_congr fun r => ?_
  rcases r with ⟨tr, out, u⟩
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  congr 1
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) _
  rcases t with q | q
  · simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self]
    exact QueryImpl.simulateQ_add_liftM_query_left _ _ q
  · simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, QueryImpl.add_apply_inr,
      QueryImpl.liftTarget_apply]
    change simulateQ _ (pure _) = pure _
    rw [simulateQ_pure]

end Run

/-! ### Execution of an embedded legacy oracle reduction -/

section Embedded

variable {ι : Type} {oSpec : OracleSpec ι} [∀ t, Inhabited (oSpec.Range t)]
  {StmtIn WitIn StmtOut WitOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface.{0, 0} (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface.{0, 0} (OStmtOut i)]

omit [∀ t, Inhabited (oSpec.Range t)] Oₘ in
private theorem map_bind_map_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}
    (x : m α) (h : α → β) (k : β → γ) (f : γ → δ) :
    f <$> ((h <$> x) >>= fun v => pure (k v)) = x >>= fun a => pure (f (k (h a))) := by
  simp

omit [∀ t, Inhabited (oSpec.Range t)] Oₘ in
theorem liftComp_eq_simulateQ_liftShared {α : Type} (x : OracleComp oSpec α) :
    liftComp x (oSpec + [pSpec.Challenge]ₒ) = simulateQ (liftShared oSpec pSpec) x := rfl

/-- The common result of an oracle run: forget a rejected run, and decode the transcript of an
accepted one. The result keeps the prover's output statement, output oracle data and witness, and
the verifier's output statement and output oracle data. -/
def oracleFinalize
    (r : Observation oracleSig (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i))) :
    LegacyResult pSpec (StmtOut × (∀ i, OStmtOut i)) WitOut :=
  r.2.2.map fun t => ((oracleDecode pSpec r.1, r.2.1), t)

omit [∀ t, Inhabited (oSpec.Range t)] Oₛₒ in
theorem oracleFinalize_toOracleObservation
    (r : Observation plainSig (protocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) (fun _ => StmtOut × (∀ i, OStmtOut i))) :
    oracleFinalize (toOracleObservation (Out := fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut)
      r) = finalize r := by
  simp only [oracleFinalize, toOracleObservation, finalize, oracleDecode_toOraclePath]

/-- The decision of the embedded oracle verifier on the actual payloads of a run is legacy
`verify` on the decoded challenges, with message and input-oracle queries answered from the
decoded messages and the input data. The ambient queries go to any implementation `amb`. -/
theorem simulateQ_embedOracleVerifier_decide {m : Type → Type} [Monad m] [LawfulMonad m]
    (amb : QueryImpl oSpec m)
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) (tr : PathAlong oracleSig (oracleProtocol pSpec)) :
    simulateQ (QueryImpl.addLift amb
        ((pathResources (family OStmtIn) _ (projectPathAlong oracleSig _ tr)).answer
          (oStmt, payloads _ tr)))
        ((embedOracleVerifier V).decide stmt (projectPathAlong oracleSig _ tr)
          (toView _ tr)).run =
      simulateQ amb
        (simulateQ (OracleInterface.simOracle2 oSpec oStmt (oracleDecode pSpec tr).messages)
          (V.verify stmt (oracleDecode pSpec tr).challenges).run) := by
  refine (simulateQ_decisionImpl amb _ (oStmt, payloads _ tr) _).trans ?_
  rw [viewChallenges_toView]
  exact congrArg (fun m => simulateQ amb
    (simulateQ (OracleInterface.simOracle2 oSpec oStmt m)
      (V.verify stmt (oracleDecode pSpec tr).challenges).run)) (pathMessages_payloads tr)

/-- The output data of the embedded oracle verifier on the actual payloads of a run are the
legacy materialized output on the decoded transcript. -/
theorem embedOracleVerifier_outputMap_f
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) (tr : PathAlong oracleSig (oracleProtocol pSpec)) :
    ((embedOracleVerifier V).outputMap stmt (projectPathAlong oracleSig _ tr) (toView _ tr)).f
        (oStmt, payloads _ tr) =
      V.materializeOutput (oracleDecode pSpec tr).challenges oStmt
        (oracleDecode pSpec tr).messages := by
  change V.materializeOutput (viewChallenges (toView _ tr).val) oStmt
    (pathMessages _ (payloads _ tr)) = _
  rw [viewChallenges_toView, pathMessages_payloads]

/-- **Oracle execution as plain execution.** Under every schedule, the oracle observation of
the embedded oracle verifier is the plain observation of the legacy verifier read as a plain
verifier (`OracleVerifier.toVerifier`), against the transported prover, with the runtime path
read back on the oracle tree. -/
theorem oracleObserveWith_embed (order : Schedule)
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) :
    oracleObserveWith order (embedOracleVerifier V) stmt oStmt p =
      toOracleObservation <$> observeWith order (embedVerifier V.toVerifier) (stmt, oStmt)
        (toPlainFrom .focal 0 n (Nat.zero_add n) p) := by
  rw [oracleObserveWith, runWith_oracleLegacySampler, observeWith, bind_map_left]
  refine Eq.trans ?_ (map_bind (m := OracleComp (oSpec + [pSpec.Challenge]ₒ)) _ _ _).symm
  refine bind_congr fun r => ?_
  dsimp only
  erw [simulateQ_embedOracleVerifier_decide]
  rw [embedOracleVerifier_outputMap_f]
  simp only [oracleDecode_toOraclePath, embedVerifier_decide]
  change _ = toOracleObservation <$> (liftComp (Option.map _ <$> simulateQ _ _) _ >>= _)
  rw [liftComp_eq_simulateQ_liftShared, simulateQ_map]
  exact (map_bind_map_pure (m := OracleComp (oSpec + [pSpec.Challenge]ₒ))
    (simulateQ (liftShared oSpec pSpec)
      (simulateQ (OracleInterface.simOracle2 oSpec oStmt (decode pSpec r.1).messages)
        (V.verify stmt (decode pSpec r.1).challenges).run))
    (Option.map fun s => (s, V.materializeOutput (decode pSpec r.1).challenges oStmt
      (decode pSpec r.1).messages))
    (fun v => (⟨r.1, r.2.1, v⟩ : Observation plainSig (protocol pSpec)
      (fun tr => Out (toOraclePath 0 n (Nat.zero_add n) tr))
      (fun _ => StmtOut × (∀ i, OStmtOut i))))
    toOracleObservation).symm

omit [∀ t, Inhabited (oSpec.Range t)] Oₛᵢ Oₛₒ in
/-- The transported embedded oracle prover is the embedded plain prover of the same legacy
prover, started on the input statement paired with its oracle data. -/
theorem toPlainFrom_embedOracleProver {WitIn WitOut : Type}
    (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    toPlainFrom .focal 0 n (Nat.zero_add n) (embedOracleProver P stmt oStmt wit) =
      embedProver P (stmt, oStmt) wit :=
  toPlainFrom_embedOracleFrom P 0 n (Nat.zero_add n) _

/-- **Execution correspondence for oracle reductions.** Under the counterpart-first schedule,
the finalized oracle observation of the embedded oracle reduction is the legacy oracle
reduction's execution. The legacy layer's transcript is decoded from the runtime path of the
oracle tree; the output statement and output oracle data are the oracle verifier's
`decide` result and output map. -/
theorem oracleFinalize_observeWith_counterpartFirst
    {WitIn WitOut : Type}
    (R : _root_.OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    oracleFinalize <$> oracleObserveWith .counterpartFirst (embedOracleVerifier R.verifier) stmt
        oStmt (embedOracleProver R.prover stmt oStmt wit) = (R.run stmt oStmt wit).run := by
  rw [oracleObserveWith_embed, toPlainFrom_embedOracleProver,
    _root_.OracleReduction.run_eq_run_reduction,
    ← finalize_observeWith_counterpartFirst R.toReduction (stmt, oStmt) wit]
  refine (comp_map (f := OracleComp (oSpec + [pSpec.Challenge]ₒ))
    (toOracleObservation (Out := fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut))
    oracleFinalize _).symm.trans ?_
  exact congrArg (· <$> _) (funext fun r => oracleFinalize_toOracleObservation r)

omit [∀ t, Inhabited (oSpec.Range t)] in
/-- For the embedded honest oracle prover with pure challenge slots, the two schedules give the
same oracle observation. -/
theorem oracleObserveWith_focalFirst_eq [∀ t, Inhabited (oSpec.Range t)] {WitIn WitOut : Type}
    (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (hP : PureChallengeSlots P)
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    oracleObserveWith .focalFirst (embedOracleVerifier V) stmt oStmt
        (embedOracleProver P stmt oStmt wit) =
      oracleObserveWith .counterpartFirst (embedOracleVerifier V) stmt oStmt
        (embedOracleProver P stmt oStmt wit) := by
  rw [oracleObserveWith_embed, oracleObserveWith_embed, toPlainFrom_embedOracleProver]
  exact congrArg _ (observeWith_focalFirst_eq P hP _ (stmt, oStmt) wit)

/-- **Execution correspondence for oracle reductions as program equality.** When the honest
prover's challenge slots are pure, reindexing the challenges of the finalized run of the
embedded oracle verifier against the embedded oracle prover gives the legacy oracle reduction's
execution. -/
theorem simulateQ_oracleFinalize_run {WitIn WitOut : Type}
    (R : _root_.OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (hP : PureChallengeSlots R.prover) (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i)
    (wit : WitIn) :
    simulateQ (oracleChallengeReindex oSpec pSpec)
        (oracleFinalize <$> (embedOracleVerifier R.verifier).run stmt oStmt
          (embedOracleProver R.prover stmt oStmt wit)) =
      (R.run stmt oStmt wit).run := by
  rw [simulateQ_map, simulateQ_oracleVerifier_run, oracleObserveWith_focalFirst_eq _ hP]
  exact oracleFinalize_observeWith_counterpartFirst R stmt oStmt wit

/-- **Oracle execution as plain execution, reindexed.** Reindexing the challenges of a run of
the embedded oracle verifier gives the reindexed plain run of the legacy verifier read as a
plain verifier, against the transported prover, with the path read back on the oracle tree. -/
theorem simulateQ_embedOracleVerifier_run
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) :
    simulateQ (oracleChallengeReindex oSpec pSpec) ((embedOracleVerifier V).run stmt oStmt p) =
      toOracleObservation <$> simulateQ (challengeReindex oSpec pSpec)
        ((embedVerifier V.toVerifier).run (stmt, oStmt)
          (toPlainFrom .focal 0 n (Nat.zero_add n) p)) := by
  rw [simulateQ_oracleVerifier_run, oracleObserveWith_embed, simulateQ_verifier_run]

variable {σ : Type}

/-- **Oracle experiments as plain experiments.** Every statistic of the run of the embedded
oracle verifier, in the experiment with the reindexed legacy challenge implementation, is the
same statistic of the plain run of the legacy verifier read as a plain verifier, against the
transported prover. -/
theorem experiment_embedOracleVerifier_run (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) {β : Type}
    (f : Observation oracleSig (oracleProtocol pSpec) Out
      (fun _ => StmtOut × (∀ i, OStmtOut i)) → β) :
    experiment init impl (oracleChallengeImpl chImpl)
        (f <$> (embedOracleVerifier V).run stmt oStmt p) =
      experiment init impl (plainChallengeImpl chImpl)
        ((f ∘ toOracleObservation) <$>
          (embedVerifier V.toVerifier).run (stmt, oStmt)
            (toPlainFrom .focal 0 n (Nat.zero_add n) p)) := by
  rw [Layout.experiment_challengeReindex, experiment_challengeReindex, simulateQ_map,
    simulateQ_map]
  erw [simulateQ_embedOracleVerifier_run]
  exact congrArg (experiment init impl chImpl)
    (comp_map (f := OracleComp (oSpec + [pSpec.Challenge]ₒ)) toOracleObservation f _).symm

/-- The two schedules of the oracle observation of the embedded oracle verifier have the same
distribution from every shared state. -/
theorem distEqFrom_oracleObserveWith (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) :
    DistEqFrom impl chImpl (oracleObserveWith .focalFirst (embedOracleVerifier V) stmt oStmt p)
      (oracleObserveWith .counterpartFirst (embedOracleVerifier V) stmt oStmt p) := by
  rw [oracleObserveWith_embed, oracleObserveWith_embed]
  exact (distEqFrom_observeWith impl chImpl _ _ _).map _

/-- **Oracle observation transfer.** For every prover, the oracle observation under the
reindexed challenge implementation has the distribution of the counterpart-first oracle
observation. -/
theorem experiment_oracleVerifier_run_evalDistEq (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) (stmt : StmtIn)
    (oStmt : ∀ i, OStmtIn i) {Out : PathAlong oracleSig (oracleProtocol pSpec) → Type}
    (p : Core.Prover oracleSig oSpec (oracleProtocol pSpec) Out) {β : Type}
    (f : Observation oracleSig (oracleProtocol pSpec) Out
      (fun _ => StmtOut × (∀ i, OStmtOut i)) → β) :
    experiment init impl (oracleChallengeImpl chImpl)
        (f <$> (embedOracleVerifier V).run stmt oStmt p) =ᵈ
      experiment init impl chImpl
        (f <$> oracleObserveWith .counterpartFirst (embedOracleVerifier V) stmt oStmt p) := by
  rw [oracleChallengeImpl, Layout.experiment_challengeReindex, simulateQ_map,
    simulateQ_oracleVerifier_run]
  exact experiment_evalDistEq init impl chImpl
    ((distEqFrom_oracleObserveWith impl chImpl V stmt oStmt p).map f)

/-- **Execution correspondence for oracle reductions in distribution.** The finalized run of
the embedded oracle verifier against the embedded oracle prover, with challenges drawn by the
reindexed legacy challenge implementation, has the distribution of the legacy oracle reduction's
execution. -/
theorem experiment_oracleFinalize_run_evalDistEq {WitIn WitOut : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (R : _root_.OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    experiment init impl (oracleChallengeImpl chImpl)
        (oracleFinalize <$> (embedOracleVerifier R.verifier).run stmt oStmt
          (embedOracleProver R.prover stmt oStmt wit)) =ᵈ
      experiment init impl chImpl (R.run stmt oStmt wit).run := by
  rw [← oracleFinalize_observeWith_counterpartFirst]
  exact experiment_oracleVerifier_run_evalDistEq init impl chImpl _ stmt oStmt _ oracleFinalize

/-- **Execution correspondence for oracle reductions as measures.** -/
theorem evalDist_experiment_oracleFinalize_run {WitIn WitOut : Type}
    [MeasurableSpace (LegacyResult pSpec (StmtOut × (∀ i, OStmtOut i)) WitOut)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (chImpl : QueryImpl [pSpec.Challenge]ₒ ProbComp)
    (R : _root_.OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    𝒟[experiment init impl (oracleChallengeImpl chImpl)
        (oracleFinalize <$> (embedOracleVerifier R.verifier).run stmt oStmt
          (embedOracleProver R.prover stmt oStmt wit))] =
      𝒟[experiment init impl chImpl (R.run stmt oStmt wit).run] :=
  (experiment_oracleFinalize_run_evalDistEq init impl chImpl R stmt oStmt wit).evalDist_eq

end Embedded

end Interaction.Core.Legacy

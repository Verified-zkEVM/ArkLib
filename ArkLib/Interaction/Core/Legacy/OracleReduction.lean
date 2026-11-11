/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.Verifier
public import ArkLib.Interaction.Core.OracleVerifier

/-!
# Legacy oracle reductions on oracle trees

A legacy oracle reduction runs on the oracle tree of its protocol, where each prover message is
an oracle payload with its legacy query interface. This file embeds its two parties.

* The oracle prover is a legacy prover, embedded slot for slot as in `Legacy.Prover`.
* The oracle verifier's sampler draws legacy challenges, as for plain verifiers.
* The decision reads the challenges off the verifier's view and runs legacy `verify`. Its
  queries to input statement oracles and to prover messages become queries to the oracle family
  of the completed path.
* The output map has the legacy materialization as its data map `f`. Its query implementation is
  legacy `simulateOutputQuery`, which covers both legacy output representations. Its law is
  legacy `simulateOutputQuery_eq`.

The output query implementation of the interaction layer cannot query the shared oracles. Legacy
`simulateOutputQuery` is typed with access to them, but its law shows that no reachable query
uses them. `dropAmbient` removes those queries by answering them with a default value, so the
embedding assumes inhabited answer types of the shared oracles.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens OracleComp OracleSpec ProtocolSpec Oracle

/-! ### Removing unreachable ambient queries -/

section DropAmbient

variable {ι κ : Type} {oSpec : OracleSpec ι} {spec : OracleSpec κ}

/-- Answer each shared-oracle query with a default value, and keep the other queries. -/
def dropAmbient [∀ t, Inhabited (oSpec.Range t)] :
    QueryImpl (oSpec + spec) (OracleComp spec) :=
  QueryImpl.add (fun _ => pure default) (fun t => liftM (spec.query t))

/-- If a computation simulates to `pure x` while its shared-oracle queries are passed through,
then it reaches no shared-oracle query, so dropping them leaves the value `x`. -/
theorem simulateQ_dropAmbient_of_eq_pure [∀ t, Inhabited (oSpec.Range t)]
    (g : QueryImpl spec Id) {α : Type} (oa : OracleComp (oSpec + spec) α) (x : α)
    (h : simulateQ (QueryImpl.addLift (QueryImpl.id oSpec) g :
      QueryImpl (oSpec + spec) (OracleComp oSpec)) oa = pure x) :
    simulateQ g (simulateQ dropAmbient oa) = x := by
  induction oa using OracleComp.inductionOn generalizing x with
  | pure a =>
    simp only [simulateQ_pure] at h ⊢
    exact (OracleComp.pure_inj _ _).mp h
  | query_bind t k ih =>
    rcases t with t | t
    · simp only [simulateQ_bind, simulateQ_query, QueryImpl.addLift_def, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.id_apply] at h
      obtain ⟨_, h1, _⟩ := (OracleComp.bind_eq_pure_iff _ _ _).mp h
      exact absurd h1 (OracleComp.liftM_ne_pure _ _)
    · simp only [simulateQ_bind, simulateQ_query, QueryImpl.addLift_def, OracleQuery.cont_query,
        OracleQuery.input_query, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply] at h
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, dropAmbient] at h ⊢
      simp only [OracleComp.bind_eq_pure_iff] at h
      obtain ⟨y, hy, hk⟩ := h
      have hgy : g t = y := (OracleComp.pure_inj _ _).mp hy
      change (simulateQ g (liftM (spec.query t)) >>= fun r =>
        simulateQ g (simulateQ dropAmbient (k r))) = x
      simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query]
      subst hgy
      exact ih _ _ hk

end DropAmbient

variable {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface.{0, 0} (pSpec.Message i)]

/-! ### The oracle prover and sampler -/

/-- A receiver node of the oracle tree is a challenge round. -/
theorem oracle_dir_eq_of_owner {j : Fin n} : {d : Direction} → {hd : pSpec.dir j = d} →
    owner oracleSig (oraclePos pSpec j d hd) = .receiver → d = .V_to_P
  | .P_to_V, _, h => nomatch h
  | .V_to_P, _, _ => rfl

/-- A challenge round's node in the oracle tree belongs to the receiver. -/
theorem oracle_owner_of_dir {j : Fin n} : {d : Direction} → {hd : pSpec.dir j = d} →
    d = .V_to_P → owner oracleSig (oraclePos pSpec j d hd) = .receiver
  | .V_to_P, _, _ => rfl

/-- The oracle tree as a layout. -/
abbrev oracleLayout (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)] :
    Layout pSpec where
  P := OraclePoly
  l := oracleSig
  pos := oracleRound pSpec
  move j := oracleMoveEquiv pSpec j _ rfl
  owner_iff _ := ⟨oracle_dir_eq_of_owner, oracle_owner_of_dir⟩

/-- The legacy challenge index of a challenge node in the oracle tree from round `k`. -/
abbrev oracleChallengeRound : (k m : ℕ) → (h : k + m = n) →
    ChallengeNode oracleSig (oracleSuffix pSpec k m h) → pSpec.ChallengeIdx :=
  (oracleLayout pSpec).challengeRound

/-- The move at a challenge node of the oracle tree is the legacy challenge of its round. -/
abbrev oracleChallengeMove : (k m : ℕ) → (h : k + m = n) →
    (c : ChallengeNode oracleSig (oracleSuffix pSpec k m h)) →
    challengeSpec oracleSig (oracleSuffix pSpec k m h) c ≃
      pSpec.Challenge (oracleChallengeRound k m h c) :=
  (oracleLayout pSpec).challengeMove

/-- Draw at a challenge node of the oracle tree from a source of legacy challenges. -/
abbrev oracleLegacyDraw {M : Type → Type} [Functor M]
    (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) (k m : ℕ) (h : k + m = n)
    (c : ChallengeNode oracleSig (oracleSuffix pSpec k m h)) :
    M (challengeSpec oracleSig (oracleSuffix pSpec k m h) c) :=
  (oracleLayout pSpec).draw src k m h c

/-- The public-coin sampler of the oracle tree, drawing each challenge from `src`. -/
abbrev oracleLegacySampler {M : Type → Type} [Monad M] (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
    (src : (i : pSpec.ChallengeIdx) → M (pSpec.Challenge i)) :
    Counterpart oracleSig M (oracleProtocol pSpec) (fun _ => PUnit) :=
  sampler oracleSig (oracleProtocol pSpec) (oracleLegacyDraw src 0 n (Nat.zero_add n))

section Prover

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}

/-- The prover's node slot at round `j` of the oracle tree, for direction `d`. -/
def oracleRoundSlot (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin n) :
    (d : Direction) → (hd : pSpec.dir j = d) → P.PrvState j.castSucc →
    OracleComp oSpec (Choice .focal (owner oracleSig (oraclePos pSpec j d hd))
      (Move oracleSig (oraclePos pSpec j d hd)) (fun _ => P.PrvState j.succ))
  | .P_to_V, hd, st => (fun r => ⟨r.1, r.2⟩) <$> P.sendMessage ⟨j, hd⟩ st
  | .V_to_P, hd, st => P.receiveChallenge ⟨j, hd⟩ st

/-- The embedded prover on the oracle tree from round `k`. -/
def embedOracleFrom (P : _root_.Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    (k m : ℕ) → (h : k + m = n) → P.PrvState ⟨k, by omega⟩ →
    Core.Prover oracleSig oSpec (oracleSuffix pSpec k m h) (fun _ => StmtOut × WitOut)
  | k, 0, h, st => P.output (cast (congrArg P.PrvState (Fin.ext h)) st)
  | k, m + 1, h, st =>
    Choice.map .focal _ (fun _ st' => embedOracleFrom P (k + 1) m (by omega) st') <$>
      oracleRoundSlot P ⟨k, by omega⟩ (pSpec.dir ⟨k, by omega⟩) rfl st

end Prover

/-! ### The verifier's view -/

/-- The verifier's per-round view: the challenge, or a marker for an oracle payload. -/
abbrev viewSpec (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)] :
    ProtocolSpec n :=
  ⟨pSpec.dir, fun j => Move viewSig (oracleRound pSpec j)⟩

/-- The verifier's views of a run are its per-round views. -/
def viewEquiv (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)] :
    PathAlong viewSig (oracleProtocol pSpec) ≃ FullTranscript (viewSpec pSpec) :=
  chainEquiv (pSpec := viewSpec pSpec) viewSig (oracleRound pSpec) (fun _ => Equiv.refl _)

/-- The challenge in the view of a challenge round. -/
def viewChallenge (j : Fin n) : (d : Direction) → (hd : pSpec.dir j = d) → d = .V_to_P →
    Move viewSig (oraclePos pSpec j d hd) → pSpec.«Type» j
  | .V_to_P, _, _, x => x
  | .P_to_V, _, h, _ => nomatch h

/-- The challenges in a verifier view. -/
def viewChallenges (v : PathAlong viewSig (oracleProtocol pSpec)) : pSpec.Challenges :=
  fun i => viewChallenge i.1 _ rfl i.2 (viewEquiv pSpec v i.1)


/-! ### Messages on the oracle family of a path -/

/-- Queries to the right summand of a sum family. -/
def liftRight {I J : Type} {A : I → Type} {B : J → Type} (a : OracleFamily.{0, 0, 0} I A)
    (b : OracleFamily.{0, 0, 0} J B) : QueryImpl b.spec (OracleComp (sumFamily a b).spec) :=
  fun q => liftM ((sumFamily a b).spec.query ⟨.inr q.1, q.2⟩)

omit Oₘ in
/-- A message round other than a challenge round `j` lies after `j`. -/
theorem lt_of_challenge {j : Fin n} (hd : pSpec.dir j = .V_to_P) (i : pSpec.MessageIdx)
    (hi : j.val ≤ i.1.val) : j.val < i.1.val := by
  refine Nat.lt_of_le_of_ne hi fun h => ?_
  have := i.2
  rw [show i.1 = j from Fin.ext h.symm, hd] at this
  cases this

/-- Read message `i` at the node of round `j`, or from the rest of the path. -/
def readMsgNode (j : Fin n) (rest : OracleProtocol.{0})
    (recur : (p : Path rest) → (∀ o, OracleData rest p o) → (i : pSpec.MessageIdx) →
      j.val < i.1.val → pSpec.Message i) :
    (d : Direction) → (hd : pSpec.dir j = d) →
    (p : Path (FreeM.liftBind (oraclePos pSpec j d hd) (fun _ => rest))) →
    (∀ o, OracleData _ p o) → (i : pSpec.MessageIdx) → j.val ≤ i.1.val → pSpec.Message i
  | .P_to_V, _, ⟨_, p⟩, x, i, hi =>
    if hij : i.1.val = j.val then cast (congrArg pSpec.«Type» (Fin.ext hij).symm) (x (.inl ⟨⟩))
    else recur p (fun o => x (.inr o)) i (by omega)
  | .V_to_P, hd, ⟨_, p⟩, x, i, hi => recur p x i (lt_of_challenge hd i hi)

/-- Query message `i` at the node of round `j`, or in the rest of the path. -/
def queryMsgNode (j : Fin n) (rest : OracleProtocol.{0})
    (recur : (p : Path rest) → (i : pSpec.MessageIdx) → j.val < i.1.val →
      (q : (Oₘ i).Query) → OracleComp (pathFamily rest p).spec ((Oₘ i).Response q)) :
    (d : Direction) → (hd : pSpec.dir j = d) →
    (p : Path (FreeM.liftBind (oraclePos pSpec j d hd) (fun _ => rest))) →
    (i : pSpec.MessageIdx) → j.val ≤ i.1.val → (q : (Oₘ i).Query) →
    OracleComp (pathFamily _ p).spec ((Oₘ i).Response q)
  | .P_to_V, hd, ⟨b, p⟩, i, hi, q =>
    if hij : i.1.val = j.val then
      match i, (Subtype.ext (Fin.ext hij) : i = ⟨j, hd⟩), q with
      | _, rfl, q => liftM ((pathFamily (FreeM.liftBind (oraclePos pSpec j .P_to_V hd)
          (fun _ => rest)) ⟨b, p⟩).spec.query ⟨.inl ⟨⟩, q⟩)
    else simulateQ (liftRight _ _) (recur p i (by omega) q)
  | .V_to_P, hd, ⟨_, p⟩, i, hi, q => recur p i (lt_of_challenge hd i hi) q

theorem queryMsgNode_law (j : Fin n) (rest : OracleProtocol.{0})
    (read : (p : Path rest) → (∀ o, OracleData rest p o) → (i : pSpec.MessageIdx) →
      j.val < i.1.val → pSpec.Message i)
    (query : (p : Path rest) → (i : pSpec.MessageIdx) → j.val < i.1.val →
      (q : (Oₘ i).Query) → OracleComp (pathFamily rest p).spec ((Oₘ i).Response q))
    (law : ∀ p x i hi q, simulateQ ((pathFamily rest p).behaviorOfRealizations x)
      (query p i hi q) = (Oₘ i).answer (read p x i hi) q) :
    ∀ (d : Direction) (hd : pSpec.dir j = d) p x i hi q,
      simulateQ ((pathFamily _ p).behaviorOfRealizations x)
          (queryMsgNode j rest query d hd p i hi q) =
        (Oₘ i).answer (readMsgNode j rest read d hd p x i hi) q
  | .P_to_V, hd, ⟨b, p⟩, x, i, hi, q => by
    by_cases hij : i.1.val = j.val
    · obtain ⟨⟨iv, hiv⟩, i2⟩ := i
      simp only at hij
      subst hij
      simp only [queryMsgNode, readMsgNode, ↓reduceDIte]
      rfl
    · simp only [queryMsgNode, readMsgNode, hij, ↓reduceDIte]
      exact (QueryImpl.simulateQ_simulateQ_eq_of_apply
        (impl := (pathFamily rest p).behaviorOfRealizations (fun o => x (.inr o)))
        (fun _ => rfl) _).trans (law p _ i _ q)
  | .V_to_P, hd, ⟨_, p⟩, x, i, hi, q => law p x i _ q

/-- Read message `i` from the oracle data of a path through the tree from round `k`. -/
def readMsg : (k m : ℕ) → (h : k + m = n) → (p : Path (oracleSuffix pSpec k m h)) →
    (∀ o, OracleData _ p o) → (i : pSpec.MessageIdx) → k ≤ i.1.val → pSpec.Message i
  | k, 0, h, _, _, i, hi => absurd i.1.isLt (by omega)
  | k, m + 1, h, p, x, i, hi =>
    readMsgNode ⟨k, by omega⟩ (oracleSuffix pSpec (k + 1) m (by omega))
      (fun p x i hi => readMsg (k + 1) m (by omega) p x i hi) _ rfl p x i hi

/-- Query message `i` in the oracle family of a path through the tree from round `k`. -/
def queryMsg : (k m : ℕ) → (h : k + m = n) → (p : Path (oracleSuffix pSpec k m h)) →
    (i : pSpec.MessageIdx) → k ≤ i.1.val → (q : (Oₘ i).Query) →
    OracleComp (pathFamily _ p).spec ((Oₘ i).Response q)
  | k, 0, h, _, i, hi, _ => absurd i.1.isLt (by omega)
  | k, m + 1, h, p, i, hi, q =>
    queryMsgNode ⟨k, by omega⟩ (oracleSuffix pSpec (k + 1) m (by omega))
      (fun p i hi q => queryMsg (k + 1) m (by omega) p i hi q) _ rfl p i hi q

theorem queryMsg_law : (k m : ℕ) → (h : k + m = n) → (p : Path (oracleSuffix pSpec k m h)) →
    (x : ∀ o, OracleData _ p o) → (i : pSpec.MessageIdx) → (hi : k ≤ i.1.val) →
    (q : (Oₘ i).Query) →
    simulateQ ((pathFamily _ p).behaviorOfRealizations x) (queryMsg k m h p i hi q) =
      (Oₘ i).answer (readMsg k m h p x i hi) q
  | k, 0, h, _, _, i, hi, _ => absurd i.1.isLt (by omega)
  | k, m + 1, h, p, x, i, hi, q =>
    queryMsgNode_law ⟨k, by omega⟩ (oracleSuffix pSpec (k + 1) m (by omega)) _ _
      (fun p x i hi q => queryMsg_law (k + 1) m (by omega) p x i hi q) _ rfl p x i hi q

/-- The legacy messages held by the oracle data of a completed path. -/
def pathMessages (p : Path (oracleProtocol pSpec)) (x : ∀ o, OracleData _ p o) :
    pSpec.Messages :=
  fun i => readMsg 0 n _ p x i (Nat.zero_le _)

section Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface.{0, 0} (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface.{0, 0} (OStmtOut i)]

/-- The oracle family given by the legacy instances. -/
abbrev family {I : Type} (T : I → Type) [O : ∀ i, OracleInterface.{0, 0} (T i)] :
    OracleFamily.{0, 0, 0} I T := ⟨O⟩

/-- Route legacy input-statement and message queries to the oracle resources of a path. -/
def resourceImpl (p : Path (oracleProtocol pSpec)) :
    QueryImpl ([OStmtIn]ₒ + [pSpec.Message]ₒ)
      (OracleComp (sumFamily (family OStmtIn) (pathFamily (oracleProtocol pSpec) p)).spec) :=
  QueryImpl.add
    (fun q => liftM ((sumFamily (family OStmtIn) (pathFamily (oracleProtocol pSpec) p)).spec.query
      ⟨.inl q.1, q.2⟩))
    (fun q => simulateQ (liftRight _ _) (queryMsg 0 n _ p q.1 (Nat.zero_le _) q.2))

/-- Routing answers each legacy query from the statement data and the path's messages. -/
theorem resourceImpl_law (p : Path (oracleProtocol pSpec))
    (r : ∀ o, Sum.elim OStmtIn (OracleData (oracleProtocol pSpec) p) o)
    (q : ([OStmtIn]ₒ + [pSpec.Message]ₒ).Domain) :
    simulateQ ((sumFamily (family OStmtIn) (pathFamily _ p)).behaviorOfRealizations r)
        (resourceImpl p q) =
      QueryImpl.add (OracleInterface.simOracle0 OStmtIn (fun i => r (.inl i)))
        (OracleInterface.simOracle0 pSpec.Message
          (pathMessages p (fun o => r (.inr o)))) q := by
  rcases q with q | q
  · rfl
  · exact (QueryImpl.simulateQ_simulateQ_eq_of_apply
      (impl := (pathFamily _ p).behaviorOfRealizations (fun o => r (.inr o)))
      (fun _ => rfl) _).trans (queryMsg_law 0 n _ p _ q.1 _ q.2)

/-- Route all legacy decision queries, passing shared-oracle queries through. -/
def decisionImpl (p : Path (oracleProtocol pSpec)) :
    QueryImpl (oSpec + ([OStmtIn]ₒ + [pSpec.Message]ₒ))
      (OracleComp (oSpec +
        (sumFamily (family OStmtIn) (pathFamily (oracleProtocol pSpec) p)).spec)) :=
  QueryImpl.add
    (fun q => liftM ((oSpec + (sumFamily (family OStmtIn)
      (pathFamily (oracleProtocol pSpec) p)).spec).query (.inl q)))
    (fun q => simulateQ (fun t => liftM ((oSpec + (sumFamily (family OStmtIn)
      (pathFamily (oracleProtocol pSpec) p)).spec).query (.inr t))) (resourceImpl p q))

/-- The output map of a legacy output-oracle simulation, for the challenges of a run. Its data
map is the legacy materialization on the input data and the path's messages, and its queries
follow legacy `simulateOutputQuery`, routed to the input and path oracles. -/
def _root_.Interaction.Core.OracleMap.ofLegacySimulation [∀ t, Inhabited (oSpec.Range t)]
    (S : OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec)
    (challenges : pSpec.Challenges) (p : Path (oracleProtocol pSpec)) :
    OracleMap (sumFamily (family OStmtIn) (pathFamily (oracleProtocol pSpec) p))
      (family OStmtOut) where
  f r := S.materializeOutput challenges (fun i => r (.inl i)) (pathMessages p (fun o => r (.inr o)))
  impl q := simulateQ (resourceImpl p) (simulateQ dropAmbient (S.simulateOutputQuery challenges q))
  law r q := by
    rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (resourceImpl_law p r)]
    exact simulateQ_dropAmbient_of_eq_pure _ _ _
      (S.simulateOutputQuery_eq challenges _ _ q)

/-- **Agreement with the legacy simulation.** The answer to a query of the output map from
realized input and path data is the answer of legacy `simulateOutputQuery` under `simOracle2` on
the input data and the path's messages. -/
theorem simulateQ_ofLegacySimulation_impl [∀ t, Inhabited (oSpec.Range t)]
    (S : OracleOutputSimulation oSpec OStmtIn OStmtOut pSpec)
    (challenges : pSpec.Challenges) (p : Path (oracleProtocol pSpec))
    (r : ∀ o, Sum.elim OStmtIn (OracleData (oracleProtocol pSpec) p) o) (q : [OStmtOut]ₒ.Domain) :
    (pure (simulateQ ((sumFamily (family OStmtIn) (pathFamily _ p)).behaviorOfRealizations r)
        ((OracleMap.ofLegacySimulation S challenges p).impl q)) : OracleComp oSpec _) =
      simulateQ (OracleInterface.simOracle2 (T₁ := OStmtIn) (T₂ := pSpec.Message) oSpec
        (fun i => r (.inl i)) (pathMessages p (fun o => r (.inr o))))
        (S.simulateOutputQuery challenges q) := by
  rw [(OracleMap.ofLegacySimulation S challenges p).law]
  exact (S.simulateOutputQuery_eq challenges (fun i => r (.inl i))
    (pathMessages p (fun o => r (.inr o))) q).symm

/-- The output map of a legacy oracle verifier, for the challenges of a run: the output map of
its output-oracle semantics read as a simulation. -/
def legacyOutputMap [∀ t, Inhabited (oSpec.Range t)]
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (challenges : pSpec.Challenges) (p : Path (oracleProtocol pSpec)) :
    OracleMap (sumFamily (family OStmtIn) (pathFamily (oracleProtocol pSpec) p))
      (family OStmtOut) :=
  OracleMap.ofLegacySimulation ⟨V.materializeOutput, V.simulateOutputQuery,
    V.simulateOutputQuery_eq⟩ challenges p

/-- The embedded oracle verifier. It decides by running legacy `verify` on the challenges of its
view, and outputs the legacy output oracles. -/
def embedOracleVerifier [∀ t, Inhabited (oSpec.Range t)]
    (V : _root_.OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    Core.OracleVerifier oSpec (oracleProtocol pSpec) StmtIn (fun _ => StmtOut) (family OStmtIn)
      (fun _ => family OStmtOut) where
  decide stmt p view :=
    OptionT.mk (simulateQ (decisionImpl p) (V.verify stmt (viewChallenges view.val)).run)
  outputMap _ p view := legacyOutputMap V (viewChallenges view.val) p

/-- The embedded oracle prover, started on the input statement, its oracle data and the
witness. Its output keeps the legacy output statement, output oracle data and witness. -/
def embedOracleProver {WitIn WitOut : Type}
    (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    Core.Prover oracleSig oSpec (oracleProtocol pSpec)
      (fun _ => (StmtOut × (∀ i, OStmtOut i)) × WitOut) :=
  embedOracleFrom P 0 n (Nat.zero_add n) (P.input ((stmt, oStmt), wit))

end Verifier

end Interaction.Core.Legacy

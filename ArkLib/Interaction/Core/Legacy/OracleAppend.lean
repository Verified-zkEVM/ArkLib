/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Legacy.OracleExecution
public import ArkLib.Interaction.Core.LegacyAppend

/-!
# Oracle trees of appended legacy specifications

The oracle tree of a legacy specification is a chain of oracle rounds. This file relates the
chain of an appended specification `A ++ₚ B` to the chains of its parts, for use when an
interaction-layer protocol built round by round is identified with the oracle tree of a legacy
protocol built by appending.

* **Trees.** `chain_congr_len` and `chain_natAdd` reindex chains; `oracleRound_append_castAdd` and
  `oracleRound_append_natAdd` identify the rounds of `A ++ₚ B` with those of `A` and `B`.
* **Decoding.** `decodeFrom_append_natAdd` reads the rounds of `B` off a path through the chain of
  `A ++ₚ B` past `A`.
* **Routing.** `queryMsg_append_natAdd` routes a message query of `B` within the chain of
  `A ++ₚ B` past `A` to the node that routing within the chain of `B` selects.
* **Challenges.** `oracleChallengeImpl_heq` reads the reindexed challenge oracle at a node as the
  legacy challenge oracle at the node's round, and `uniform_append` combines uniform challenge
  sampling of the two parts.

Rounds of the two sides have propositionally, not definitionally, equal positions, so the
statements relate dependent moves, paths and programs heterogeneously.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens Oracle OracleComp OracleSpec ProtocolSpec

/-! ## Chains -/

section Chain
variable {P : PFunctor.{1, 0}}

/-- Chains of equal remaining length are equal. -/
theorem chain_congr_len {N : ℕ} (pos : Fin N → P.A) (k : ℕ) {m m' : ℕ} (hm : m = m')
    (h : k + m = N) (h' : k + m' = N) : chain pos k m h = chain pos k m' h' := by
  subst hm; rfl

/-- A chain that starts `a` positions into `pos` is the chain of `pos'` when the positions of
`pos` past `a` are those of `pos'`. -/
theorem chain_natAdd {a M : ℕ} (pos : Fin (a + M) → P.A) (pos' : Fin M → P.A)
    (hpos : ∀ j, pos (Fin.natAdd a j) = pos' j) :
    ∀ (k m : ℕ) (h : a + k + m = a + M) (h' : k + m = M),
      chain pos (a + k) m h = chain pos' k m h'
  | _, 0, _, _ => rfl
  | k, m + 1, h, h' => by
    have ih := chain_natAdd pos pos' hpos (k + 1) m (by omega) (by omega)
    change FreeM.liftBind (pos (Fin.natAdd a ⟨k, by omega⟩))
        (fun _ => chain pos (a + (k + 1)) m (by omega)) =
      FreeM.liftBind (pos' ⟨k, by omega⟩) (fun _ => chain pos' (k + 1) m (by omega))
    rw [hpos, ih]

end Chain

/-! ## Oracle rounds -/

section Round
/-- Oracle positions with equal payload types and interfaces are equal. -/
private theorem oracle_congr {X X' : Type} {I : OracleInterface X} {I' : OracleInterface X'}
    (hX : X = X') (hI : HEq I I') : OraclePos.oracle X I = OraclePos.oracle X' I' := by
  subst hX; cases eq_of_heq hI; rfl

variable {N N' : ℕ} (p : ProtocolSpec N) (p' : ProtocolSpec N')
  [O : ∀ i, OracleInterface (p.Message i)] [O' : ∀ i, OracleInterface (p'.Message i)]

/-- Rounds with equal directions, types and message interfaces give equal oracle positions. -/
private theorem oraclePos_congr (j : Fin N) (j' : Fin N') (hT : p.«Type» j = p'.«Type» j')
    (hO : ∀ h h', HEq (O ⟨j, h⟩) (O' ⟨j', h'⟩)) :
    ∀ (d d' : Direction) (h : p.dir j = d) (h' : p'.dir j' = d'), d = d' →
      oraclePos p j d h = oraclePos p' j' d' h'
  | .P_to_V, _, h, h', rfl => oracle_congr hT (hO h h')
  | .V_to_P, _, _, _, rfl => congrArg OraclePos.challenge hT

/-- Rounds with equal directions, types and message interfaces give equal oracle rounds. -/
theorem oracleRound_congr (j : Fin N) (j' : Fin N') (hd : p.dir j = p'.dir j')
    (hT : p.«Type» j = p'.«Type» j') (hO : ∀ h h', HEq (O ⟨j, h⟩) (O' ⟨j', h'⟩)) :
    oracleRound p j = oracleRound p' j' :=
  oraclePos_congr p p' j j' hT hO _ _ rfl rfl hd

end Round

section Append
variable {a b : ℕ} (A : ProtocolSpec a) (B : ProtocolSpec b)
  [OA : ∀ i, OracleInterface (A.Message i)] [OB : ∀ i, OracleInterface (B.Message i)]

/-- A round of an appended specification past its first part is the round of the second part. -/
theorem oracleRound_append_natAdd (j : Fin b) :
    oracleRound (A ++ₚ B) (Fin.natAdd a j) = oracleRound B j :=
  oracleRound_congr _ _ _ _ (Fin.vappend_right _ _ j) (Fin.vappend_right _ _ j)
    fun _ h' => (message_interface_inr (pSpec₁ := A) ⟨j, h'⟩).symm

/-- A round of an appended specification within its first part is the round of the first part. -/
theorem oracleRound_append_castAdd (j : Fin a) :
    oracleRound (A ++ₚ B) (Fin.castAdd b j) = oracleRound A j :=
  oracleRound_congr _ _ _ _ (Fin.vappend_left _ _ j) (Fin.vappend_left _ _ j)
    fun _ h' => (message_interface_inl (pSpec₂ := B) ⟨j, h'⟩).symm

end Append

/-! ## Decoding -/

section Path
variable {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly.{0})


/-- Heterogeneously equal paths through equal nodes have heterogeneously equal moves and
rests. -/
theorem heq_pathAlong_liftBind {a a' : P.A} {t t' : FreeM P PUnit.{1}} (ha : a = a') (ht : t = t')
    {d : Move l a} {r : PathAlong l t} {d' : Move l a'} {r' : PathAlong l t'}
    (h : HEq (⟨d, r⟩ : PathAlong l (FreeM.liftBind a fun _ => t))
      (⟨d', r'⟩ : PathAlong l (FreeM.liftBind a' fun _ => t'))) :
    HEq d d' ∧ HEq r r' := by
  subst ha ht
  cases eq_of_heq h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- Heterogeneously equal pairs of heterogeneously typed components have equal components. -/
private theorem heq_of_sigma_heq {X X' Y Y' : Type} (hX : X = X') (hY : Y = Y') {x : X} {y : Y}
    {x' : X'} {y' : Y'} (h : HEq (⟨x, y⟩ : (_ : X) × Y) (⟨x', y'⟩ : (_ : X') × Y')) :
    HEq x x' ∧ HEq y y' := by
  subst hX hY
  cases eq_of_heq h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- Decoding along chains of equal remaining length agrees on heterogeneously equal paths. -/
theorem decodeFrom_congr_len {n : ℕ} {pSpec : ProtocolSpec n} (pos : Fin n → P.A)
    (e : (j : Fin n) → Move l (pos j) ≃ pSpec.«Type» j) (k : ℕ) {m m' : ℕ} (hm : m = m')
    (h : k + m = n) (h' : k + m' = n) (pre : Transcript ⟨k, by omega⟩ pSpec)
    (p : PathAlong l (chain pos k m h)) (p' : PathAlong l (chain pos k m' h')) (hp : HEq p p') :
    decodeFrom l pos e k m' h' pre p' = decodeFrom l pos e k m h pre p := by
  subst hm; cases eq_of_heq hp; rfl

end Path

section Decode
variable {N : ℕ} (p : ProtocolSpec N) [O : ∀ i, OracleInterface (p.Message i)]

/-- The move equivalence of an oracle round is the identity up to the type equality. -/
theorem oracleMoveEquiv_heq (j : Fin N) :
    ∀ (d : Direction) (h : p.dir j = d) (x : Move oracleSig (oraclePos p j d h)),
      HEq (oracleMoveEquiv p j d h x) x
  | .P_to_V, _, _ => HEq.rfl
  | .V_to_P, _, _ => HEq.rfl

end Decode

section DecodeAppend
variable {a b : ℕ} (A : ProtocolSpec a) (B : ProtocolSpec b)
  [OA : ∀ i, OracleInterface (A.Message i)] [OB : ∀ i, OracleInterface (B.Message i)]

/-- Reading a chain over an appended spec past its first part reads the chain over the second
part. -/
theorem decodeFrom_append_natAdd : ∀ (k m : ℕ) (h : a + k + m = a + b) (h' : k + m = b)
    (pre : Transcript ⟨a + k, by omega⟩ (A ++ₚ B)) (pre' : Transcript ⟨k, by omega⟩ B)
    (q : PathAlong oracleSig (chain (oracleRound (A ++ₚ B)) (a + k) m h))
    (q' : PathAlong oracleSig (chain (oracleRound B) k m h')) (_ : HEq q q')
    (j : Fin b) (_ : k ≤ j.val),
    HEq (decodeFrom oracleSig (oracleRound (A ++ₚ B))
        (fun j => oracleMoveEquiv (A ++ₚ B) j _ rfl) (a + k) m h pre q (Fin.natAdd a j))
      (decodeFrom oracleSig (oracleRound B) (fun j => oracleMoveEquiv B j _ rfl) k m h' pre' q' j)
  | k, 0, _, h', _, _, _, _, _, j, hj => absurd j.isLt (by omega)
  | k, m + 1, h, h', pre, pre', ⟨d, q⟩, ⟨d', q'⟩, hq, ⟨j, hjb⟩, hj => by
    obtain ⟨hd, hq⟩ := heq_of_sigma_heq
      (congrArg (Move oracleSig) (oracleRound_append_natAdd A B ⟨k, by omega⟩))
      (congrArg (PathAlong oracleSig)
        (chain_natAdd _ _ (oracleRound_append_natAdd A B) (k + 1) m (by omega) (by omega))) hq
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · rw [decodeFrom_succ, decodeFrom_succ]
      exact decodeFrom_append_natAdd (k + 1) m (by omega) (by omega) _ _ q q' hq ⟨j, hjb⟩ hlt
    · refine (heq_of_eq (decodeFrom_succ_self oracleSig _ _ (a + k) m h pre d q)).trans ?_
      refine HEq.trans ?_ (heq_of_eq (decodeFrom_succ_self oracleSig _ _ k m h' pre' d' q').symm)
      exact (oracleMoveEquiv_heq _ _ _ _ d).trans (hd.trans (oracleMoveEquiv_heq _ _ _ _ d').symm)

end DecodeAppend

/-! ## Routing message queries -/

section Routing

/-- Heterogeneously equal paths through equal nodes have heterogeneously equal rests. -/
theorem heq_path_liftBind {a a' : OraclePos.{0}} {t t' : OracleProtocol.{0}} (ha : a = a')
    (ht : t = t') {x : OraclePoly.B a} {r : Path t} {x' : OraclePoly.B a'} {r' : Path t'}
    (h : HEq (⟨x, r⟩ : Path (FreeM.liftBind a fun _ => t))
      (⟨x', r'⟩ : Path (FreeM.liftBind a' fun _ => t'))) : HEq r r' := by
  subst ha ht
  cases eq_of_heq h
  exact HEq.rfl

/-- A query to the payload at the root of an oracle node, at corresponding nodes. -/
theorem heq_query_root {X X' : Type} {I : OracleInterface X} {I' : OracleInterface X'}
    (hX : X = X') (hI : HEq I I') {t t' : OracleProtocol.{0}} (ht : t = t') {r : Path t}
    {r' : Path t'} (hr : HEq r r') {q : I.Query} {q' : I'.Query} (hq : HEq q q') :
    HEq (liftM ((pathFamily (FreeM.liftBind (OraclePos.oracle X I) fun _ => t) ⟨⟨⟩, r⟩).spec.query
        ⟨.inl ⟨⟩, q⟩) :
        OracleComp (pathFamily (FreeM.liftBind (OraclePos.oracle X I) fun _ => t) ⟨⟨⟩, r⟩).spec
          (I.Response q))
      (liftM ((pathFamily (FreeM.liftBind (OraclePos.oracle X' I') fun _ => t')
          ⟨⟨⟩, r'⟩).spec.query ⟨.inl ⟨⟩, q'⟩) :
        OracleComp (pathFamily (FreeM.liftBind (OraclePos.oracle X' I') fun _ => t')
          ⟨⟨⟩, r'⟩).spec (I'.Response q')) := by
  subst hX ht
  cases eq_of_heq hI
  cases eq_of_heq hr
  cases eq_of_heq hq
  rfl

/-- Corresponding queries of equal interfaces have equal response types. -/
theorem response_eq {X X' : Type} {I : OracleInterface X} {I' : OracleInterface X'}
    (hX : X = X') (hI : HEq I I') {q : I.Query} {q' : I'.Query} (hq : HEq q q') :
    I.Response q = I'.Response q' := by
  subst hX
  cases eq_of_heq hI
  cases eq_of_heq hq
  rfl

/-- Queries past the root of an oracle node, at corresponding nodes. -/
theorem heq_simulateQ_liftRight {X X' : Type} {I : OracleInterface X}
    {I' : OracleInterface X'} (hX : X = X') (hI : HEq I I') {t t' : OracleProtocol.{0}}
    (ht : t = t') {r : Path t} {r' : Path t'} (hr : HEq r r') {α α' : Type} (hα : α = α')
    {x : OracleComp (pathFamily t r).spec α} {x' : OracleComp (pathFamily t' r').spec α'}
    (hx : HEq x x') :
    HEq (simulateQ (liftRight (singletonFamily I) (pathFamily t r)) x :
        OracleComp (pathFamily (FreeM.liftBind (OraclePos.oracle X I) fun _ => t) ⟨⟨⟩, r⟩).spec α)
      (simulateQ (liftRight (singletonFamily I') (pathFamily t' r')) x' :
        OracleComp (pathFamily (FreeM.liftBind (OraclePos.oracle X' I') fun _ => t')
          ⟨⟨⟩, r'⟩).spec α') := by
  subst hX ht hα
  cases eq_of_heq hI
  cases eq_of_heq hr
  cases eq_of_heq hx
  rfl

variable {N N' : ℕ} {P : ProtocolSpec N} {P' : ProtocolSpec N'}
  [O : ∀ i, OracleInterface.{0, 0} (P.Message i)] [O' : ∀ i, OracleInterface.{0, 0} (P'.Message i)]

/-- Querying a message at corresponding nodes of two oracle chains gives corresponding programs,
when the rounds and the messages correspond and so do the queries of the rest of the chains. -/
theorem queryMsgNode_heq (j : Fin N) (j' : Fin N') {rest rest' : OracleProtocol.{0}}
    (hrest : rest = rest')
    (recur : (p : Path rest) → (i : P.MessageIdx) → j.val < i.1.val →
      (q : (O i).Query) → OracleComp (pathFamily rest p).spec ((O i).Response q))
    (recur' : (p : Path rest') → (i : P'.MessageIdx) → j'.val < i.1.val →
      (q : (O' i).Query) → OracleComp (pathFamily rest' p).spec ((O' i).Response q))
    (hT : P.«Type» j = P'.«Type» j') (hO : ∀ h h', HEq (O ⟨j, h⟩) (O' ⟨j', h'⟩))
    (i : P.MessageIdx) (i' : P'.MessageIdx) (hii : i.1.val = j.val ↔ i'.1.val = j'.val)
    (hTi : P.«Type» i.1 = P'.«Type» i'.1) (hOi : HEq (O i) (O' i'))
    (hrec : ∀ p p', HEq p p' → ∀ hi hi' q q', HEq q q' →
      HEq (recur p i hi q) (recur' p' i' hi' q')) :
    ∀ (d d' : Direction) (hd : P.dir j = d) (hd' : P'.dir j' = d'), d = d' →
      ∀ p p', HEq p p' → ∀ hi hi' q q', HEq q q' →
        HEq (queryMsgNode j rest recur d hd p i hi q)
          (queryMsgNode j' rest' recur' d' hd' p' i' hi' q')
  | .V_to_P, _, hd, hd', rfl, ⟨_, p⟩, ⟨_, p'⟩, hp, hi, hi', q, q', hq =>
    hrec p p' (heq_path_liftBind (congrArg OraclePos.challenge hT) hrest hp) _ _ q q' hq
  | .P_to_V, _, hd, hd', rfl, ⟨b, p⟩, ⟨b', p'⟩, hp, hi, hi', q, q', hq => by
    have hpos : oraclePos P j .P_to_V hd = oraclePos P' j' .P_to_V hd' :=
      oracle_congr hT (hO hd hd')
    have hr := heq_path_liftBind hpos hrest hp
    by_cases hij : i.1.val = j.val
    · have hij' := hii.mp hij
      obtain ⟨⟨iv, hiv⟩, i2⟩ := i
      obtain ⟨⟨iv', hiv'⟩, i2'⟩ := i'
      obtain ⟨jv, hjv⟩ := j
      obtain ⟨jv', hjv'⟩ := j'
      simp only at hij hij'
      subst hij hij'
      simp only [queryMsgNode, ↓reduceDIte]
      exact heq_query_root hT (hO hd hd') hrest hr hq
    · have hij' : ¬ i'.1.val = j'.val := fun h => hij (hii.mpr h)
      simp only [queryMsgNode, hij, hij', ↓reduceDIte]
      exact heq_simulateQ_liftRight hT (hO hd hd') hrest hr (response_eq hTi hOi hq)
        (hrec p p' hr _ _ q q' hq)

/-- Routing a message query at the node of its own round is the query to that node's payload. -/
theorem queryMsgNode_heq_root (j : Fin N) (rest : OracleProtocol.{0})
    (recur : (p : Path rest) → (i : P.MessageIdx) → j.val < i.1.val →
      (q : (O i).Query) → OracleComp (pathFamily rest p).spec ((O i).Response q))
    (d : Direction) (hd : P.dir j = d) (hdP : d = .P_to_V)
    (p : Path (FreeM.liftBind (oraclePos P j d hd) fun _ => rest)) (i : P.MessageIdx)
    (hij : i.1 = j) (hi : j.val ≤ i.1.val) (q : (O i).Query) {X : Type} {I : OracleInterface X}
    {t : OracleProtocol.{0}} {r : Path t} {q' : I.Query} (hX : P.«Type» j = X)
    (hI : ∀ h, HEq (O ⟨j, h⟩) I) (ht : rest = t) (hr : HEq p.2 r) (hq : HEq q q') :
    HEq (queryMsgNode j rest recur d hd p i hi q)
      (liftM ((pathFamily (FreeM.liftBind (OraclePos.oracle X I) fun _ => t)
          ⟨⟨⟩, r⟩).spec.query ⟨.inl ⟨⟩, q'⟩) :
        OracleComp (pathFamily (FreeM.liftBind (OraclePos.oracle X I) fun _ => t)
          ⟨⟨⟩, r⟩).spec (I.Response q')) := by
  subst hdP
  obtain ⟨b, p⟩ := p
  obtain ⟨i, i2⟩ := i
  subst hij
  simp only [queryMsgNode, ↓reduceDIte]
  exact heq_query_root hX (hI hd) ht hr hq

/-- Routing a message query at the node of an earlier message round routes it in the rest of the
chain, lifted past the node's payload. -/
theorem queryMsgNode_heq_liftRight (j : Fin N) (rest : OracleProtocol.{0})
    (recur : (p : Path rest) → (i : P.MessageIdx) → j.val < i.1.val →
      (q : (O i).Query) → OracleComp (pathFamily rest p).spec ((O i).Response q))
    (d : Direction) (hd : P.dir j = d) (hdP : d = .P_to_V)
    (p : Path (FreeM.liftBind (oraclePos P j d hd) fun _ => rest)) (i : P.MessageIdx)
    (hij : i.1.val ≠ j.val) (hi : j.val ≤ i.1.val) (q : (O i).Query) {X : Type}
    {I : OracleInterface X} {t : OracleProtocol.{0}} {r : Path t} {α : Type}
    {x : OracleComp (pathFamily t r).spec α} (hX : P.«Type» j = X)
    (hI : ∀ h, HEq (O ⟨j, h⟩) I) (ht : rest = t) (hr : HEq p.2 r) (hα : (O i).Response q = α)
    (hx : ∀ hlt, HEq (recur p.2 i hlt q) x) :
    HEq (queryMsgNode j rest recur d hd p i hi q)
      (simulateQ (liftRight (singletonFamily I) (pathFamily t r)) x :
        OracleComp (pathFamily (FreeM.liftBind (OraclePos.oracle X I) fun _ => t) ⟨⟨⟩, r⟩).spec
          α) := by
  subst hdP
  obtain ⟨b, p⟩ := p
  simp only [queryMsgNode, hij, ↓reduceDIte]
  exact heq_simulateQ_liftRight hX (hI hd) ht hr hα (hx _)

/-- Routing a message query at a challenge node routes it in the rest of the chain. -/
theorem queryMsgNode_heq_challenge (j : Fin N) (rest : OracleProtocol.{0})
    (recur : (p : Path rest) → (i : P.MessageIdx) → j.val < i.1.val →
      (q : (O i).Query) → OracleComp (pathFamily rest p).spec ((O i).Response q))
    (d : Direction) (hd : P.dir j = d) (hdV : d = .V_to_P)
    (p : Path (FreeM.liftBind (oraclePos P j d hd) fun _ => rest)) (i : P.MessageIdx)
    (hi : j.val ≤ i.1.val) (q : (O i).Query) (hlt : j.val < i.1.val) :
    HEq (queryMsgNode j rest recur d hd p i hi q) (recur p.2 i hlt q) := by
  subst hdV
  rfl

/-- Routing along chains of equal remaining length agrees on heterogeneously equal paths. -/
theorem queryMsg_congr_len (k : ℕ) {m m' : ℕ} (hm : m = m') (h : k + m = N) (h' : k + m' = N)
    (p : Path (oracleSuffix P k m h)) (p' : Path (oracleSuffix P k m' h')) (hp : HEq p p')
    (i : P.MessageIdx) (hi : k ≤ i.1.val) (q : (O i).Query) :
    HEq (queryMsg k m h p i hi q) (queryMsg k m' h' p' i hi q) := by
  subst hm; cases eq_of_heq hp; rfl

end Routing

section RouteAppend
variable {a b : ℕ} (A : ProtocolSpec a) (B : ProtocolSpec b)
  [OA : ∀ i, OracleInterface (A.Message i)] [OB : ∀ i, OracleInterface (B.Message i)]

/-- Routing a message query of `B` within the chain of `A ++ₚ B` past `A` selects the node that
routing within the chain of `B` selects. -/
theorem queryMsg_append_natAdd : ∀ (k m : ℕ) (h : a + k + m = a + b) (h' : k + m = b)
    (p : Path (oracleSuffix (A ++ₚ B) (a + k) m h))
    (p' : Path (oracleSuffix B k m h')) (_ : HEq p p') (i : B.MessageIdx)
    (hi : a + k ≤ (MessageIdx.inr (pSpec₁ := A) i).1.val) (hi' : k ≤ i.1.val)
    (q : OracleInterface.Query ((A ++ₚ B).Message (MessageIdx.inr i))) (q' : (OB i).Query)
    (_ : HEq q q'),
    HEq (queryMsg (pSpec := A ++ₚ B) (a + k) m h p (MessageIdx.inr i) hi q)
      (queryMsg (pSpec := B) k m h' p' i hi' q')
  | k, 0, _, h', _, _, _, i, _, hi', _, _, _ => absurd i.1.isLt (by omega)
  | k, m + 1, h, h', p, p', hp, i, hi, hi', q, q', hq =>
    queryMsgNode_heq (P := A ++ₚ B) (P' := B) ⟨a + k, by omega⟩ ⟨k, by omega⟩
      (chain_natAdd _ _ (oracleRound_append_natAdd A B) (k + 1) m (by omega) (by omega)) _ _
      (Fin.vappend_right _ _ ⟨k, by omega⟩)
      (fun _ h' => (message_interface_inr (pSpec₁ := A) ⟨⟨k, by omega⟩, h'⟩).symm)
      (MessageIdx.inr i) i (by simp [MessageIdx.inr])
      (Fin.vappend_right _ _ i.1) (message_interface_inr i).symm
      (fun p p' hp hi hi' q q' hq =>
        queryMsg_append_natAdd (k + 1) m (by omega) (by omega) p p' hp i hi hi' q q' hq)
      _ _ rfl rfl (Fin.vappend_right _ _ ⟨k, by omega⟩) p p' hp hi hi' q q' hq

end RouteAppend

/-! ## Challenges -/

section Uniform

/-- A sampler mapped along a type equality is the same sampler. -/
private theorem heq_of_cast_map {α β : Type} (h : α = β) {x : ProbComp α} {y : ProbComp β}
    (hxy : cast h <$> x = y) : HEq x y := by
  subst h; subst hxy; exact (heq_of_eq (LawfulFunctor.id_map x)).symm

/-- If every challenge of two specifications is sampled as `x`, then so is every challenge of
their append. -/
theorem uniform_append {a b : ℕ} (A : ProtocolSpec a) (B : ProtocolSpec b)
    [∀ i, SampleableType (A.Challenge i)] [∀ i, SampleableType (B.Challenge i)] {X : Type}
    (x : ProbComp X) (hA : ∀ i, HEq ($ᵗ (A.Challenge i)) x) (hB : ∀ i, HEq ($ᵗ (B.Challenge i)) x) :
    ∀ i : (A ++ₚ B).ChallengeIdx, HEq ($ᵗ ((A ++ₚ B).Challenge i)) x := by
  intro i
  obtain ⟨j | j, rfl⟩ := (ChallengeIdx.sumEquiv (pSpec₁ := A) (pSpec₂ := B)).surjective i
  · exact (heq_of_cast_map _ (uniformSample_challenge_append_inl j)).trans (hA j)
  · exact (heq_of_cast_map _ (uniformSample_challenge_append_inr j)).trans (hB j)

end Uniform

section ChallengeImpl

/-- Mapping a sampler along a function that is the identity up to a type equality gives the same
sampler. -/
private theorem map_heq_self {X Y : Type} (hXY : X = Y) (f : X → Y) (hf : ∀ x, HEq (f x) x)
    (x : ProbComp X) : HEq (f <$> x) x := by
  subst hXY
  have : f = id := funext fun y => eq_of_heq (hf y)
  subst this
  exact heq_of_eq (LawfulFunctor.id_map x)

variable {N : ℕ} (p : ProtocolSpec N) [O : ∀ i, OracleInterface (p.Message i)]

/-- The move type of an oracle round is the round's type. -/
private theorem oracleMove_eq (j : Fin N) :
    ∀ (d : Direction) (h : p.dir j = d), Move oracleSig (oraclePos p j d h) = p.«Type» j
  | .P_to_V, _ => rfl
  | .V_to_P, _ => rfl

/-- The inverse move equivalence of an oracle round is the identity up to the type equality. -/
theorem oracleMoveEquiv_symm_heq (j : Fin N) :
    ∀ (d : Direction) (h : p.dir j = d) (y : p.«Type» j),
      HEq ((oracleMoveEquiv p j d h).symm y) y
  | .P_to_V, _, _ => HEq.rfl
  | .V_to_P, _, _ => HEq.rfl

/-- A challenge node of a chain of oracle rounds has the type of its legacy challenge round. -/
theorem oracleChallengeSpec_eq : ∀ (k m : ℕ) (h : k + m = N)
    (c : ChallengeNode oracleSig (chain (oracleRound p) k m h)),
    challengeSpec oracleSig (chain (oracleRound p) k m h) c =
      p.Challenge ((oracleLayout p).challengeRound k m h c)
  | _, 0, _, c => c.val.elim
  | k, _ + 1, _, ⟨.inl _, _⟩ => oracleMove_eq p ⟨k, by omega⟩ _ rfl
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩ => oracleChallengeSpec_eq (k + 1) m _ ⟨c, hc⟩

/-- Reading a legacy challenge as a move of its challenge node is the identity up to the type
equality. -/
theorem oracleChallengeMove_symm_heq : ∀ (k m : ℕ) (h : k + m = N)
    (c : ChallengeNode oracleSig (chain (oracleRound p) k m h))
    (y : p.Challenge ((oracleLayout p).challengeRound k m h c)),
    HEq (((oracleLayout p).challengeMove k m h c).symm y) y
  | _, 0, _, c, _ => c.val.elim
  | k, _ + 1, _, ⟨.inl _, _⟩, y => oracleMoveEquiv_symm_heq p ⟨k, by omega⟩ _ rfl y
  | k, m + 1, _, ⟨.inr ⟨_, c⟩, hc⟩, y => oracleChallengeMove_symm_heq (k + 1) m _ ⟨c, hc⟩ y

/-- The reindexed challenge oracle answers a challenge node with the legacy challenge oracle at
the node's round, up to the type equality. -/
theorem oracleChallengeImpl_heq (chImpl : QueryImpl [p.Challenge]ₒ ProbComp)
    (c : ChallengeNode oracleSig (oracleProtocol p)) :
    HEq (oracleChallengeImpl (pSpec := p) chImpl c)
      (chImpl ⟨oracleChallengeRound 0 N (Nat.zero_add N) c, ()⟩) :=
  map_heq_self (oracleChallengeSpec_eq p 0 _ _ c).symm _ (oracleChallengeMove_symm_heq p 0 _ _ c) _

end ChallengeImpl

end Interaction.Core.Legacy

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.QueriesByMoveLaws
public import ArkLib.Interaction.Oracle.Routing

/-!
# Sent oracle messages at a partial transcript

A prover oracle can be queried only after the prover has sent its oracle message. At a partial
transcript, the sent oracle messages are the oracle messages that the moves already made contain.
Each sent oracle message has a node name: the node of the protocol where it was sent. The node
name does not depend on later moves. When a longer partial transcript continues a shorter one, it
includes the shorter one's sent oracle messages, and it keeps their node names and their query
behavior.

The core (`Interaction/OracleVerifier.lean`) names the oracle messages of a completed path with
`OracleMessageIndex`, `OracleMessage`, `oracleMessageFamily` and `oracleMessages`. A partial
transcript has the same data for the messages sent so far. This file therefore uses the same
stems with a `Sent` prefix: `SentOracleMessageIndex`, `SentOracleMessage`,
`sentOracleMessageFamily` and `sentOracleMessages`. They differ from the core names in the type
they depend on: a partial transcript instead of a path. `oracleMessagesToSent` identifies the
core's `oracleMessageFamily` of a completed transcript with the sent oracle messages of the same
transcript.

This file is a general utility for reasoning about oracle access partway through a run. Under P1
the core verifier queries bundles only in its final decision, so the current tests use only the
basic pieces (`IsSent`, `SentOracleMessageIndex.node_lift`, `liftQuery_node`,
`sentOracleMessageMap`). The general routing and inclusion laws (`availableMap`, `liftQuery_index`,
`liftQuery_response`, `oracleMessagesToSent`, `toPathBundle`, `firstMovesLe`,
`QueriesAt.availableData`, `isSent_at_decision` and `runWithAmbientQueriesByMove_before_le`) have
no caller yet. They are kept for later clients that query sent oracles before the end of a run,
such as a round-by-round extractor that reads the oracles sent so far, or a verifier or sampler
with oracle access before its final decision.
-/

@[expose] public section

universe u q uI dI

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace PartialTranscript

/-- The oracle messages already sent in a partial transcript, one index for each oracle node that
the moves made so far have passed. -/
def SentOracleMessageIndex :
    {s : OracleProtocol.{u, q}} → PartialTranscript oracleSig s → Type u
  | .pure _, _ => PEmpty
  | .liftBind _ _, none => PEmpty
  | .liftBind (.message _) _, some ⟨_, tail⟩ => SentOracleMessageIndex tail
  | .liftBind (.challenge _) _, some ⟨_, tail⟩ => SentOracleMessageIndex tail
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩ => PUnit ⊕ SentOracleMessageIndex tail

/-- The type of the oracle message at a sent index. -/
def SentOracleMessage : {s : OracleProtocol.{u, q}} → (h : PartialTranscript oracleSig s) →
    SentOracleMessageIndex h → Type u
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨_, tail⟩, i => SentOracleMessage tail i
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => SentOracleMessage tail i
  | .liftBind (.oracle X _) _, some ⟨_, tail⟩, i =>
    Sum.elim (fun _ => X) (SentOracleMessage tail) i

/-- The family of the oracle messages already sent. -/
def sentOracleMessageFamily :
    {s : OracleProtocol.{u, q}} → (h : PartialTranscript oracleSig s) →
    OracleFamily (SentOracleMessageIndex h) (SentOracleMessage h)
  | .pure _, _ => ⟨fun i => i.elim⟩
  | .liftBind _ _, none => ⟨fun i => i.elim⟩
  | .liftBind (.message _) _, some ⟨_, tail⟩ => sentOracleMessageFamily tail
  | .liftBind (.challenge _) _, some ⟨_, tail⟩ => sentOracleMessageFamily tail
  | .liftBind (.oracle _ I) _, some ⟨_, tail⟩ =>
    sumFamily (singletonFamily I) (sentOracleMessageFamily tail)

/-- The oracle message that was sent for each sent index. -/
def sentOracleMessages : {s : OracleProtocol.{u, q}} → (h : PartialTranscript oracleSig s) →
    (i : SentOracleMessageIndex h) → SentOracleMessage h i
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨_, tail⟩, i => sentOracleMessages tail i
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => sentOracleMessages tail i
  | .liftBind (.oracle _ _) _, some ⟨x, _⟩, .inl _ => x
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩, .inr i => sentOracleMessages tail i

namespace SentOracleMessageIndex

/-- The node of the original protocol where a sent oracle message was sent. It does not depend on
later moves. -/
def node : {s : OracleProtocol.{u, q}} → (h : PartialTranscript oracleSig s) →
    SentOracleMessageIndex h → Node s
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨x, tail⟩, i => .inr ⟨x, node tail i⟩
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => .inr ⟨⟨⟩, node tail i⟩
  | .liftBind (.oracle _ _) _, some ⟨_, _⟩, .inl _ => .inl ⟨⟩
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩, .inr i => .inr ⟨⟨⟩, node tail i⟩

end SentOracleMessageIndex

/-- The oracle at a node has been sent exactly when the node is the node of a sent oracle
message. -/
def IsSent {s : OracleProtocol.{u, q}} (h : PartialTranscript oracleSig s) (n : Node s) : Prop :=
  ∃ i, SentOracleMessageIndex.node h i = n

/-- The oracle bundle available at a partial transcript: the inputs, and exactly the oracle messages
already sent. -/
def availableBundle (inputs : OracleBundle.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    (h : PartialTranscript oracleSig s) :=
  inputs.sum (OracleBundle.ofFamily h.sentOracleMessageFamily)

/-- The name of a bundle query: an input index, or the node of a sent oracle. -/
def queryNode (inputs : OracleBundle.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    (h : PartialTranscript oracleSig s) :
    (h.availableBundle inputs).Index → inputs.Index ⊕ Node s
  | .inl i => .inl i
  | .inr ⟨i, _⟩ => .inr (SentOracleMessageIndex.node h i)

/-- `Le h k` says that the partial transcript `k` continues `h` and keeps every earlier move of
`h`. -/
inductive Le : {s : OracleProtocol.{u, q}} → PartialTranscript oracleSig s →
    PartialTranscript oracleSig s → Type (max (u + 1) (q + 1)) where
  | empty {s} (h : PartialTranscript oracleSig s) : Le (.empty : PartialTranscript oracleSig s) h
  | cons {a : OraclePos.{u, q}} {next : OraclePoly.B a → OracleProtocol}
      (x : Move oracleSig a) {h k : PartialTranscript oracleSig (next (oracleSig.toFunB a x))}
      (tail : Le h k) : Le (.cons x h) (.cons x k)

/-- Every partial transcript is below itself, with its concrete challenge and oracle message
values. -/
def Le.refl : {s : OracleProtocol.{u, q}} → (h : PartialTranscript oracleSig s) → Le h h
  | .pure _, none => .empty _
  | .pure _, some impossible => impossible.elim
  | .liftBind _ _, none => .empty _
  | .liftBind _ _, some ⟨x, tail⟩ => .cons x (Le.refl tail)

namespace SentOracleMessageIndex

/-- Include the oracle messages sent in the shorter partial transcript among those sent in the
longer one. -/
def lift : {s : OracleProtocol.{u, q}} → {h k : PartialTranscript oracleSig s} →
    Le h k → SentOracleMessageIndex h → SentOracleMessageIndex k
  | s, _, _, .empty _, i => by cases s <;> exact PEmpty.elim i
  | _, _, _, @Le.cons (.message _) next x h k tail, i =>
    lift (s := next x) (h := h) (k := k) tail i
  | _, _, _, @Le.cons (.challenge _) next _ h k tail, i =>
    lift (s := next ⟨⟩) (h := h) (k := k) tail i
  | _, _, _, @Le.cons (.oracle _ _) _ _ h k tail, .inl i => .inl i
  | _, _, _, @Le.cons (.oracle _ _) _ _ h k tail, .inr i =>
    .inr (lift (h := h) (k := k) tail i)

/-- Including a sent oracle message keeps its node name. -/
theorem node_lift : {s : OracleProtocol.{u, q}} → {h k : PartialTranscript oracleSig s} →
    (e : Le h k) → (i : SentOracleMessageIndex h) → node k (lift e i) = node h i
  | s, _, _, .empty _, i => by cases s <;> exact PEmpty.elim i
  | _, _, _, @Le.cons (.message X) next x h k tail, i =>
    congrArg (fun n : Node (next x) =>
      (Sum.inr ⟨x, n⟩ : Node (P := OraclePoly.{u, q}) (.liftBind (.message X) next)))
      (node_lift tail i)
  | _, _, _, @Le.cons (.challenge C) next _ h k tail, i =>
    congrArg (fun n : Node (next ⟨⟩) =>
      (Sum.inr ⟨⟨⟩, n⟩ : Node (P := OraclePoly.{u, q}) (.liftBind (.challenge C) next)))
      (node_lift tail i)
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, .inl _ => rfl
  | _, _, _, @Le.cons (.oracle X I) next _ h k tail, .inr i =>
    congrArg (fun n : Node (next ⟨⟩) =>
      (Sum.inr ⟨⟨⟩, n⟩ : Node (P := OraclePoly.{u, q}) (.liftBind (.oracle X I) next)))
      (node_lift tail i)

end SentOracleMessageIndex

/-- Extending a partial transcript does not remove a sent oracle message. -/
theorem IsSent.mono {s : OracleProtocol.{u, q}} {h k : PartialTranscript oracleSig s} (e : Le h k)
    {n : Node s} (sent : h.IsSent n) : k.IsSent n := by
  obtain ⟨i, rfl⟩ := sent
  exact ⟨SentOracleMessageIndex.lift e i, SentOracleMessageIndex.node_lift e i⟩

/-- Include a query to an earlier sent oracle message in the longer partial transcript, keeping its
query argument. -/
def liftQuery : {s : OracleProtocol.{u, q}} → {h k : PartialTranscript oracleSig s} →
    Le h k → (sentOracleMessageFamily h).spec.Domain → (sentOracleMessageFamily k).spec.Domain
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) next x h k tail, r =>
    liftQuery (s := next x) (h := h) (k := k) tail r
  | _, _, _, @Le.cons (.challenge _) next _ h k tail, r =>
    liftQuery (s := next ⟨⟩) (h := h) (k := k) tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl i, r⟩ => ⟨.inl i, r⟩
  | _, _, _, @Le.cons (.oracle _ _) _ _ h k tail, ⟨.inr i, r⟩ =>
    let query := liftQuery (h := h) (k := k) tail ⟨i, r⟩
    ⟨.inr query.1, query.2⟩

/-- Including a query uses the same inclusion of sent oracle messages as for the available
bundle. -/
theorem liftQuery_index : {s : OracleProtocol.{u, q}} → {h k : PartialTranscript oracleSig s} →
    (e : Le h k) → (r : (sentOracleMessageFamily h).spec.Domain) →
    (liftQuery e r).1 = SentOracleMessageIndex.lift e r.1
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) _ _ _ _ tail, r => liftQuery_index tail r
  | _, _, _, @Le.cons (.challenge _) _ _ _ _ tail, r => liftQuery_index tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => rfl
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ tail, ⟨.inr i, r⟩ =>
    congrArg Sum.inr (liftQuery_index tail ⟨i, r⟩)

/-- An included query names exactly the node of the earlier sent oracle message. -/
theorem liftQuery_node {s : OracleProtocol.{u, q}} {h k : PartialTranscript oracleSig s}
    (e : Le h k) (r : (sentOracleMessageFamily h).spec.Domain) :
    SentOracleMessageIndex.node k (liftQuery e r).1 = SentOracleMessageIndex.node h r.1 := by
  rw [liftQuery_index, SentOracleMessageIndex.node_lift]

/-- Including a query keeps the response type as well as the query argument. -/
theorem liftQuery_response :
    {s : OracleProtocol.{u, q}} → {h k : PartialTranscript oracleSig s} →
    (e : Le h k) → (r : (sentOracleMessageFamily h).spec.Domain) →
    (sentOracleMessageFamily h).spec r = (sentOracleMessageFamily k).spec (liftQuery e r)
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) _ _ _ _ tail, r => liftQuery_response tail r
  | _, _, _, @Le.cons (.challenge _) _ _ _ _ tail, r => liftQuery_response tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => rfl
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ tail, ⟨.inr i, r⟩ =>
    liftQuery_response tail ⟨i, r⟩

/-- Restrict the sent oracle message family of the longer partial transcript to that of the shorter
one. -/
def sentOracleMessageMap : {s : OracleProtocol.{u, q}} → {h k : PartialTranscript oracleSig s} →
    Le h k → OracleMap (sentOracleMessageFamily k) (sentOracleMessageFamily h)
  | s, _, _, .empty _ => by
    cases s <;> exact
      { f := fun _ i => PEmpty.elim i
        impl.toFun r := PEmpty.elim r.1
        law := fun _ r => PEmpty.elim r.1 }
  | _, _, _, @Le.cons (.message _) next x h k tail =>
    sentOracleMessageMap (s := next x) (h := h) (k := k) tail
  | _, _, _, @Le.cons (.challenge _) next _ h k tail =>
    sentOracleMessageMap (s := next ⟨⟩) (h := h) (k := k) tail
  | _, _, _, @Le.cons (.oracle _ I) _ _ h k tail =>
    (OracleMap.id (OracleBundle.ofFamily (singletonFamily I))).sum
      (sentOracleMessageMap (h := h) (k := k) tail)

/-- The restriction answers each query by querying the included sent oracle message with the same
argument. -/
theorem sentOracleMessageMap_query :
    {s : OracleProtocol.{u, q}} → {h k : PartialTranscript oracleSig s} →
    (e : Le h k) → (r : (sentOracleMessageFamily h).spec.Domain) →
    HEq ((sentOracleMessageMap e).impl r)
      (liftM ((sentOracleMessageFamily k).spec.query (liftQuery e r)) :
        OracleComp (sentOracleMessageFamily k).spec _)
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) _ _ _ _ tail, r => sentOracleMessageMap_query tail r
  | _, _, _, @Le.cons (.challenge _) _ _ _ _ tail, r => sentOracleMessageMap_query tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => by
    rfl
  | _, _, _, @Le.cons (.oracle _ I) _ _ h k tail, ⟨.inr i, r⟩ => by
    dsimp only [sentOracleMessageMap]
    erw [OracleMap.sum_impl_inr]
    have ih := sentOracleMessageMap_query tail ⟨i, r⟩
    let handler : QueryImpl (sentOracleMessageFamily k).spec
        (OracleComp (sumFamily (singletonFamily I) (sentOracleMessageFamily k)).spec) :=
      (OracleMap.embedding (sumFamily (singletonFamily I) (sentOracleMessageFamily k))
        Sum.inr).impl
    have lift_heq {α β : Type u} (eq : α = β)
        {p : OracleComp (sentOracleMessageFamily k).spec α}
        {p' : OracleComp (sentOracleMessageFamily k).spec β}
        (same : HEq p p') : HEq (simulateQ handler p) (simulateQ handler p') := by
      subst β
      cases same
      rfl
    have lifted := lift_heq (liftQuery_response tail ⟨i, r⟩) ih
    change HEq (simulateQ handler ((sentOracleMessageMap tail).impl ⟨i, r⟩))
      (liftM ((sumFamily (singletonFamily I) (sentOracleMessageFamily k)).spec.query
        ⟨.inr (liftQuery tail ⟨i, r⟩).1, (liftQuery tail ⟨i, r⟩).2⟩) :
          OracleComp (sumFamily (singletonFamily I) (sentOracleMessageFamily k)).spec _)
    simp only [handler, OracleMap.embedding] at lifted
    exact lifted

/-- Route queries to the bundle available at the shorter partial transcript through the bundle
available at the longer one. -/
def availableMap (inputs : OracleBundle.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : PartialTranscript oracleSig s} (e : Le h k) :
    OracleMap (k.availableBundle inputs) (h.availableBundle inputs) :=
  (OracleMap.id inputs).par (sentOracleMessageMap e)

/-- Include an input or a sent oracle message of the shorter partial transcript among those of the
longer one. -/
def liftNode (inputs : OracleBundle.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : PartialTranscript oracleSig s} (e : Le h k) :
    inputs.Index ⊕ SentOracleMessageIndex h → inputs.Index ⊕ SentOracleMessageIndex k :=
  Sum.map id (SentOracleMessageIndex.lift e)

/-- Including an input or a sent oracle message keeps its name in the original protocol. -/
theorem availableMap_node (inputs : OracleBundle.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : PartialTranscript oracleSig s} (e : Le h k)
    (i : inputs.Index ⊕ SentOracleMessageIndex h) :
    Sum.map id (SentOracleMessageIndex.node k) (liftNode inputs e i) =
      Sum.map id (SentOracleMessageIndex.node h) i := by
  cases i with
  | inl i => rfl
  | inr i => exact congrArg Sum.inr (SentOracleMessageIndex.node_lift e i)

/-- Identify the sent oracle messages of a completed transcript with the oracle message family on
the path that the verifier uses. -/
def oracleMessagesToSent : (s : OracleProtocol.{u, q}) → (tr : Transcript oracleSig s) →
    OracleMap (oracleMessageFamily s tr.path) (sentOracleMessageFamily (ofTranscript s tr))
  | .pure _, _ =>
    { f := fun _ i => i.elim
      impl := ⟨fun r => r.1.elim⟩
      law := fun _ r => r.1.elim }
  | .liftBind (.message _) next, ⟨x, tr⟩ => oracleMessagesToSent (next x) tr
  | .liftBind (.challenge _) next, ⟨_, tr⟩ => oracleMessagesToSent (next ⟨⟩) tr
  | .liftBind (.oracle _ I) next, ⟨_, tr⟩ =>
    (OracleMap.id (OracleBundle.ofFamily (singletonFamily I))).sum
      (oracleMessagesToSent (next ⟨⟩) tr)

/-- This identification reads exactly the oracle messages of the same transcript. -/
theorem oracleMessagesToSent_data :
    (s : OracleProtocol.{u, q}) → (tr : Transcript oracleSig s) →
    (oracleMessagesToSent s tr).f (oracleMessages s tr) = sentOracleMessages (ofTranscript s tr)
  | .pure _, _ => by funext i; exact i.elim
  | .liftBind (.message _) next, ⟨x, tr⟩ => oracleMessagesToSent_data (next x) tr
  | .liftBind (.challenge _) next, ⟨_, tr⟩ => oracleMessagesToSent_data (next ⟨⟩) tr
  | .liftBind (.oracle _ _) next, ⟨_, tr⟩ => by
    funext i
    cases i with
    | inl _ => rfl
    | inr i => exact congrFun (oracleMessagesToSent_data (next ⟨⟩) tr) i

/-- Route the verifier's bundle along the completed path to the bundle available at the
completed transcript. -/
def toPathBundle (inputs : OracleBundle.{u, uI, dI})
    (s : OracleProtocol.{u, q}) (tr : Transcript oracleSig s) :
    OracleMap (pathBundle inputs s tr.path)
      ((ofTranscript s tr).availableBundle inputs) :=
  (OracleMap.id inputs).par (oracleMessagesToSent s tr)

/-- Routing from `pathBundle` keeps the inputs and exactly the oracle messages that were sent. -/
theorem toPathBundle_data (inputs : OracleBundle.{u, uI, dI}) (input : inputs.Data)
    (s : OracleProtocol.{u, q}) (tr : Transcript oracleSig s) :
    (toPathBundle inputs s tr).f (input, oracleMessages s tr) =
      (input, sentOracleMessages (ofTranscript s tr)) := by
  exact congrArg (input, ·) (oracleMessagesToSent_data s tr)

/-- The partial transcript of the appended protocol `s₁.append s₂` that ends at the seam: it
holds every move of `tr₁` and no move of the second protocol. -/
def firstMoves : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : Transcript oracleSig s₁) →
    PartialTranscript oracleSig (s₁.append s₂)
  | .pure _, _, _ => .empty
  | .liftBind a next, s₂, ⟨x, tr⟩ =>
    .cons x (firstMoves (next (oracleSig.toFunB a x))
      (fun p => s₂ ⟨oracleSig.toFunB a x, p⟩) tr)

/-- The first moves of the appended run are below its whole transcript. -/
def firstMovesLe : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : Transcript oracleSig s₁) →
    (tr₂ : Transcript oracleSig (s₂ tr₁.path)) →
    Le (firstMoves s₁ s₂ tr₁)
      (ofTranscript (s₁.append s₂) (Transcript.append s₁ s₂ tr₁ tr₂))
  | .pure _, _, _, _ => .empty _
  | .liftBind a next, s₂, ⟨x, tr₁⟩, tr₂ =>
    .cons x (firstMovesLe (next (oracleSig.toFunB a x))
      (fun p => s₂ ⟨oracleSig.toFunB a x, p⟩) tr₁ tr₂)

/-- A sent oracle message at the seam keeps its node name at the end of the appended run. -/
theorem firstMovesLe_node (s₁ : OracleProtocol.{u, q})
    (s₂ : Path s₁ → OracleProtocol.{u, q}) (tr₁ : Transcript oracleSig s₁)
    (tr₂ : Transcript oracleSig (s₂ tr₁.path))
    (i : SentOracleMessageIndex (firstMoves s₁ s₂ tr₁)) :
    SentOracleMessageIndex.node (ofTranscript _ (Transcript.append s₁ s₂ tr₁ tr₂))
        (SentOracleMessageIndex.lift (firstMovesLe s₁ s₂ tr₁ tr₂) i) =
      SentOracleMessageIndex.node (firstMoves s₁ s₂ tr₁) i :=
  SentOracleMessageIndex.node_lift _ _

/-- Every outcome of PolyFun's exchange `step` on two logged actions starts with one logged entry
for each action (the prover's, then the sampler's), followed by the entries of the continuation.
This is a property of the exchange in the writer layer. -/
theorem mem_support_logMove {ι : Type} {spec : OracleSpec ι}
    {root s : OracleProtocol.{0, q}} {X R : Type} {A B : X → Type}
    (env : PartialTranscript oracleSig s → PartialTranscript oracleSig root)
    (role : TwoParty.Role)
    (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → WriterT (List (QueriesAt spec root)) (OracleComp spec) R)
    {r : R × List (QueriesAt spec root)}
    (hr : r ∈ support ((step role .focalFirst
      (logMove env .focal p) (logMove env .counterpart c) k).run)) :
    ∃ x pn cn lp lc child, child ∈ support ((k x pn cn).run) ∧
      r = (child.1, ⟨env .empty, .prover, lp⟩ :: ⟨env .empty, .sampler, lc⟩ :: child.2) := by
  cases role <;>
    simp only [step, Schedule.seq, logMove, WriterT.run_bind, WriterT.run_mk,
      bind_map_left, _root_.map_bind, Functor.map_map, mem_support_bind_iff] at hr
  · obtain ⟨vp, _, vc, _, h⟩ := hr
    obtain ⟨child, hc, heq⟩ := mem_support_map_peel _ _ h
    exact ⟨vp.1.1, vp.1.2, vc.1 vp.1.1, vp.2, vc.2, child, hc, heq⟩
  · obtain ⟨vp, _, vc, _, h⟩ := hr
    obtain ⟨child, hc, heq⟩ := mem_support_map_peel _ _ h
    exact ⟨vc.1.1, vp.1 vc.1.1, vc.1.2, vp.2, vc.2, child, hc, heq⟩

/-- Every entry logged while the core runner runs wrapped strategies has a partial transcript that
is below the whole transcript of the run, as embedded by `env`. The embedding `env` places the
partial transcripts of the rest of the protocol inside the root protocol. -/
theorem mapMovesWith_before_le {ι : Type} {spec : OracleSpec ι}
    {root : OracleProtocol.{0, q}} :
    (s : OracleProtocol.{0, q}) → {OutP OutC : Transcript oracleSig s → Type} →
    (env : PartialTranscript oracleSig s → PartialTranscript oracleSig root) →
    (preserves : ∀ h k, Le h k → Nonempty (Le (env h) (env k))) →
    (p : Focal oracleSig (OracleComp spec) s OutP) →
    (c : Counterpart oracleSig (OracleComp spec) s OutC) →
    {r : ((tr : Transcript oracleSig s) × OutP tr × OutC tr) ×
      List (QueriesAt spec root)} →
    r ∈ support ((TwoParty.Lens.run s
      (MoveInstrumentation.mapMovesWith
        (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig root)
        (@logMove ι spec root) (@embedAfterMove root) env .focal p)
      (MoveInstrumentation.mapMovesWith
        (C := fun t => PartialTranscript oracleSig t → PartialTranscript oracleSig root)
        (@logMove ι spec root) (@embedAfterMove root) env .counterpart c)).run) →
    (entry : QueriesAt spec root) → entry ∈ r.2 →
      Nonempty (Le entry.before (env (ofTranscript s r.1.1)))
  | .pure leaf, _, _, env, preserves, p, c, r, hr, entry, hp => by
    cases leaf
    simp only [MoveInstrumentation.mapMovesWith, FreeM.pure_eq_pure, run_done,
      logMove, WriterT.run_bind, WriterT.run_mk, WriterT.run_pure,
      bind_map_left, _root_.map_bind, Functor.map_map,
      mem_support_bind_iff] at hr
    obtain ⟨vp, _, vc, _, heq⟩ := hr
    simp only [LawfulApplicative.map_pure, mem_support_pure_iff] at heq
    subst r
    simp only [List.empty_eq, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact preserves _ _ (.empty _)
  | .liftBind a next, _, _, env, preserves, p, c, r, hr, entry, hp => by
    rw [run_node] at hr
    simp only [MoveInstrumentation.mapMovesWith, step_map_left, step_map_right] at hr
    obtain ⟨x, pn, cn, lp, lc, child, hc, heq⟩ := mem_support_logMove env _ _ _ _ hr
    simp only [WriterT.run_bind, WriterT.run_pure, LawfulApplicative.map_pure,
      mem_support_bind_iff, mem_support_pure_iff, List.empty_eq, List.append_nil] at hc
    obtain ⟨result, hresult, hchild⟩ := hc
    subst child
    subst r
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact preserves _ _ (.empty _)
    · exact preserves _ _ (.empty _)
    · exact mapMovesWith_before_le (next (oracleSig.toFunB a x))
        (embedAfterMove a next x env) (fun h k e => preserves _ _ (.cons x e))
        pn cn hresult entry hp

/-- At the root, every entry logged by `runLoggingMoves` has a partial transcript that is below the
whole transcript of the run. -/
theorem runLoggingMoves_before_le {ι : Type} {spec : OracleSpec ι}
    (s : OracleProtocol.{0, q}) {OutP OutC : Transcript oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC)
    {r : ((tr : Transcript oracleSig s) × OutP tr × OutC tr) × List (QueriesAt spec s)}
    (hr : r ∈ support (runLoggingMoves s p c))
    (entry : QueriesAt spec s) (hp : entry ∈ r.2) :
    Nonempty (Le entry.before (ofTranscript s r.1.1)) :=
  mapMovesWith_before_le s id (fun _ _ e => ⟨e⟩) p c hr entry hp

end PartialTranscript

namespace QueriesAt

/-- The bundle available at this entry: the one available at its partial transcript. -/
abbrev availableContext {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (entry : QueriesAt spec s) (inputs : OracleBundle.{0, uI, dI}) :=
  entry.before.availableBundle inputs

/-- The input data and the oracle messages already sent give data for this entry's available
bundle. -/
def availableData {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (entry : QueriesAt spec s) (inputs : OracleBundle.{0, uI, dI}) (input : inputs.Data) :
    (entry.availableContext inputs).Data :=
  (input, PartialTranscript.sentOracleMessages entry.before)

/-- Include an earlier entry's available bundle in that of a later entry whose partial
transcript continues the earlier one. -/
def availableMap {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (entry later : QueriesAt spec s) (inputs : OracleBundle.{0, uI, dI})
    (e : PartialTranscript.Le entry.before later.before) :
    OracleMap (later.availableContext inputs) (entry.availableContext inputs) :=
  PartialTranscript.availableMap inputs e

end QueriesAt

namespace OracleVerifier

/-- Every entry in the queries by move of a run has a partial transcript that is below the whole
transcript of the run. -/
theorem runWithQueriesByMove_before_le {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleBundle.{0, 0, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : QueriesByMove V Out}
    (hr : r ∈ support (V.runWithQueriesByMove stmt input prover))
    (entry : QueriesAt ambient s) (hp : entry ∈ r.withDecision) :
    Nonempty (PartialTranscript.Le entry.before
      (PartialTranscript.ofTranscript s r.outcome.1)) := by
  simp only [runWithQueriesByMove, executeWith, _root_.map_bind, LawfulApplicative.map_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨entries, hi, decision, _, heq⟩ := hr
  subst r
  simp only [QueriesByMove.withDecision, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hp
    subst entry
    exact PartialTranscript.runLoggingMoves_before_le s _ _ hi raw hraw
  · exact ⟨PartialTranscript.Le.refl _⟩

/-- An oracle message sent before an entry of the run is still sent at the decision. -/
theorem isSent_at_decision {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleBundle.{0, 0, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : QueriesByMove V Out}
    (hr : r ∈ support (V.runWithQueriesByMove stmt input prover))
    (entry : QueriesAt ambient s) (hp : entry ∈ r.withDecision) {n : Node s}
    (sent : entry.before.IsSent n) : r.decision.before.IsSent n := by
  obtain ⟨e⟩ := V.runWithQueriesByMove_before_le stmt input prover hr entry hp
  exact sent.mono e

/-- The ambient queries by move also give every entry a partial transcript that is below the whole
transcript, for arbitrary bundle-query universes. -/
theorem runWithAmbientQueriesByMove_before_le {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, q}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleBundle.{0, uI, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : Transcript oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : AmbientQueriesByMove V Out}
    (hr : r ∈ support (V.runWithAmbientQueriesByMove stmt input prover))
    (entry : QueriesAt ambient s) (hp : entry ∈ r.withDecision) :
    Nonempty (PartialTranscript.Le entry.before
      (PartialTranscript.ofTranscript s r.outcome.1)) := by
  simp only [runWithAmbientQueriesByMove, executeWith, _root_.map_bind, LawfulApplicative.map_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨entries, hi, decision, _, heq⟩ := hr
  subst r
  simp only [AmbientQueriesByMove.withDecision, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hp
    subst entry
    exact PartialTranscript.runLoggingMoves_before_le s _ _ hi raw hraw
  · exact ⟨PartialTranscript.Le.refl _⟩

end OracleVerifier
end Interaction

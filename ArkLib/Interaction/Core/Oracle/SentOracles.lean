/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Oracle.StepLogLaws
public import ArkLib.Interaction.Core.Oracle.Routing

/-!
# Sent oracles at a transcript prefix

A prover oracle can be queried only after the prover has sent its payload. At a transcript prefix,
the sent oracles are the oracles whose payloads the moves so far already contain. Each sent oracle
has a node name: the node of the protocol where it was sent. The node name does not depend on later
moves. When a longer prefix continues a shorter one, it includes the shorter prefix's sent oracles,
and it keeps their node names and their query behavior.
-/

@[expose] public section

universe u q uI dI

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace TranscriptPrefix

/-- The oracles already sent in the transcript so far, one for each oracle node that the moves
have passed. -/
def SentOracle : {s : OracleProtocol.{u, q}} → TranscriptPrefix s → Type u
  | .pure _, _ => PEmpty
  | .liftBind _ _, none => PEmpty
  | .liftBind (.message _) _, some ⟨_, tail⟩ => SentOracle tail
  | .liftBind (.challenge _) _, some ⟨_, tail⟩ => SentOracle tail
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩ => PUnit ⊕ SentOracle tail

namespace SentOracle

/-- The type of the payload of a sent oracle. -/
def Payload : {s : OracleProtocol.{u, q}} → (h : TranscriptPrefix s) → SentOracle h → Type u
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨_, tail⟩, i => Payload tail i
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => Payload tail i
  | .liftBind (.oracle X _) _, some ⟨_, tail⟩, i => Sum.elim (fun _ => X) (Payload tail) i

end SentOracle

/-- The family of the oracle payloads already sent. -/
def sentFamily : {s : OracleProtocol.{u, q}} → (h : TranscriptPrefix s) →
    OracleFamily (SentOracle h) (SentOracle.Payload h)
  | .pure _, _ => ⟨fun i => i.elim⟩
  | .liftBind _ _, none => ⟨fun i => i.elim⟩
  | .liftBind (.message _) _, some ⟨_, tail⟩ => sentFamily tail
  | .liftBind (.challenge _) _, some ⟨_, tail⟩ => sentFamily tail
  | .liftBind (.oracle _ I) _, some ⟨_, tail⟩ => sumFamily (singletonFamily I) (sentFamily tail)

namespace SentOracle

/-- The payload that was sent for each sent oracle. -/
def payload : {s : OracleProtocol.{u, q}} → (h : TranscriptPrefix s) → (i : SentOracle h) →
    Payload h i
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨_, tail⟩, i => payload tail i
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => payload tail i
  | .liftBind (.oracle _ _) _, some ⟨x, _⟩, .inl _ => x
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩, .inr i => payload tail i

/-- The node of the original protocol where a sent oracle was sent. It does not depend on later
moves. -/
def node : {s : OracleProtocol.{u, q}} → (h : TranscriptPrefix s) → SentOracle h → Node s
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨x, tail⟩, i => .inr ⟨x, node tail i⟩
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => .inr ⟨⟨⟩, node tail i⟩
  | .liftBind (.oracle _ _) _, some ⟨_, _⟩, .inl _ => .inl ⟨⟩
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩, .inr i => .inr ⟨⟨⟩, node tail i⟩

end SentOracle

/-- The oracle at a node has been sent exactly when the node is the node of a sent oracle. -/
def IsSent {s : OracleProtocol.{u, q}} (h : TranscriptPrefix s) (n : Node s) : Prop :=
  ∃ i, SentOracle.node h i = n

/-- The resources available at a transcript prefix: the inputs, and exactly the payloads already
sent. -/
def availableResources (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    (h : TranscriptPrefix s) :=
  inputs.sum (Resources.ofFamily h.sentFamily)

/-- The name of a resource query: an input index, or the node of a sent oracle. -/
def queryNode (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    (h : TranscriptPrefix s) :
    (h.availableResources inputs).Index → inputs.Index ⊕ Node s
  | .inl i => .inl i
  | .inr ⟨i, _⟩ => .inr (SentOracle.node h i)

/-- `Le h k` says that the transcript prefix `k` continues `h` and keeps every earlier move of
`h`. -/
inductive Le : {s : OracleProtocol.{u, q}} → TranscriptPrefix s → TranscriptPrefix s →
    Type (max (u + 1) (q + 1)) where
  | empty {s} (h : TranscriptPrefix s) : Le (.empty : TranscriptPrefix s) h
  | cons {a : OraclePos.{u, q}} {next : OraclePoly.B a → OracleProtocol}
      (x : Move oracleSig a) {h k : TranscriptPrefix (next (oracleSig.toFunB a x))}
      (tail : Le h k) : Le (.cons x h) (.cons x k)

/-- Every prefix is below itself, with its concrete challenge and payload values. -/
def Le.refl : {s : OracleProtocol.{u, q}} → (h : TranscriptPrefix s) → Le h h
  | .pure _, none => .empty _
  | .pure _, some impossible => impossible.elim
  | .liftBind _ _, none => .empty _
  | .liftBind _ _, some ⟨x, tail⟩ => .cons x (Le.refl tail)

namespace SentOracle

/-- Include the oracles sent in the shorter prefix among those sent in the longer prefix. -/
def lift : {s : OracleProtocol.{u, q}} → {h k : TranscriptPrefix s} →
    Le h k → SentOracle h → SentOracle k
  | s, _, _, .empty _, i => by cases s <;> exact PEmpty.elim i
  | _, _, _, @Le.cons (.message _) next x h k tail, i =>
    lift (s := next x) (h := h) (k := k) tail i
  | _, _, _, @Le.cons (.challenge _) next _ h k tail, i =>
    lift (s := next ⟨⟩) (h := h) (k := k) tail i
  | _, _, _, @Le.cons (.oracle _ _) _ _ h k tail, .inl i => .inl i
  | _, _, _, @Le.cons (.oracle _ _) _ _ h k tail, .inr i =>
    .inr (lift (h := h) (k := k) tail i)

/-- Including a sent oracle keeps its node name. -/
theorem node_lift : {s : OracleProtocol.{u, q}} → {h k : TranscriptPrefix s} →
    (e : Le h k) → (i : SentOracle h) → node k (lift e i) = node h i
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

end SentOracle

/-- Extending a transcript prefix does not remove a sent oracle. -/
theorem IsSent.mono {s : OracleProtocol.{u, q}} {h k : TranscriptPrefix s} (e : Le h k)
    {n : Node s} (sent : h.IsSent n) : k.IsSent n := by
  obtain ⟨i, rfl⟩ := sent
  exact ⟨SentOracle.lift e i, SentOracle.node_lift e i⟩

/-- Include a query to an earlier sent oracle in the longer prefix, keeping its query
argument. -/
def liftQuery : {s : OracleProtocol.{u, q}} → {h k : TranscriptPrefix s} →
    Le h k → (sentFamily h).spec.Domain → (sentFamily k).spec.Domain
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) next x h k tail, r =>
    liftQuery (s := next x) (h := h) (k := k) tail r
  | _, _, _, @Le.cons (.challenge _) next _ h k tail, r =>
    liftQuery (s := next ⟨⟩) (h := h) (k := k) tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl i, r⟩ => ⟨.inl i, r⟩
  | _, _, _, @Le.cons (.oracle _ _) _ _ h k tail, ⟨.inr i, r⟩ =>
    let query := liftQuery (h := h) (k := k) tail ⟨i, r⟩
    ⟨.inr query.1, query.2⟩

/-- Including a query uses the same inclusion of sent oracles as for the available resources. -/
theorem liftQuery_index : {s : OracleProtocol.{u, q}} → {h k : TranscriptPrefix s} →
    (e : Le h k) → (r : (sentFamily h).spec.Domain) →
    (liftQuery e r).1 = SentOracle.lift e r.1
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) _ _ _ _ tail, r => liftQuery_index tail r
  | _, _, _, @Le.cons (.challenge _) _ _ _ _ tail, r => liftQuery_index tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => rfl
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ tail, ⟨.inr i, r⟩ =>
    congrArg Sum.inr (liftQuery_index tail ⟨i, r⟩)

/-- An included query names exactly the node of the earlier sent oracle. -/
theorem liftQuery_node {s : OracleProtocol.{u, q}} {h k : TranscriptPrefix s}
    (e : Le h k) (r : (sentFamily h).spec.Domain) :
    SentOracle.node k (liftQuery e r).1 = SentOracle.node h r.1 := by
  rw [liftQuery_index, SentOracle.node_lift]

/-- Including a query keeps the response type as well as the query argument. -/
theorem liftQuery_response : {s : OracleProtocol.{u, q}} → {h k : TranscriptPrefix s} →
    (e : Le h k) → (r : (sentFamily h).spec.Domain) →
    (sentFamily h).spec r = (sentFamily k).spec (liftQuery e r)
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) _ _ _ _ tail, r => liftQuery_response tail r
  | _, _, _, @Le.cons (.challenge _) _ _ _ _ tail, r => liftQuery_response tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => rfl
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ tail, ⟨.inr i, r⟩ =>
    liftQuery_response tail ⟨i, r⟩

/-- Restrict the payload family of the longer prefix to that of the shorter prefix. -/
def sentFamilyMap : {s : OracleProtocol.{u, q}} → {h k : TranscriptPrefix s} →
    Le h k → OracleMap (sentFamily k) (sentFamily h)
  | s, _, _, .empty _ => by
    cases s <;> exact
      { f := fun _ i => PEmpty.elim i
        impl := fun r => PEmpty.elim r.1
        law := fun _ r => PEmpty.elim r.1 }
  | _, _, _, @Le.cons (.message _) next x h k tail =>
    sentFamilyMap (s := next x) (h := h) (k := k) tail
  | _, _, _, @Le.cons (.challenge _) next _ h k tail =>
    sentFamilyMap (s := next ⟨⟩) (h := h) (k := k) tail
  | _, _, _, @Le.cons (.oracle _ I) _ _ h k tail =>
    (OracleMap.id (Resources.ofFamily (singletonFamily I))).sum
      (sentFamilyMap (h := h) (k := k) tail)

/-- The restriction answers each query by querying the included sent oracle with the same
argument. -/
theorem sentFamilyMap_query : {s : OracleProtocol.{u, q}} → {h k : TranscriptPrefix s} →
    (e : Le h k) → (r : (sentFamily h).spec.Domain) →
    HEq ((sentFamilyMap e).impl r)
      (liftM ((sentFamily k).spec.query (liftQuery e r)) : OracleComp (sentFamily k).spec _)
  | s, _, _, .empty _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Le.cons (.message _) _ _ _ _ tail, r => sentFamilyMap_query tail r
  | _, _, _, @Le.cons (.challenge _) _ _ _ _ tail, r => sentFamilyMap_query tail r
  | _, _, _, @Le.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => by
    rfl
  | _, _, _, @Le.cons (.oracle _ I) _ _ h k tail, ⟨.inr i, r⟩ => by
    dsimp only [sentFamilyMap]
    erw [OracleMap.sum_impl_inr]
    have ih := sentFamilyMap_query tail ⟨i, r⟩
    let handler : QueryImpl (sentFamily k).spec
        (OracleComp (sumFamily (singletonFamily I) (sentFamily k)).spec) := fun r =>
      liftM ((sumFamily (singletonFamily I) (sentFamily k)).spec.query ⟨.inr r.1, r.2⟩)
    have lift_heq {α β : Type u} (eq : α = β)
        {p : OracleComp (sentFamily k).spec α} {p' : OracleComp (sentFamily k).spec β}
        (same : HEq p p') : HEq (simulateQ handler p) (simulateQ handler p') := by
      subst β
      cases same
      rfl
    have lifted := lift_heq (liftQuery_response tail ⟨i, r⟩) ih
    change HEq (simulateQ handler ((sentFamilyMap tail).impl ⟨i, r⟩))
      (liftM ((sumFamily (singletonFamily I) (sentFamily k)).spec.query
        ⟨.inr (liftQuery tail ⟨i, r⟩).1, (liftQuery tail ⟨i, r⟩).2⟩) :
          OracleComp (sumFamily (singletonFamily I) (sentFamily k)).spec _)
    simp only [simulateQ_spec_query, handler] at lifted
    exact lifted

/-- Route queries to the resources available at the shorter prefix through the resources available
at the longer prefix. -/
def availableMap (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : TranscriptPrefix s} (e : Le h k) :
    OracleMap (k.availableResources inputs) (h.availableResources inputs) :=
  (OracleMap.id inputs).par (sentFamilyMap e)

/-- Include an input or a sent oracle of the shorter prefix among those of the longer prefix. -/
def liftNode (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : TranscriptPrefix s} (e : Le h k) :
    inputs.Index ⊕ SentOracle h → inputs.Index ⊕ SentOracle k :=
  Sum.map id (SentOracle.lift e)

/-- Including an input or a sent oracle keeps its name in the original protocol. -/
theorem availableMap_node (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : TranscriptPrefix s} (e : Le h k) (i : inputs.Index ⊕ SentOracle h) :
    Sum.map id (SentOracle.node k) (liftNode inputs e i) =
      Sum.map id (SentOracle.node h) i := by
  cases i with
  | inl i => rfl
  | inr i => exact congrArg Sum.inr (SentOracle.node_lift e i)

/-- Identify the sent oracles of a completed transcript with the path family that the verifier
uses. -/
def sentAtTranscript : (s : OracleProtocol.{u, q}) → (tr : PathAlong oracleSig s) →
    OracleMap (pathFamily s (projectPathAlong oracleSig s tr)) (sentFamily (ofTranscript s tr))
  | .pure _, _ =>
    { f := fun _ i => i.elim
      impl := fun r => r.1.elim
      law := fun _ r => r.1.elim }
  | .liftBind (.message _) next, ⟨x, tr⟩ => sentAtTranscript (next x) tr
  | .liftBind (.challenge _) next, ⟨_, tr⟩ => sentAtTranscript (next ⟨⟩) tr
  | .liftBind (.oracle _ I) next, ⟨_, tr⟩ =>
    (OracleMap.id (Resources.ofFamily (singletonFamily I))).sum (sentAtTranscript (next ⟨⟩) tr)

/-- This identification reads exactly the payloads of the same transcript. -/
theorem sentAtTranscript_data : (s : OracleProtocol.{u, q}) → (tr : PathAlong oracleSig s) →
    (sentAtTranscript s tr).f (payloads s tr) = SentOracle.payload (ofTranscript s tr)
  | .pure _, _ => by funext i; exact i.elim
  | .liftBind (.message _) next, ⟨x, tr⟩ => sentAtTranscript_data (next x) tr
  | .liftBind (.challenge _) next, ⟨_, tr⟩ => sentAtTranscript_data (next ⟨⟩) tr
  | .liftBind (.oracle _ _) next, ⟨_, tr⟩ => by
    funext i
    cases i with
    | inl _ => rfl
    | inr i => exact congrFun (sentAtTranscript_data (next ⟨⟩) tr) i

/-- Route the verifier's resources along the completed path to the resources available at the
completed transcript. -/
def toPathResources (inputs : Resources.{u, uI, dI})
    (s : OracleProtocol.{u, q}) (tr : PathAlong oracleSig s) :
    OracleMap (pathResources inputs s (projectPathAlong oracleSig s tr))
      ((ofTranscript s tr).availableResources inputs) :=
  (OracleMap.id inputs).par (sentAtTranscript s tr)

/-- Routing from `pathResources` keeps the inputs and exactly the payloads that were sent. -/
theorem toPathResources_data (inputs : Resources.{u, uI, dI}) (input : inputs.Data)
    (s : OracleProtocol.{u, q}) (tr : PathAlong oracleSig s) :
    (toPathResources inputs s tr).f (input, payloads s tr) =
      (input, SentOracle.payload (ofTranscript s tr)) := by
  exact congrArg (input, ·) (sentAtTranscript_data s tr)

/-- The transcript prefix of the appended protocol `s₁.append s₂` that ends at the seam: it holds
every move of `tr₁` and no move of the second protocol. -/
def seamPrefix : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : PathAlong oracleSig s₁) →
    TranscriptPrefix (s₁.append s₂)
  | .pure _, _, _ => .empty
  | .liftBind a next, s₂, ⟨x, tr⟩ =>
    .cons x (seamPrefix (next (oracleSig.toFunB a x))
      (fun p => s₂ ⟨oracleSig.toFunB a x, p⟩) tr)

/-- The seam prefix is below the whole transcript of the appended run. -/
def seamLeEnd : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : PathAlong oracleSig s₁) →
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁))) →
    Le (seamPrefix s₁ s₂ tr₁)
      (ofTranscript (s₁.append s₂) (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂))
  | .pure _, _, _, _ => .empty _
  | .liftBind a next, s₂, ⟨x, tr₁⟩, tr₂ =>
    .cons x (seamLeEnd (next (oracleSig.toFunB a x))
      (fun p => s₂ ⟨oracleSig.toFunB a x, p⟩) tr₁ tr₂)

/-- A sent oracle at the seam keeps its node name at the end of the appended run. -/
theorem seamLeEnd_node (s₁ : OracleProtocol.{u, q})
    (s₂ : Path s₁ → OracleProtocol.{u, q}) (tr₁ : PathAlong oracleSig s₁)
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁)))
    (i : SentOracle (seamPrefix s₁ s₂ tr₁)) :
    SentOracle.node (ofTranscript _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂))
        (SentOracle.lift (seamLeEnd s₁ s₂ tr₁ tr₂) i) =
      SentOracle.node (seamPrefix s₁ s₂ tr₁) i := SentOracle.node_lift _ _

/-- Every outcome of PolyFun's exchange `step` on two logged actions starts with one logged step
for each action (the prover's, then the challenger's), followed by the steps of the continuation.
This is a property of the exchange in the writer layer. -/
theorem mem_support_logStep {ι : Type} {spec : OracleSpec ι}
    {root s : OracleProtocol.{0, q}} {X R : Type} {A B : X → Type}
    (env : TranscriptPrefix s → TranscriptPrefix root) (role : TwoParty.Role)
    (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → WriterT (List (LoggedStep spec root)) (OracleComp spec) R)
    {r : R × List (LoggedStep spec root)}
    (hr : r ∈ support ((step role .focalFirst
      (logStep env .focal p) (logStep env .counterpart c) k).run)) :
    ∃ x pn cn lp lc child, child ∈ support ((k x pn cn).run) ∧
      r = (child.1, ⟨env .empty, .prover, lp⟩ :: ⟨env .empty, .challenger, lc⟩ :: child.2) := by
  cases role <;>
    simp only [step, Schedule.seq, logStep, WriterT.run_bind, WriterT.run_mk,
      bind_map_left, _root_.map_bind, Functor.map_map, mem_support_bind_iff] at hr
  · obtain ⟨vp, _, vc, _, h⟩ := hr
    obtain ⟨child, hc, heq⟩ := mem_support_map_peel _ _ h
    exact ⟨vp.1.1, vp.1.2, vc.1 vp.1.1, vp.2, vc.2, child, hc, heq⟩
  · obtain ⟨vp, _, vc, _, h⟩ := hr
    obtain ⟨child, hc, heq⟩ := mem_support_map_peel _ _ h
    exact ⟨vc.1.1, vp.1 vc.1.1, vc.1.2, vp.2, vc.2, child, hc, heq⟩

/-- Every step logged while the core runner runs wrapped strategies has a transcript so far that
is below the whole transcript of the run, as embedded by `env`. The embedding `env` places the
transcripts of the rest of the protocol inside the root protocol. -/
theorem mapStepsWith_prefixes {ι : Type} {spec : OracleSpec ι}
    {root : OracleProtocol.{0, q}} :
    (s : OracleProtocol.{0, q}) → {OutP OutC : PathAlong oracleSig s → Type} →
    (env : TranscriptPrefix s → TranscriptPrefix root) →
    (preserves : ∀ h k, Le h k → Nonempty (Le (env h) (env k))) →
    (p : Focal oracleSig (OracleComp spec) s OutP) →
    (c : Counterpart oracleSig (OracleComp spec) s OutC) →
    {r : ((tr : PathAlong oracleSig s) × OutP tr × OutC tr) ×
      List (LoggedStep spec root)} →
    r ∈ support ((TwoParty.Lens.run s
      (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix root)
        (@logStep ι spec root) (@extendPrefix root) env .focal p)
      (StepInstrumentation.mapStepsWith (C := fun t => TranscriptPrefix t → TranscriptPrefix root)
        (@logStep ι spec root) (@extendPrefix root) env .counterpart c)).run) →
    (step : LoggedStep spec root) → step ∈ r.2 →
      Nonempty (Le step.before (env (ofTranscript s r.1.1)))
  | .pure leaf, _, _, env, preserves, p, c, r, hr, step, hp => by
    cases leaf
    simp only [StepInstrumentation.mapStepsWith, FreeM.pure_eq_pure, run_done,
      logStep, WriterT.run_bind, WriterT.run_mk, WriterT.run_pure,
      bind_map_left, _root_.map_bind, Functor.map_map,
      mem_support_bind_iff] at hr
    obtain ⟨vp, _, vc, _, heq⟩ := hr
    subst r
    simp only [List.empty_eq, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact preserves _ _ (.empty _)
  | .liftBind a next, _, _, env, preserves, p, c, r, hr, step, hp => by
    rw [run_node] at hr
    simp only [StepInstrumentation.mapStepsWith, step_map_left, step_map_right] at hr
    obtain ⟨x, pn, cn, lp, lc, child, hc, heq⟩ := mem_support_logStep env _ _ _ _ hr
    simp only [WriterT.run_bind, WriterT.run_pure, LawfulApplicative.map_pure,
      mem_support_bind_iff, mem_support_pure_iff, List.empty_eq, List.append_nil] at hc
    obtain ⟨result, hresult, hchild⟩ := hc
    subst child
    subst r
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact preserves _ _ (.empty _)
    · exact preserves _ _ (.empty _)
    · exact mapStepsWith_prefixes (next (oracleSig.toFunB a x))
        (extendPrefix a next x env) (fun h k e => preserves _ _ (.cons x e))
        pn cn hresult step hp

/-- At the root, every step logged by `runLoggingSteps` has a transcript so far that is below the
whole transcript of the run. -/
theorem runLoggingSteps_prefixes {ι : Type} {spec : OracleSpec ι}
    (s : OracleProtocol.{0, q}) {OutP OutC : PathAlong oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC)
    {r : ((tr : PathAlong oracleSig s) × OutP tr × OutC tr) × List (LoggedStep spec s)}
    (hr : r ∈ support (runLoggingSteps s p c))
    (step : LoggedStep spec s) (hp : step ∈ r.2) :
    Nonempty (Le step.before (ofTranscript s r.1.1)) :=
  mapStepsWith_prefixes s id (fun _ _ e => ⟨e⟩) p c hr step hp

end TranscriptPrefix
namespace LoggedStep

/-- The resources available at this step: those available at its transcript so far. -/
abbrev availableContext {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (step : LoggedStep spec s) (inputs : Resources.{0, uI, dI}) :=
  step.before.availableResources inputs

/-- The input data and the payloads already sent give data for this step's available
resources. -/
def availableData {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (step : LoggedStep spec s) (inputs : Resources.{0, uI, dI}) (input : inputs.Data) :
    (step.availableContext inputs).Data :=
  (input, TranscriptPrefix.SentOracle.payload step.before)

/-- Include an earlier step's available resources in those of a later step whose transcript so far
continues the earlier one. -/
def availableMap {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (step later : LoggedStep spec s) (inputs : Resources.{0, uI, dI})
    (e : TranscriptPrefix.Le step.before later.before) :
    OracleMap (later.availableContext inputs) (step.availableContext inputs) :=
  TranscriptPrefix.availableMap inputs e

end LoggedStep

namespace OracleVerifier

/-- Every step in the step log of a run has a transcript so far that is below the whole transcript
of the run. -/
theorem runWithStepLog_prefixes {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : Resources.{0, 0, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : StepLog V Out}
    (hr : r ∈ support (V.runWithStepLog stmt input prover))
    (step : LoggedStep ambient s) (hp : step ∈ r.allSteps) :
    Nonempty (TranscriptPrefix.Le step.before
      (TranscriptPrefix.ofTranscript s r.observation.1)) := by
  simp only [runWithStepLog, executeWith, _root_.map_bind, LawfulApplicative.map_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨steps, hi, decision, _, heq⟩ := hr
  subst r
  simp only [StepLog.allSteps, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hp
    subst step
    exact TranscriptPrefix.runLoggingSteps_prefixes s _ _ hi raw hraw
  · exact ⟨TranscriptPrefix.Le.refl _⟩

/-- An oracle sent before a step of the run is still sent at the decision step. -/
theorem isSent_at_decision {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : Resources.{0, 0, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : StepLog V Out}
    (hr : r ∈ support (V.runWithStepLog stmt input prover))
    (step : LoggedStep ambient s) (hp : step ∈ r.allSteps) {n : Node s}
    (sent : step.before.IsSent n) : r.decisionStep.before.IsSent n := by
  obtain ⟨e⟩ := V.runWithStepLog_prefixes stmt input prover hr step hp
  exact sent.mono e

/-- The ambient step log also gives every step a transcript so far that is below the whole
transcript, for arbitrary resource-query universes. -/
theorem runWithAmbientStepLog_prefixes {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, q}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : Resources.{0, uI, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : AmbientStepLog V Out}
    (hr : r ∈ support (V.runWithAmbientStepLog stmt input prover))
    (step : LoggedStep ambient s) (hp : step ∈ r.allSteps) :
    Nonempty (TranscriptPrefix.Le step.before
      (TranscriptPrefix.ofTranscript s r.observation.1)) := by
  simp only [runWithAmbientStepLog, executeWith, _root_.map_bind, LawfulApplicative.map_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨steps, hi, decision, _, heq⟩ := hr
  subst r
  simp only [AmbientStepLog.allSteps, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hp
    subst step
    exact TranscriptPrefix.runLoggingSteps_prefixes s _ _ hi raw hraw
  · exact ⟨TranscriptPrefix.Le.refl _⟩

end OracleVerifier
end Interaction.Core

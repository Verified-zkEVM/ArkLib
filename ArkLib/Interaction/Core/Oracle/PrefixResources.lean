/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Oracle.Provenance
public import ArkLib.Interaction.Core.Oracle.Routing

/-!
# Resources at actual execution prefixes

An oracle becomes available only after its payload has been sent. Available oracle occurrences
have canonical structural node names. Extending a prefix includes its resources without changing
those names or their query behavior.
-/

@[expose] public section

universe u q uI dI

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace FullPrefix

/-- Oracle occurrences available strictly before a boundary. -/
def Index : {s : OracleProtocol.{u, q}} → FullPrefix s → Type u
  | .pure _, _ => PEmpty
  | .liftBind _ _, none => PEmpty
  | .liftBind (.message _) _, some ⟨_, tail⟩ => Index tail
  | .liftBind (.challenge _) _, some ⟨_, tail⟩ => Index tail
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩ => PUnit ⊕ Index tail

/-- The concrete payload type at an available occurrence. -/
def Data : {s : OracleProtocol.{u, q}} → (h : FullPrefix s) → Index h → Type u
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨_, tail⟩, i => Data tail i
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => Data tail i
  | .liftBind (.oracle X _) _, some ⟨_, tail⟩, i => Sum.elim (fun _ => X) (Data tail) i

/-- The canonical family of already sent oracle payloads. -/
def family : {s : OracleProtocol.{u, q}} → (h : FullPrefix s) → OracleFamily (Index h) (Data h)
  | .pure _, _ => ⟨fun i => i.elim⟩
  | .liftBind _ _, none => ⟨fun i => i.elim⟩
  | .liftBind (.message _) _, some ⟨_, tail⟩ => family tail
  | .liftBind (.challenge _) _, some ⟨_, tail⟩ => family tail
  | .liftBind (.oracle _ I) _, some ⟨_, tail⟩ => sumFamily (singletonFamily I) (family tail)

/-- The actual concrete data already sent in this full prefix. -/
def data : {s : OracleProtocol.{u, q}} → (h : FullPrefix s) → (i : Index h) → Data h i
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨_, tail⟩, i => data tail i
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => data tail i
  | .liftBind (.oracle _ _) _, some ⟨x, _⟩, .inl _ => x
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩, .inr i => data tail i

/-- Canonical names are node occurrences in the original protocol, independent of later moves. -/
def name : {s : OracleProtocol.{u, q}} → (h : FullPrefix s) → Index h → Node s
  | .pure _, _, i => i.elim
  | .liftBind _ _, none, i => i.elim
  | .liftBind (.message _) _, some ⟨x, tail⟩, i => .inr ⟨x, name tail i⟩
  | .liftBind (.challenge _) _, some ⟨_, tail⟩, i => .inr ⟨⟨⟩, name tail i⟩
  | .liftBind (.oracle _ _) _, some ⟨_, _⟩, .inl _ => .inl ⟨⟩
  | .liftBind (.oracle _ _) _, some ⟨_, tail⟩, .inr i => .inr ⟨⟨⟩, name tail i⟩

/-- A node is available precisely when it names an already sent oracle. -/
def Available {s : OracleProtocol.{u, q}} (h : FullPrefix s) (n : Node s) : Prop :=
  ∃ i, h.name i = n

/-- Inputs and exactly the already sent payloads are available at a prefix. -/
def resources (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}} (h : FullPrefix s) :=
  inputs.sum (Resources.ofFamily h.family)

/-- A resource query's canonical input name or sent-oracle occurrence. -/
def queryName (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}} (h : FullPrefix s) :
    (h.resources inputs).Index → inputs.Index ⊕ Node s
  | .inl i => .inl i
  | .inr ⟨i, _⟩ => .inr (h.name i)

/-- Inclusion of actual prefixes, preserving every earlier move. -/
inductive Extends : {s : OracleProtocol.{u, q}} → FullPrefix s → FullPrefix s →
    Type (max (u + 1) (q + 1)) where
  | here {s} (h : FullPrefix s) : Extends (.here : FullPrefix s) h
  | cons {a : OraclePos.{u, q}} {next : OraclePoly.B a → OracleProtocol}
      (x : Move oracleSig a) {h k : FullPrefix (next (oracleSig.toFunB a x))}
      (tail : Extends h k) : Extends (.cons x h) (.cons x k)

/-- Every prefix includes itself, including its concrete challenge and payload values. -/
def Extends.refl : {s : OracleProtocol.{u, q}} → (h : FullPrefix s) → Extends h h
  | .pure _, none => .here _
  | .pure _, some impossible => impossible.elim
  | .liftBind _ _, none => .here _
  | .liftBind _ _, some ⟨x, tail⟩ => .cons x (Extends.refl tail)

/-- Include the earlier available occurrences in the later context. -/
def includeIndex : {s : OracleProtocol.{u, q}} → {h k : FullPrefix s} →
    Extends h k → Index h → Index k
  | s, _, _, .here _, i => by cases s <;> exact PEmpty.elim i
  | _, _, _, @Extends.cons (.message _) next x h k tail, i =>
    includeIndex (s := next x) (h := h) (k := k) tail i
  | _, _, _, @Extends.cons (.challenge _) next _ h k tail, i =>
    includeIndex (s := next ⟨⟩) (h := h) (k := k) tail i
  | _, _, _, @Extends.cons (.oracle _ _) _ _ h k tail, .inl i => .inl i
  | _, _, _, @Extends.cons (.oracle _ _) _ _ h k tail, .inr i =>
    .inr (includeIndex (h := h) (k := k) tail i)

/-- Prefix inclusion preserves the canonical occurrence name. -/
theorem includeIndex_name : {s : OracleProtocol.{u, q}} → {h k : FullPrefix s} →
    (e : Extends h k) → (i : Index h) → k.name (includeIndex e i) = h.name i
  | s, _, _, .here _, i => by cases s <;> exact PEmpty.elim i
  | _, _, _, @Extends.cons (.message X) next x h k tail, i =>
    congrArg (fun n : Node (next x) =>
      (Sum.inr ⟨x, n⟩ : Node (P := OraclePoly.{u, q}) (.liftBind (.message X) next)))
      (includeIndex_name tail i)
  | _, _, _, @Extends.cons (.challenge C) next _ h k tail, i =>
    congrArg (fun n : Node (next ⟨⟩) =>
      (Sum.inr ⟨⟨⟩, n⟩ : Node (P := OraclePoly.{u, q}) (.liftBind (.challenge C) next)))
      (includeIndex_name tail i)
  | _, _, _, @Extends.cons (.oracle _ _) _ _ _ _ _, .inl _ => rfl
  | _, _, _, @Extends.cons (.oracle X I) next _ h k tail, .inr i =>
    congrArg (fun n : Node (next ⟨⟩) =>
      (Sum.inr ⟨⟨⟩, n⟩ : Node (P := OraclePoly.{u, q}) (.liftBind (.oracle X I) next)))
      (includeIndex_name tail i)

/-- Extending an actual prefix cannot remove an available occurrence. -/
theorem Available.mono {s : OracleProtocol.{u, q}} {h k : FullPrefix s} (e : Extends h k)
    {n : Node s} (available : h.Available n) : k.Available n := by
  obtain ⟨i, rfl⟩ := available
  exact ⟨includeIndex e i, includeIndex_name e i⟩

/-- Include an earlier typed query, retaining its actual query argument. -/
def includeQuery : {s : OracleProtocol.{u, q}} → {h k : FullPrefix s} →
    Extends h k → (family h).spec.Domain → (family k).spec.Domain
  | s, _, _, .here _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Extends.cons (.message _) next x h k tail, r =>
    includeQuery (s := next x) (h := h) (k := k) tail r
  | _, _, _, @Extends.cons (.challenge _) next _ h k tail, r =>
    includeQuery (s := next ⟨⟩) (h := h) (k := k) tail r
  | _, _, _, @Extends.cons (.oracle _ _) _ _ _ _ _, ⟨.inl i, r⟩ => ⟨.inl i, r⟩
  | _, _, _, @Extends.cons (.oracle _ _) _ _ h k tail, ⟨.inr i, r⟩ =>
    let query := includeQuery (h := h) (k := k) tail ⟨i, r⟩
    ⟨.inr query.1, query.2⟩

/-- Query inclusion uses the same canonical occurrence inclusion as the resource context. -/
theorem includeQuery_index : {s : OracleProtocol.{u, q}} → {h k : FullPrefix s} →
    (e : Extends h k) → (r : (family h).spec.Domain) →
    (includeQuery e r).1 = includeIndex e r.1
  | s, _, _, .here _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Extends.cons (.message _) _ _ _ _ tail, r => includeQuery_index tail r
  | _, _, _, @Extends.cons (.challenge _) _ _ _ _ tail, r => includeQuery_index tail r
  | _, _, _, @Extends.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => rfl
  | _, _, _, @Extends.cons (.oracle _ _) _ _ _ _ tail, ⟨.inr i, r⟩ =>
    congrArg Sum.inr (includeQuery_index tail ⟨i, r⟩)

/-- Naming an included query gives exactly its earlier canonical occurrence. -/
theorem includeQuery_name {s : OracleProtocol.{u, q}} {h k : FullPrefix s}
    (e : Extends h k) (r : (family h).spec.Domain) :
    k.name (includeQuery e r).1 = h.name r.1 := by
  rw [includeQuery_index, includeIndex_name]

/-- Typed inclusion preserves the response type as well as the query argument. -/
theorem includeQuery_response : {s : OracleProtocol.{u, q}} → {h k : FullPrefix s} →
    (e : Extends h k) → (r : (family h).spec.Domain) →
    (family h).spec r = (family k).spec (includeQuery e r)
  | s, _, _, .here _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Extends.cons (.message _) _ _ _ _ tail, r => includeQuery_response tail r
  | _, _, _, @Extends.cons (.challenge _) _ _ _ _ tail, r => includeQuery_response tail r
  | _, _, _, @Extends.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => rfl
  | _, _, _, @Extends.cons (.oracle _ _) _ _ _ _ tail, ⟨.inr i, r⟩ =>
    includeQuery_response tail ⟨i, r⟩

/-- Restrict the later payload family to the earlier prefix. -/
def familyInclusion : {s : OracleProtocol.{u, q}} → {h k : FullPrefix s} →
    Extends h k → OracleMap (family k) (family h)
  | s, _, _, .here _ => by
    cases s <;> exact
      { f := fun _ i => PEmpty.elim i
        impl := fun r => PEmpty.elim r.1
        law := fun _ r => PEmpty.elim r.1 }
  | _, _, _, @Extends.cons (.message _) next x h k tail =>
    familyInclusion (s := next x) (h := h) (k := k) tail
  | _, _, _, @Extends.cons (.challenge _) next _ h k tail =>
    familyInclusion (s := next ⟨⟩) (h := h) (k := k) tail
  | _, _, _, @Extends.cons (.oracle _ I) _ _ h k tail =>
    (OracleMap.id (Resources.ofFamily (singletonFamily I))).sum
      (familyInclusion (h := h) (k := k) tail)

/-- Inclusion routes each query to the included occurrence with its unchanged argument. -/
theorem familyInclusion_query : {s : OracleProtocol.{u, q}} → {h k : FullPrefix s} →
    (e : Extends h k) → (r : (family h).spec.Domain) →
    HEq ((familyInclusion e).impl r)
      (liftM ((family k).spec.query (includeQuery e r)) : OracleComp (family k).spec _)
  | s, _, _, .here _, r => by cases s <;> exact PEmpty.elim r.1
  | _, _, _, @Extends.cons (.message _) _ _ _ _ tail, r => familyInclusion_query tail r
  | _, _, _, @Extends.cons (.challenge _) _ _ _ _ tail, r => familyInclusion_query tail r
  | _, _, _, @Extends.cons (.oracle _ _) _ _ _ _ _, ⟨.inl _, _⟩ => by
    rfl
  | _, _, _, @Extends.cons (.oracle _ I) _ _ h k tail, ⟨.inr i, r⟩ => by
    dsimp only [familyInclusion]
    erw [OracleMap.sum_impl_inr]
    have ih := familyInclusion_query tail ⟨i, r⟩
    let handler : QueryImpl (family k).spec
        (OracleComp (sumFamily (singletonFamily I) (family k)).spec) := fun r =>
      liftM ((sumFamily (singletonFamily I) (family k)).spec.query ⟨.inr r.1, r.2⟩)
    have lift_heq {α β : Type u} (eq : α = β)
        {p : OracleComp (family k).spec α} {p' : OracleComp (family k).spec β}
        (same : HEq p p') : HEq (simulateQ handler p) (simulateQ handler p') := by
      subst β
      cases same
      rfl
    have lifted := lift_heq (includeQuery_response tail ⟨i, r⟩) ih
    change HEq (simulateQ handler ((familyInclusion tail).impl ⟨i, r⟩))
      (liftM ((sumFamily (singletonFamily I) (family k)).spec.query
        ⟨.inr (includeQuery tail ⟨i, r⟩).1, (includeQuery tail ⟨i, r⟩).2⟩) :
          OracleComp (sumFamily (singletonFamily I) (family k)).spec _)
    simp only [simulateQ_spec_query, handler] at lifted
    exact lifted

/-- Prefix-resource inclusion routes earlier queries through the later available resources. -/
def contextInclusion (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : FullPrefix s} (e : Extends h k) : OracleMap (k.resources inputs) (h.resources inputs) :=
  (OracleMap.id inputs).par (familyInclusion e)

/-- Earlier input names and sent-oracle names are preserved by canonical inclusion. -/
def includeName (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : FullPrefix s} (e : Extends h k) :
    inputs.Index ⊕ Index h → inputs.Index ⊕ Index k := Sum.map id (includeIndex e)

/-- The inclusion's names agree in the original protocol, before and after extension. -/
theorem contextInclusion_name (inputs : Resources.{u, uI, dI}) {s : OracleProtocol.{u, q}}
    {h k : FullPrefix s} (e : Extends h k) (i : inputs.Index ⊕ Index h) :
    Sum.map id k.name (includeName inputs e i) = Sum.map id h.name i := by
  cases i with
  | inl i => rfl
  | inr i => exact congrArg Sum.inr (includeIndex_name e i)

/-- Identify a completed prefix's family with the path family used by the verifier. -/
def pathInclusion : (s : OracleProtocol.{u, q}) → (tr : PathAlong oracleSig s) →
    OracleMap (pathFamily s (projectPathAlong oracleSig s tr)) (family (complete s tr))
  | .pure _, _ =>
    { f := fun _ i => i.elim
      impl := fun r => r.1.elim
      law := fun _ r => r.1.elim }
  | .liftBind (.message _) next, ⟨x, tr⟩ => pathInclusion (next x) tr
  | .liftBind (.challenge _) next, ⟨_, tr⟩ => pathInclusion (next ⟨⟩) tr
  | .liftBind (.oracle _ I) next, ⟨_, tr⟩ =>
    (OracleMap.id (Resources.ofFamily (singletonFamily I))).sum (pathInclusion (next ⟨⟩) tr)

/-- The prefix bridge reads exactly the concrete payloads of the same transcript. -/
theorem pathInclusion_data : (s : OracleProtocol.{u, q}) → (tr : PathAlong oracleSig s) →
    (pathInclusion s tr).f (payloads s tr) = data (complete s tr)
  | .pure _, _ => by funext i; exact i.elim
  | .liftBind (.message _) next, ⟨x, tr⟩ => pathInclusion_data (next x) tr
  | .liftBind (.challenge _) next, ⟨_, tr⟩ => pathInclusion_data (next ⟨⟩) tr
  | .liftBind (.oracle _ _) next, ⟨_, tr⟩ => by
    funext i
    cases i with
    | inl _ => rfl
    | inr i => exact congrFun (pathInclusion_data (next ⟨⟩) tr) i

/-- Route the verifier's completed-path resources to the canonical completed prefix. -/
def pathResourcesInclusion (inputs : Resources.{u, uI, dI})
    (s : OracleProtocol.{u, q}) (tr : PathAlong oracleSig s) :
    OracleMap (pathResources inputs s (projectPathAlong oracleSig s tr))
      ((complete s tr).resources inputs) :=
  (OracleMap.id inputs).par (pathInclusion s tr)

/-- Routing from `pathResources` retains inputs and the exact sent payloads. -/
theorem pathResourcesInclusion_data (inputs : Resources.{u, uI, dI}) (input : inputs.Data)
    (s : OracleProtocol.{u, q}) (tr : PathAlong oracleSig s) :
    (pathResourcesInclusion inputs s tr).f (input, payloads s tr) =
      (input, data (complete s tr)) := by
  exact congrArg (input, ·) (pathInclusion_data s tr)

/-- The actual boundary after a completed prefix protocol, before the suffix's first slot. -/
def joinPrefix : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : PathAlong oracleSig s₁) →
    FullPrefix (s₁.append s₂)
  | .pure _, _, _ => .here
  | .liftBind a next, s₂, ⟨x, tr⟩ =>
    .cons x (joinPrefix (next (oracleSig.toFunB a x))
      (fun p => s₂ ⟨oracleSig.toFunB a x, p⟩) tr)

/-- The actual join prefix extends to the full transcript of the appended execution. -/
def joinToTerminal : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) → (tr₁ : PathAlong oracleSig s₁) →
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁))) →
    Extends (joinPrefix s₁ s₂ tr₁)
      (complete (s₁.append s₂) (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂))
  | .pure _, _, _, _ => .here _
  | .liftBind a next, s₂, ⟨x, tr₁⟩, tr₂ =>
    .cons x (joinToTerminal (next (oracleSig.toFunB a x))
      (fun p => s₂ ⟨oracleSig.toFunB a x, p⟩) tr₁ tr₂)

/-- A join resource keeps its canonical name at the terminal boundary. -/
theorem joinToTerminal_name (s₁ : OracleProtocol.{u, q})
    (s₂ : Path s₁ → OracleProtocol.{u, q}) (tr₁ : PathAlong oracleSig s₁)
    (tr₂ : PathAlong oracleSig (s₂ (projectPathAlong oracleSig s₁ tr₁)))
    (i : Index (joinPrefix s₁ s₂ tr₁)) :
    (complete _ (PathAlong.append oracleSig s₁ s₂ tr₁ tr₂)).name
        (includeIndex (joinToTerminal s₁ s₂ tr₁ tr₂) i) =
      (joinPrefix s₁ s₂ tr₁).name i := includeIndex_name _ _

/-- Support of an instrumented exchange contains exactly its two slot labels before the
continuation's labels. This is a writer-layer property of PolyFun's exchange operation. -/
theorem mem_support_observedStep {ι : Type} {spec : OracleSpec ι}
    {root s : OracleProtocol.{0, q}} {X R : Type} {A B : X → Type}
    (env : FullPrefix s → FullPrefix root) (role : TwoParty.Role)
    (p : OracleComp spec (Choice .focal role X A))
    (c : OracleComp spec (Choice .counterpart role X B))
    (k : ∀ x, A x → B x → WriterT (List (SlotPhase spec root)) (OracleComp spec) R)
    {r : R × List (SlotPhase spec root)}
    (hr : r ∈ support ((step role .focalFirst
      (observeSlot env .focal p) (observeSlot env .counterpart c) k).run)) :
    ∃ x pn cn lp lc child, child ∈ support ((k x pn cn).run) ∧
      r = (child.1, ⟨env .here, .prover, lp⟩ :: ⟨env .here, .sampler, lc⟩ :: child.2) := by
  cases role <;>
    simp only [step, Schedule.seq, observeSlot, WriterT.run_bind, WriterT.run_mk,
      bind_map_left, _root_.map_bind, Functor.map_map, mem_support_bind_iff] at hr
  · obtain ⟨vp, _, vc, _, h⟩ := hr
    obtain ⟨child, hc, heq⟩ := mem_support_map_peel _ _ h
    exact ⟨vp.1.1, vp.1.2, vc.1 vp.1.1, vp.2, vc.2, child, hc, heq⟩
  · obtain ⟨vp, _, vc, _, h⟩ := hr
    obtain ⟨child, hc, heq⟩ := mem_support_map_peel _ _ h
    exact ⟨vc.1.1, vp.1 vc.1.1, vc.1.2, vp.2, vc.2, child, hc, heq⟩

/-- Every writer label produced by the authoritative runner is an actual transcript prefix.
The environment embeds the current suffix's prefixes in the original execution. -/
theorem instrumented_prefixes {ι : Type} {spec : OracleSpec ι}
    {root : OracleProtocol.{0, q}} :
    (s : OracleProtocol.{0, q}) → {OutP OutC : PathAlong oracleSig s → Type} →
    (env : FullPrefix s → FullPrefix root) →
    (preserves : ∀ h k, Extends h k → Nonempty (Extends (env h) (env k))) →
    (p : Focal oracleSig (OracleComp spec) s OutP) →
    (c : Counterpart oracleSig (OracleComp spec) s OutC) →
    {r : ((tr : PathAlong oracleSig s) × OutP tr × OutC tr) ×
      List (SlotPhase spec root)} →
    r ∈ support ((TwoParty.Lens.run s
      (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix root)
        (@observeSlot ι spec root) (@descendPrefix root) env .focal p)
      (SlotInstrumentation.transform (C := fun t => FullPrefix t → FullPrefix root)
        (@observeSlot ι spec root) (@descendPrefix root) env .counterpart c)).run) →
    (phase : SlotPhase spec root) → phase ∈ r.2 →
      Nonempty (Extends phase.prefix (env (complete s r.1.1)))
  | .pure leaf, _, _, env, preserves, p, c, r, hr, phase, hp => by
    cases leaf
    simp only [SlotInstrumentation.transform, FreeM.pure_eq_pure, run_done,
      observeSlot, WriterT.run_bind, WriterT.run_mk, WriterT.run_pure,
      bind_map_left, _root_.map_bind, Functor.map_map,
      mem_support_bind_iff] at hr
    obtain ⟨vp, _, vc, _, heq⟩ := hr
    subst r
    simp only [List.empty_eq, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact preserves _ _ (.here _)
  | .liftBind a next, _, _, env, preserves, p, c, r, hr, phase, hp => by
    rw [run_node] at hr
    simp only [SlotInstrumentation.transform, step_map_left, step_map_right] at hr
    obtain ⟨x, pn, cn, lp, lc, child, hc, heq⟩ := mem_support_observedStep env _ _ _ _ hr
    simp only [WriterT.run_bind, WriterT.run_pure, LawfulApplicative.map_pure,
      mem_support_bind_iff, mem_support_pure_iff, List.empty_eq, List.append_nil] at hc
    obtain ⟨result, hresult, hchild⟩ := hc
    subst child
    subst r
    simp only [List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · exact preserves _ _ (.here _)
    · exact preserves _ _ (.here _)
    · exact instrumented_prefixes (next (oracleSig.toFunB a x))
        (descendPrefix a next x env) (fun h k e => preserves _ _ (.cons x e))
        pn cn hresult phase hp

/-- Root instrumentation starts at the empty actual prefix. -/
theorem observeInteraction_prefixes {ι : Type} {spec : OracleSpec ι}
    (s : OracleProtocol.{0, q}) {OutP OutC : PathAlong oracleSig s → Type}
    (p : Focal oracleSig (OracleComp spec) s OutP)
    (c : Counterpart oracleSig (OracleComp spec) s OutC)
    {r : ((tr : PathAlong oracleSig s) × OutP tr × OutC tr) × List (SlotPhase spec s)}
    (hr : r ∈ support (observeInteraction s p c))
    (phase : SlotPhase spec s) (hp : phase ∈ r.2) :
    Nonempty (Extends phase.prefix (complete s r.1.1)) :=
  instrumented_prefixes s id (fun _ _ e => ⟨e⟩) p c hr phase hp

end FullPrefix
namespace SlotPhase

/-- The canonical resources available at this phase's actual preceding prefix. -/
abbrev availableContext {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (phase : SlotPhase spec s) (inputs : Resources.{0, uI, dI}) :=
  phase.prefix.resources inputs

/-- Actual input data and already sent payloads materialize this phase's available resources. -/
def availableData {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (phase : SlotPhase spec s) (inputs : Resources.{0, uI, dI}) (input : inputs.Data) :
    (phase.availableContext inputs).Data := (input, phase.prefix.data)

/-- Include an earlier phase's resources in a later actual prefix. -/
def contextInclusion {ι : Type} {spec : OracleSpec ι} {s : OracleProtocol.{0, q}}
    (phase later : SlotPhase spec s) (inputs : Resources.{0, uI, dI})
    (e : FullPrefix.Extends phase.prefix later.prefix) :
    OracleMap (later.availableContext inputs) (phase.availableContext inputs) :=
  FullPrefix.contextInclusion inputs e

end SlotPhase

namespace OracleVerifier

/-- Every phase of a produced verifier trace has an actual prefix of its completed transcript. -/
theorem runWithTrace_prefixes {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : Resources.{0, 0, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : TracedRun V Out}
    (hr : r ∈ support (V.runWithTrace stmt input prover))
    (phase : SlotPhase ambient s) (hp : phase ∈ r.phases) :
    Nonempty (FullPrefix.Extends phase.prefix (FullPrefix.complete s r.observation.1)) := by
  simp only [runWithTrace, executeWith, _root_.map_bind, LawfulApplicative.map_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨interaction, hi, decision, _, heq⟩ := hr
  subst r
  simp only [TracedRun.phases, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hp
    subst phase
    exact FullPrefix.observeInteraction_prefixes s _ _ hi raw hraw
  · exact ⟨FullPrefix.Extends.refl _⟩

/-- Every oracle available at a produced phase remains available at the terminal prefix. -/
theorem available_at_terminal {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : Resources.{0, 0, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : TracedRun V Out}
    (hr : r ∈ support (V.runWithTrace stmt input prover))
    (phase : SlotPhase ambient s) (hp : phase ∈ r.phases) {n : Node s}
    (available : phase.prefix.Available n) : r.terminalPhase.prefix.Available n := by
  obtain ⟨e⟩ := V.runWithTrace_prefixes stmt input prover hr phase hp
  exact available.mono e

/-- Ambient traces retain actual prefix provenance for arbitrary resource-query universes. -/
theorem runWithAmbientTrace_prefixes {ι : Type} {S : Type u} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, q}} {T : Path s → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : Resources.{0, uI, dI}}
    {outputs : (p : Path s) → OracleFamily (J p) (B p)}
    {Out : PathAlong oracleSig s → Type}
    (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (input : inputs.Data)
    (prover : Prover oracleSig ambient s Out) {r : AmbientTracedRun V Out}
    (hr : r ∈ support (V.runWithAmbientTrace stmt input prover))
    (phase : SlotPhase ambient s) (hp : phase ∈ r.phases) :
    Nonempty (FullPrefix.Extends phase.prefix (FullPrefix.complete s r.observation.1)) := by
  simp only [runWithAmbientTrace, executeWith, _root_.map_bind, LawfulApplicative.map_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨interaction, hi, decision, _, heq⟩ := hr
  subst r
  simp only [AmbientTracedRun.phases, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hp
    subst phase
    exact FullPrefix.observeInteraction_prefixes s _ _ hi raw hraw
  · exact ⟨FullPrefix.Extends.refl _⟩

end OracleVerifier
end Interaction.Core

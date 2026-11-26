/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Routing
public import VCVio.OracleComp.EvalDist

/-!
# Appended oracle verifiers on completed runs

This file states the final decision and the output data of a passive oracle verifier on a
completed transcript, as `OracleVerifier.decideOn` and `OracleVerifier.outputOn`. Both read the
transcript's path and view, and answer the bundle queries from the input data and the
transcript's oracle messages.

On an appended run `Transcript.append s₁ s₂ tr₁ tr₂`, the verifier `V₁.append V₂ c` decides as
`V₁` on `tr₁` followed, after acceptance only, by `V₂` on `tr₂` (`OracleVerifier.append_decideOn`).
The suffix decision starts from the accepted intermediate statement and the prefix output data.
Once the prefix decision accepts, the output data is the suffix output data
(`OracleVerifier.append_outputOn`).

`OracleVerifier.append_append_decideOn` and `OracleVerifier.append_append_outputOn` reassociate
the append of three verifiers. The left association runs on `append (append tr₁ tr₂) tr₃`, the
right association on `append tr₁ (append tr₂ tr₃')`, and `Transcript.append_append_heq` relates
the two transcripts. The two associations have different protocols, and their paths and statement
types agree only propositionally. Each law is therefore an `HEq` between the two sides. The laws are
stated on runs, not as an equation of verifiers, for two reasons. First, the output map of an
appended verifier is the output map of its certificate, and that map agrees with the composite of
the two output maps only on accepted intermediate statements. The certificates of the two
associations are independent, and the two verifiers can differ off the accepted runs. Second, a
client rewrites a decision or output data on a run, which these laws state directly.
-/

@[expose] public section

universe u q w uY uA v z

namespace Interaction
open PFunctor FreeM TwoParty.Lens OracleComp Oracle

attribute [local implicit_reducible] projectPathAlong projectPathAlongLocalMap
  Displayed.LocalMap.toHom Displayed.LocalMap.toHomFun

/-! ## Views and bundle data of an appended run -/

/-- Split views, packaged with their split path. -/
abbrev SplitViews (s₁ : OracleProtocol.{u, q}) (s₂ : Path s₁ → OracleProtocol.{u, q}) :=
  (z : (p : Path s₁) × Path (s₂ p)) × View s₁ z.1 × View (s₂ z.1) z.2

/-- Splitting the view of an appended path gives the views of the two parts of its transcript
split, at the split path. -/
theorem View.split_mk (s₁ : OracleProtocol.{u, q}) (s₂ : Path s₁ → OracleProtocol.{u, q})
    (x : Transcript viewSig (s₁.append s₂)) :
    (⟨Path.split s₁ s₂ x.path, View.split s₁ s₂ x.path ⟨x, rfl⟩⟩ : SplitViews s₁ s₂) =
      ⟨⟨(Transcript.split s₁ s₂ x).1.path, (Transcript.split s₁ s₂ x).2.path⟩,
        (⟨(Transcript.split s₁ s₂ x).1, rfl⟩, ⟨(Transcript.split s₁ s₂ x).2, rfl⟩)⟩ := by
  have key : ∀ {a b : (p : Path s₁) × Path (s₂ p)} (h : a = b)
      (y : View s₁ a.1 × View (s₂ a.1) a.2),
      (⟨b, h ▸ y⟩ : SplitViews s₁ s₂) = ⟨a, y⟩ := by
    intro a b h y
    subst h
    rfl
  exact key (project_split viewSig s₁ s₂ x) _

/-- Erasing the oracle messages of an appended transcript and splitting the result gives the
paths and views of the two parts. -/
theorem split_mapMoves_append : (s₁ : OracleProtocol.{u, q}) →
    (s₂ : Path s₁ → OracleProtocol.{u, q}) →
    (tr₁ : Transcript oracleSig s₁) → (tr₂ : Transcript oracleSig (s₂ tr₁.path)) →
    (⟨⟨(Transcript.split s₁ s₂ (Transcript.mapMoves eraseOracle
          (Transcript.append s₁ s₂ tr₁ tr₂))).1.path,
        (Transcript.split s₁ s₂ (Transcript.mapMoves eraseOracle
          (Transcript.append s₁ s₂ tr₁ tr₂))).2.path⟩,
      (⟨(Transcript.split s₁ s₂ (Transcript.mapMoves eraseOracle
          (Transcript.append s₁ s₂ tr₁ tr₂))).1, rfl⟩,
        ⟨(Transcript.split s₁ s₂ (Transcript.mapMoves eraseOracle
          (Transcript.append s₁ s₂ tr₁ tr₂))).2, rfl⟩)⟩ : SplitViews s₁ s₂) =
      ⟨⟨tr₁.path, tr₂.path⟩, (toView s₁ tr₁, toView _ tr₂)⟩
  | .pure _, s₂, ⟨⟩, tr₂ => by
    have key : ∀ p (h : (Transcript.mapMoves eraseOracle tr₂).path = p),
        (⟨⟨⟨⟩, (Transcript.mapMoves eraseOracle tr₂).path⟩,
          (⟨⟨⟩, rfl⟩, ⟨Transcript.mapMoves eraseOracle tr₂, rfl⟩)⟩ :
            SplitViews (.pure ⟨⟩) s₂) =
          ⟨⟨⟨⟩, p⟩, (⟨⟨⟩, rfl⟩, ⟨Transcript.mapMoves eraseOracle tr₂, h⟩)⟩ := by
      intro p h
      subst h
      rfl
    exact key _ _
  | .liftBind (.message X) next, s₂, ⟨x, tr₁⟩, tr₂ =>
    congrArg (fun z : SplitViews (next x) (fun p => s₂ ⟨x, p⟩) =>
      (⟨⟨⟨x, z.1.1⟩, z.1.2⟩, (⟨⟨x, z.2.1.1⟩, congrArg (Sigma.mk _) z.2.1.2⟩, z.2.2)⟩ :
        SplitViews (.liftBind (.message X) next) s₂))
      (split_mapMoves_append (next x) (fun p => s₂ ⟨x, p⟩) tr₁ tr₂)
  | .liftBind (.challenge X) next, s₂, ⟨x, tr₁⟩, tr₂ =>
    congrArg (fun z : SplitViews (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) =>
      (⟨⟨⟨⟨⟩, z.1.1⟩, z.1.2⟩, (⟨⟨x, z.2.1.1⟩, congrArg (Sigma.mk _) z.2.1.2⟩, z.2.2)⟩ :
        SplitViews (.liftBind (.challenge X) next) s₂))
      (split_mapMoves_append (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) tr₁ tr₂)
  | .liftBind (.oracle X I) next, s₂, ⟨x, tr₁⟩, tr₂ =>
    congrArg (fun z : SplitViews (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) =>
      (⟨⟨⟨⟨⟩, z.1.1⟩, z.1.2⟩, (⟨⟨⟨⟩, z.2.1.1⟩, congrArg (Sigma.mk _) z.2.1.2⟩, z.2.2)⟩ :
        SplitViews (.liftBind (.oracle X I) next) s₂))
      (split_mapMoves_append (next ⟨⟩) (fun p => s₂ ⟨⟨⟩, p⟩) tr₁ tr₂)

/-- The view of an appended transcript splits into the views of its parts. -/
theorem toView_split_append (s₁ : OracleProtocol.{u, q}) (s₂ : Path s₁ → OracleProtocol.{u, q})
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path)) :
    (⟨Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path,
      View.split s₁ s₂ _ (toView _ (Transcript.append s₁ s₂ tr₁ tr₂))⟩ : SplitViews s₁ s₂) =
      ⟨⟨tr₁.path, tr₂.path⟩, (toView s₁ tr₁, toView _ tr₂)⟩ := by
  have key : ∀ (x : Transcript viewSig (s₁.append s₂)) p (h : x.path = p),
      (⟨Path.split s₁ s₂ p, View.split s₁ s₂ p ⟨x, h⟩⟩ : SplitViews s₁ s₂) =
        ⟨Path.split s₁ s₂ x.path, View.split s₁ s₂ x.path ⟨x, rfl⟩⟩ := by
    intro x p h
    subst h
    rfl
  exact (key _ _ _).trans ((View.split_mk s₁ s₂ _).trans
    (split_mapMoves_append s₁ s₂ tr₁ tr₂))


/-! ## Transport helpers for dependent pairs -/

/-- Extend an equality of dependent pairs by a heterogeneously equal component. -/
theorem sigma_extend {Q : Type _} {A : Q → Type _} {B : Q → Type _} {q q' : Q} {a : A q}
    {a' : A q'} {b : B q} {b' : B q'} (h : (⟨q, a⟩ : (q : Q) × A q) = ⟨q', a'⟩)
    (hb : HEq b b') : (⟨q, (a, b)⟩ : (q : Q) × A q × B q) = ⟨q', (a', b')⟩ := by
  obtain ⟨rfl, ha⟩ := Sigma.mk.inj_iff.mp h
  cases ha
  cases hb
  rfl

/-- Pair two equalities of dependent pairs over the same index. -/
theorem sigma_extend' {Q : Type _} {A : Q → Type _} {B : Q → Type _} {q q' : Q} {a : A q}
    {a' : A q'} {b : B q} {b' : B q'} (h : (⟨q, a⟩ : (q : Q) × A q) = ⟨q', a'⟩)
    (hb : (⟨q, b⟩ : (q : Q) × B q) = ⟨q', b'⟩) :
    (⟨q, (a, b)⟩ : (q : Q) × A q × B q) = ⟨q', (a', b')⟩ :=
  sigma_extend h (Sigma.mk.inj_iff.mp hb).2

/-- A dependent function of equal arguments gives heterogeneously equal values. -/
theorem heq_apply₂ {X : Type _} {M : X → Type _} {R : (x : X) → M x → Type _}
    (G : (x : X) → (m : M x) → R x m) {x x' : X} (hx : x = x') {m : M x} {m' : M x'}
    (hm : HEq m m') : HEq (G x m) (G x' m') := by
  subst hx
  cases hm
  rfl

namespace OracleVerifier

section Transcripts

variable {ι : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}} {S : Type}
  {T : Path s → Type} {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}

/-- The decision on a completed transcript: at its path and view, with the bundle queries answered
from the input data and the transcript's oracle messages. -/
def decideOn (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (tr : Transcript oracleSig s) : OracleComp ambient (Option (T tr.path)) :=
  V.decideWith stmt tr.path (toView s tr) (data, oracleMessages s tr)

/-- The output data on a completed transcript: the output map at its path and view, applied to
the input data and the transcript's oracle messages. -/
def outputOn (V : OracleVerifier ambient s S T inputs outputs) (stmt : S) (data : inputs.Data)
    (tr : Transcript oracleSig s) : (outputs tr.path).Data :=
  (V.outputMap stmt tr.path (toView s tr)).f (data, oracleMessages s tr)

end Transcripts

variable {ι : Type} {ambient : OracleSpec ι}
  {inputs : OracleBundle}
  {s₁ : OracleProtocol.{0, 0}} {s₂ : Path s₁ → OracleProtocol.{0, 0}} {S : Type}
  {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
  {middle : Path s₁ → OracleBundle}
  {outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle}

/-- The split path of an appended run with the split views, the prefix bundle data and the suffix
oracle messages. -/
abbrev SplitRun (inputs : OracleBundle) (s₁ : OracleProtocol.{0, 0})
    (s₂ : Path s₁ → OracleProtocol.{0, 0}) :=
  (z : (p : Path s₁) × Path (s₂ p)) × (View s₁ z.1 × View (s₂ z.1) z.2) ×
    ((pathBundle inputs s₁ z.1).Data ×
      (OracleBundle.ofFamily (oracleMessageFamily (s₂ z.1) z.2)).Data)

/-- In an appended run, the split path, views and bundle data are those of the two parts. -/
theorem splitRun_append (data : inputs.Data) (tr₁ : Transcript oracleSig s₁)
    (tr₂ : Transcript oracleSig (s₂ tr₁.path)) :
    (⟨Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path,
      (View.split s₁ s₂ _ (toView _ (Transcript.append s₁ s₂ tr₁ tr₂)),
        (splitPathBundle (inputs := inputs) (Transcript.append s₁ s₂ tr₁ tr₂).path).f
          (data, oracleMessages _ (Transcript.append s₁ s₂ tr₁ tr₂)))⟩ :
      SplitRun inputs s₁ s₂) =
      ⟨⟨tr₁.path, tr₂.path⟩, ((toView s₁ tr₁, toView _ tr₂),
        ((data, oracleMessages s₁ tr₁), oracleMessages _ tr₂))⟩ := by
  refine sigma_extend' (B := fun z : (p : Path s₁) × Path (s₂ p) =>
    (pathBundle inputs s₁ z.1).Data ×
      (OracleBundle.ofFamily (oracleMessageFamily (s₂ z.1) z.2)).Data)
    (toView_split_append s₁ s₂ tr₁ tr₂) ?_
  exact congrArg (fun z : SplitOracleMessages s₁ s₂ =>
      (⟨z.1, ((data, fun i => z.2 (.inl i)), fun j => z.2 (.inr j))⟩ :
        (z : (p : Path s₁) × Path (s₂ p)) × (pathBundle inputs s₁ z.1).Data ×
          (OracleBundle.ofFamily (oracleMessageFamily (s₂ z.1) z.2)).Data))
    (splitOracleMessages_oracleMessages s₁ s₂ tr₁ tr₂)

/-- The decision of an appended verifier on an appended run, followed by a continuation `k` that
reads the final decision and the output data, packaged with the result type. It equals the prefix
decision, the suffix decision and the continuation in sequence. The continuation also reads a
value `y` at the split path, given again as `y'` at the pair of paths; this lets the chain laws
carry the suffix transcript and evidence through the equation. -/
theorem append_decideOn_bind {Y : (p₁ : Path s₁) → Path (s₂ p₁) → Type uY}
    {Z : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → Y p₁ p₂ → Type}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OutputCompatibility V₁ V₂)
    (k : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → (y : Y p₁ p₂) → U p₁ p₂ →
      (outputs p₁ p₂).Data →
      OracleComp ambient (Option (Z p₁ p₂ y)))
    (stmt : S) (data : inputs.Data) (tr₁ : Transcript oracleSig s₁)
    (tr₂ : Transcript oracleSig (s₂ tr₁.path))
    (y : Y (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).1
      (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).2)
    (y' : Y tr₁.path tr₂.path) (hy : HEq y y') :
    (⟨Z _ _ y, (V₁.append V₂ compatible).decideOn stmt data (Transcript.append s₁ s₂ tr₁ tr₂) >>=
      fun
        | none => pure none
        | some out => k _ _ y out
          ((V₁.append V₂ compatible).outputOn stmt data (Transcript.append s₁ s₂ tr₁ tr₂))⟩ :
      (β : Type) × OracleComp ambient (Option β)) =
    ⟨Z _ _ y', V₁.decideOn stmt data tr₁ >>= fun
      | none => pure none
      | some mid => (V₂ tr₁.path).decideOn mid (V₁.outputOn stmt data tr₁) tr₂ >>= fun
        | none => pure none
        | some out => k _ _ y' out
          ((V₂ tr₁.path).outputOn mid (V₁.outputOn stmt data tr₁) tr₂)⟩ := by
  have hΞ := sigma_extend (B := fun z : (p : Path s₁) × Path (s₂ p) => Y z.1 z.2)
    (splitRun_append (inputs := inputs) data tr₁ tr₂) hy
  have h2 := congrArg (fun Ξ : (z : (p : Path s₁) × Path (s₂ p)) ×
      ((View s₁ z.1 × View (s₂ z.1) z.2) × ((pathBundle inputs s₁ z.1).Data ×
        (OracleBundle.ofFamily (oracleMessageFamily (s₂ z.1) z.2)).Data)) × Y z.1 z.2 =>
    (⟨Z Ξ.1.1 Ξ.1.2 Ξ.2.2, V₁.decideWith stmt Ξ.1.1 Ξ.2.1.1.1 Ξ.2.1.2.1 >>= fun
      | none => pure none
      | some mid => (V₂ Ξ.1.1).decideWith mid Ξ.1.2 Ξ.2.1.1.2
          ((V₁.outputMap stmt Ξ.1.1 Ξ.2.1.1.1).f Ξ.2.1.2.1, Ξ.2.1.2.2) >>= fun
        | none => pure none
        | some out => k Ξ.1.1 Ξ.1.2 Ξ.2.2 out (((V₂ Ξ.1.1).outputMap mid Ξ.1.2 Ξ.2.1.1.2).f
            ((V₁.outputMap stmt Ξ.1.1 Ξ.2.1.1.1).f Ξ.2.1.2.1, Ξ.2.1.2.2))⟩ :
      (β : Type) × OracleComp ambient (Option β))) hΞ
  refine Eq.trans ?_ (h2.trans ?_)
  rotate_left
  · refine congrArg (Sigma.mk _) ?_
    refine congrArg (_ >>= ·) (funext fun o => ?_)
    cases o with
    | none => rfl
    | some mid =>
      refine congrArg (_ >>= ·) (funext fun o' => ?_)
      cases o' <;> rfl
  refine congrArg (Sigma.mk _) ?_
  simp only [decideOn, outputOn]
  rw [append_decideWith, bind_assoc]
  refine bind_congr_of_forall_mem_support _ fun o ho => ?_
  cases o with
  | none => exact LawfulMonad.pure_bind _ _
  | some mid =>
    refine bind_congr_of_forall_mem_support _ fun o' _ => ?_
    cases o' with
    | none => rfl
    | some out =>
      exact congrArg (k _ _ y out) (compatible.agrees stmt _ _ _ mid ho)

/-- Binding a computation to a continuation that returns every result unchanged is the
computation. -/
theorem bind_eq_self_of_forall {α : Type} (x : OracleComp ambient α)
    {f : α → OracleComp ambient α} (hf : ∀ a, f a = pure a) : x >>= f = x := by
  rw [funext hf, _root_.bind_pure]

/-- The decision of an appended verifier on an appended run, packaged with its statement type. -/
theorem append_decideOn_sigma (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OutputCompatibility V₁ V₂) (stmt : S) (data : inputs.Data)
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path)) :
    (⟨_, (V₁.append V₂ compatible).decideOn stmt data (Transcript.append s₁ s₂ tr₁ tr₂)⟩ :
      (β : Type) × OracleComp ambient (Option β)) =
    ⟨U tr₁.path tr₂.path, V₁.decideOn stmt data tr₁ >>= fun
      | none => pure none
      | some mid => (V₂ tr₁.path).decideOn mid (V₁.outputOn stmt data tr₁) tr₂⟩ := by
  have h := append_decideOn_bind (Y := fun _ _ => PUnit.{1}) (Z := fun p₁ p₂ _ => U p₁ p₂)
    V₁ V₂ compatible (fun _ _ _ out _ => pure (some out)) stmt data tr₁ tr₂ ⟨⟩ ⟨⟩ HEq.rfl
  refine Eq.trans ?_ (h.trans ?_)
  · exact congrArg (Sigma.mk _)
      (bind_eq_self_of_forall _ fun o => by cases o <;> rfl).symm
  · refine congrArg (Sigma.mk _) (congrArg (_ >>= ·) (funext fun o => ?_))
    cases o with
    | none => rfl
    | some mid => exact bind_eq_self_of_forall _ fun o => by cases o <;> rfl

/-- The decision of an appended verifier on an appended run is the prefix decision on the prefix
run followed, after acceptance, by the suffix decision on the suffix run. The suffix decision
starts from the accepted intermediate statement and the prefix output data. The two sides have
the statement types of the appended path and of the two parts. The equation is an `HEq`. -/
theorem append_decideOn (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OutputCompatibility V₁ V₂) (stmt : S) (data : inputs.Data)
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path)) :
    HEq ((V₁.append V₂ compatible).decideOn stmt data (Transcript.append s₁ s₂ tr₁ tr₂))
      (V₁.decideOn stmt data tr₁ >>= fun
        | none => pure none
        | some mid => (V₂ tr₁.path).decideOn mid (V₁.outputOn stmt data tr₁) tr₂) :=
  (Sigma.mk.inj_iff.mp (append_decideOn_sigma V₁ V₂ compatible stmt data tr₁ tr₂)).2

/-- The output data of an appended verifier on an appended run, once the prefix decision accepts
`mid`, is the suffix output data on the suffix run from `mid` and the prefix output data. -/
theorem append_outputOn (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
    (compatible : OutputCompatibility V₁ V₂) (stmt : S) (data : inputs.Data)
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path)) (mid : T tr₁.path)
    (hmid : some mid ∈ support (V₁.decideOn stmt data tr₁)) :
    HEq ((V₁.append V₂ compatible).outputOn stmt data (Transcript.append s₁ s₂ tr₁ tr₂))
      ((V₂ tr₁.path).outputOn mid (V₁.outputOn stmt data tr₁) tr₂) := by
  have hΞ := splitRun_append (inputs := inputs) data tr₁ tr₂
  have hT := congrArg (fun Ξ : SplitRun inputs s₁ s₂ => T Ξ.1.1) hΞ.symm
  have hX : (⟨_, cast hT mid⟩ : (Ξ : SplitRun inputs s₁ s₂) × T Ξ.1.1) = ⟨_, mid⟩ :=
    Sigma.ext hΞ (cast_heq _ _)
  have hsupp := (congrArg (fun X : (Ξ : SplitRun inputs s₁ s₂) × T Ξ.1.1 =>
    some X.2 ∈ support (V₁.decideWith stmt X.1.1.1 X.1.2.1.1 X.1.2.2.1)) hX).mpr hmid
  refine HEq.trans (heq_of_eq (compatible.agrees stmt _ _ _ _ hsupp)) ?_
  exact congr_arg_heq (fun X : (Ξ : SplitRun inputs s₁ s₂) × T Ξ.1.1 =>
    ((V₂ X.1.1.1).outputMap X.2 X.1.1.2 X.1.2.1.2).f
      ((V₁.outputMap stmt X.1.1.1 X.1.2.1.1).f X.1.2.2.1, X.1.2.2.2)) hX

end OracleVerifier

/-! ## Associativity of appended protocols and transcripts -/

section Assoc
variable {P : PFunctor.{uA, u}} {α : Type v} {β : Type w} {γ : Type z}

/-- Grafting `R` and then, at each path of the result, the tree `G` selects at the split path,
gives the same tree as grafting at each path of `s` the graft of `R` and `G` there. -/
theorem append_append_split : (s : FreeM P α) →
    (R : Path s → FreeM P β) → (G : (p : Path s) → Path (R p) → FreeM P γ) →
    (s.append R).append (fun q => G (Path.split s R q).1 (Path.split s R q).2) =
      s.append fun p => (R p).append (G p)
  | .pure _, _, _ => rfl
  | .liftBind a rest, R, G => congrArg (FreeM.liftBind a) (funext fun b =>
      append_append_split (rest b) (fun p => R ⟨b, p⟩) (fun p => G ⟨b, p⟩))

namespace Transcript

variable {l : PFunctor.Lens P rolePoly.{u}}

/-- Transcripts through a node with equal branch families are heterogeneously equal when their
moves agree and their remaining transcripts are heterogeneously equal. -/
theorem heq_node {a : P.A} {F F' : P.B a → FreeM P γ} (hF : F = F')
    (d : rolePoly.B (l.toFunA a)) {x : Transcript l (F (l.toFunB a d))}
    {x' : Transcript l (F' (l.toFunB a d))} (h : HEq x x') :
    HEq (⟨d, x⟩ : Transcript l (FreeM.liftBind a F))
      (⟨d, x'⟩ : Transcript l (FreeM.liftBind a F')) := by
  subst hF; cases h; rfl

/-- Appending a third transcript to an appended pair agrees with appending to the first
transcript the append of the other two. The third transcript is given at the split path of the
appended pair and again at the pair of paths, and the two are heterogeneously equal. -/
theorem append_append_heq : (s : FreeM P α) → (R : Path s → FreeM P β) →
    (G : (p : Path s) → Path (R p) → FreeM P γ) → (tr₁ : Transcript l s) →
    (tr₂ : Transcript l (R tr₁.path)) →
    (tr₃ : Transcript l (G (Path.split s R (append s R tr₁ tr₂).path).1
      (Path.split s R (append s R tr₁ tr₂).path).2)) →
    (tr₃' : Transcript l (G tr₁.path tr₂.path)) → HEq tr₃ tr₃' →
    HEq (append (s.append R) (fun q => G (Path.split s R q).1 (Path.split s R q).2)
        (append s R tr₁ tr₂) tr₃)
      (append s (fun p => (R p).append (G p)) tr₁ (append (R tr₁.path) (G tr₁.path) tr₂ tr₃'))
  | .pure _, _, _, ⟨⟩, _, _, _, h => by cases h; rfl
  | .liftBind a rest, R, G, ⟨d, tr₁⟩, tr₂, tr₃, tr₃', h =>
    heq_node (l := l) (funext fun b => append_append_split (rest b) (fun p => R ⟨b, p⟩)
      (fun p => G ⟨b, p⟩)) d
      (append_append_heq (rest (l.toFunB a d)) (fun p => R ⟨_, p⟩) (fun p => G ⟨_, p⟩)
        tr₁ tr₂ tr₃ tr₃' h)

end Transcript
end Assoc

section Helpers

namespace Transcript

variable {P : PFunctor.{uA, u}} {α : Type v} {β : Type w} {l : PFunctor.Lens P rolePoly.{u}}

/-- The split of the path of an appended transcript is the pair of the two paths. -/
theorem split_path_append (s₁ : FreeM P α) (s₂ : Path s₁ → FreeM P β) (tr₁ : Transcript l s₁)
    (tr₂ : Transcript l (s₂ tr₁.path)) :
    Path.split s₁ s₂ (append s₁ s₂ tr₁ tr₂).path = ⟨tr₁.path, tr₂.path⟩ := by
  rw [path_append]
  exact Path.split_append s₁ s₂ tr₁.path tr₂.path

/-- Appended transcripts of equal suffix families are heterogeneously equal only if their prefixes
are equal and their suffixes are heterogeneously equal. -/
theorem eq_and_heq_of_append_heq {s₁ : FreeM P α} {s₂ s₂' : Path s₁ → FreeM P β} (hs : s₂ = s₂')
    {tr₁ tr₁' : Transcript l s₁} {tr₂ : Transcript l (s₂ tr₁.path)}
    {tr₂' : Transcript l (s₂' tr₁'.path)}
    (h : HEq (append s₁ s₂ tr₁ tr₂) (append s₁ s₂' tr₁' tr₂')) : tr₁ = tr₁' ∧ HEq tr₂ tr₂' := by
  subst hs
  have h' := congrArg (split s₁ s₂) (eq_of_heq h)
  rw [split_append, split_append] at h'
  exact Sigma.mk.inj_iff.mp h'

end Transcript

/-- Pairs over equal indices are heterogeneously equal when their components are. -/
theorem heq_prod_mk {Q : Sort _} {Y₁ Y₂ : Q → Type _} {q q' : Q} (hq : q = q') {a : Y₁ q}
    {a' : Y₁ q'} {b : Y₂ q} {b' : Y₂ q'} (ha : HEq a a') (hb : HEq b b') :
    HEq ((a, b) : Y₁ q × Y₂ q) ((a', b') : Y₁ q' × Y₂ q') := by
  subst hq; cases ha; cases hb; rfl

section SigmaComp

variable {ι : Type u} {ambient : OracleSpec.{u, u} ι}

/-- Rejecting computations of equal result types are equal as packaged computations. -/
theorem sigma_pure_none {β β' : Type u} (h : β = β') :
    (⟨β, pure none⟩ : (β : Type u) × OracleComp ambient (Option β)) = ⟨β', pure none⟩ := by
  subst h; rfl

/-- Binding one computation to continuations that agree as packaged computations, with equal
result types, gives packaged computations that agree. -/
theorem sigma_bind_congr {α β β' : Type u} (hβ : β = β') (x : OracleComp ambient α)
    {F : α → OracleComp ambient (Option β)} {G : α → OracleComp ambient (Option β')}
    (h : ∀ a, (⟨β, F a⟩ : (β : Type u) × OracleComp ambient (Option β)) = ⟨β', G a⟩) :
    (⟨β, x >>= F⟩ : (β : Type u) × OracleComp ambient (Option β)) = ⟨β', x >>= G⟩ := by
  subst hβ
  rw [funext fun a => eq_of_heq (Sigma.mk.inj_iff.mp (h a)).2]

/-- An accepted result of one packaged computation gives a heterogeneously equal accepted result
of an equal packaged computation. -/
theorem exists_mem_support_of_sigma_eq {β β' : Type u} {x : OracleComp ambient (Option β)}
    {y : OracleComp ambient (Option β')}
    (h : (⟨β, x⟩ : (β : Type u) × OracleComp ambient (Option β)) = ⟨β', y⟩) {b : β}
    (hb : some b ∈ support x) : ∃ b' : β', HEq b b' ∧ some b' ∈ support y := by
  obtain ⟨rfl, hxy⟩ := Sigma.mk.inj_iff.mp h
  cases hxy
  exact ⟨b, HEq.rfl, hb⟩

end SigmaComp

/-- Quadruples over equal indices are heterogeneously equal when their components are. -/
theorem heq_tuple4 {Q : Sort _} {Y₁ Y₂ Y₃ Y₄ : Q → Type _} {q q' : Q} (hq : q = q')
    {a : Y₁ q} {a' : Y₁ q'} {b : Y₂ q} {b' : Y₂ q'} {c : Y₃ q} {c' : Y₃ q'} {d : Y₄ q}
    {d' : Y₄ q'} (ha : HEq a a') (hb : HEq b b') (hc : HEq c c') (hd : HEq d d') :
    HEq ((a, b, c, d) : Y₁ q × Y₂ q × Y₃ q × Y₄ q)
      ((a', b', c', d') : Y₁ q' × Y₂ q' × Y₃ q' × Y₄ q') := by
  subst hq; cases ha; cases hb; cases hc; cases hd; rfl

/-- Triples over equal indices are heterogeneously equal when their components are. -/
theorem heq_tuple3 {Q : Sort _} {Y₁ Y₂ Y₃ : Q → Type _} {q q' : Q} (hq : q = q')
    {a : Y₁ q} {a' : Y₁ q'} {b : Y₂ q} {b' : Y₂ q'} {c : Y₃ q} {c' : Y₃ q'}
    (ha : HEq a a') (hb : HEq b b') (hc : HEq c c') :
    HEq ((a, b, c) : Y₁ q × Y₂ q × Y₃ q) ((a', b', c') : Y₁ q' × Y₂ q' × Y₃ q') := by
  subst hq; cases ha; cases hb; cases hc; rfl

end Helpers

namespace OracleVerifier

variable {ι : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}} {S : Type}
  {T : Path s → Type} {inputs : OracleBundle}
  {outputs : Path s → OracleBundle}

/-- Verifiers with the same decision function decide alike on every run. -/
theorem decideOn_eq_of_decide_eq {V V' : OracleVerifier ambient s S T inputs outputs}
    (h : V.decide = V'.decide) : V.decideOn = V'.decideOn := by
  unfold decideOn decideWith
  rw [h]

end OracleVerifier

/-- The decision of an appended verifier depends on the suffix verifiers only through their
decision functions. -/
theorem OracleVerifier.append_decide_congr {ι : Type} {ambient : OracleSpec ι}
    {inputs : OracleBundle}
    {s₁ : OracleProtocol.{0, 0}} {s₂ : Path s₁ → OracleProtocol.{0, 0}} {S : Type}
    {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
    {middle : Path s₁ → OracleBundle}
    {outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle}
    (V₁ : OracleVerifier ambient s₁ S T inputs middle)
    {V₂ V₂' : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p)}
    (compatible : OracleVerifier.OutputCompatibility V₁ V₂)
    (compatible' : OracleVerifier.OutputCompatibility V₁ V₂')
    (h : ∀ p, (V₂ p).decide = (V₂' p).decide) :
    (V₁.append V₂ compatible).decide = (V₁.append V₂' compatible').decide := by
  simp only [OracleVerifier.append, h]



/-! ## Reassociation of appended verifiers -/

namespace OracleVerifier

section Reassociation

variable {ι : Type} {ambient : OracleSpec ι}
  {inputs : OracleBundle}
  {s₁ : OracleProtocol.{0, 0}} {s₂ : Path s₁ → OracleProtocol.{0, 0}}
  {s₃ : (p₁ : Path s₁) → Path (s₂ p₁) → OracleProtocol.{0, 0}} {S : Type}
  {T : Path s₁ → Type} {U : (p : Path s₁) → Path (s₂ p) → Type}
  {W : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → Path (s₃ p₁ p₂) → Type}
  {middle : Path s₁ → OracleBundle}
  {outputs : (p₁ : Path s₁) → Path (s₂ p₁) → OracleBundle}
  {finals :
    (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) → Path (s₃ p₁ p₂) → OracleBundle}
  (V₁ : OracleVerifier ambient s₁ S T inputs middle)
  (V₂ : (p : Path s₁) → OracleVerifier ambient (s₂ p) (T p) (U p) (middle p) (outputs p))
  (V₃ : (p₁ : Path s₁) → (p₂ : Path (s₂ p₁)) →
    OracleVerifier ambient (s₃ p₁ p₂) (U p₁ p₂) (W p₁ p₂) (outputs p₁ p₂) (finals p₁ p₂))
  (c₁₂ : OutputCompatibility V₁ V₂)
  (cL : OutputCompatibility (V₁.append V₂ c₁₂)
    fun P => V₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2)
  (c₂₃ : (p : Path s₁) → OutputCompatibility (V₂ p) (V₃ p))
  (cR : OutputCompatibility V₁ fun p => (V₂ p).append (V₃ p) (c₂₃ p))

/-- The left association decides as the three decisions in sequence. -/
theorem append_append_decideOn_sigma_left (stmt : S) (data : inputs.Data)
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path))
    (tr₃ : Transcript oracleSig (s₃
      (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).1
      (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).2))
    (tr₃' : Transcript oracleSig (s₃ tr₁.path tr₂.path)) (h : HEq tr₃ tr₃') :
    (⟨_, ((V₁.append V₂ c₁₂).append
        (fun P => V₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2) cL).decideOn stmt data
        (Transcript.append (s₁.append s₂)
          (fun P => s₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2)
          (Transcript.append s₁ s₂ tr₁ tr₂) tr₃)⟩ :
      (β : Type) × OracleComp ambient (Option β)) =
    ⟨W tr₁.path tr₂.path tr₃'.path, V₁.decideOn stmt data tr₁ >>= fun
      | none => pure none
      | some m => (V₂ tr₁.path).decideOn m (V₁.outputOn stmt data tr₁) tr₂ >>= fun
        | none => pure none
        | some mid => (V₃ tr₁.path tr₂.path).decideOn mid
            ((V₂ tr₁.path).outputOn m (V₁.outputOn stmt data tr₁) tr₂) tr₃'⟩ := by
  have hl := append_decideOn_sigma (V₁.append V₂ c₁₂)
    (fun P => V₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2) cL stmt data
    (Transcript.append s₁ s₂ tr₁ tr₂) tr₃
  have hct := append_decideOn_bind (Y := fun p₁ p₂ => Transcript oracleSig (s₃ p₁ p₂))
    (Z := fun p₁ p₂ y => W p₁ p₂ y.path) V₁ V₂ c₁₂
    (fun p₁ p₂ y mid d => (V₃ p₁ p₂).decideOn mid d y) stmt data tr₁ tr₂ tr₃ tr₃' h
  refine hl.trans (Eq.trans ?_ hct)
  refine congrArg (Sigma.mk _) (congrArg (_ >>= ·) (funext fun o => ?_))
  cases o <;> rfl

/-- The right association decides as the three decisions in sequence. -/
theorem append_append_decideOn_sigma_right (stmt : S) (data : inputs.Data)
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path))
    (tr₃' : Transcript oracleSig (s₃ tr₁.path tr₂.path)) :
    (⟨_, (V₁.append (fun p => (V₂ p).append (V₃ p) (c₂₃ p)) cR).decideOn stmt data
        (Transcript.append s₁ (fun p => (s₂ p).append (s₃ p)) tr₁
          (Transcript.append (s₂ tr₁.path) (s₃ tr₁.path) tr₂ tr₃'))⟩ :
      (β : Type) × OracleComp ambient (Option β)) =
    ⟨W tr₁.path tr₂.path tr₃'.path, V₁.decideOn stmt data tr₁ >>= fun
      | none => pure none
      | some m => (V₂ tr₁.path).decideOn m (V₁.outputOn stmt data tr₁) tr₂ >>= fun
        | none => pure none
        | some mid => (V₃ tr₁.path tr₂.path).decideOn mid
            ((V₂ tr₁.path).outputOn m (V₁.outputOn stmt data tr₁) tr₂) tr₃'⟩ := by
  have hβ := congrArg (fun z : (p : Path (s₂ tr₁.path)) × Path (s₃ tr₁.path p) =>
    W tr₁.path z.1 z.2) (Transcript.split_path_append (s₂ tr₁.path) (s₃ tr₁.path) tr₂ tr₃')
  refine (append_decideOn_sigma V₁ (fun p => (V₂ p).append (V₃ p) (c₂₃ p)) cR stmt data tr₁
    (Transcript.append (s₂ tr₁.path) (s₃ tr₁.path) tr₂ tr₃')).trans
    (sigma_bind_congr hβ _ fun o => ?_)
  cases o with
  | none => exact sigma_pure_none hβ
  | some m =>
    refine (append_decideOn_sigma (V₂ tr₁.path) (V₃ tr₁.path) (c₂₃ tr₁.path) m
      (V₁.outputOn stmt data tr₁) tr₂ tr₃').trans ?_
    refine congrArg (Sigma.mk _) (congrArg (_ >>= ·) (funext fun o => ?_))
    cases o <;> rfl

/-- Reassociation of appended verifiers, for the decision. On a run of the left-associated
protocol and the corresponding run of the right-associated protocol, the two associations decide
alike. The third transcript is given at the split path and at the pair of paths, and the two are
heterogeneously equal; `Transcript.append_append_heq` relates the two runs. The two sides have
the statement types of the two protocols. The equation is therefore an `HEq`. -/
theorem append_append_decideOn (stmt : S) (data : inputs.Data)
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path))
    (tr₃ : Transcript oracleSig (s₃
      (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).1
      (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).2))
    (tr₃' : Transcript oracleSig (s₃ tr₁.path tr₂.path)) (h : HEq tr₃ tr₃') :
    HEq (((V₁.append V₂ c₁₂).append
        (fun P => V₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2) cL).decideOn stmt data
        (Transcript.append (s₁.append s₂)
          (fun P => s₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2)
          (Transcript.append s₁ s₂ tr₁ tr₂) tr₃))
      ((V₁.append (fun p => (V₂ p).append (V₃ p) (c₂₃ p)) cR).decideOn stmt data
        (Transcript.append s₁ (fun p => (s₂ p).append (s₃ p)) tr₁
          (Transcript.append (s₂ tr₁.path) (s₃ tr₁.path) tr₂ tr₃'))) :=
  (Sigma.mk.inj_iff.mp ((append_append_decideOn_sigma_left V₁ V₂ V₃ c₁₂ cL stmt data tr₁ tr₂
    tr₃ tr₃' h).trans (append_append_decideOn_sigma_right V₁ V₂ V₃ c₂₃ cR stmt data tr₁ tr₂
      tr₃').symm)).2

/-- Reassociation of appended verifiers, for the output data. Once the first decision accepts `m`
and the second accepts `mid` from it, the two associations export the same output data: the
third verifier's output data on its run. -/
theorem append_append_outputOn (stmt : S) (data : inputs.Data)
    (tr₁ : Transcript oracleSig s₁) (tr₂ : Transcript oracleSig (s₂ tr₁.path))
    (tr₃ : Transcript oracleSig (s₃
      (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).1
      (Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path).2))
    (tr₃' : Transcript oracleSig (s₃ tr₁.path tr₂.path)) (h : HEq tr₃ tr₃') (m : T tr₁.path)
    (hm : some m ∈ support (V₁.decideOn stmt data tr₁)) (mid : U tr₁.path tr₂.path)
    (hmid : some mid ∈ support ((V₂ tr₁.path).decideOn m (V₁.outputOn stmt data tr₁) tr₂)) :
    HEq (((V₁.append V₂ c₁₂).append
        (fun P => V₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2) cL).outputOn stmt data
        (Transcript.append (s₁.append s₂)
          (fun P => s₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2)
          (Transcript.append s₁ s₂ tr₁ tr₂) tr₃))
      ((V₁.append (fun p => (V₂ p).append (V₃ p) (c₂₃ p)) cR).outputOn stmt data
        (Transcript.append s₁ (fun p => (s₂ p).append (s₃ p)) tr₁
          (Transcript.append (s₂ tr₁.path) (s₃ tr₁.path) tr₂ tr₃'))) := by
  have hR := (append_outputOn V₁ (fun p => (V₂ p).append (V₃ p) (c₂₃ p)) cR stmt data tr₁
    (Transcript.append (s₂ tr₁.path) (s₃ tr₁.path) tr₂ tr₃') m hm).trans
    (append_outputOn (V₂ tr₁.path) (V₃ tr₁.path) (c₂₃ tr₁.path) m (V₁.outputOn stmt data tr₁)
      tr₂ tr₃' mid hmid)
  have hmem : some mid ∈ support (V₁.decideOn stmt data tr₁ >>= fun
      | none => pure none
      | some m => (V₂ tr₁.path).decideOn m (V₁.outputOn stmt data tr₁) tr₂) :=
    by rw [mem_support_bind_iff]; exact ⟨some m, hm, hmid⟩
  obtain ⟨mid', hmid', hmem'⟩ := exists_mem_support_of_sigma_eq
    (append_decideOn_sigma V₁ V₂ c₁₂ stmt data tr₁ tr₂).symm hmem
  have hd := append_outputOn V₁ V₂ c₁₂ stmt data tr₁ tr₂ m hm
  have hz := Transcript.split_path_append s₁ s₂ tr₁ tr₂
  have hX : (⟨Path.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂).path,
      (tr₃, mid', (V₁.append V₂ c₁₂).outputOn stmt data (Transcript.append s₁ s₂ tr₁ tr₂))⟩ :
      (z : (p : Path s₁) × Path (s₂ p)) × Transcript oracleSig (s₃ z.1 z.2) × U z.1 z.2 ×
        ((outputs z.1 z.2).Data)) =
      ⟨⟨tr₁.path, tr₂.path⟩,
        (tr₃', mid, (V₂ tr₁.path).outputOn m (V₁.outputOn stmt data tr₁) tr₂)⟩ :=
    Sigma.ext hz (heq_tuple3 (Y₁ := fun z => Transcript oracleSig (s₃ z.1 z.2))
      (Y₂ := fun z => U z.1 z.2) (Y₃ := fun z => (outputs z.1 z.2).Data) hz h hmid'.symm hd)
  refine (append_outputOn (V₁.append V₂ c₁₂)
    (fun P => V₃ (Path.split s₁ s₂ P).1 (Path.split s₁ s₂ P).2) cL stmt data
    (Transcript.append s₁ s₂ tr₁ tr₂) tr₃ mid' hmem').trans (HEq.trans ?_ hR.symm)
  exact congr_arg_heq (fun X : (z : (p : Path s₁) × Path (s₂ p)) ×
      Transcript oracleSig (s₃ z.1 z.2) × U z.1 z.2 × (outputs z.1 z.2).Data =>
    (V₃ X.1.1 X.1.2).outputOn X.2.2.1 X.2.2.2 X.2.1) hX

end Reassociation

end OracleVerifier

end Interaction

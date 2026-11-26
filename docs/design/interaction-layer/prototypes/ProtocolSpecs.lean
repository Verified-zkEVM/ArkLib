/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.IntervalCompleteness
import ArkLib.ProofSystem.Sumcheck.Indexed

/-!
# Protocol specifications (prototype)

This file is stage 0 of the protocol-specification proposal. It writes an interactive oracle
reduction once, as a description in plain Lean combinators that reads like a paper's protocol
figure. From that one description it derives the interaction layer's objects: the
`OracleProtocol` tree, the honest prover as a `Focal` strategy, the passive verifier's decision,
named accessors for transcripts and views, and a computable skeleton. `main` exports the skeleton
of each example as JSON and as a `cryptocode` figure.

Run `lake env lean --run docs/design/interaction-layer/prototypes/ProtocolSpecs.lean` from the
repository root to write `docs/design/interaction-layer/prototypes/out/*.{json,tex}`.

## Sections

1. The description type `Desc` and its combinators: `message`, `oracle`, `challenge`, `check`,
   `compute` (a local `let`), `rounds` and `stage`, each with optional `tex` and `doc`.
2. Elaboration: `Spec.tree`, `Spec.prover`, `Spec.decision`, `Spec.verifier`, the accessors
   `tr.msg` and `v.msg`, and the skeleton (`Spec.skeleton`, `Spec.rows`).
3. Sum-check, with its agreement theorems against ArkLib's sum-check.
4. A Spartan-shaped composed example in two stages.
5. A FRI-shaped example.
6. Export of JSON and TeX.
7. This note, and "Open problems" at the end of the file.

## How a description works

A description `Desc M W T t ks` is a program in continuation-passing style. `W` is the witness,
`T` the output and `M` the monad in which the verifier's checks and local values run. The tree
`t` and the skeleton `ks` are type indices, so a challenge value, an oracle handle or a local value
cannot change the shape. The honest prover runs the description at `M = Id` and answers its own
oracle queries from its honest values. The verifier runs it at `M = OracleComp` over the oracle
messages of the path. It reaches every check, but decides only at the leaf, after the whole
interaction. An oracle message reaches the verifier as an `Oracle` handle, which offers only
`query`. Because the skeleton is a type index, `Spec.skeleton` is computable even when the
description uses noncomputable Mathlib polynomials.

## Before and after: sum-check

After. The sum-check description is `sumcheckRound` and `sumcheck` in Section 3: 19 lines with
docstrings. With the claim type, the type-name instance, the final claim and the `Spec` wrapper
(which adds the `stage` and its claims) it is 46 lines. A reader sees one round in protocol order:
the prover sends the oracle `g` with its honest formula, the verifier checks the sum of `g` over
`D` by querying `g`, samples `r`, and sets the next claim to `g(r)`. Each step carries its LaTeX.
The skeleton, the JSON and the figure come from the same lines.

Before. Today's sum-check spreads the same content over these files under
`ArkLib/ProofSystem/Sumcheck/`, 2351 lines in all:

| file | lines | what it holds |
|---|---|---|
| `MessageTree.lean` | 47 | the fixed message tree `Interpreted.protocol` |
| `Tree.lean` | 123 | the polynomial tree `Sumcheck.protocol` and its sampler |
| `Types.lean` | 47 | `RoundStatement`, `polynomialFamily` |
| `InterpretedPath.lean` | 91 | first-round accessors `message`, `challenge`, `tail` |
| `Interpreted.lean` | 129 | the generic round verdict and decision |
| `Fold.lean` | 63 | the polynomial instance of the fold |
| `Interval.lean` | 200 | `IntervalClaim`, `intervalCheck` |
| `IndexedDomain.lean` | 161 | `projectedRoundPolynomial` (the honest message) |
| `Indexed.lean` | 841 | `indexedVerifier` (lines 1-85) and its soundness proofs |
| `Protocol.lean` | 234 | `consProver`, `foldRounds` |
| `IntervalCompleteness.lean` | 228 | `intervalProver` and its completeness proofs |
| `SingleRound.lean` | 187 | one round as a standalone protocol |

A reader of today's files reconstructs one round from the tree (`MessageTree`), the claim
(`Interval`), the honest message (`IndexedDomain`), the prover fold (`Protocol`,
`IntervalCompleteness`) and the verifier fold (`Interpreted`, `Fold`, `Indexed`). The soundness
and completeness proofs stay necessary with either form. Section 3 proves that the description
yields the same tree (`sumcheck_tree`, by `rfl`), the same honest prover (`sumcheck_prover`) and
the same decision on every transcript (`sumcheck_decide`, `sumcheck_outputMap`), so those proofs
carry over.
-/

namespace ProtocolSpecs
open PFunctor FreeM Interaction Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec Polynomial MvPolynomial

/-! ## 1. The description type and its combinators -/

/-- The kind of a step. -/
inductive Kind
  | message | oracle | challenge | check | let_
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Optional display metadata of a step: a LaTeX rendering and a short description. -/
structure Display where
  tex : String := ""
  doc : String := ""

/-- A claim that a stage consumes or produces, with the point at which it is stated. -/
structure ClaimDecl where
  label : String
  point : String := ""

/-- One entry of the skeleton. Steps are the moves, checks and local definitions; the other
entries mark round and stage boundaries. -/
inductive Item
  | step (label : String) (kind : Kind) (ty : String) (display : Display)
  | beginRound (block : String) (i : ℕ) (error : String)
  | endRound
  | beginStage (name : String) (input output : ClaimDecl)
  | endStage

/-- The printed name of a type, used by the skeleton. -/
class TypeName (X : Type) where
  name : String

/-- A handle on an oracle message: the verifier reads it only through the queries of its
interface. -/
structure Oracle (M : Type → Type) (X : Type) (I : OracleInterface X) where
  query : (q : I.Query) → M (I.spec q)

/-- A description of an interactive oracle protocol, in continuation-passing style.

`M` is the monad of verifier computations, `W` the prover's witness and `T` the output. The
indices are the protocol tree and the skeleton. They never depend on challenge values, oracle
handles or local values, so the continuations cannot change the shape. -/
inductive Desc (M : Type → Type) (W T : Type) : OracleProtocol → List Item → Type 1 where
  | done (out : T) : Desc M W T (.pure ⟨⟩) []
  | message (label : String) (X : Type) (name : String) (honest : W → X) (display : Display)
      {t : X → OracleProtocol} {ks : List Item} (rest : (x : X) → Desc M W T (t x) ks) :
      Desc M W T (.liftBind (.message X) t) (.step label .message name display :: ks)
  | oracle (label : String) (X : Type) (I : OracleInterface X) (name : String)
      (honest : W → X) (display : Display) {t : OracleProtocol} {ks : List Item}
      (rest : Oracle M X I → Desc M W T t ks) :
      Desc M W T (.liftBind (.oracle X I) fun _ => t) (.step label .oracle name display :: ks)
  | challenge (label : String) (C : Type) (name : String) (display : Display)
      {t : OracleProtocol} {ks : List Item} (rest : C → Desc M W T t ks) :
      Desc M W T (.liftBind (.challenge C) fun _ => t) (.step label .challenge name display :: ks)
  | check (label : String) (c : M Bool) (display : Display) {t : OracleProtocol}
      {ks : List Item} (rest : Desc M W T t ks) :
      Desc M W T t (.step label .check "Bool" display :: ks)
  | compute (label : String) {α : Type} (name : String) (x : M α) (display : Display)
      {t : OracleProtocol} {ks : List Item} (rest : α → Desc M W T t ks) :
      Desc M W T t (.step label .let_ name display :: ks)
  | mark (item : Item) {t : OracleProtocol} {ks : List Item} (rest : Desc M W T t ks) :
      Desc M W T t (item :: ks)

variable {M : Type → Type} {W T : Type}

/-- The protocol ends with output `out`. -/
abbrev done (out : T) : Desc M W T (.pure ⟨⟩) [] := .done out

/-- The prover sends the plain message `label : X`, honestly `honest w`. -/
abbrev message (label : String) (X : Type) [TypeName X] (honest : W → X)
    {t : X → OracleProtocol} {ks : List Item} (rest : (x : X) → Desc M W T (t x) ks)
    (tex doc : String := "") :=
  Desc.message label X (TypeName.name X) honest ⟨tex, doc⟩ rest

/-- The prover sends the oracle message `label : X`, honestly `honest w`. The verifier gets a
handle that it can only query. -/
abbrev oracle (label : String) (X : Type) [I : OracleInterface X] [TypeName X] (honest : W → X)
    {t : OracleProtocol} {ks : List Item} (rest : Oracle M X I → Desc M W T t ks)
    (tex doc : String := "") :=
  Desc.oracle label X I (TypeName.name X) honest ⟨tex, doc⟩ rest

/-- The verifier samples the public challenge `label : C`. -/
abbrev challenge (label : String) (C : Type) [TypeName C] {t : OracleProtocol}
    {ks : List Item} (rest : C → Desc M W T t ks) (tex doc : String := "") :=
  Desc.challenge label C (TypeName.name C) ⟨tex, doc⟩ rest

/-- The verifier checks `c`. The decision rejects when `c` returns `false`. -/
abbrev check (label : String) (c : M Bool) {t : OracleProtocol} {ks : List Item}
    (rest : Desc M W T t ks) (tex doc : String := "") :=
  Desc.check label c ⟨tex, doc⟩ rest

/-- The verifier computes the local value `label := x`, for example by querying an oracle. -/
abbrev compute (label : String) (α : Type) [TypeName α] (x : M α) {t : OracleProtocol}
    {ks : List Item} (rest : α → Desc M W T t ks) (tex doc : String := "") :=
  Desc.compute label (TypeName.name α) x ⟨tex, doc⟩ rest

/-- The tree of `k` rounds of the same shape `F`, followed by `t`. -/
@[reducible] def roundsTree (F : OracleProtocol → OracleProtocol) (t : OracleProtocol) :
    ℕ → OracleProtocol
  | 0 => t
  | k + 1 => F (roundsTree F t k)

/-- The skeleton of `k` rounds starting at round `j`, each between round markers. -/
@[reducible] def roundsSkel (name : String) (error : ℕ → String)
    (G : ℕ → List Item → List Item) (ks : List Item) : ℕ → ℕ → List Item
  | 0, _ => ks
  | k + 1, j => .beginRound name j (error j) :: G j (.endRound :: roundsSkel name error G ks k (j + 1))

/-- The rounds `j, …, j + k - 1` of a `rounds` block. -/
def roundsGo {State : ℕ → Type} {F : OracleProtocol → OracleProtocol}
    {G : ℕ → List Item → List Item} (name : String) (error : ℕ → String) (n : ℕ)
    (body : ∀ {t : OracleProtocol} {ks : List Item}, (i : ℕ) → i < n → State i →
      (State (i + 1) → Desc M W T t ks) → Desc M W T (F t) (G i ks))
    {t : OracleProtocol} {ks : List Item} (next : State n → Desc M W T t ks) :
    (k j : ℕ) → j + k = n → State j →
      Desc M W T (roundsTree F t k) (roundsSkel name error G ks k j)
  | 0, _, h, st => next (h ▸ st)
  | k + 1, j, h, st => .mark (.beginRound name j (error j)) <|
      body j (by omega) st fun st' =>
        .mark .endRound (roundsGo name error n body next k (j + 1) (by omega) st')

/-- `n` rounds with round-indexed state: round `i` (counting up from `0`) maps `State i` to
`State (i + 1)`. Every round has the same tree shape. -/
abbrev rounds (name : String) (n : ℕ) {State : ℕ → Type} (init : State 0)
    {F : OracleProtocol → OracleProtocol} {G : ℕ → List Item → List Item}
    (body : ∀ {t : OracleProtocol} {ks : List Item}, (i : ℕ) → i < n → State i →
      (State (i + 1) → Desc M W T t ks) → Desc M W T (F t) (G i ks))
    {t : OracleProtocol} {ks : List Item} (next : State n → Desc M W T t ks)
    (error : ℕ → String := fun _ => "") :=
  roundsGo name error n body next n 0 (Nat.zero_add n) init

/-- A named stage. It consumes the claim `input` and produces the claim `output`, which the
continuation receives. -/
abbrev stage (name : String) (input output : ClaimDecl) {S : Type} {t t' : OracleProtocol}
    {ks ks' : List Item} (body : (S → Desc M W T t (.endStage :: ks)) → Desc M W T t' ks')
    (next : S → Desc M W T t ks) : Desc M W T t' (.beginStage name input output :: ks') :=
  .mark (.beginStage name input output) (body fun s => .mark .endStage (next s))

/-! ## 2. Elaboration -/

section Elaboration

/-- The honest prover: it sends `honest w` at each message and answers its own oracle queries
from the honest values. -/
def Desc.prove {m : Type → Type} [Monad m] (w : W) :
    {t : OracleProtocol} → {ks : List Item} → Desc Id W T t ks →
      Focal oracleSig m t (fun _ => T)
  | _, _, .done out => (pure out : m T)
  | _, _, .message _ _ _ h _ rest => pure ⟨h w, Desc.prove w (rest (h w))⟩
  | _, _, .oracle _ _ I _ h _ rest =>
      pure ⟨h w, Desc.prove w (rest ⟨fun q => (pure (I.answer (h w) q) : Id _)⟩)⟩
  | _, _, .challenge _ _ _ _ rest => pure fun c => Desc.prove w (rest c)
  | _, _, .check _ _ _ rest => Desc.prove w rest
  | _, _, .compute _ _ x _ rest => Desc.prove w (rest x)
  | _, _, .mark _ rest => Desc.prove w rest

/-- The view after a node whose branch is `Unit` (a challenge or an oracle message). -/
def View.tail {a : OraclePos} {t : OracleProtocol}
    {p : FreeM.Path (FreeM.liftBind (P := OraclePoly) a fun _ => t)}
    (v : View (.liftBind a fun _ => t) p) : View t p.2 :=
  ⟨v.1.2, congrArg (fun q : (_ : OraclePoly.B a) × FreeM.Path t => q.2) v.2⟩

/-- The challenge at the root of a view. -/
def View.head {C : Type} {t : OracleProtocol}
    {p : FreeM.Path (FreeM.liftBind (P := OraclePoly) (OraclePos.challenge C) fun _ => t)}
    (v : View (FreeM.liftBind (P := OraclePoly) (OraclePos.challenge C) fun _ => t) p) : C :=
  v.1.1

/-- The view after a plain message. The path fixes the message. -/
def View.msgTail {X : Type} {t : X → OracleProtocol}
    {p : FreeM.Path (FreeM.liftBind (P := OraclePoly) (OraclePos.message X) t)}
    (v : View (FreeM.liftBind (P := OraclePoly) (OraclePos.message X) t) p) :
    View (t p.1) p.2 := by
  obtain ⟨⟨x', tr⟩, h⟩ := v
  obtain ⟨x, p⟩ := p
  have h' : (⟨x', Transcript.path (l := viewSig) tr⟩ : (y : X) × FreeM.Path (t y)) = ⟨x, p⟩ := h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj h'
  exact ⟨tr, eq_of_heq h2⟩

/-- The passive verifier's decision. It walks the description along the view, queries each
oracle message through `lift`, and returns `none` at the first failed check. -/
def Desc.decision {ι : Type} {S : OracleSpec ι} :
    {t : OracleProtocol} → {ks : List Item} → Desc (OracleComp S) W T t ks →
      (p : FreeM.Path t) → View t p → QueryImpl (oracleMessageSpec t p) (OracleComp S) →
      OracleComp S (Option T)
  | _, _, .done out, _, _, _ => pure (some out)
  | _, _, .message _ _ _ _ _ rest, p, v, lift => (rest p.1).decision p.2 (View.msgTail v) lift
  | _, _, .oracle _ _ _ _ _ _ rest, p, v, lift =>
      (rest ⟨fun q => lift (.inl q)⟩).decision p.2 (View.tail v) fun q => lift (.inr q)
  | _, _, .challenge _ _ _ _ rest, p, v, lift =>
      (rest (View.head v)).decision p.2 (View.tail v) lift
  | _, _, .check _ c _ rest, p, v, lift => do
      if (← c) then rest.decision p v lift else pure none
  | _, _, .compute _ _ x _ rest, p, v, lift => do (rest (← x)).decision p v lift
  | _, _, .mark _ rest, p, v, lift => rest.decision p v lift

/-- A protocol specification: a description for every input statement and every verifier
monad. -/
abbrev Spec (S W T : Type) (t : OracleProtocol) (ks : List Item) : Type 1 :=
  S → (M : Type → Type) → [Monad M] → Desc M W T t ks

namespace Spec
variable {S : Type} {t : OracleProtocol} {ks : List Item}

/-- The protocol tree of a specification. -/
abbrev tree (_ : Spec S W T t ks) : OracleProtocol := t

/-- The skeleton of a specification, read from its type. Compiler inlining drops the
description, which is usually noncomputable. -/
@[macro_inline] def skeleton (_ : Spec S W T t ks) : List Item := ks

/-- The honest prover of a specification. -/
def prover {m : Type → Type} [Monad m] (d : Spec S W T t ks) (stmt : S) (w : W) :
    Focal oracleSig m t (fun _ => T) :=
  (d stmt Id).prove w

/-- The decision over the oracle messages of the path `p`. -/
def decision (d : Spec S W T t ks) (stmt : S) (p : FreeM.Path t) (v : View t p) :
    OracleComp (oracleMessageSpec t p) (Option T) :=
  (d stmt (OracleComp (oracleMessageSpec t p))).decision p v
    fun q => liftM ((oracleMessageSpec t p).query q)

/-- The passive oracle verifier of a specification. It keeps its input oracles. -/
def verifier (d : Spec S W T t ks) {ι : Type} (ambient : OracleSpec ι) (inputs : OracleBundle) :
    OracleVerifier ambient t S (fun _ => T) inputs (fun _ => inputs) where
  decide stmt p v := OptionT.mk (simulateQ (pathLift ambient inputs p) (d.decision stmt p v))
  outputMap _ _ _ := OracleMap.fst _ _

end Spec

/-! ### Named accessors

A proof names a move by its label and occurrence: `tr.msg "g" i` is the move labeled `"g"` in its
`i`-th occurrence (round `i` inside a `rounds` block). The skeleton gives the position
(`movePos`), and `moveAt` walks the transcript to it. At a concrete size both reduce by `rfl` or
`simp`. -/

/-- The type of move number `m` along the lens `l`, or `PUnit` past the end of the tree. -/
def MoveTy (l : PFunctor.Lens OraclePoly rolePoly0) :
    (t : OracleProtocol) → PathAlong l t → ℕ → Type
  | .pure _, _, _ => PUnit
  | .liftBind a _, _, 0 => Move l a
  | .liftBind a k, tr, m + 1 => MoveTy l (k (l.toFunB a tr.1)) tr.2 m

/-- Move number `m` of a transcript along the lens `l`. -/
def moveAt (l : PFunctor.Lens OraclePoly rolePoly0) :
    (t : OracleProtocol) → (tr : PathAlong l t) → (m : ℕ) → MoveTy l t tr m
  | .pure _, _, _ => PUnit.unit
  | .liftBind _ _, tr, 0 => tr.1
  | .liftBind _ _, tr, m + 1 => moveAt l _ tr.2 m

@[simp] theorem moveAt_zero (l : PFunctor.Lens OraclePoly rolePoly0) (a : OraclePos)
    (k : OraclePoly.B a → OracleProtocol) (tr : PathAlong l (FreeM.liftBind a k)) :
    moveAt l (.liftBind a k) tr 0 = tr.1 := rfl

@[simp] theorem moveAt_succ (l : PFunctor.Lens OraclePoly rolePoly0) (a : OraclePos)
    (k : OraclePoly.B a → OracleProtocol) (tr : PathAlong l (FreeM.liftBind a k)) (m : ℕ) :
    moveAt l (.liftBind a k) tr (m + 1) = moveAt l _ tr.2 m := rfl

/-- Messages, oracle messages and challenges are moves; checks and local definitions are not. -/
def Kind.isMove : Kind → Bool
  | .message | .oracle | .challenge => true
  | _ => false

/-- The position, among the moves of a skeleton, of the `i`-th move labeled `label`. -/
def movePos (label : String) : List Item → ℕ → ℕ
  | [], _ => 0
  | .step l k _ _ :: ks, i =>
    if k.isMove then
      if l = label then
        match i with
        | 0 => 0
        | i + 1 => movePos label ks i + 1
      else movePos label ks i + 1
    else movePos label ks i
  | _ :: ks, i => movePos label ks i

namespace Spec
variable {S : Type} {t : OracleProtocol} {ks : List Item}

/-- The transcripts of a specification. The name lets `tr.msg` resolve. -/
def Tr (_ : Spec S W T t ks) : Type := Transcript oracleSig t

/-- The verifier's views of a specification along the path `p`. -/
def Vw (_ : Spec S W T t ks) (p : FreeM.Path t) : Type := View t p

/-- The `i`-th move labeled `label` of a transcript. -/
def Tr.msg {d : Spec S W T t ks} (tr : d.Tr) (label : String) (i : ℕ) :
    MoveTy oracleSig t tr (movePos label ks i) :=
  moveAt oracleSig t tr (movePos label ks i)

/-- The `i`-th move labeled `label` of a view. An oracle message shows as `()`. -/
def Vw.msg {d : Spec S W T t ks} {p : FreeM.Path t} (v : d.Vw p) (label : String) (i : ℕ) :
    MoveTy viewSig t v.1 (movePos label ks i) :=
  moveAt viewSig t v.1 (movePos label ks i)

@[simp] theorem Tr.msg_eq {d : Spec S W T t ks} (tr : d.Tr) (label : String) (i : ℕ) :
    tr.msg label i = moveAt oracleSig t tr (movePos label ks i) := rfl

@[simp] theorem Vw.msg_eq {d : Spec S W T t ks} {p : FreeM.Path t} (v : d.Vw p) (label : String)
    (i : ℕ) : v.msg label i = moveAt viewSig t v.1 (movePos label ks i) := rfl

end Spec

/-! ### The skeleton as rows and claim edges

`Skeleton.ofItems` folds the item list of a specification into the rows a renderer draws. Each
row records its owner, kind, `rounds` block, round, stage and printed type. Each stage adds claim
edges: one from the previous producer (`input` at first) labeled with the stage's input claim,
and one from the stage to the next check, the next stage or `output`, labeled with its output
claim. -/

/-- The owner of a step: the prover sends messages, the verifier does everything else. -/
def Kind.owner : Kind → String
  | .message | .oracle => "prover"
  | _ => "verifier"

/-- The printed name of a kind. -/
def Kind.name : Kind → String
  | .message => "message"
  | .oracle => "oracle"
  | .challenge => "challenge"
  | .check => "check"
  | .let_ => "let"

/-- A step of the skeleton together with its position. -/
structure Row where
  id : String
  label : String
  kind : Kind
  block : String
  round : Option ℕ
  stage : String
  ty : String
  display : Display

/-- A claim passed from the node `src` to the node `dst`, stated at `point`. -/
structure ClaimEdge where
  src : String
  dst : String
  label : String
  point : String

/-- A round of a `rounds` block, the stage it belongs to, and its soundness error. -/
structure RoundInfo where
  block : String
  stage : String
  round : ℕ
  error : String

/-- A stage and the claims it consumes and produces. -/
structure StageInfo where
  id : String
  name : String
  input : ClaimDecl
  output : ClaimDecl

/-- The skeleton of a specification, ready for export. -/
structure Skeleton where
  rows : Array Row := #[]
  claims : Array ClaimEdge := #[]
  rounds : Array RoundInfo := #[]
  stages : Array StageInfo := #[]

namespace Skeleton

/-- The state of the fold over the items. -/
structure Fold where
  out : Skeleton := {}
  next : ℕ := 0
  round : Option (String × ℕ) := none
  open_ : List (String × ClaimDecl) := []
  producer : String := "input"
  pending : Option (String × ClaimDecl) := none

/-- Add the edge of a pending output claim, if any, ending at `dst`. -/
def Fold.flush (s : Fold) (dst : String) : Fold :=
  match s.pending with
  | some (src, c) =>
    { s with pending := none,
             out := { s.out with claims := s.out.claims.push ⟨src, dst, c.label, c.point⟩ } }
  | none => s

/-- Process one item. -/
def Fold.item (s : Fold) : Item → Fold
  | .step label kind ty display =>
    let id := "s" ++ toString s.next
    let s := if kind == .check then s.flush id else s
    let row : Row := { id, label, kind, ty, display, block := (s.round.map (·.1)).getD "",
                       round := s.round.map (·.2), stage := (s.open_.head?.map (·.1)).getD "" }
    { s with next := s.next + 1, out := { s.out with rows := s.out.rows.push row } }
  | .beginRound block i error =>
    { s with round := some (block, i),
             out := { s.out with
               rounds := s.out.rounds.push ⟨block, (s.open_.head?.map (·.1)).getD "", i, error⟩ } }
  | .endRound => { s with round := none }
  | .beginStage name input output =>
    let id := "stage:" ++ name
    -- The previous output claim and this input claim are one edge when they coincide.
    let same := match s.pending with
      | some (src, c) => src == s.producer && c.label == input.label && c.point == input.point
      | none => false
    let s := s.flush id
    let claims := if same then s.out.claims
      else s.out.claims.push ⟨s.producer, id, input.label, input.point⟩
    { s with open_ := (name, output) :: s.open_,
             out := { s.out with claims, stages := s.out.stages.push ⟨id, name, input, output⟩ } }
  | .endStage =>
    match s.open_ with
    | (name, output) :: rest =>
      { s with open_ := rest, producer := "stage:" ++ name, pending := some ("stage:" ++ name, output) }
    | [] => s

/-- Fold a list of items into a skeleton. -/
def ofItems (ks : List Item) : Skeleton :=
  ((ks.foldl Fold.item {}).flush "output").out

end Skeleton

/-- The skeleton of a specification as rows and claim edges. -/
@[macro_inline] def Spec.rows {S : Type} {t : OracleProtocol} {ks : List Item}
    (d : Spec S W T t ks) : Skeleton :=
  Skeleton.ofItems d.skeleton

end Elaboration

/-! ## 3. Sum-check -/

section Sumcheck

/-- The claim after `i` rounds: the current target and the challenges so far. -/
structure Claim (R : Type) (i : ℕ) where
  target : R
  challenges : Fin i → R

variable {R : Type} [CommSemiring R] [DecidableEq R] [TypeName R] {d k : ℕ}

instance : TypeName (R⦃≤ d⦄[X]) := ⟨TypeName.name R ++ "_{\\le " ++ toString d ++ "}[X]"⟩

variable [Monad M]

/-- Round `i` of sum-check over the domain `D`, for the polynomial `poly w`. -/
noncomputable def sumcheckRound (n : ℕ) (D : Fin k → R) (poly : W → R⦃≤ d⦄[X Fin n])
    {t : OracleProtocol} {ks : List Item}
    (i : ℕ) (hi : i < n) (st : Claim R i) (next : Claim R (i + 1) → Desc M W T t ks) :=
  oracle "g" (R⦃≤ d⦄[X]) (fun w => Sumcheck.projectedRoundPolynomial D ⟨i, hi⟩ st.challenges (poly w))
    (tex := "g_i(X) = \\sum_{x \\in D^{n-i-1}} p(r_{<i}, X, x)") fun g =>
  check "sum" (do
      let vs ← (List.finRange k).mapM fun a => g.query (D a)
      pure (decide (vs.sum = st.target)))
    (tex := "\\sum_{a \\in D} g_i(a) = c_i") <|
  challenge "r" R (tex := "r_i \\gets \\mathbb{F}") fun r =>
  compute "c" R (g.query r) (tex := "c_{i+1} = g_i(r_i)") fun c =>
  next ⟨c, Fin.snoc st.challenges r⟩

/-- Sum-check: `n` rounds from the claim `input`. -/
noncomputable def sumcheck (n : ℕ) (D : Fin k → R) (poly : W → R⦃≤ d⦄[X Fin n]) (input : Claim R 0)
    {t : OracleProtocol} {ks : List Item} (next : Claim R n → Desc M W T t ks) :=
  rounds "sumcheck" n input (sumcheckRound n D poly) next
    (error := fun _ => toString d ++ "/|F|")

/-- The same rounds with the round body written inline, as `rounds n (fun i … => …)`. The
definitions above name the round body only so that the proofs below can refer to it. -/
example (n : ℕ) (D : Fin k → R) (poly : W → R⦃≤ d⦄[X Fin n]) (input : Claim R 0)
    {t : OracleProtocol} {ks : List Item} (next : Claim R n → Desc M W T t ks) :
    rounds "sumcheck" n input (fun i hi st next =>
      oracle "g" (R⦃≤ d⦄[X])
        (fun w => Sumcheck.projectedRoundPolynomial D ⟨i, hi⟩ st.challenges (poly w))
        (tex := "g_i(X) = \\sum_{x \\in D^{n-i-1}} p(r_{<i}, X, x)") fun g =>
      check "sum" (do
          let vs ← (List.finRange k).mapM fun a => g.query (D a)
          pure (decide (vs.sum = st.target)))
        (tex := "\\sum_{a \\in D} g_i(a) = c_i") <|
      challenge "r" R (tex := "r_i \\gets \\mathbb{F}") fun r =>
      compute "c" R (g.query r) (tex := "c_{i+1} = g_i(r_i)") fun c =>
      next ⟨c, Fin.snoc st.challenges r⟩) next (error := fun _ => toString d ++ "/|F|") =
    sumcheck n D poly input next := rfl

open Sumcheck in
/-- The final claim of sum-check, as ArkLib's `RoundStatement`. -/
abbrev sumcheckFinish (n : ℕ) (st : Claim R n) :
    Desc M W (RoundStatement R n (Fin.last n)) (.pure ⟨⟩) [] :=
  done ⟨st.target, st.challenges⟩

variable (R) in
open Sumcheck in
/-- The sum-check specification. The input claim is a `RoundStatement` and the witness is the
polynomial. -/
noncomputable def sumcheckSpec (d n : ℕ) (D : Fin k → R) :=
  fun (stmt : RoundStatement R n 0) (M : Type → Type) [Monad M] =>
    stage "sumcheck" ⟨"\\sum_{x \\in D^n} p(x) = c_0", "D^n"⟩ ⟨"p(r) = c_n", "r"⟩
      (sumcheck (W := R⦃≤ d⦄[X Fin n]) (M := M) n D id ⟨stmt.target, stmt.challenges⟩)
      (sumcheckFinish n)

set_option smartUnfolding false in
/-- The tree of the description is ArkLib's sum-check tree. -/
theorem sumcheck_tree (d n : ℕ) (D : Fin k → R) :
    Spec.tree (sumcheckSpec R d n D) = Sumcheck.protocol R d n := rfl

open Sumcheck in
/-- The ArkLib interval claim that corresponds to the claim `st` at round `j`. -/
def Claim.toIndexed {n j k : ℕ} (h : j + k = n) (st : Claim R j) : IndexedClaim R n k :=
  ⟨⟨j, by omega⟩, h, ⟨st.target, st.challenges⟩⟩

set_option smartUnfolding false in
open Sumcheck in
theorem prove_roundsGo {n : ℕ} (D : Fin k → R) (p : R⦃≤ d⦄[X Fin n]) {m : Type → Type}
    [Monad m] : ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j),
    Desc.prove (m := m) p (roundsGo (M := Id) "sumcheck" (fun _ => toString d ++ "/|F|") n
        (sumcheckRound n D id) (fun s => .mark .endStage (sumcheckFinish n s)) r j h st) =
      intervalProver D p r (Claim.toIndexed h st)
  | 0, j, h, st => by
    subst h
    rfl
  | r + 1, j, h, st => by
    have ih := fun c ch => prove_roundsGo (m := m) D p r (j + 1) (by omega) ⟨c, ch⟩
    rw [roundsGo.eq_2, Desc.prove.eq_7, sumcheckRound]
    simp only [oracle, check, challenge, compute, Desc.prove.eq_3, Desc.prove.eq_4, Desc.prove.eq_5,
      Desc.prove.eq_6, Desc.prove.eq_7, ih]
    rfl

set_option smartUnfolding false in
open Sumcheck in
/-- The honest prover of the description is ArkLib's honest interval prover. -/
theorem sumcheck_prover {n : ℕ} (D : Fin k → R) (stmt : RoundStatement R n 0)
    (p : R⦃≤ d⦄[X Fin n]) {m : Type → Type} [Monad m] :
    Spec.prover (m := m) (sumcheckSpec R d n D) stmt p =
      intervalProver D p n (IndexedClaim.initial stmt) :=
  prove_roundsGo D p n 0 (Nat.zero_add n) ⟨stmt.target, stmt.challenges⟩

omit [CommSemiring R] [DecidableEq R] [TypeName R] in
private theorem mapM_id_eq {α β : Type} (f : α → Id β) (l : List α) :
    l.mapM f = pure (l.map f) := List.idRun_mapM

set_option smartUnfolding false in
open Sumcheck in
theorem decision_roundsGo {n : ℕ} (D : Fin k → R) {ι : Type} {S : OracleSpec ι}
    (impl : QueryImpl S Id) :
    ∀ (r j : ℕ) (h : j + r = n) (st : Claim R j) (tr : Transcript oracleSig (protocol R d r))
      (lift : QueryImpl (oracleMessageSpec (protocol R d r) tr.path) (OracleComp S)),
      (∀ q, simulateQ impl (lift q) = oracleMessageImpl _ tr q) →
      simulateQ impl (Desc.decision (roundsGo (M := OracleComp S) (W := R⦃≤ d⦄[X Fin n])
        "sumcheck" (fun _ => toString d ++ "/|F|") n (sumcheckRound n D id)
        (fun s => .mark .endStage (sumcheckFinish n s)) r j h st) tr.path (toView _ tr) lift) =
        indexedVerdict D r (some (Claim.toIndexed h st)) tr
  | 0, j, h, st, tr, lift, hl => by
    subst h
    rfl
  | r + 1, j, h, st, tr, lift, hl => by
    rw [indexedVerdict_succ, roundsGo.eq_2, Desc.decision.eq_7, sumcheckRound]
    simp only [oracle, check, challenge, compute, Desc.decision.eq_3, Desc.decision.eq_4,
      Desc.decision.eq_5, Desc.decision.eq_6, Desc.decision.eq_7]
    have hc : View.head (View.tail (toView (protocol R d (r + 1)) tr)) =
      Interpreted.challenge tr := rfl
    simp only [hc, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure, hl, mapM_id_eq,
      LawfulMonad.pure_bind]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    unfold indexedNext
    simp only [Option.bind_some]
    split <;> rename_i h1 <;> split <;> rename_i h2
    · simp only [simulateQ_bind, hl]
      exact decision_roundsGo D impl r (j + 1) (by omega)
        ⟨(Interpreted.message tr).val.eval (Interpreted.challenge tr),
          Fin.snoc st.challenges (Interpreted.challenge tr)⟩
        (Interpreted.tail tr) (fun q => lift (.inr q)) (fun q => hl (.inr q))
    · exact absurd (of_decide_eq_true h1) h2
    · exact absurd (decide_eq_true h2) h1
    · rfl

set_option smartUnfolding false in
open Sumcheck in
/-- On every transcript, the description's verifier decision agrees with ArkLib's
`indexedVerifier` once the oracle queries are answered from the transcript and the input data. -/
theorem sumcheck_decide {n : ℕ} (D : Fin k → R) {ι : Type} {ambient : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m)
    (stmt : RoundStatement R n 0) (data : ∀ i, PolynomialData R n d i)
    (tr : Transcript oracleSig (protocol R d n)) :
    simulateQ (QueryImpl.addLift (r := m) impl ((pathBundle (polynomialFamily R n d)
        (protocol R d n) tr.path).answer (data, oracleMessages _ tr)))
      ((Spec.verifier (sumcheckSpec R d n D) ambient (polynomialFamily R n d)).decide stmt _
        (toView _ tr)).run =
    simulateQ (QueryImpl.addLift (r := m) impl ((pathBundle (polynomialFamily R n d)
        (protocol R d n) tr.path).answer (data, oracleMessages _ tr)))
      ((indexedVerifier R d n D ambient).decide stmt _ (toView _ tr)).run := by
  rw [simulateQ_indexedVerifier_decide]
  change simulateQ _ (simulateQ (pathLift ambient _ _) _) = _
  rw [simulateQ_pathLift]
  exact congrArg pure (decision_roundsGo D _ n 0 (Nat.zero_add n) _ tr _ fun _ => rfl)

set_option smartUnfolding false in
open Sumcheck in
/-- Both verifiers keep the input polynomial as their output oracle. -/
theorem sumcheck_outputMap {n : ℕ} (D : Fin k → R) {ι : Type} (ambient : OracleSpec ι) :
    (Spec.verifier (sumcheckSpec R d n D) ambient (polynomialFamily R n d)).outputMap =
      (indexedVerifier R d n D ambient).outputMap := rfl

/-! ### Named accessors on sum-check transcripts -/

/-- At `n = 3`, `tr.msg "g" 1` is the round polynomial of round 1. -/
example (D : Fin k → R) (tr : Spec.Tr (sumcheckSpec R d 3 D)) :
    (tr.msg "g" 1 : R⦃≤ d⦄[X]) = tr.2.2.1 := rfl

/-- At `n = 3`, `tr.msg "r" 2` is the last challenge. -/
example (D : Fin k → R) (tr : Spec.Tr (sumcheckSpec R d 3 D)) :
    (tr.msg "r" 2 : R) = tr.2.2.2.2.2.1 := rfl

set_option smartUnfolding false in
open Sumcheck in
/-- For every `n`, the first round polynomial is ArkLib's `Interpreted.message`. -/
theorem sumcheck_msg_g_zero {n : ℕ} (D : Fin k → R)
    (tr : Transcript oracleSig (Sumcheck.protocol R d (n + 1))) :
    (Spec.Tr.msg (d := sumcheckSpec R d (n + 1) D) tr "g" 0 : R⦃≤ d⦄[X]) =
      Interpreted.message tr := rfl

set_option smartUnfolding false in
open Sumcheck in
/-- For every `n`, the first challenge is ArkLib's `Interpreted.challenge`. -/
theorem sumcheck_msg_r_zero {n : ℕ} (D : Fin k → R)
    (tr : Transcript oracleSig (Sumcheck.protocol R d (n + 1))) :
    (Spec.Tr.msg (d := sumcheckSpec R d (n + 1) D) tr "r" 0 : R) =
      Interpreted.challenge tr := rfl

end Sumcheck

/-! ## 4. A composed example: Spartan-shaped

A toy R1CS instance supplies the honest polynomials of both sum-checks and the verifier's own
evaluations as functions. The description keeps Spartan's stage structure: the witness oracle,
the outer sum-check of degree 3, the three claimed values, the inner sum-check of degree 2 and the
final check, which queries the witness oracle. Both stages reuse `sumcheck` from Section 3. -/

section Spartan

variable {R : Type} [CommRing R] [DecidableEq R] [TypeName R] [Monad M]

instance {n : ℕ} : TypeName (Fin n → R) := ⟨TypeName.name R ++ "^{" ++ toString n ++ "}"⟩

instance {d : ℕ} {σ : Type} : TypeName (R⦃≤ d⦄[X σ]) :=
  ⟨TypeName.name R ++ "_{\\le " ++ toString d ++ "}[X_1, \\dots]"⟩

/-- A toy R1CS-like instance over `m` constraint variables and `s` witness variables. -/
structure ToyR1CS (R : Type) [CommRing R] (m s : ℕ) where
  /-- The outer sum-check polynomial `eq(τ, x) (Az(x) Bz(x) - Cz(x))` of the witness `z`. -/
  outer : (Fin m → R) → R⦃≤ 1⦄[X Fin s] → R⦃≤ 3⦄[X Fin m]
  /-- The honest values `(Az(r_x), Bz(r_x), Cz(r_x))`. -/
  evals : (Fin m → R) → R⦃≤ 1⦄[X Fin s] → R × R × R
  /-- The inner sum-check polynomial `(A + ρB + ρ²C)(r_x, y) z(y)`. -/
  inner : (Fin m → R) → R → R⦃≤ 1⦄[X Fin s] → R⦃≤ 2⦄[X Fin s]
  /-- The verifier's own evaluation `(A + ρB + ρ²C)(r_x, r_y)`. -/
  matrices : (Fin m → R) → R → (Fin s → R) → R
  /-- The verifier's own evaluation `eq(τ, r_x)`. -/
  eq : (Fin m → R) → (Fin m → R) → R

/-- The Boolean domain `{0, 1}` of both sum-checks. -/
def bits : Fin 2 → R := fun a => (a.val : R)

variable (R) in
/-- The Spartan-shaped protocol. -/
noncomputable def spartanSpec (m s : ℕ) :=
  fun (A : ToyR1CS R m s) (M : Type → Type) [Monad M] =>
  oracle (M := M) (T := Unit) "z" (R⦃≤ 1⦄[X Fin s]) id (tex := "\\tilde z") fun z =>
  challenge "tau" (Fin m → R) (tex := "\\tau \\gets \\mathbb{F}^m") fun τ =>
  stage "outer"
    ⟨"\\sum_{x} \\widetilde{eq}(\\tau, x)\\,(\\widetilde{Az}\\,\\widetilde{Bz} - \\widetilde{Cz})(x) = 0",
      "\\{0,1\\}^m"⟩
    ⟨"\\widetilde{eq}(\\tau, r_x)\\,(v_A v_B - v_C) = c_x", "r_x"⟩
    (sumcheck m bits (A.outer τ) ⟨0, Fin.elim0⟩) fun cx =>
  message "vA" R (fun w => (A.evals cx.challenges w).1) (tex := "v_A = \\widetilde{Az}(r_x)") fun vA =>
  message "vB" R (fun w => (A.evals cx.challenges w).2.1) (tex := "v_B = \\widetilde{Bz}(r_x)") fun vB =>
  message "vC" R (fun w => (A.evals cx.challenges w).2.2) (tex := "v_C = \\widetilde{Cz}(r_x)") fun vC =>
  check "outer" (pure (decide (A.eq τ cx.challenges * (vA * vB - vC) = cx.target)))
    (tex := "\\widetilde{eq}(\\tau, r_x)\\,(v_A v_B - v_C) = c_x") <|
  challenge "rho" R (tex := "\\rho \\gets \\mathbb{F}") fun ρ =>
  stage "inner"
    ⟨"\\sum_{y} (\\tilde A + \\rho \\tilde B + \\rho^2 \\tilde C)(r_x, y)\\,\\tilde z(y) = v_A + \\rho v_B + \\rho^2 v_C",
      "\\{0,1\\}^s"⟩
    ⟨"(\\tilde A + \\rho \\tilde B + \\rho^2 \\tilde C)(r_x, r_y)\\,\\tilde z(r_y) = c_y", "r_y"⟩
    (sumcheck s bits (A.inner cx.challenges ρ) ⟨vA + ρ * vB + ρ ^ 2 * vC, Fin.elim0⟩) fun cy =>
  compute "zr" R (z.query cy.challenges) (tex := "e = \\tilde z(r_y)") fun e =>
  check "final" (pure (decide (A.matrices cx.challenges ρ cy.challenges * e = cy.target)))
    (tex := "(\\tilde A + \\rho \\tilde B + \\rho^2 \\tilde C)(r_x, r_y)\\cdot e = c_y") <|
  done ()

/-- The first claimed value, by name. -/
example (tr : Spec.Tr (spartanSpec R 2 2)) : (tr.msg "vA" 0 : R) = tr.2.2.2.2.2.2.1 := rfl

end Spartan

/-! ## 5. An oracle-heavy example: FRI-shaped

The toy domain is `Fin N` with two index maps `lo` and `hi`. Every oracle is a function
`Fin N → R`, queried pointwise. Folding round `i` samples `α_i` and sends `f_{i+1} = fold f_i α_i`.
The prover then sends the final value `c`, and each of the `l` query rounds samples a point `x` and
checks every folding step by querying `f_i` and `f_{i+1}` by name. -/

section FRI

variable {R : Type} [CommRing R] [DecidableEq R] [TypeName R] {N : ℕ}

instance : TypeName (Fin N) := ⟨"D_{" ++ toString N ++ "}"⟩

/-- One folding step: `fold f α x = f (lo x) + α · f (hi x)`. -/
def fold (lo hi : Fin N → Fin N) (f : Fin N → R) (α : R) : Fin N → R :=
  fun x => f (lo x) + α * f (hi x)

/-- The honest `f_i`: fold `f_0` with `α_0, …, α_{i-1}`. -/
def foldAll (lo hi : Fin N → Fin N) (f₀ : Fin N → R) : {i : ℕ} → (Fin i → R) → Fin N → R
  | 0, _ => f₀
  | _ + 1, α => fold lo hi (foldAll lo hi f₀ (Fin.init α)) (α (Fin.last _))

/-- The verifier's state after `i` folding rounds: the challenges and the oracle handles of
`f_0, …, f_i`. -/
structure FriState (M : Type → Type) (R : Type) (N i : ℕ) where
  alphas : Fin i → R
  f : Fin (i + 1) → Oracle M (Fin N → R) inferInstance

variable [Monad M]

/-- Folding round `i`. -/
def friFoldRound (k : ℕ) (lo hi : Fin N → Fin N) {t : OracleProtocol} {ks : List Item}
    (i : ℕ) (_ : i < k) (st : FriState M R N i)
    (next : FriState M R N (i + 1) → Desc M (Fin N → R) T t ks) :=
  challenge "alpha" R (tex := "\\alpha_i \\gets \\mathbb{F}") fun α =>
  oracle "f" (Fin N → R) (fun w => fold lo hi (foldAll lo hi w st.alphas) α)
    (tex := "f_{i+1} = \\mathrm{fold}(f_i, \\alpha_i)") fun f =>
  next ⟨Fin.snoc (α := fun _ => R) st.alphas α, Fin.snoc (α := fun _ => _) st.f f⟩

/-- Query round `j`: sample `x` and check every folding step at `x`, then the final value. -/
def friQueryRound (k : ℕ) (lo hi : Fin N → Fin N) (st : FriState M R N k) (c : R)
    {l : ℕ} {t : OracleProtocol} {ks : List Item} (j : ℕ) (_ : j < l) (_ : Unit)
    (next : Unit → Desc M (Fin N → R) T t ks) :=
  challenge "x" (Fin N) (tex := "x_j \\gets D") fun x =>
  check "fold" ((List.finRange k).allM fun i => do
      let a ← (st.f i.castSucc).query (lo x)
      let b ← (st.f i.castSucc).query (hi x)
      let e ← (st.f i.succ).query x
      pure (decide (e = a + st.alphas i * b)))
    (tex := "\\forall i < k:\\ f_{i+1}(x_j) = f_i(\\mathrm{lo}(x_j)) + \\alpha_i f_i(\\mathrm{hi}(x_j))") <|
  check "final" (do pure (decide ((← (st.f (Fin.last k)).query x) = c)))
    (tex := "f_k(x_j) = c") <|
  next ()

/-- The commit phase: `f_0`, then `k` folding rounds, then the final value `c`. -/
def friCommit (k : ℕ) (lo hi : Fin N → Fin N) (x₀ : Fin N) {t : OracleProtocol} {ks : List Item}
    (next : FriState M R N k × R → Desc M (Fin N → R) T t ks) :=
  oracle "f" (Fin N → R) id (tex := "f_0") fun f₀ =>
  rounds "fold" k (State := FriState M R N) ⟨Fin.elim0, fun _ => f₀⟩ (friFoldRound k lo hi)
    (error := fun _ => "|D|/|\\mathbb{F}|") fun st =>
  message "c" R (fun w => foldAll lo hi w st.alphas x₀) (tex := "c = f_k") fun c =>
  next (st, c)

/-- The query phase: `l` query rounds. -/
def friQuery (k l : ℕ) (lo hi : Fin N → Fin N) (st : FriState M R N k) (c : R)
    {t : OracleProtocol} {ks : List Item} (next : Unit → Desc M (Fin N → R) T t ks) :=
  rounds "query" l (State := fun _ => Unit) () (friQueryRound (l := l) k lo hi st c)
    (error := fun _ => "1 - \\delta") next

variable (R) in
/-- The FRI-shaped protocol with `k` folding rounds and `l` queries. -/
def friSpec (k l : ℕ) (lo hi : Fin N → Fin N) (x₀ : Fin N) :=
  fun (_ : Unit) (M : Type → Type) [Monad M] =>
  stage (M := M) (T := Unit) "commit" ⟨"f_0 \\in \\mathrm{RS}", "D"⟩ ⟨"f_k \\equiv c", "D"⟩
    (friCommit (R := R) k lo hi x₀) fun (st, c) =>
  stage "query" ⟨"f_k \\equiv c", "D"⟩ ⟨"accept", "x_0, \\dots, x_{l-1}"⟩
    (friQuery k l lo hi st c) fun _ =>
  done ()

/-- The oracle `f_2`, by name: the label `"f"` in its occurrence `2`. -/
example (lo hi : Fin N → Fin N) (x₀ : Fin N) (tr : Spec.Tr (friSpec R 2 2 lo hi x₀)) :
    (tr.msg "f" 2 : Fin N → R) = tr.2.2.2.2.1 := rfl

end FRI

/-! ## 6. Export

`main` writes `out/<name>.json` and `out/<name>.tex` for each example. The JSON file has this
schema (all strings unless noted):

```
{ "name":      example name,
  "schema":    "arklib-protocol-skeleton/0",
  "terminals": [ { "id": "input" | "output", "kind": "input" | "output" } ],
  "steps":     [ { "id": "s<k>", "kind": "message" | "oracle" | "challenge" | "check" | "let",
                   "label", "owner": "prover" | "verifier", "block": rounds block or "",
                   "round": number or null, "stage": innermost stage or "",
                   "type": printed type (LaTeX), "tex", "doc" } ],
  "stages":    [ { "id": "stage:<name>", "kind": "stage", "name",
                   "input":  { "label", "point" }, "output": { "label", "point" } } ],
  "claims":    [ { "from": node id, "to": node id, "kind": "claim", "label", "point" } ],
  "rounds":    [ { "block", "stage", "round": number, "error" } ] }
```

Steps, stages and terminals are the nodes: each has an `id` and a `kind`, as in the Binary Jolt
Book's book graph. Claims are the typed edges between them. The TeX file is a `cryptocode`
`\procedure` with a prover column and a verifier column. -/

section Export
open Lean

instance : TypeName ℚ := ⟨"\\mathbb{F}"⟩

/-- A row as a JSON node. -/
def Row.toJson (r : Row) : Json :=
  Json.mkObj [("id", .str r.id), ("kind", .str r.kind.name), ("label", .str r.label),
    ("owner", .str r.kind.owner), ("block", .str r.block),
    ("round", match r.round with | some i => Lean.toJson i | none => .null),
    ("stage", .str r.stage), ("type", .str r.ty), ("tex", .str r.display.tex),
    ("doc", .str r.display.doc)]

/-- A claim declaration as JSON. -/
def ClaimDecl.toJson (c : ClaimDecl) : Json :=
  Json.mkObj [("label", .str c.label), ("point", .str c.point)]

/-- A skeleton as JSON, following the schema above. -/
def Skeleton.toJson (name : String) (sk : Skeleton) : Json :=
  Json.mkObj [("name", .str name), ("schema", .str "arklib-protocol-skeleton/0"),
    ("terminals", .arr #[Json.mkObj [("id", .str "input"), ("kind", .str "input")],
      Json.mkObj [("id", .str "output"), ("kind", .str "output")]]),
    ("steps", .arr (sk.rows.map Row.toJson)),
    ("stages", .arr (sk.stages.map fun st => Json.mkObj [("id", .str st.id),
      ("kind", .str "stage"), ("name", .str st.name), ("input", st.input.toJson),
      ("output", st.output.toJson)])),
    ("claims", .arr (sk.claims.map fun e => Json.mkObj [("from", .str e.src), ("to", .str e.dst),
      ("kind", .str "claim"), ("label", .str e.label), ("point", .str e.point)])),
    ("rounds", .arr (sk.rounds.map fun r => Json.mkObj [("block", .str r.block),
      ("stage", .str r.stage), ("round", Lean.toJson r.round), ("error", .str r.error)]))]

/-- The name of a move in the figure: its label, with the round as a subscript. -/
def Row.texName (r : Row) : String :=
  "\\mathsf{" ++ r.label ++ "}" ++
    match r.round with
    | some i => "_{" ++ toString i ++ "}"
    | none => ""

/-- One line of the figure, without its line break. Prover formulas go in the left column, the
message arrow in the middle and the verifier's challenges, checks and local values in the right
column. -/
def Row.texLine (r : Row) : String :=
  let body := if r.display.tex.isEmpty then r.texName else r.display.tex
  match r.kind with
  | .message => body ++ " \\< \\sendmessageright*{" ++ r.texName ++ " \\in " ++ r.ty ++ "} \\<"
  | .oracle => body ++ " \\< \\sendmessageright*{[\\![" ++ r.texName ++ "]\\!] \\in " ++ r.ty ++
      "} \\<"
  | .challenge => " \\< \\sendmessageleft*{" ++ r.texName ++ "} \\< " ++ body
  | .check => " \\< \\< \\text{check } " ++ body
  | .let_ => " \\< \\< " ++ body

/-- The figure: a `\procedure` whose rows follow the skeleton. A dotted division opens each stage
and each round. `cryptocode` requires `\pclb` instead of `\\` before a division and allows only
one division in a row. -/
def Skeleton.toTex (title : String) (sk : Skeleton) : String := Id.run do
  let mut lines : Array String := #["\\textbf{Prover} \\< \\< \\textbf{Verifier}"]
  let mut divided : Array Bool := #[false]
  let mut stage := ""
  let mut round : Option (String × ℕ) := none
  for r in sk.rows do
    let mut divs : Array String := #[]
    if r.stage != stage then
      stage := r.stage
      if !stage.isEmpty then
        divs := divs.push ("stage \\textsf{" ++ stage ++ "}")
    let key := r.round.map (r.block, ·)
    if key != round then
      round := key
      if let some (b, i) := key then
        divs := divs.push ("\\textsf{" ++ b ++ "}, round " ++ toString i)
    if !divs.isEmpty then
      divided := divided.set! (divided.size - 1) true
    let division := if divs.isEmpty then ""
      else "\\pcintertext[dotted]{" ++ String.intercalate "; " divs.toList ++ "}\n"
    lines := lines.push (division ++ r.texLine)
    divided := divided.push false
  -- Line `k` ends with `\pclb` when a division follows it, with `\\` otherwise, and the last
  -- line ends with nothing.
  let body := (List.range lines.size).map fun k =>
    lines[k]! ++
      if k + 1 == lines.size then "" else if divided[k]! then " \\pclb" else " \\\\"
  return "% Generated by docs/design/interaction-layer/prototypes/ProtocolSpecs.lean.\n" ++
    "% Requires \\usepackage{amsmath,amssymb} and \\usepackage{cryptocode}.\n" ++
    "\\begin{figure}\n\\centering\n\\procedure{" ++ title ++ "}{%\n" ++
    String.intercalate "\n" body ++
    "\n}\n\\caption{" ++ title ++ ", generated from the skeleton.}\n\\end{figure}\n"

/-- Write the JSON and TeX files of one example. -/
def writeExample (dir : System.FilePath) (name title : String) (sk : Skeleton) : IO Unit := do
  IO.FS.writeFile (dir / (name ++ ".json")) ((sk.toJson name).pretty ++ "\n")
  IO.FS.writeFile (dir / (name ++ ".tex")) (sk.toTex title)

end Export


/-! ## Open problems

1. **Input oracles.** A description cannot query the input oracle bundle. `Spec.verifier` keeps
   its inputs through `OracleMap.fst` and never reads them. Sum-check does not need the input
   polynomial inside the interaction, but the FRI example has to send `f_0` as an oracle message
   instead of reading it as an input, and Spartan's final check reads the witness oracle that the
   prover sent, not an input commitment. Adding an `input` handle to `Desc` needs `Desc.decision`
   to take the input part of `pathBundle`.

2. **Agreement for each protocol.** The prover and the verifier come from one description run in
   two monads. Lean has no parametricity theorem, so the agreement of `Spec.decision` with a
   hand-written verifier needs its own induction for each protocol (`decision_roundsGo` for
   sum-check). A general theorem "the honest prover passes every check" needs a separate
   completeness statement per check.

3. **`smartUnfolding`.** `sumcheck_tree` holds by `rfl` for every `n`, but only under
   `set_option smartUnfolding false`. Without it the elaborator does not unfold the structural
   recursion of `roundsTree` and `Sumcheck.protocol` against each other and reports
   `Type mismatch: rfl has type ?m.13 = ?m.13 but is expected to have type
   Spec.tree (sumcheckSpec R d n D) = protocol R d n`. Under that option `simp` unfolds definitions to their `brecOn`
   internals, so the proofs rewrite with the equation lemmas `roundsGo.eq_2`, `Desc.prove.eq_N`
   and `Desc.decision.eq_N` instead.

4. **Uniform round shape.** `rounds` requires every round to have the same tree shape
   `F : OracleProtocol → OracleProtocol`. Real FRI halves the domain in each round, so its oracle
   type changes with `i`. The toy FRI keeps one domain `Fin N`. A dependent variant would take
   `F : ℕ → OracleProtocol → OracleProtocol` and carry the round index in the tree.

5. **`simp` cannot compute positions.** `tr.msg "g" 1` reduces by `rfl` at a concrete size, and
   `moveAt_zero`, `moveAt_succ`, `Spec.Tr.msg_eq` are `@[simp]` lemmas. But `simp` and `dsimp`
   cannot evaluate the position `movePos "g" ks 1` in place, because the result type of `tr.msg`
   depends on it: after `rw [Spec.Tr.msg_eq]` the goal keeps the stuck term
   `moveAt oracleSig … tr (if true = true then if "g" = "g" then … )`, and `simp only [moveAt_succ]`
   does not fire on `roundsTree F t 3`. A proof uses `rfl` or `change moveAt oracleSig _ tr 2 = _`.
   A macro that computes the position at elaboration time would remove this.

6. **Labels are global.** `tr.msg "g" i` counts occurrences of `"g"` across the whole
   description. In the Spartan example `"g"` occurs in both stages, so `tr.msg "g" 2` is the first
   round polynomial of the inner stage. Qualifying labels by stage (`"inner.g"`) is a small change
   to `movePos`.

7. **Dot notation on specifications.** A `Spec` definition elaborates to its unfolded function
   type, so `(sumcheckSpec R d 3 D).Tr` fails with
   `Invalid field 'Tr': The environment does not contain 'Function.Tr'`. The accessors are written
   `Spec.Tr (sumcheckSpec R d 3 D)`. Giving the definition the type `Spec …` explicitly needs the
   tree and skeleton written out, which defeats the point.

8. **The final state uses a cast.** `roundsGo` passes the state at round `j` with `j + 0 = n` to
   the continuation as `h ▸ st`. The cast is internal to `rounds` and never appears in a
   description, but a proof about the last round sees it (`subst h` removes it).
-/

end ProtocolSpecs

open ProtocolSpecs in
/-- Write the skeletons of sum-check at `n = 3`, the Spartan-shaped example and the FRI-shaped
example at `k = 2`, `l = 2`. -/
def main : IO Unit := do
  let dir : System.FilePath := "docs/design/interaction-layer/prototypes/out"
  IO.FS.createDirAll dir
  writeExample dir "sumcheck" "Sum-check ($n = 3$, $d = 2$)"
    (Spec.rows (sumcheckSpec ℚ 2 3 (bits (R := ℚ))))
  writeExample dir "spartan" "Spartan-shaped protocol ($m = s = 2$)"
    (Spec.rows (spartanSpec ℚ 2 2))
  writeExample dir "fri" "FRI-shaped protocol ($k = 2$, $l = 2$)"
    (Spec.rows (friSpec ℚ 2 2 (N := 4) id id 0))
  IO.println "wrote sumcheck, spartan and fri to docs/design/interaction-layer/prototypes/out"

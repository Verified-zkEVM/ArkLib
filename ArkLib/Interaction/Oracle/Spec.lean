/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.Basic.Append
import PolyFun.Interaction.TwoParty.Strategy
import ArkLib.Interaction.Reduction
import ArkLib.OracleReduction.OracleInterface

open Interaction.TwoParty

/-!
# Oracle Protocol Specification

`Oracle.Spec` is the canonical protocol specification for oracle reductions.
It distinguishes two kinds of message nodes:

- `.public X rest`: the continuation depends on the message value `x : X`. Used
  for plain sender messages (metadata) and receiver messages (challenges). Both
  parties see the message value directly.

- `.oracle X rest`: the continuation is structurally constant. Used for oracle
  sender messages: the prover sends the message, but the verifier only accesses
  it through oracle queries. The key invariant is that `rest : Oracle.Spec` does
  not depend on the message, so all downstream types are definitionally
  independent of the oracle message value.

This structural distinction gives:
- **`PublicTranscript`**: transcript of `.public` nodes only, the verifier's
  direct view of the interaction.
- **`QueryHandle` / `toOracleSpec`**: indexed by `PublicTranscript`, not by the
  full transcript. No casts needed for oracle spec composition.
- **`toMonadDecoration`**: at `.oracle` nodes the monad is `Id` (verifier ignores
  the message), but the accumulated oracle spec grows for subsequent queries.

## Polynomial substrate

`Oracle.Spec` is *definitionally* the free monad over a coproduct polynomial
that distinguishes the two kinds of position:

```
Oracle.Spec := PFunctor.FreeM Oracle.Spec.basePFunctor PUnit
```

NOTE (universe polymorphism): the entire stack is currently pinned at
`Type 1` (with `X : Type`, `Position : Type 1`, `Spec : Type 1`, `PUnit.{1}`
fibers). VCVio's `Interaction.Spec.{u} : Type (u+1)` is universe-polymorphic;
aligning `Oracle.Spec` would cascade through `OracleDeco`, `toMonadDecoration`,
`toOracleSpec`, and every downstream protocol. No current ArkLib client uses
`Oracle.Spec` at a non-default universe, and `OracleSpec.{0,0}` is the
ambient query-spec universe across the codebase, so polymorphizing buys no
expressivity today. Track polymorphization as a follow-up if an oracle
message type at higher universe is needed.

where `Oracle.Spec.basePFunctor.A := Oracle.Position` is a two-constructor
inductive (`.public X` and `.oracle X`), and the child family is

```
B (.public X) := X        -- continuation depends on the message
B (.oracle X) := PUnit     -- continuation is structurally constant
```

The non-dependence of oracle continuations is therefore enforced at the
polynomial level, not by external invariants.

All three smart constructors `Spec.done`, `Spec.public`, `Spec.oracle` are
tagged `@[match_pattern]` and have *symmetric shape*: each takes its
continuation in first-class position so that Lean's pattern compiler can
invert it. In particular `oracle X cont` takes `cont : PUnit → Spec` (mirroring
`public X rest`'s `rest : X → Spec`); the `PUnit`-indexed function is the
type-level expression of "structurally constant continuation". Construction
sites pass `fun _ => rest`; pattern bodies recover the rest via `cont ⟨⟩`.

A hand-rolled `casesOn` / `recOn` pair is registered so that `cases s` /
`induction s` expose the same three-case shape as the underlying patterns
without leaking `.roll` or the polynomial substrate.

## Main definitions

### Core types
- `Oracle.Position` — coproduct of public / oracle position kinds.
- `Oracle.Spec.basePFunctor` — the polynomial functor whose free monad is `Spec`.
- `Oracle.Spec` — `PFunctor.FreeM Oracle.Spec.basePFunctor PUnit`.
- `Spec.RoleDeco` — role assignment on `.public` nodes only.
- `Spec.OracleDeco` — oracle interface assignment on `.oracle` nodes only.

### Runtime map
- `Oracle.executionLens` — expose oracle specs as plain interaction specs.
- `Spec.toInteractionSpec` — convert to `Interaction.Spec` through
  `Oracle.executionLens`.
- `Spec.toSpecRoles` — lift role decoration.

### Transcripts
- `Spec.PublicTranscript` — verifier/control path with `PUnit` oracle markers.
- `Spec.FullTranscript` — runtime path containing actual oracle messages.
- `Spec.projectPublic` — project full transcript to `PublicTranscript`.

### Oracle query infrastructure
- `Spec.QueryHandle` — query index type, indexed by `PublicTranscript`.
- `Spec.toOracleSpec` — oracle spec, indexed by `PublicTranscript`.
- `Spec.answerQuery` — answer queries using full transcript data.

### Verifier monad decoration
- `Spec.toMonadDecoration` — per-node monad assignment for the verifier.
-/

universe u v

open OracleComp OracleSpec

namespace Interaction.Oracle

/-! ## Polynomial substrate -/

/-- Position kinds for an oracle protocol node. A `.public X` position carries
a message of type `X` whose value is observable by both parties (the
continuation may depend on it). A `.oracle X` position also carries a message
of type `X`, but the continuation is structurally constant: the verifier only
reaches the value through oracle queries, so the protocol cannot branch on
it. -/
inductive Position : Type 1 where
  | «public» : (X : Type) → Position
  | «oracle» : (X : Type) → Position

/-- Child family of the oracle `basePFunctor`: a public position has an `X`-
indexed continuation, an oracle position has a `PUnit`-indexed (i.e.
structurally constant) continuation. -/
def Position.B : Position → Type
  | .public X => X
  | .oracle _ => PUnit

namespace Spec

/-- The polynomial functor that generates the shape of an oracle protocol
spec. Positions are `Oracle.Position` (a coproduct of public/oracle kinds);
the child family is `Position.B`. The non-dependence of oracle continuations
is encoded structurally by `B (.oracle X) = PUnit`. -/
@[reducible]
def basePFunctor : PFunctor.{1, 0} where
  A := Position
  B := Position.B

end Spec

/-- The canonical protocol specification for oracle reductions, defined as
the free monad on `Oracle.Spec.basePFunctor` with `PUnit` payloads.

Use `Oracle.Spec.done`, `Oracle.Spec.public`, and `Oracle.Spec.oracle` to
construct nodes. All three aliases double as `match` patterns thanks to
their symmetric shape: `oracle` takes `cont : PUnit → Spec` in first-class
position, mirroring `public`'s `rest : X → Spec`. Construction sites pass
`fun _ => rest` for non-dependent oracle continuations; pattern bodies
recover the rest as `cont ⟨⟩`. -/
def Spec : Type 1 := PFunctor.FreeM Spec.basePFunctor PUnit.{1}

namespace Spec

/-- Terminal node: the interaction is over. -/
@[match_pattern, reducible]
def done : Spec := PFunctor.FreeM.pure PUnit.unit

/-- Public-message node: a value `x : X` is exchanged in plain view, then the
protocol continues with `rest x`. -/
@[match_pattern, reducible]
def «public» (X : Type) (rest : X → Spec) : Spec :=
  PFunctor.FreeM.roll (P := basePFunctor) (.public X) rest

/-- Oracle-message node: a value `x : X` is committed by the prover, then the
protocol continues with `cont ⟨⟩`, *independently* of `x`. The verifier only
accesses `x` through oracle queries.

The continuation type `PUnit → Spec` is the type-level expression of
"structurally constant continuation": the polynomial fiber `B (.oracle X)`
is `PUnit`, so `cont` cannot branch on `x`. Construction sites pass
`fun _ => rest`; pattern bodies recover the rest as `cont ⟨⟩`. -/
@[match_pattern, reducible]
def «oracle» (X : Type) (cont : PUnit.{1} → Spec) : Spec :=
  PFunctor.FreeM.roll (P := basePFunctor) (.oracle X) cont

/-- Cases eliminator on `Oracle.Spec` exposing the high-level
`done` / `public` / `oracle` alternatives. Registered as the default `cases`
eliminator so that `cases s with | done => ... | public X rest => ... |
oracle X cont => ...` works on top of the polynomial substrate. -/
@[elab_as_elim, cases_eliminator]
def casesOn {motive : Spec → Sort v}
    (s : Spec)
    (done : motive Spec.done)
    («public» : (X : Type) → (rest : X → Spec) → motive (Spec.«public» X rest))
    («oracle» : (X : Type) → (cont : PUnit.{1} → Spec) →
        motive (Spec.«oracle» X cont)) :
    motive s :=
  match s with
  | .done                  => done
  | .«public» X rest       => «public» X rest
  | .«oracle» X cont       => «oracle» X cont

/-- Structural recursion eliminator on `Oracle.Spec` exposing the high-level
`done` / `public` / `oracle` alternatives, with induction hypotheses on each
recursive continuation. Registered as the default `induction` eliminator. -/
@[elab_as_elim, induction_eliminator]
def recOn {motive : Spec → Sort v}
    (s : Spec)
    (done : motive Spec.done)
    («public» : (X : Type) → (rest : X → Spec) →
        ((x : X) → motive (rest x)) → motive (Spec.«public» X rest))
    («oracle» : (X : Type) → (cont : PUnit.{1} → Spec) →
        motive (cont ⟨⟩) → motive (Spec.«oracle» X cont)) :
    motive s :=
  match s with
  | .done => done
  | .«public» X rest =>
      «public» X rest (fun x => recOn (rest x) done «public» «oracle»)
  | .«oracle» X cont =>
      «oracle» X cont (recOn (cont ⟨⟩) done «public» «oracle»)

/-! ## Role and oracle decorations -/

/-- Displayed-family shape for role assignments on `Oracle.Spec`. -/
def roleDecoShape : PFunctor.FreeM.Displayed.Shape.{1, 0, 0, 1} basePFunctor PUnit.{1} where
  leaf := fun _ => PUnit.{1}
  node := fun
    | .public X => fun child => Interaction.TwoParty.Role × ((x : X) → child x)
    | .oracle _ => fun child => child ⟨⟩

/-- Role assignment for an `Oracle.Spec`. Only `.public` nodes carry a role
(`sender` or `receiver`). `.oracle` nodes are always sender, so no annotation
is stored. -/
abbrev RoleDeco (s : Spec) : Type :=
  PFunctor.FreeM.Displayed roleDecoShape s

/-- Displayed-family shape for oracle interfaces on `Oracle.Spec`. -/
def oracleDecoShape : PFunctor.FreeM.Displayed.Shape.{1, 0, 0, 2} basePFunctor PUnit.{1} where
  leaf := fun _ => PUnit.{2}
  node := fun
    | .public X => fun child => (x : X) → child x
    | .oracle X => fun child => OracleInterface X × child ⟨⟩

/-- Oracle interface assignment. `.oracle` nodes carry an `OracleInterface`
(defining the query-response structure). `.public` nodes just recurse. -/
abbrev OracleDeco (s : Spec) : Type 1 :=
  PFunctor.FreeM.Displayed oracleDecoShape s

/-! ## Runtime map to Interaction.Spec -/

/-- Execution lens from oracle control specs to plain interaction specs.

At public nodes, the runtime direction is exactly the public branch. At oracle
nodes, the runtime direction is the prover's oracle message, and the lens maps
every such message to the unique control branch `PUnit.unit`. Thus the control
tree cannot branch on oracle messages, while the full runtime path can still
record them. -/
def executionLens : PFunctor.Lens basePFunctor Interaction.Spec.basePFunctor where
  toFunA
    | .public X => X
    | .oracle X => X
  toFunB
    | .public _, x => x
    | .oracle _, _ => PUnit.unit

/-- Convert an `Oracle.Spec` to a plain `Interaction.Spec`. `.oracle` nodes
become nodes with *definitionally constant* continuation. -/
def toInteractionSpec (s : Spec) : Interaction.Spec :=
  s.mapLens executionLens

/-- Lift role decoration to `RoleDecoration` on `toInteractionSpec`. `.oracle`
nodes are always `.sender`. -/
def toSpecRoles : (s : Spec) → RoleDeco s → RoleDecoration s.toInteractionSpec
  | .done, _ => ⟨⟩
  | .«public» _ rest, ⟨role, rRest⟩ =>
      ⟨role, fun x => toSpecRoles (rest x) (rRest x)⟩
  | .«oracle» _ cont, roles =>
      ⟨.sender, fun _ => toSpecRoles (cont ⟨⟩) roles⟩

/-- Lift role decoration to every node of the native oracle control tree.

Public nodes use the stored role. Oracle-message nodes are sender nodes:
the prover chooses the oracle message as a runtime direction, while the
verifier observes it only through oracle queries. -/
def toRuntimeRoles : (s : Spec) → RoleDeco s →
    _root_.Interaction.Decoration (fun _ : Position => _root_.Interaction.TwoParty.Role) s
  | .done, _ => ⟨⟩
  | .«public» _ rest, ⟨role, rRest⟩ =>
      ⟨role, fun x => toRuntimeRoles (rest x) (rRest x)⟩
  | .«oracle» _ cont, roles =>
      ⟨.sender, fun _ => toRuntimeRoles (cont ⟨⟩) roles⟩

/-! ## Public transcript -/

/-- The public/control transcript visible to the verifier. Public nodes record
their message value; oracle nodes record the unique `PUnit` branch as a marker
that an oracle message was sent. The actual oracle message is not present here;
it is available only in `FullTranscript` and through oracle queries. -/
abbrev PublicTranscript (s : Spec) : Type :=
  PFunctor.FreeM.Path s

/-- The full/runtime transcript of an oracle protocol. Public nodes record
their public message value, while oracle nodes record the prover's oracle
message. -/
abbrev FullTranscript (s : Spec) : Type :=
  PFunctor.FreeM.PathAlong executionLens s

/-- View a full/runtime transcript as a transcript of `s.toInteractionSpec`. -/
def FullTranscript.toInteractionTranscript (s : Spec) :
    FullTranscript s → Interaction.Spec.Transcript s.toInteractionSpec :=
  PFunctor.FreeM.pathAlongToMapLensPath executionLens s

/-- View a transcript of `s.toInteractionSpec` as a full/runtime transcript. -/
def FullTranscript.ofInteractionTranscript (s : Spec) :
    Interaction.Spec.Transcript s.toInteractionSpec → FullTranscript s :=
  PFunctor.FreeM.mapLensPathToPathAlong executionLens s

/-- Lens-native paired syntax for oracle specs. -/
abbrev pairedSyntaxOver (m : Type → Type) :
    _root_.Interaction.SyntaxOver executionLens _root_.Interaction.TwoParty.Participant.{0}
      (fun _ : Position => _root_.Interaction.TwoParty.Role) :=
  SyntaxOver.TwoParty.paired executionLens m

/-- Functorial shape for lens-native paired syntax on oracle specs. -/
abbrev pairedShapeOver (m : Type → Type) [Functor m] :
    _root_.Interaction.ShapeOver executionLens _root_.Interaction.TwoParty.Participant.{0}
      (fun _ : Position => _root_.Interaction.TwoParty.Role) :=
  ShapeOver.TwoParty.paired executionLens m

/-- Lens-native role-aware strategy over an oracle spec.

Unlike the legacy surface using `toInteractionSpec`, the output is indexed by
`FullTranscript s`, i.e. by runtime paths through `s` along `executionLens`. -/
abbrev StrategyOver (m : Type → Type)
    (agent : _root_.Interaction.TwoParty.Participant.{0})
    (s : Spec) (roles : RoleDeco s)
    (Output : FullTranscript s → Type) : Type :=
  _root_.Interaction.StrategyOver (pairedSyntaxOver m) agent s (toRuntimeRoles s roles) Output

/-- Lens-native focal strategy over an oracle spec. -/
abbrev FocalStrategy (m : Type → Type)
    (s : Spec) (roles : RoleDeco s)
    (Output : FullTranscript s → Type) : Type :=
  StrategyOver m (_root_.Interaction.TwoParty.Participant.focal :
    _root_.Interaction.TwoParty.Participant.{0}) s roles Output

/-- Lens-native counterpart strategy over an oracle spec. -/
abbrev CounterpartStrategy (m : Type → Type)
    (s : Spec) (roles : RoleDeco s)
    (Output : FullTranscript s → Type) : Type :=
  StrategyOver m (_root_.Interaction.TwoParty.Participant.counterpart :
    _root_.Interaction.TwoParty.Participant.{0}) s roles Output

/-- Project a full/runtime transcript to the verifier/control transcript. -/
def projectPublicFull (s : Spec) : FullTranscript s → PublicTranscript s :=
  PFunctor.FreeM.projectPathAlong executionLens s

/-- Project a plain interaction transcript of `s.toInteractionSpec` to the
verifier/control transcript. -/
def projectPublic (s : Spec) :
    Interaction.Spec.Transcript s.toInteractionSpec → PublicTranscript s :=
  fun tr => projectPublicFull s (FullTranscript.ofInteractionTranscript s tr)

@[simp]
theorem projectPublic_done
    (tr : Interaction.Spec.Transcript Spec.done.toInteractionSpec) :
    Spec.done.projectPublic tr = ⟨⟩ :=
  rfl

@[simp]
theorem projectPublic_public (X : Type) (rest : X → Spec)
    (tr : Interaction.Spec.Transcript (Spec.«public» X rest).toInteractionSpec) :
    (Spec.«public» X rest).projectPublic tr =
      ⟨tr.1, (rest tr.1).projectPublic tr.2⟩ :=
  rfl

@[simp]
theorem projectPublic_oracle (X : Type) (cont : PUnit.{1} → Spec)
    (tr : Interaction.Spec.Transcript (Spec.«oracle» X cont).toInteractionSpec) :
    (Spec.«oracle» X cont).projectPublic tr =
      ⟨⟨⟩, (cont ⟨⟩).projectPublic tr.2⟩ :=
  rfl

/-! ## Oracle query infrastructure -/

/-- Index type for oracle queries, parameterized by `PublicTranscript`.
At `.oracle` nodes, the verifier can query the current node's oracle interface
(`.inl q`) or recurse into subsequent oracles (`.inr h`). At `.public` nodes,
the transcript determines which subtree to recurse into. -/
def QueryHandle :
    (s : Spec) → OracleDeco s → PublicTranscript s → Type
  | .done, _, _ => Empty
  | .«public» _ rest, odRest, ⟨x, pt⟩ =>
      QueryHandle (rest x) (odRest x) pt
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨_, pt⟩ =>
      oi.Query ⊕ QueryHandle (cont ⟨⟩) odRest pt

/-- The oracle specification for querying oracle messages along a given
`PublicTranscript` path. Maps each `QueryHandle` to its response type. -/
def toOracleSpec :
    (s : Spec) → (od : OracleDeco s) →
    (pt : PublicTranscript s) → OracleSpec (QueryHandle s od pt)
  | .done, _, _ => fun q => q.elim
  | .«public» _ rest, odRest, ⟨x, pt⟩ =>
      toOracleSpec (rest x) (odRest x) pt
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨_, pt⟩ => fun
    | .inl q => oi.toOC.spec q
    | .inr handle => toOracleSpec (cont ⟨⟩) odRest pt handle

/-- Answer oracle queries using the message values from a full transcript.
At each `.oracle` node, the transcript provides the actual message `x : X`,
which is used to compute responses via `OracleInterface`. -/
def answerQuery :
    (s : Spec) → (od : OracleDeco s) →
    (tr : Interaction.Spec.Transcript s.toInteractionSpec) →
    QueryImpl (toOracleSpec s od (s.projectPublic tr)) Id
  | .done, _, _ => fun q => q.elim
  | .«public» _ rest, odRest, ⟨x, tr⟩ =>
      answerQuery (rest x) (odRest x) tr
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨x, tr⟩ => fun
    | .inl q => (oi.toOC.impl q).run x
    | .inr handle => answerQuery (cont ⟨⟩) odRest tr handle

/-- Extend an accumulated oracle spec by the oracle messages encountered along
a concrete transcript.

This follows the same accumulator order as verifier execution: at an `.oracle`
node the current oracle is appended to the accumulator before recurring. That
shape is more useful for execution theorems than reassociating through
`accSpec + s.toOracleSpec od pt`. -/
def accumulatedSpec :
    (s : Spec) → (od : OracleDeco s) →
    Interaction.Spec.Transcript s.toInteractionSpec →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Σ ιₐ', OracleSpec.{0, 0} ιₐ'
  | .done, _, _, _, accSpec => ⟨_, accSpec⟩
  | .«public» _ rest, odRest, ⟨x, tr⟩, _, accSpec =>
      accumulatedSpec (rest x) (odRest x) tr accSpec
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨_, tr⟩, _, accSpec =>
      accumulatedSpec (cont ⟨⟩) odRest tr
        (accSpec + @OracleInterface.spec _ oi)

@[simp]
theorem accumulatedSpec_done
    (od : OracleDeco Spec.done)
    (tr : Interaction.Spec.Transcript Spec.done.toInteractionSpec)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :
    Spec.accumulatedSpec Spec.done od tr accSpec = ⟨_, accSpec⟩ :=
  rfl

@[simp]
theorem accumulatedSpec_public (X : Type) (rest : X → Spec)
    (od : OracleDeco (Spec.«public» X rest))
    (tr : Interaction.Spec.Transcript (Spec.«public» X rest).toInteractionSpec)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :
    Spec.accumulatedSpec (Spec.«public» X rest) od tr accSpec =
      Spec.accumulatedSpec (rest tr.1) (od tr.1) tr.2 accSpec :=
  rfl

@[simp]
theorem accumulatedSpec_oracle (X : Type) (cont : PUnit.{1} → Spec)
    (od : OracleDeco (Spec.«oracle» X cont))
    (tr : Interaction.Spec.Transcript (Spec.«oracle» X cont).toInteractionSpec)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :
    Spec.accumulatedSpec (Spec.«oracle» X cont) od tr accSpec =
      Spec.accumulatedSpec (cont ⟨⟩) od.2 tr.2
        (accSpec + @OracleInterface.spec _ od.1) :=
  rfl

/-- Answer queries for `accumulatedSpec`, extending an existing
accumulator implementation with the oracle messages in a full transcript. -/
def accumulatedImpl :
    (s : Spec) → (od : OracleDeco s) →
    (tr : Interaction.Spec.Transcript s.toInteractionSpec) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → QueryImpl accSpec Id →
    QueryImpl (accumulatedSpec s od tr accSpec).2 Id
  | .done, _, _, _, _, accImpl => accImpl
  | .«public» _ rest, odRest, ⟨x, tr⟩, _, accSpec, accImpl =>
      accumulatedImpl (rest x) (odRest x) tr accSpec accImpl
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨x, tr⟩, _, accSpec, accImpl =>
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id :=
        fun q => (oi.toOC.impl q).run x
      accumulatedImpl (cont ⟨⟩) odRest tr
        (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX)

@[simp]
theorem accumulatedImpl_done
    (od : OracleDeco Spec.done)
    (tr : Interaction.Spec.Transcript Spec.done.toInteractionSpec)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) (accImpl : QueryImpl accSpec Id) :
    Spec.accumulatedImpl Spec.done od tr accSpec accImpl = accImpl :=
  rfl

@[simp]
theorem accumulatedImpl_public (X : Type) (rest : X → Spec)
    (od : OracleDeco (Spec.«public» X rest))
    (tr : Interaction.Spec.Transcript (Spec.«public» X rest).toInteractionSpec)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) (accImpl : QueryImpl accSpec Id) :
    Spec.accumulatedImpl (Spec.«public» X rest) od tr accSpec accImpl =
      Spec.accumulatedImpl (rest tr.1) (od tr.1) tr.2 accSpec accImpl :=
  rfl

@[simp]
theorem accumulatedImpl_oracle (X : Type) (cont : PUnit.{1} → Spec)
    (od : OracleDeco (Spec.«oracle» X cont))
    (tr : Interaction.Spec.Transcript (Spec.«oracle» X cont).toInteractionSpec)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) (accImpl : QueryImpl accSpec Id) :
    Spec.accumulatedImpl (Spec.«oracle» X cont) od tr accSpec accImpl =
      Spec.accumulatedImpl (cont ⟨⟩) od.2 tr.2
        (accSpec + @OracleInterface.spec _ od.1)
        (QueryImpl.add accImpl (fun q => (od.1.toOC.impl q).run tr.1)) :=
  rfl

/-! ## Node monads -/

/-- The pure node monad used at nodes where a party only observes a message and
does not perform ambient effects. -/
abbrev pureNodeMonad : BundledMonad.{0, 0} :=
  ⟨Id, inferInstance⟩

/-! ## Prover monad decoration -/

/-- The default prover node monad for native oracle reductions. -/
abbrev proverNodeMonad {ι : Type} (oSpec : OracleSpec.{0, 0} ι) : BundledMonad.{0, 0} :=
  ⟨OracleComp oSpec, inferInstance⟩

/-- Default prover-side monad decoration: every prover node runs in the same
ambient `OracleComp oSpec` monad. -/
def toProverMonadDecoration {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (s : Spec) :
    Interaction.Spec.MonadDecoration s.toInteractionSpec :=
  Interaction.Spec.MonadDecoration.constant (proverNodeMonad oSpec) s.toInteractionSpec

/-! ## Verifier monad decoration -/

/-- Default oracle-query spec available to an oracle verifier at receiver nodes:
ambient oracles, input oracle statements, and oracle messages accumulated so far. -/
abbrev verifierAccessSpec {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :=
  oSpec + [OStmtIn]ₒ + accSpec

/-- Default receiver-node monad for oracle verifiers. This is the point where
the oracle verifier gets query access to the ambient oracles, input oracle
statements, and accumulated prover oracle messages. -/
abbrev verifierAccessMonad {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :
    BundledMonad.{0, 0} :=
  ⟨OracleComp (verifierAccessSpec oSpec OStmtIn accSpec), inferInstance⟩

/-- Compute a verifier-side `MonadDecoration` from caller-supplied node effects.

The decoration still tracks accumulated oracle messages structurally, but it
does not prescribe which monad is used at public sender, public receiver, or
oracle-message nodes. The standard oracle verifier is recovered by choosing
`Id` for sender/oracle nodes and `verifierAccessMonad` for receiver nodes. -/
def toMonadDecorationWith
    (senderMonad receiverMonad oracleMonad :
      {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → BundledMonad.{0, 0}) :
    (s : Spec) → (roles : RoleDeco s) → (od : OracleDeco s) →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ →
    Interaction.Spec.MonadDecoration s.toInteractionSpec
  | .done, _, _, _, _ => ⟨⟩
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec =>
      ⟨senderMonad accSpec,
       fun x => toMonadDecorationWith senderMonad receiverMonad oracleMonad
         (rest x) (rRest x) (odRest x) accSpec⟩
  | .«public» _ rest, ⟨.receiver, rRest⟩, odRest, _, accSpec =>
      ⟨receiverMonad accSpec,
       fun x => toMonadDecorationWith senderMonad receiverMonad oracleMonad
         (rest x) (rRest x) (odRest x) accSpec⟩
  | .«oracle» _ cont, roles, ⟨oi, odRest⟩, _, accSpec =>
      ⟨oracleMonad accSpec,
       fun _ => toMonadDecorationWith senderMonad receiverMonad oracleMonad
         (cont ⟨⟩) roles odRest (accSpec + @OracleInterface.spec _ oi)⟩

/-- Pure verifier-side monad decoration: every node uses `Id`.

This is useful for protocols whose verifier has no ambient effects, while still
sharing the same `Oracle.Spec` tree shape. -/
def toPureMonadDecoration :
    (s : Spec) → (roles : RoleDeco s) → (od : OracleDeco s) →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ →
    Interaction.Spec.MonadDecoration s.toInteractionSpec :=
  toMonadDecorationWith
    (fun _ => pureNodeMonad)
    (fun _ => pureNodeMonad)
    (fun _ => pureNodeMonad)

/-- Compute the per-node `MonadDecoration` for the verifier on `toInteractionSpec`.

- At `.oracle` nodes: monad is `Id` (verifier ignores the message value),
  but the accumulated oracle spec grows (verifier can query this oracle at
  subsequent `.public .receiver` nodes).
- At `.public .sender` nodes: monad is `Id`, no accumulation.
- At `.public .receiver` nodes: monad is `OracleComp` with full accumulated
  access (external oracles + input oracle statements + accumulated oracle
  messages). -/
def toMonadDecoration {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)] :
    (s : Spec) → (roles : RoleDeco s) → (od : OracleDeco s) →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ →
    Interaction.Spec.MonadDecoration s.toInteractionSpec :=
  toMonadDecorationWith
    (fun _ => pureNodeMonad)
    (fun accSpec => verifierAccessMonad oSpec OStmtIn accSpec)
    (fun _ => pureNodeMonad)

/-! ## Sequential composition -/

/-- Sequential composition of `Oracle.Spec`: run `s₁` first, then continue with
`s₂ pt₁` where `pt₁ : PublicTranscript s₁` records the public messages from the
first phase. At `.oracle` nodes the public transcript records the unique
`PUnit` marker, so the suffix is indexed by `⟨PUnit.unit, pt₁⟩`. -/
def append (s₁ : Spec) : (PublicTranscript s₁ → Spec) → Spec :=
  Spec.recOn s₁
    (fun s₂ => s₂ ⟨⟩)
    (fun X _rest ih s₂ =>
      Spec.«public» X (fun x => ih x (fun pt => s₂ ⟨x, pt⟩)))
    (fun X _cont ih s₂ =>
      Spec.«oracle» X (fun _ => ih (fun pt => s₂ ⟨⟨⟩, pt⟩)))

@[simp]
theorem append_done (s₂ : PublicTranscript Spec.done → Spec) :
    Spec.append Spec.done s₂ = s₂ ⟨⟩ :=
  rfl

@[simp]
theorem append_public (X : Type) (rest : X → Spec)
    (s₂ : PublicTranscript (Spec.«public» X rest) → Spec) :
    Spec.append (Spec.«public» X rest) s₂ =
      Spec.«public» X (fun x => Spec.append (rest x) (fun pt => s₂ ⟨x, pt⟩)) :=
  rfl

@[simp]
theorem append_oracle (X : Type) (cont : PUnit.{1} → Spec)
    (s₂ : PublicTranscript (Spec.«oracle» X cont) → Spec) :
    Spec.append (Spec.«oracle» X cont) s₂ =
      Spec.«oracle» X (fun _ =>
        Spec.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)) :=
  rfl

/-- Role decoration for an appended `Oracle.Spec`. -/
def RoleDeco.append :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    RoleDeco s₁ → ((pt : PublicTranscript s₁) → RoleDeco (s₂ pt)) →
    RoleDeco (s₁.append s₂)
  | .done, _, _, r₂ => r₂ ⟨⟩
  | .«public» _ rest, s₂, ⟨role, rRest⟩, r₂ =>
      ⟨role, fun x => RoleDeco.append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (rRest x) (fun pt => r₂ ⟨x, pt⟩)⟩
  | .«oracle» _ cont, s₂, r₁, r₂ =>
      RoleDeco.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) r₁
        (fun pt => r₂ ⟨⟨⟩, pt⟩)

@[simp]
theorem RoleDeco.append_done
    (s₂ : PublicTranscript Spec.done → Spec)
    (r₁ : RoleDeco Spec.done)
    (r₂ : (pt : PublicTranscript Spec.done) → RoleDeco (s₂ pt)) :
    RoleDeco.append Spec.done s₂ r₁ r₂ = r₂ ⟨⟩ :=
  rfl

@[simp]
theorem RoleDeco.append_public (X : Type) (rest : X → Spec)
    (s₂ : PublicTranscript (Spec.«public» X rest) → Spec)
    (r₁ : RoleDeco (Spec.«public» X rest))
    (r₂ : (pt : PublicTranscript (Spec.«public» X rest)) → RoleDeco (s₂ pt)) :
    RoleDeco.append (Spec.«public» X rest) s₂ r₁ r₂ =
      ⟨r₁.1, fun x => RoleDeco.append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (r₁.2 x) (fun pt => r₂ ⟨x, pt⟩)⟩ :=
  rfl

@[simp]
theorem RoleDeco.append_oracle (X : Type) (cont : PUnit.{1} → Spec)
    (s₂ : PublicTranscript (Spec.«oracle» X cont) → Spec)
    (r₁ : RoleDeco (Spec.«oracle» X cont))
    (r₂ : (pt : PublicTranscript (Spec.«oracle» X cont)) → RoleDeco (s₂ pt)) :
    RoleDeco.append (Spec.«oracle» X cont) s₂ r₁ r₂ =
      RoleDeco.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) r₁
        (fun pt => r₂ ⟨⟨⟩, pt⟩) :=
  rfl

/-- Oracle decoration for an appended `Oracle.Spec`. -/
def OracleDeco.append :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    OracleDeco s₁ → ((pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    OracleDeco (s₁.append s₂)
  | .done, _, _, od₂ => od₂ ⟨⟩
  | .«public» _ rest, s₂, od₁, od₂ =>
      fun x => OracleDeco.append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩)
  | .«oracle» _ cont, s₂, ⟨oi, odRest⟩, od₂ =>
      ⟨oi, OracleDeco.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩)⟩

@[simp]
theorem OracleDeco.append_done
    (s₂ : PublicTranscript Spec.done → Spec)
    (od₁ : OracleDeco Spec.done)
    (od₂ : (pt : PublicTranscript Spec.done) → OracleDeco (s₂ pt)) :
    OracleDeco.append Spec.done s₂ od₁ od₂ = od₂ ⟨⟩ :=
  rfl

@[simp]
theorem OracleDeco.append_public (X : Type) (rest : X → Spec)
    (s₂ : PublicTranscript (Spec.«public» X rest) → Spec)
    (od₁ : OracleDeco (Spec.«public» X rest))
    (od₂ : (pt : PublicTranscript (Spec.«public» X rest)) → OracleDeco (s₂ pt)) :
    OracleDeco.append (Spec.«public» X rest) s₂ od₁ od₂ =
      fun x => OracleDeco.append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) :=
  rfl

@[simp]
theorem OracleDeco.append_oracle (X : Type) (cont : PUnit.{1} → Spec)
    (s₂ : PublicTranscript (Spec.«oracle» X cont) → Spec)
    (od₁ : OracleDeco (Spec.«oracle» X cont))
    (od₂ : (pt : PublicTranscript (Spec.«oracle» X cont)) → OracleDeco (s₂ pt)) :
    OracleDeco.append (Spec.«oracle» X cont) s₂ od₁ od₂ =
      ⟨od₁.1, OracleDeco.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        od₁.2 (fun pt => od₂ ⟨⟨⟩, pt⟩)⟩ :=
  rfl

namespace MonadDecoration

/-- Append monad decorations along `Oracle.Spec.append`.

This is the oracle-public analogue of `Interaction.Spec.Decoration.append`:
the suffix decoration is indexed by the prefix public transcript, while the
first-phase decoration may still depend on every concrete message in
`toInteractionSpec`, including oracle messages that are not public. -/
def appendPublic :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    Interaction.Spec.MonadDecoration s₁.toInteractionSpec →
    ((pt₁ : PublicTranscript s₁) →
      Interaction.Spec.MonadDecoration (s₂ pt₁).toInteractionSpec) →
    Interaction.Spec.MonadDecoration (s₁.append s₂).toInteractionSpec
  | .done, _, _, md₂ => md₂ ⟨⟩
  | .«public» _ rest, s₂, ⟨m₁, mdRest⟩, md₂ =>
      ⟨m₁, fun x =>
        appendPublic (rest x) (fun pt => s₂ ⟨x, pt⟩)
          (mdRest x) (fun pt => md₂ ⟨x, pt⟩)⟩
  | .«oracle» _ cont, s₂, ⟨m₁, mdRest⟩, md₂ =>
      ⟨m₁, fun x =>
        appendPublic (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
          (mdRest x) (fun pt => md₂ ⟨⟨⟩, pt⟩)⟩

/-- Appending two constant monad decorations embeds into the constant
decoration on the appended oracle spec.

The result is stated as a nodewise homomorphism rather than an equality, so
callers can retarget strategies without relying on unfolding an unknown
`Oracle.Spec`. -/
def appendPublicConstantHom (bm : BundledMonad) :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    Interaction.Spec.MonadDecoration.Hom (s₁.append s₂).toInteractionSpec
      (appendPublic s₁ s₂
        (Interaction.Spec.MonadDecoration.constant bm s₁.toInteractionSpec)
        (fun pt₁ => Interaction.Spec.MonadDecoration.constant bm (s₂ pt₁).toInteractionSpec))
      (Interaction.Spec.MonadDecoration.constant bm (s₁.append s₂).toInteractionSpec)
  | .done, s₂ =>
      Interaction.Spec.MonadDecoration.Hom.id (s₂ ⟨⟩).toInteractionSpec
        (Interaction.Spec.MonadDecoration.constant bm (s₂ ⟨⟩).toInteractionSpec)
  | .«public» _ rest, s₂ =>
      ⟨fun x => x, fun x =>
        appendPublicConstantHom bm (rest x) (fun pt => s₂ ⟨x, pt⟩)⟩
  | .«oracle» _ cont, s₂ =>
      ⟨fun x => x, fun _ =>
        appendPublicConstantHom bm (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)⟩

end MonadDecoration

/-- `PublicTranscript` of an appended spec decomposes into a prefix and suffix. -/
def PublicTranscript.append :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) →
    PublicTranscript (s₁.append s₂)
  | .done, _, _, pt₂ => pt₂
  | .«public» _ rest, s₂, ⟨x, pt₁⟩, pt₂ =>
      ⟨x, PublicTranscript.append (rest x) (fun pt => s₂ ⟨x, pt⟩) pt₁ pt₂⟩
  | .«oracle» _ cont, s₂, ⟨_, pt₁⟩, pt₂ =>
      ⟨⟨⟩, PublicTranscript.append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) pt₁ pt₂⟩

/-- Split a `PublicTranscript` of an appended spec into prefix and suffix. -/
def PublicTranscript.split :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    PublicTranscript (s₁.append s₂) →
    (pt₁ : PublicTranscript s₁) × PublicTranscript (s₂ pt₁)
  | .done, _, pt => ⟨⟨⟩, pt⟩
  | .«public» _ rest, s₂, ⟨x, ptRest⟩ =>
      let ⟨pt₁, pt₂⟩ := PublicTranscript.split (rest x) (fun pt => s₂ ⟨x, pt⟩) ptRest
      ⟨⟨x, pt₁⟩, pt₂⟩
  | .«oracle» _ cont, s₂, ⟨_, ptRest⟩ =>
      let ⟨pt₁, pt₂⟩ :=
        PublicTranscript.split (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) ptRest
      ⟨⟨⟨⟩, pt₁⟩, pt₂⟩

/-- Splitting after appending recovers the original components. -/
@[simp]
theorem PublicTranscript.split_append :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    PublicTranscript.split s₁ s₂ (PublicTranscript.append s₁ s₂ pt₁ pt₂) = ⟨pt₁, pt₂⟩
  | .done, _, _, _ => rfl
  | .«public» _ rest, s₂, ⟨x, pt₁⟩, pt₂ => by
      simp only [PublicTranscript.append, PublicTranscript.split]
      rw [split_append]
  | .«oracle» _ cont, s₂, ⟨⟨⟩, pt₁⟩, pt₂ => by
      simp only [PublicTranscript.append, PublicTranscript.split]
      rw [split_append]

/-- Appending the components produced by `split` recovers the original. -/
@[simp]
theorem PublicTranscript.append_split :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (pt : PublicTranscript (s₁.append s₂)) →
    let ⟨pt₁, pt₂⟩ := PublicTranscript.split s₁ s₂ pt
    PublicTranscript.append s₁ s₂ pt₁ pt₂ = pt
  | .done, _, _ => rfl
  | .«public» _ rest, s₂, ⟨x, ptRest⟩ => by
      simp only [PublicTranscript.split, PublicTranscript.append]
      rw [append_split]
  | .«oracle» _ cont, s₂, ⟨⟨⟩, ptRest⟩ => by
      simp only [PublicTranscript.split, PublicTranscript.append]
      rw [append_split]

/-- Lift a two-argument type family indexed by per-phase `PublicTranscript`s to a
single-argument family on the combined `PublicTranscript` of `s₁.append s₂`.

`liftAppend s₁ s₂ F (PublicTranscript.append s₁ s₂ pt₁ pt₂)` reduces
**definitionally** to `F pt₁ pt₂`. -/
def PublicTranscript.liftAppend :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    ((pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    PublicTranscript (s₁.append s₂) → Type u
  | .done, _, F, pt => F ⟨⟩ pt
  | .«public» _ rest, s₂, F, ⟨x, ptRest⟩ =>
      liftAppend (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) ptRest
  | .«oracle» _ cont, s₂, F, ⟨_, ptRest⟩ =>
      liftAppend (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        (fun pt₁ pt₂ => F ⟨⟨⟩, pt₁⟩ pt₂) ptRest

/-- `liftAppend` on an appended transcript reduces to the original family. -/
@[simp]
theorem PublicTranscript.liftAppend_append :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    PublicTranscript.liftAppend s₁ s₂ F
      (PublicTranscript.append s₁ s₂ pt₁ pt₂) = F pt₁ pt₂
  | .done, _, _, _, _ => rfl
  | .«public» _ rest, s₂, F, ⟨x, pt₁⟩, pt₂ => by
      simp only [PublicTranscript.append, PublicTranscript.liftAppend]
      exact liftAppend_append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) pt₁ pt₂
  | .«oracle» _ cont, s₂, F, ⟨_, pt₁⟩, pt₂ =>
      liftAppend_append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        (fun pt₁ pt₂ => F ⟨⟨⟩, pt₁⟩ pt₂) pt₁ pt₂

/-- `liftAppend` equals the original family applied to the split components. -/
theorem PublicTranscript.liftAppend_split :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt : PublicTranscript (s₁.append s₂)) →
    let ⟨pt₁, pt₂⟩ := PublicTranscript.split s₁ s₂ pt
    PublicTranscript.liftAppend s₁ s₂ F pt = F pt₁ pt₂
  | .done, _, _, _ => rfl
  | .«public» _ rest, s₂, F, ⟨x, ptRest⟩ => by
      simp only [PublicTranscript.split, PublicTranscript.liftAppend]
      exact liftAppend_split (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) ptRest
  | .«oracle» _ cont, s₂, F, ⟨_, ptRest⟩ =>
      liftAppend_split (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        (fun pt₁ pt₂ => F ⟨⟨⟩, pt₁⟩ pt₂) ptRest

/-- Transport a `liftAppend` value to the pair-indexed family via `split`. -/
def PublicTranscript.unliftAppend :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt : PublicTranscript (s₁.append s₂)) →
    PublicTranscript.liftAppend s₁ s₂ F pt →
    let ⟨pt₁, pt₂⟩ := PublicTranscript.split s₁ s₂ pt
    F pt₁ pt₂
  | .done, _, _, _, x => x
  | .«public» _ rest, s₂, F, ⟨x, ptRest⟩, val =>
      unliftAppend (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) ptRest val
  | .«oracle» _ cont, s₂, F, ⟨_, ptRest⟩, val =>
      unliftAppend (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        (fun pt₁ pt₂ => F ⟨⟨⟩, pt₁⟩ pt₂) ptRest val

/-- Transport a pair-indexed value into `liftAppend` via `append`. -/
def PublicTranscript.packAppend :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    F pt₁ pt₂ → liftAppend s₁ s₂ F (append s₁ s₂ pt₁ pt₂)
  | .done, _, _, ⟨⟩, _, x => x
  | .«public» _ rest, s₂, F, ⟨xm, pt₁⟩, pt₂, x =>
      packAppend (rest xm) (fun pt => s₂ ⟨xm, pt⟩)
        (fun pt₁ pt₂ => F ⟨xm, pt₁⟩ pt₂) pt₁ pt₂ x
  | .«oracle» _ cont, s₂, F, ⟨_, pt₁⟩, pt₂, x =>
      packAppend (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        (fun pt₁ pt₂ => F ⟨⟨⟩, pt₁⟩ pt₂) pt₁ pt₂ x

/-- `toInteractionSpec` commutes with `append`: the interaction spec of a
composed oracle spec is the interaction spec append (with appropriate indexing
through `projectPublic`). -/
theorem toInteractionSpec_append :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (s₁.append s₂).toInteractionSpec =
      s₁.toInteractionSpec.append (fun tr => (s₂ (s₁.projectPublic tr)).toInteractionSpec)
  | .done, _ => rfl
  | .«public» X rest, s₂ => by
      change
        (Interaction.Spec.node X fun x =>
          toInteractionSpec (append (rest x) (fun pt => s₂ ⟨x, pt⟩))) =
        Interaction.Spec.node X (fun x =>
          (toInteractionSpec (rest x)).append
            (fun tr => toInteractionSpec (s₂ ⟨x, projectPublic (rest x) tr⟩)))
      congr 1
      funext x
      exact toInteractionSpec_append (rest x) (fun pt => s₂ ⟨x, pt⟩)
  | .«oracle» X cont, s₂ => by
      change
        (Interaction.Spec.node X fun _ =>
          toInteractionSpec (append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩))) =
        Interaction.Spec.node X (fun _ =>
          (toInteractionSpec (cont ⟨⟩)).append
            (fun tr => toInteractionSpec (s₂ ⟨⟨⟩, projectPublic (cont ⟨⟩) tr⟩)))
      congr 1
      funext _
      exact toInteractionSpec_append (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)

/-- Embed a pair of `Interaction.Spec.Transcript`s (one for each phase) into a
single transcript of the composed oracle spec. Defined by structural recursion
on `Oracle.Spec`, so `toInteractionSpec` reduces at each step. -/
def transcriptAppend :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) →
    Interaction.Spec.Transcript
      ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec) →
    Interaction.Spec.Transcript (s₁.append s₂).toInteractionSpec
  | .done, _, _, tr₂ => tr₂
  | .«public» _ rest, s₂, ⟨x, tr₁⟩, tr₂ =>
      ⟨x, transcriptAppend (rest x) (fun pt => s₂ ⟨x, pt⟩) tr₁ tr₂⟩
  | .«oracle» _ cont, s₂, ⟨x, tr₁⟩, tr₂ =>
      ⟨x, transcriptAppend (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) tr₁ tr₂⟩

/-- Pack a value indexed by the two phase public transcripts into the public
transcript of `transcriptAppend`.

Unlike `PublicTranscript.packAppend`, this targets the public transcript
computed from the concrete combined transcript, so callers do not need to
rewrite by `projectPublic_transcriptAppend`. -/
def PublicTranscript.packTranscriptAppend :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) →
    (tr₂ : Interaction.Spec.Transcript
      ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec)) →
    F (s₁.projectPublic tr₁) ((s₂ (s₁.projectPublic tr₁)).projectPublic tr₂) →
    liftAppend s₁ s₂ F ((s₁.append s₂).projectPublic (transcriptAppend s₁ s₂ tr₁ tr₂))
  | .done, _, _, _, _, x => x
  | .«public» _ rest, s₂, F, ⟨xm, tr₁⟩, tr₂, x =>
      packTranscriptAppend (rest xm) (fun pt => s₂ ⟨xm, pt⟩)
        (fun pt₁ pt₂ => F ⟨xm, pt₁⟩ pt₂) tr₁ tr₂ x
  | .«oracle» _ cont, s₂, F, ⟨_, tr₁⟩, tr₂, x =>
      packTranscriptAppend (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        (fun pt₁ pt₂ => F ⟨⟨⟩, pt₁⟩ pt₂) tr₁ tr₂ x

/-- `projectPublic` commutes with `transcriptAppend`. -/
theorem projectPublic_transcriptAppend :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) →
    (tr₂ : Interaction.Spec.Transcript
      ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec)) →
    (s₁.append s₂).projectPublic (transcriptAppend s₁ s₂ tr₁ tr₂) =
      PublicTranscript.append s₁ s₂ (s₁.projectPublic tr₁)
        ((s₂ (s₁.projectPublic tr₁)).projectPublic tr₂)
  | .done, _, _, _ => rfl
  | .«public» X rest, s₂, ⟨x, tr₁⟩, tr₂ => by
      change
        (⟨x,
          projectPublic (append (rest x) (fun pt => s₂ ⟨x, pt⟩))
            (transcriptAppend (rest x) (fun pt => s₂ ⟨x, pt⟩) tr₁ tr₂)⟩ :
          (x : X) × PublicTranscript (append (rest x) (fun pt => s₂ ⟨x, pt⟩))) =
        (⟨x,
          PublicTranscript.append (rest x) (fun pt => s₂ ⟨x, pt⟩)
            (projectPublic (rest x) tr₁)
            (projectPublic (s₂ ⟨x, projectPublic (rest x) tr₁⟩) tr₂)⟩ :
          (x : X) × PublicTranscript (append (rest x) (fun pt => s₂ ⟨x, pt⟩)))
      congr 1
      exact projectPublic_transcriptAppend (rest x) (fun pt => s₂ ⟨x, pt⟩) tr₁ tr₂
  | .«oracle» _ cont, s₂, ⟨x, tr₁⟩, tr₂ => by
      simp only [append_oracle, transcriptAppend, projectPublic_oracle, PublicTranscript.append]
      congr 1
      exact projectPublic_transcriptAppend (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩) tr₁ tr₂

/-! ## Query infrastructure for appended specs -/

/-- Embed a query handle from the first phase into the appended spec. -/
def QueryHandle.appendLeft :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    QueryHandle s₁ od₁ pt₁ →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
      (PublicTranscript.append s₁ s₂ pt₁ pt₂)
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      QueryHandle.appendLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .«oracle» _ _, _, ⟨_, _⟩, _, ⟨_, _⟩, _, .inl q => .inl q
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, pt₁⟩, pt₂, .inr h =>
      .inr (QueryHandle.appendLeft (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) pt₁ pt₂ h)

/-- Embed a query handle from the second phase into the appended spec. -/
def QueryHandle.appendRight :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    QueryHandle (s₂ pt₁) (od₂ pt₁) pt₂ →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
      (PublicTranscript.append s₁ s₂ pt₁ pt₂)
  | .done, _, _, _, _, _, q => q
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      QueryHandle.appendRight (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, pt₁⟩, pt₂, q =>
      .inr (QueryHandle.appendRight (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) pt₁ pt₂ q)

/-- Decompose a query handle of the appended spec into a left (first phase) or
right (second phase) query handle. Inverse of `appendLeft`/`appendRight`. -/
def QueryHandle.splitAppend :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt →
    QueryHandle s₁ od₁ (PublicTranscript.split s₁ s₂ pt).1 ⊕
      QueryHandle (s₂ (PublicTranscript.split s₁ s₂ pt).1)
        (od₂ (PublicTranscript.split s₁ s₂ pt).1)
        (PublicTranscript.split s₁ s₂ pt).2
  | .done, _, _, _, _, q => .inr q
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, q =>
      splitAppend (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest q
  | .«oracle» _ _, _, ⟨_, _⟩, _, ⟨_, _⟩, .inl q => .inl (.inl q)
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, ptRest⟩, .inr q =>
      match splitAppend (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
          odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) ptRest q with
      | .inl q₁ => .inl (.inr q₁)
      | .inr q₂ => .inr q₂

/-- Route a first-phase query handle into the combined spec indexed by `pt`,
where `pt : PublicTranscript (s₁.append s₂)`. Unlike `appendLeft` (which
takes `pt₁` and `pt₂` separately and produces a handle at `append pt₁ pt₂`),
this takes the combined `pt` directly and indexes the input handle by
`(split pt).1`. The key property is that `toOracleSpec` at the routed handle
**definitionally** agrees with the first phase's `toOracleSpec`. -/
def QueryHandle.routeLeft :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    QueryHandle s₁ od₁ (PublicTranscript.split s₁ s₂ pt).1 →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt
  | .done, _, _, _, _, q => q.elim
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, q =>
      routeLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest q
  | .«oracle» _ _, _, ⟨_, _⟩, _, ⟨_, _⟩, .inl q => .inl q
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, ptRest⟩, .inr h =>
      .inr (routeLeft (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) ptRest h)

/-- Route a second-phase query handle into the combined spec indexed by `pt`.
Unlike `appendRight`, takes the combined `pt` directly and indexes the input
handle by `(split pt).1` and `(split pt).2`. The key property is that
`toOracleSpec` at the routed handle **definitionally** agrees with the second
phase's `toOracleSpec`. -/
def QueryHandle.routeRight :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    QueryHandle (s₂ (PublicTranscript.split s₁ s₂ pt).1)
      (od₂ (PublicTranscript.split s₁ s₂ pt).1)
      (PublicTranscript.split s₁ s₂ pt).2 →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt
  | .done, _, _, _, _, q => q
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, q =>
      routeRight (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest q
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, ptRest⟩, q =>
      .inr (routeRight (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) ptRest q)

/-- The oracle spec at a routed left query handle in the appended spec matches
the first phase's oracle spec.

This is the transcript-indexed analogue of `toOracleSpec_appendLeft`, for
callers that have an already-combined public transcript and route through
`QueryHandle.routeLeft`. -/
theorem toOracleSpec_routeLeft :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    (q : QueryHandle s₁ od₁ (PublicTranscript.split s₁ s₂ pt).1) →
    toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt
      (QueryHandle.routeLeft s₁ s₂ od₁ od₂ pt q) =
    toOracleSpec s₁ od₁ (PublicTranscript.split s₁ s₂ pt).1 q
  | .done, _, _, _, _, q => q.elim
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, q =>
      toOracleSpec_routeLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest q
  | .«oracle» _ _, _, ⟨_, _⟩, _, ⟨_, _⟩, .inl _ => rfl
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, ptRest⟩, .inr h =>
      toOracleSpec_routeLeft (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) ptRest h

/-- The oracle spec at a routed right query handle in the appended spec matches
the second phase's oracle spec.

This is the transcript-indexed analogue of `toOracleSpec_appendRight`, for
callers that have an already-combined public transcript and route through
`QueryHandle.routeRight`. -/
theorem toOracleSpec_routeRight :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    (q :
      QueryHandle (s₂ (PublicTranscript.split s₁ s₂ pt).1)
        (od₂ (PublicTranscript.split s₁ s₂ pt).1)
        (PublicTranscript.split s₁ s₂ pt).2) →
    toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt
      (QueryHandle.routeRight s₁ s₂ od₁ od₂ pt q) =
    toOracleSpec
      (s₂ (PublicTranscript.split s₁ s₂ pt).1)
      (od₂ (PublicTranscript.split s₁ s₂ pt).1)
      (PublicTranscript.split s₁ s₂ pt).2 q
  | .done, _, _, _, _, _ => rfl
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, q =>
      toOracleSpec_routeRight (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest q
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, ptRest⟩, q =>
      toOracleSpec_routeRight (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) ptRest q

/-- The oracle spec at a left query handle in the appended spec matches the
first phase's oracle spec. -/
theorem toOracleSpec_appendLeft :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    (q : QueryHandle s₁ od₁ pt₁) →
    toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
      (PublicTranscript.append s₁ s₂ pt₁ pt₂)
      (QueryHandle.appendLeft s₁ s₂ od₁ od₂ pt₁ pt₂ q) =
    toOracleSpec s₁ od₁ pt₁ q
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      toOracleSpec_appendLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .«oracle» _ _, _, ⟨_, _⟩, _, ⟨_, _⟩, _, .inl _ => rfl
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, pt₁⟩, pt₂, .inr h =>
      toOracleSpec_appendLeft (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) pt₁ pt₂ h

/-- The oracle spec at a right query handle in the appended spec matches the
second phase's oracle spec. -/
theorem toOracleSpec_appendRight :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    (q : QueryHandle (s₂ pt₁) (od₂ pt₁) pt₂) →
    toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
      (PublicTranscript.append s₁ s₂ pt₁ pt₂)
      (QueryHandle.appendRight s₁ s₂ od₁ od₂ pt₁ pt₂ q) =
    toOracleSpec (s₂ pt₁) (od₂ pt₁) pt₂ q
  | .done, _, _, _, _, _, _ => rfl
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      toOracleSpec_appendRight (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, pt₁⟩, pt₂, q =>
      toOracleSpec_appendRight (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) pt₁ pt₂ q

/-- Restrict an oracle query implementation for the combined `toOracleSpec` of
`s₁.append s₂` at combined transcript `pt` to answer only first-phase queries.

Defined by structural recursion on `s₁`. At each step, `toOracleSpec`,
`OracleDeco.append`, and `PublicTranscript.split` all reduce definitionally,
so no casts are needed. At `.oracle` nodes, first-phase handles are in `.inl`
position; the embedding is restricted via `.inr` to skip the current oracle
node. -/
def restrictLeft {r : Type → Type} [Monad r] :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    QueryImpl (toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt) r →
    QueryImpl (toOracleSpec s₁ od₁ (PublicTranscript.split s₁ s₂ pt).1) r
  | .done, _, _, _, _, _ => fun q => q.elim
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, embed =>
      restrictLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest embed
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, ptRest⟩, embed => fun
    | .inl q => embed (.inl q)
    | .inr h =>
        restrictLeft (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
          odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) ptRest
          (fun h' => embed (.inr h')) h

/-- Restrict an oracle query implementation for the combined `toOracleSpec` of
`s₁.append s₂` at combined transcript `pt` to answer only second-phase queries.

Defined by structural recursion on `s₁`. At `.done`, the combined spec
reduces to the second-phase spec, so the embedding applies directly. At
`.oracle` nodes, the embedding is restricted via `.inr`. At `.public` nodes,
the transcript component `x` routes into the correct subtree. -/
def restrictRight {r : Type → Type} [Monad r] :
    (s₁ : Spec) → (s₂ : PublicTranscript s₁ → Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    QueryImpl (toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt) r →
    QueryImpl (toOracleSpec (s₂ (PublicTranscript.split s₁ s₂ pt).1)
      (od₂ (PublicTranscript.split s₁ s₂ pt).1)
      (PublicTranscript.split s₁ s₂ pt).2) r
  | .done, _, _, _, _, embed => embed
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, embed =>
      restrictRight (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest embed
  | .«oracle» _ cont, s₂, ⟨_, odRest⟩, od₂, ⟨_, ptRest⟩, embed =>
      restrictRight (cont ⟨⟩) (fun pt => s₂ ⟨⟨⟩, pt⟩)
        odRest (fun pt => od₂ ⟨⟨⟩, pt⟩) ptRest (fun h => embed (.inr h))

end Spec

end Interaction.Oracle


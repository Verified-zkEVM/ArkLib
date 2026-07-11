/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.Basic.Append
import PolyFun.Interaction.TwoParty.Strategy
import ArkLib.OracleReduction.OracleInterface

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

## Main definitions

### Core types
- `Oracle.Spec` — the inductive type with `.done`, `.public`, `.oracle`.
- `Spec.RoleDeco` — role assignment on `.public` nodes only.
- `Spec.OracleDeco` — oracle interface assignment on `.oracle` nodes only.

### Forgetful map
- `Spec.toInteractionSpec` — convert to `Interaction.Spec` (W-type).
- `Spec.toSpecRoles` — lift role decoration.

### Transcripts
- `Spec.PublicTranscript` — transcript of `.public` nodes (verifier's view).
- `Spec.projectPublic` — project full transcript to `PublicTranscript`.

### Oracle query infrastructure
- `Spec.QueryHandle` — query index type, indexed by `PublicTranscript`.
- `Spec.toOracleSpec` — oracle spec, indexed by `PublicTranscript`.
- `Spec.answerQuery` — answer queries using full transcript data.

### Verifier monad decoration
- `Spec.toMonadDecoration` — per-node monad assignment for the verifier.
-/

universe u

open OracleComp OracleSpec

namespace Interaction.Oracle

open Interaction.TwoParty

/-- The canonical protocol specification for oracle reductions.

- `.public X rest`: a public message node. The continuation depends on the
  message `x : X`. Used for plain sender messages and receiver challenges.
- `.oracle X rest`: an oracle message node. The continuation is structurally
  constant (does not depend on the message). Used for prover oracle messages
  that the verifier accesses only through queries.
- `.done`: end of protocol. -/
inductive Spec : Type 1 where
  | done : Spec
  | «public» (X : Type) (rest : X → Spec) : Spec
  | oracle (X : Type) (rest : Spec) : Spec

namespace Spec

/-! ## Role and oracle decorations -/

/-- Role assignment for an `Oracle.Spec`. Only `.public` nodes carry a role
(`sender` or `receiver`). `.oracle` nodes are always sender, so no annotation
is stored. -/
def RoleDeco : Oracle.Spec → Type
  | .done => PUnit
  | .«public» _ rest => Role × ((x : _) → RoleDeco (rest x))
  | .oracle _ rest => RoleDeco rest

/-- Oracle interface assignment. `.oracle` nodes carry an `OracleInterface`
(defining the query-response structure). `.public` nodes just recurse. -/
def OracleDeco : Oracle.Spec → Type 1
  | .done => PUnit
  | .«public» _ rest => (x : _) → OracleDeco (rest x)
  | .oracle X rest => OracleInterface X × OracleDeco rest

/-! ## Forgetful map to Interaction.Spec -/

/-- Convert an `Oracle.Spec` to a plain `Interaction.Spec`. `.oracle` nodes
become nodes with *definitionally constant* continuation. -/
def toInteractionSpec : Oracle.Spec → Interaction.Spec
  | .done => .done
  | .«public» X rest => .node X (fun x => (rest x).toInteractionSpec)
  | .oracle X rest => .node X (fun _ => rest.toInteractionSpec)

/-- Lift role decoration to `RoleDecoration` on `toInteractionSpec`. `.oracle`
nodes are always `.sender`. -/
def toSpecRoles : (s : Oracle.Spec) → RoleDeco s → RoleDecoration s.toInteractionSpec
  | .done, _ => ⟨⟩
  | .«public» _ rest, ⟨role, rRest⟩ =>
      ⟨role, fun x => toSpecRoles (rest x) (rRest x)⟩
  | .oracle _ rest, roles =>
      ⟨.sender, fun _ => toSpecRoles rest roles⟩

/-! ## Public transcript -/

/-- The *public transcript* contains only `.public` node messages (challenges
and plain sender messages). All `.oracle` messages are dropped. This is the
verifier's direct view of the interaction, without oracle queries. -/
def PublicTranscript : Oracle.Spec → Type
  | .done => PUnit
  | .«public» X rest => (x : X) × PublicTranscript (rest x)
  | .oracle _ rest => PublicTranscript rest

/-- Project a full `Interaction.Spec.Transcript` to the `PublicTranscript`. -/
def projectPublic :
    (s : Oracle.Spec) →
    Interaction.Spec.Transcript s.toInteractionSpec → PublicTranscript s
  | .done, _ => ⟨⟩
  | .«public» _ rest, ⟨x, tr⟩ => ⟨x, projectPublic (rest x) tr⟩
  | .oracle _ rest, ⟨_, tr⟩ => projectPublic rest tr

/-! ## Oracle query infrastructure -/

/-- Index type for oracle queries, parameterized by `PublicTranscript`.
At `.oracle` nodes, the verifier can query the current node's oracle interface
(`.inl q`) or recurse into subsequent oracles (`.inr h`). At `.public` nodes,
the transcript determines which subtree to recurse into. -/
def QueryHandle :
    (s : Oracle.Spec) → OracleDeco s → PublicTranscript s → Type
  | .done, _, _ => Empty
  | .«public» _ rest, odRest, ⟨x, pt⟩ =>
      QueryHandle (rest x) (odRest x) pt
  | .oracle _X rest, ⟨oi, odRest⟩, pt =>
      oi.Query ⊕ QueryHandle rest odRest pt

/-- The oracle specification for querying oracle messages along a given
`PublicTranscript` path. Maps each `QueryHandle` to its response type. -/
def toOracleSpec :
    (s : Oracle.Spec) → (od : OracleDeco s) →
    (pt : PublicTranscript s) → OracleSpec (QueryHandle s od pt)
  | .done, _, _ => fun q => q.elim
  | .«public» _ rest, odRest, ⟨x, pt⟩ =>
      toOracleSpec (rest x) (odRest x) pt
  | .oracle _X rest, ⟨oi, odRest⟩, pt => fun
    | .inl q => oi.toOC.spec q
    | .inr handle => toOracleSpec rest odRest pt handle

/-- Answer oracle queries using the message values from a full transcript.
At each `.oracle` node, the transcript provides the actual message `x : X`,
which is used to compute responses via `OracleInterface`. -/
def answerQuery :
    (s : Oracle.Spec) → (od : OracleDeco s) →
    (tr : Interaction.Spec.Transcript s.toInteractionSpec) →
    QueryImpl (toOracleSpec s od (s.projectPublic tr)) Id
  | .done, _, _ => fun q => q.elim
  | .«public» _ rest, odRest, ⟨x, tr⟩ =>
      answerQuery (rest x) (odRest x) tr
  | .oracle _X rest, ⟨oi, odRest⟩, ⟨x, tr⟩ => fun
    | .inl q => (oi.toOC.impl q).run x
    | .inr handle => answerQuery rest odRest tr handle

/-! ## Verifier monad decoration -/

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
    (s : Oracle.Spec) → (roles : RoleDeco s) → (od : OracleDeco s) →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ →
    Interaction.Spec.MonadDecoration s.toInteractionSpec
  | .done, _, _, _, _ => ⟨⟩
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec =>
      ⟨⟨Id, inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odRest x) accSpec⟩
  | .«public» _ rest, ⟨.receiver, rRest⟩, odRest, _, accSpec =>
      ⟨⟨OracleComp (oSpec + [OStmtIn]ₒ + accSpec), inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odRest x) accSpec⟩
  | .oracle _ rest, roles, ⟨oi, odRest⟩, _, accSpec =>
      ⟨⟨Id, inferInstance⟩,
       fun _ => toMonadDecoration oSpec OStmtIn rest roles odRest
         (accSpec + @OracleInterface.spec _ oi)⟩

/-! ## Sequential composition -/

/-- Sequential composition of `Oracle.Spec`: run `s₁` first, then continue with
`s₂ pt₁` where `pt₁ : PublicTranscript s₁` records the public messages from the
first phase. At `.oracle` nodes the suffix is passed through unchanged, since
oracle messages do not appear in `PublicTranscript`. -/
def append : (s₁ : Oracle.Spec) → (PublicTranscript s₁ → Oracle.Spec) → Oracle.Spec
  | .done, s₂ => s₂ ⟨⟩
  | .«public» X rest, s₂ => .«public» X (fun x => (rest x).append (fun pt => s₂ ⟨x, pt⟩))
  | .oracle X rest, s₂ => .oracle X (rest.append s₂)

/-- Role decoration for an appended `Oracle.Spec`. -/
def RoleDeco.append :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    RoleDeco s₁ → ((pt : PublicTranscript s₁) → RoleDeco (s₂ pt)) → RoleDeco (s₁.append s₂)
  | .done, _, _, r₂ => r₂ ⟨⟩
  | .«public» _ rest, s₂, ⟨role, rRest⟩, r₂ =>
      ⟨role, fun x => RoleDeco.append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (rRest x) (fun pt => r₂ ⟨x, pt⟩)⟩
  | .oracle _ rest, s₂, r₁, r₂ => RoleDeco.append rest s₂ r₁ r₂

/-- Oracle decoration for an appended `Oracle.Spec`. -/
def OracleDeco.append :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    OracleDeco s₁ → ((pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    OracleDeco (s₁.append s₂)
  | .done, _, _, od₂ => od₂ ⟨⟩
  | .«public» _ rest, s₂, od₁, od₂ =>
      fun x => OracleDeco.append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩)
  | .oracle _ rest, s₂, ⟨oi, odRest⟩, od₂ =>
      ⟨oi, OracleDeco.append rest s₂ odRest od₂⟩

/-- `PublicTranscript` of an appended spec decomposes into a prefix and suffix. -/
def PublicTranscript.append :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) →
    PublicTranscript (s₁.append s₂)
  | .done, _, _, pt₂ => pt₂
  | .«public» _ rest, s₂, ⟨x, pt₁⟩, pt₂ =>
      ⟨x, PublicTranscript.append (rest x) (fun pt => s₂ ⟨x, pt⟩) pt₁ pt₂⟩
  | .oracle _ rest, s₂, pt₁, pt₂ =>
      PublicTranscript.append rest s₂ pt₁ pt₂

/-- Split a `PublicTranscript` of an appended spec into prefix and suffix. -/
def PublicTranscript.split :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    PublicTranscript (s₁.append s₂) →
    (pt₁ : PublicTranscript s₁) × PublicTranscript (s₂ pt₁)
  | .done, _, pt => ⟨⟨⟩, pt⟩
  | .«public» _ rest, s₂, ⟨x, ptRest⟩ =>
      let ⟨pt₁, pt₂⟩ := PublicTranscript.split (rest x) (fun pt => s₂ ⟨x, pt⟩) ptRest
      ⟨⟨x, pt₁⟩, pt₂⟩
  | .oracle _ rest, s₂, pt =>
      PublicTranscript.split rest s₂ pt

/-- Splitting after appending recovers the original components. -/
@[simp]
theorem PublicTranscript.split_append :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    PublicTranscript.split s₁ s₂ (PublicTranscript.append s₁ s₂ pt₁ pt₂) = ⟨pt₁, pt₂⟩
  | .done, _, _, _ => rfl
  | .«public» _ rest, s₂, ⟨x, pt₁⟩, pt₂ => by
      simp only [PublicTranscript.append, PublicTranscript.split]
      rw [split_append]
  | .oracle _ rest, s₂, pt₁, pt₂ =>
      split_append rest s₂ pt₁ pt₂

/-- Appending the components produced by `split` recovers the original. -/
@[simp]
theorem PublicTranscript.append_split :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (pt : PublicTranscript (s₁.append s₂)) →
    let ⟨pt₁, pt₂⟩ := PublicTranscript.split s₁ s₂ pt
    PublicTranscript.append s₁ s₂ pt₁ pt₂ = pt
  | .done, _, _ => rfl
  | .«public» _ rest, s₂, ⟨x, ptRest⟩ => by
      simp only [PublicTranscript.split, PublicTranscript.append]
      rw [append_split]
  | .oracle _ rest, s₂, pt =>
      append_split rest s₂ pt

/-- Lift a two-argument type family indexed by per-phase `PublicTranscript`s to a
single-argument family on the combined `PublicTranscript` of `s₁.append s₂`.

`liftAppend s₁ s₂ F (PublicTranscript.append s₁ s₂ pt₁ pt₂)` reduces
**definitionally** to `F pt₁ pt₂`. -/
def PublicTranscript.liftAppend :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    ((pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    PublicTranscript (s₁.append s₂) → Type u
  | .done, _, F, pt => F ⟨⟩ pt
  | .«public» _ rest, s₂, F, ⟨x, ptRest⟩ =>
      liftAppend (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) ptRest
  | .oracle _ rest, s₂, F, pt =>
      liftAppend rest s₂ F pt

/-- `liftAppend` on an appended transcript reduces to the original family. -/
@[simp]
theorem PublicTranscript.liftAppend_append :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    PublicTranscript.liftAppend s₁ s₂ F
      (PublicTranscript.append s₁ s₂ pt₁ pt₂) = F pt₁ pt₂
  | .done, _, _, _, _ => rfl
  | .«public» _ rest, s₂, F, ⟨x, pt₁⟩, pt₂ => by
      simp only [PublicTranscript.append, PublicTranscript.liftAppend]
      exact liftAppend_append (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) pt₁ pt₂
  | .oracle _ rest, s₂, F, pt₁, pt₂ =>
      liftAppend_append rest s₂ F pt₁ pt₂

/-- `liftAppend` equals the original family applied to the split components. -/
theorem PublicTranscript.liftAppend_split :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt : PublicTranscript (s₁.append s₂)) →
    let ⟨pt₁, pt₂⟩ := PublicTranscript.split s₁ s₂ pt
    PublicTranscript.liftAppend s₁ s₂ F pt = F pt₁ pt₂
  | .done, _, _, _ => rfl
  | .«public» _ rest, s₂, F, ⟨x, ptRest⟩ => by
      simp only [PublicTranscript.split, PublicTranscript.liftAppend]
      exact liftAppend_split (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) ptRest
  | .oracle _ rest, s₂, F, pt =>
      liftAppend_split rest s₂ F pt

/-- Transport a `liftAppend` value to the pair-indexed family via `split`. -/
def PublicTranscript.unliftAppend :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt : PublicTranscript (s₁.append s₂)) →
    PublicTranscript.liftAppend s₁ s₂ F pt →
    let ⟨pt₁, pt₂⟩ := PublicTranscript.split s₁ s₂ pt
    F pt₁ pt₂
  | .done, _, _, _, x => x
  | .«public» _ rest, s₂, F, ⟨x, ptRest⟩, val =>
      unliftAppend (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (fun pt₁ pt₂ => F ⟨x, pt₁⟩ pt₂) ptRest val
  | .oracle _ rest, s₂, F, pt, val =>
      unliftAppend rest s₂ F pt val

/-- Transport a pair-indexed value into `liftAppend` via `append`. -/
def PublicTranscript.packAppend :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (F : (pt₁ : PublicTranscript s₁) → PublicTranscript (s₂ pt₁) → Type u) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    F pt₁ pt₂ → liftAppend s₁ s₂ F (append s₁ s₂ pt₁ pt₂)
  | .done, _, _, ⟨⟩, _, x => x
  | .«public» _ rest, s₂, F, ⟨xm, pt₁⟩, pt₂, x =>
      packAppend (rest xm) (fun pt => s₂ ⟨xm, pt⟩)
        (fun pt₁ pt₂ => F ⟨xm, pt₁⟩ pt₂) pt₁ pt₂ x
  | .oracle _ rest, s₂, F, pt₁, pt₂, x =>
      packAppend rest s₂ F pt₁ pt₂ x

/-- `toInteractionSpec` commutes with `append`: the interaction spec of a
composed oracle spec is the interaction spec append (with appropriate indexing
through `projectPublic`). -/
theorem toInteractionSpec_append :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (s₁.append s₂).toInteractionSpec =
      s₁.toInteractionSpec.append (fun tr => (s₂ (s₁.projectPublic tr)).toInteractionSpec)
  | .done, _ => rfl
  | .«public» _ rest, s₂ => by
      simp only [Spec.append, toInteractionSpec]
      congr 1; ext x
      exact toInteractionSpec_append (rest x) (fun pt => s₂ ⟨x, pt⟩)
  | .oracle _ rest, s₂ => by
      simp only [Spec.append, toInteractionSpec]
      congr 1; ext _
      exact toInteractionSpec_append rest s₂

/-- Embed a pair of `Interaction.Spec.Transcript`s (one for each phase) into a
single transcript of the composed oracle spec. Defined by structural recursion
on `Oracle.Spec`, so `toInteractionSpec` reduces at each step. -/
def transcriptAppend :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) →
    Interaction.Spec.Transcript
      ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec) →
    Interaction.Spec.Transcript (s₁.append s₂).toInteractionSpec
  | .done, _, _, tr₂ => tr₂
  | .«public» _ rest, s₂, ⟨x, tr₁⟩, tr₂ =>
      ⟨x, transcriptAppend (rest x) (fun pt => s₂ ⟨x, pt⟩) tr₁ tr₂⟩
  | .oracle _ rest, s₂, ⟨x, tr₁⟩, tr₂ =>
      ⟨x, transcriptAppend rest s₂ tr₁ tr₂⟩

/-- `projectPublic` commutes with `transcriptAppend`. -/
theorem projectPublic_transcriptAppend :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (tr₁ : Interaction.Spec.Transcript s₁.toInteractionSpec) →
    (tr₂ : Interaction.Spec.Transcript
      ((s₂ (s₁.projectPublic tr₁)).toInteractionSpec)) →
    (s₁.append s₂).projectPublic (transcriptAppend s₁ s₂ tr₁ tr₂) =
      PublicTranscript.append s₁ s₂ (s₁.projectPublic tr₁)
        ((s₂ (s₁.projectPublic tr₁)).projectPublic tr₂)
  | .done, _, _, _ => rfl
  | .«public» _ rest, s₂, ⟨x, tr₁⟩, tr₂ => by
      simp only [Spec.append, projectPublic,
        transcriptAppend, PublicTranscript.append]
      congr 1
      exact projectPublic_transcriptAppend (rest x) (fun pt => s₂ ⟨x, pt⟩) tr₁ tr₂
  | .oracle _ rest, s₂, ⟨x, tr₁⟩, tr₂ => by
      simp only [Spec.append, projectPublic, transcriptAppend]
      exact projectPublic_transcriptAppend rest s₂ tr₁ tr₂

/-! ## Query infrastructure for appended specs -/

/-- Embed a query handle from the first phase into the appended spec. -/
def QueryHandle.appendLeft :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    QueryHandle s₁ od₁ pt₁ →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
      (PublicTranscript.append s₁ s₂ pt₁ pt₂)
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      QueryHandle.appendLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .oracle _ _, _, ⟨_, _⟩, _, _, _, .inl q => .inl q
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt₁, pt₂, .inr h =>
      .inr (QueryHandle.appendLeft rest s₂ odRest od₂ pt₁ pt₂ h)

/-- Embed a query handle from the second phase into the appended spec. -/
def QueryHandle.appendRight :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt : PublicTranscript s₁) → OracleDeco (s₂ pt)) →
    (pt₁ : PublicTranscript s₁) → (pt₂ : PublicTranscript (s₂ pt₁)) →
    QueryHandle (s₂ pt₁) (od₂ pt₁) pt₂ →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂)
      (PublicTranscript.append s₁ s₂ pt₁ pt₂)
  | .done, _, _, _, _, _, q => q
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, pt₁⟩, pt₂, q =>
      QueryHandle.appendRight (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) pt₁ pt₂ q
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt₁, pt₂, q =>
      .inr (QueryHandle.appendRight rest s₂ odRest od₂ pt₁ pt₂ q)

/-- Decompose a query handle of the appended spec into a left (first phase) or
right (second phase) query handle. Inverse of `appendLeft`/`appendRight`. -/
def QueryHandle.splitAppend :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
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
  | .oracle _ _, _, ⟨_, _⟩, _, _, .inl q => .inl (.inl q)
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt, .inr q =>
      match splitAppend rest s₂ odRest od₂ pt q with
      | .inl q₁ => .inl (.inr q₁)
      | .inr q₂ => .inr q₂

/-- Route a first-phase query handle into the combined spec indexed by `pt`,
where `pt : PublicTranscript (s₁.append s₂)`. Unlike `appendLeft` (which
takes `pt₁` and `pt₂` separately and produces a handle at `append pt₁ pt₂`),
this takes the combined `pt` directly and indexes the input handle by
`(split pt).1`. The key property is that `toOracleSpec` at the routed handle
**definitionally** agrees with the first phase's `toOracleSpec`. -/
def QueryHandle.routeLeft :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    QueryHandle s₁ od₁ (PublicTranscript.split s₁ s₂ pt).1 →
    QueryHandle (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt
  | .done, _, _, _, _, q => q.elim
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, q =>
      routeLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest q
  | .oracle _ _, _, ⟨_, _⟩, _, _, .inl q => .inl q
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt, .inr h =>
      .inr (routeLeft rest s₂ odRest od₂ pt h)

/-- Route a second-phase query handle into the combined spec indexed by `pt`.
Unlike `appendRight`, takes the combined `pt` directly and indexes the input
handle by `(split pt).1` and `(split pt).2`. The key property is that
`toOracleSpec` at the routed handle **definitionally** agrees with the second
phase's `toOracleSpec`. -/
def QueryHandle.routeRight :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
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
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt, q =>
      .inr (routeRight rest s₂ odRest od₂ pt q)

/-- The oracle spec at a left query handle in the appended spec matches the
first phase's oracle spec. -/
theorem toOracleSpec_appendLeft :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
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
  | .oracle _ _, _, ⟨_, _⟩, _, _, _, .inl _ => rfl
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt₁, pt₂, .inr h =>
      toOracleSpec_appendLeft rest s₂ odRest od₂ pt₁ pt₂ h

/-- The oracle spec at a right query handle in the appended spec matches the
second phase's oracle spec. -/
theorem toOracleSpec_appendRight :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
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
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt₁, pt₂, q =>
      toOracleSpec_appendRight rest s₂ odRest od₂ pt₁ pt₂ q

/-- Restrict an oracle query implementation for the combined `toOracleSpec` of
`s₁.append s₂` at combined transcript `pt` to answer only first-phase queries.

Defined by structural recursion on `s₁`. At each step, `toOracleSpec`,
`OracleDeco.append`, and `PublicTranscript.split` all reduce definitionally,
so no casts are needed. At `.oracle` nodes, first-phase handles are in `.inl`
position; the embedding is restricted via `.inr` to skip the current oracle
node. -/
def restrictLeft {r : Type → Type} [Monad r] :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
    (od₁ : OracleDeco s₁) → (od₂ : (pt₁ : PublicTranscript s₁) → OracleDeco (s₂ pt₁)) →
    (pt : PublicTranscript (s₁.append s₂)) →
    QueryImpl (toOracleSpec (s₁.append s₂) (OracleDeco.append s₁ s₂ od₁ od₂) pt) r →
    QueryImpl (toOracleSpec s₁ od₁ (PublicTranscript.split s₁ s₂ pt).1) r
  | .done, _, _, _, _, _ => fun q => q.elim
  | .«public» _ rest, s₂, od₁, od₂, ⟨x, ptRest⟩, embed =>
      restrictLeft (rest x) (fun pt => s₂ ⟨x, pt⟩)
        (od₁ x) (fun pt => od₂ ⟨x, pt⟩) ptRest embed
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt, embed => fun
    | .inl q => embed (.inl q)
    | .inr h =>
        restrictLeft rest s₂ odRest od₂ pt (fun h' => embed (.inr h')) h

/-- Restrict an oracle query implementation for the combined `toOracleSpec` of
`s₁.append s₂` at combined transcript `pt` to answer only second-phase queries.

Defined by structural recursion on `s₁`. At `.done`, the combined spec
reduces to the second-phase spec, so the embedding applies directly. At
`.oracle` nodes, the embedding is restricted via `.inr`. At `.public` nodes,
the transcript component `x` routes into the correct subtree. -/
def restrictRight {r : Type → Type} [Monad r] :
    (s₁ : Oracle.Spec) → (s₂ : PublicTranscript s₁ → Oracle.Spec) →
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
  | .oracle _ rest, s₂, ⟨_, odRest⟩, od₂, pt, embed =>
      restrictRight rest s₂ odRest od₂ pt (fun h => embed (.inr h))

end Spec

end Interaction.Oracle

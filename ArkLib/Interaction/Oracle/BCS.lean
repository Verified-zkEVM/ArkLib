/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Spec

open Interaction.TwoParty

/-!
# BCS Transform on Oracle.Spec

The Ben-Sasson–Chiesa–Spooner (BCS) transform converts an interactive oracle
protocol into a non-interactive argument by committing to oracle messages
and opening them on demand.

This module defines the BCS transform directly on `Oracle.Spec`, taking
advantage of the structural distinction between `.public` and `.oracle` nodes.
At each `.oracle` node, a `CommitDeco` selects whether to commit (`some nc`)
or leave the message in the clear (`none`). The BCS-transformed spec is
another `Oracle.Spec` where:

- Committed `.oracle X rest` → `.public nc.CommType (fun _ => ...)`: the
  commitment is a public sender message (visible to verifier, not queryable).
- Non-committed `.oracle X rest` → `.oracle X (...)`: stays as oracle.
- `.public X rest` → `.public X (fun x => ...)`: unchanged.

This gives a clean separation: the BCS `Oracle.Spec` directly encodes which
nodes are queryable (non-committed oracle messages) vs public (commitments
and original public messages).

## Main definitions

### Commitment infrastructure
- `NodeCommitment` — commitment configuration for a single message type.
- `Spec.CommitDeco` — per-`.oracle`-node commitment selection.

### Shared transcript
- `Spec.SharedTranscript` — data shared between original and BCS protocols.
  Committed oracle messages are dropped; non-committed oracle messages are
  retained.

### BCS-transformed spec
- `Spec.bcsSpec` — the BCS-transformed `Oracle.Spec`.
- `Spec.bcsRoleDeco` — role decoration for the BCS spec.
- `Spec.bcsOracleDeco` — oracle decoration for the BCS spec.

### Projection maps
- `Spec.projectShared` — project original transcript to shared.
- `Spec.bcsProjectShared` — project BCS transcript to shared.

### Prover wrapping
- `Spec.OracleWitness` — oracle messages and commitment witnesses at committed
  nodes, needed for Phase 2 opening.
- `Spec.wrapWithCommitments` — transform an original prover strategy into a
  BCS strategy.
- `Spec.wrapWithCommitmentsExt` — extended version that also extracts the
  `OracleWitness`.
-/

universe u

open Interaction OracleComp OracleSpec

namespace Interaction.Oracle

/-- Configuration for committing to a single oracle message of type `X`.
The `commit` function produces both a commitment and a witness inside the
monad `m` (typically `OracleComp oSpec`). The `WitnessType` captures whatever
private state the prover retains for the opening phase. -/
structure NodeCommitment (m : Type → Type) (X : Type) where
  CommType : Type
  WitnessType : Type
  commit : X → m (CommType × WitnessType)

namespace Spec

/-! ## Commitment decoration -/

/-- Displayed-family shape for BCS commitment selections on `Oracle.Spec`. -/
def commitDecoShape (m : Type → Type) :
    PFunctor.FreeM.Displayed.Shape.{1, 0, 0, 2} Oracle.Spec.basePFunctor PUnit.{1} where
  leaf := fun _ => PUnit.{2}
  node := fun
    | .public X => fun child => (x : X) → child x
    | .oracle X => fun child => Option (NodeCommitment m X) × child ⟨⟩

/-- Commitment selection on an `Oracle.Spec`. At each `.oracle` node, either
`some nc` (commit the oracle message using `nc`) or `none` (leave it in the
clear). `.public` nodes just recurse, indexed by the message value. -/
abbrev CommitDeco (m : Type → Type) (s : Oracle.Spec) : Type 1 :=
  PFunctor.FreeM.Displayed (commitDecoShape m) s

/-! ## Shared transcript -/

/-- Displayed-over shape for data shared between original and BCS protocols. -/
def sharedTranscriptShape (m : Type → Type) :
    PFunctor.FreeM.Displayed.OverShape (commitDecoShape m) where
  leaf := fun _ _ => PUnit.{1}
  node := fun
    | .public X => fun _ childOver cdRest => (x : X) × childOver x (cdRest x)
    | .oracle X => fun _ childOver cd =>
        match cd with
        | ⟨some _, cdRest⟩ => childOver ⟨⟩ cdRest
        | ⟨none, cdRest⟩ => X × childOver ⟨⟩ cdRest

/-- Transcript data shared between the original protocol and the BCS protocol.
Committed oracle messages are dropped; non-committed oracle messages are
retained. `.public` messages are always included. -/
abbrev SharedTranscript {m : Type → Type} (s : Oracle.Spec) (cd : CommitDeco m s) : Type :=
  PFunctor.FreeM.Displayed.Over (sharedTranscriptShape m) s cd

/-- Project an original transcript to the shared transcript. -/
def projectShared {m : Type → Type} :
    (s : Oracle.Spec) → (cd : CommitDeco m s) →
    FullTranscript s → SharedTranscript s cd
  | .done, _, _ => ⟨⟩
  | .«public» _ rest, cdRest, ⟨x, tr⟩ =>
      ⟨x, projectShared (rest x) (cdRest x) tr⟩
  | .«oracle» _ cont, ⟨some _, cdRest⟩, ⟨_, tr⟩ =>
      projectShared (cont ⟨⟩) cdRest tr
  | .«oracle» _ cont, ⟨none, cdRest⟩, ⟨x, tr⟩ =>
      ⟨x, projectShared (cont ⟨⟩) cdRest tr⟩

/-! ## BCS-transformed spec -/

section BCS
variable {m : Type → Type}

/-- BCS-transformed `Oracle.Spec`. Committed `.oracle` nodes become `.public`
sender nodes (the commitment is visible to the verifier, not queryable).
Non-committed `.oracle` nodes stay `.oracle` (the verifier accesses them
through queries). `.public` nodes pass through unchanged. -/
def bcsSpec :
    (s : Oracle.Spec) → CommitDeco m s → Oracle.Spec
  | .done, _ => .done
  | .«public» X rest, cdRest =>
      .«public» X (fun x => bcsSpec (rest x) (cdRest x))
  | .«oracle» _ cont, ⟨some nc, cdRest⟩ =>
      .«public» nc.CommType (fun _ => bcsSpec (cont ⟨⟩) cdRest)
  | .«oracle» X cont, ⟨none, cdRest⟩ =>
      .«oracle» X (fun _ => bcsSpec (cont ⟨⟩) cdRest)

/-- Role decoration for the BCS spec. Committed nodes become `.sender`
(the commitment is a prover message). -/
def bcsRoleDeco :
    (s : Oracle.Spec) → (rd : RoleDeco s) → (cd : CommitDeco m s) →
    RoleDeco (bcsSpec s cd)
  | .done, _, _ => ⟨⟩
  | .«public» _ rest, ⟨role, rRest⟩, cdRest =>
      ⟨role, fun x => bcsRoleDeco (rest x) (rRest x) (cdRest x)⟩
  | .«oracle» _ cont, roles, ⟨some _, cdRest⟩ =>
      ⟨.sender, fun _ => bcsRoleDeco (cont ⟨⟩) roles cdRest⟩
  | .«oracle» _ cont, roles, ⟨none, cdRest⟩ =>
      bcsRoleDeco (cont ⟨⟩) roles cdRest

/-- Oracle decoration for the BCS spec. Committed nodes become `.public` in
the BCS spec, so they carry no oracle decoration. Non-committed `.oracle`
nodes retain their `OracleInterface`. -/
def bcsOracleDeco :
    (s : Oracle.Spec) → (od : OracleDeco s) → (cd : CommitDeco m s) →
    OracleDeco (bcsSpec s cd)
  | .done, _, _ => ⟨⟩
  | .«public» _ rest, odRest, cdRest =>
      fun x => bcsOracleDeco (rest x) (odRest x) (cdRest x)
  | .«oracle» _ cont, ⟨_oi, odRest⟩, ⟨some _, cdRest⟩ =>
      fun _ => bcsOracleDeco (cont ⟨⟩) odRest cdRest
  | .«oracle» _ cont, ⟨oi, odRest⟩, ⟨none, cdRest⟩ =>
      ⟨oi, bcsOracleDeco (cont ⟨⟩) odRest cdRest⟩

/-- Project a full BCS transcript to the shared transcript. Uses the full
runtime transcript (not `PublicTranscript`) because non-committed oracle
messages appear in the full transcript but not in `PublicTranscript`. -/
def bcsProjectShared :
    (s : Oracle.Spec) → (cd : CommitDeco m s) →
    FullTranscript (bcsSpec s cd) →
    SharedTranscript s cd
  | .done, _, _ => ⟨⟩
  | .«public» _ rest, cdRest, ⟨x, tr⟩ =>
      ⟨x, bcsProjectShared (rest x) (cdRest x) tr⟩
  | .«oracle» _ cont, ⟨some _, cdRest⟩, ⟨_, tr⟩ =>
      bcsProjectShared (cont ⟨⟩) cdRest tr
  | .«oracle» _ cont, ⟨none, cdRest⟩, ⟨x, tr⟩ =>
      ⟨x, bcsProjectShared (cont ⟨⟩) cdRest tr⟩

/-! ## Prover wrapping -/

variable [Monad m]

/-- Oracle messages and commitment witnesses retained at committed `.oracle`
nodes. At each committed node, stores both the original oracle message `X`
and the commitment witness `nc.WitnessType` (needed for Phase 2 opening).
Non-committed oracle messages are already visible in `SharedTranscript`
and don't need witnessing. -/
def OracleWitness :
    (s : Oracle.Spec) → (cd : CommitDeco m s) → SharedTranscript s cd → Type
  | .done, _, _ => PUnit
  | .«public» _ rest, cdRest, ⟨x, st⟩ =>
      OracleWitness (rest x) (cdRest x) st
  | .«oracle» X _, ⟨some nc, cdRest⟩, st =>
      X × nc.WitnessType × OracleWitness _ cdRest st
  | .«oracle» _ _, ⟨none, cdRest⟩, ⟨_, st⟩ =>
      OracleWitness _ cdRest st

/-- BCS prover wrapping: transform a prover strategy on the original
`Oracle.Spec` into a strategy on `bcsSpec`. At committed `.oracle` nodes,
the oracle message is replaced by its commitment. At non-committed `.oracle`
nodes, the message passes through. `.public` nodes are unchanged.

The output type must factor through `SharedTranscript`, ensuring type
compatibility between original and BCS strategies. -/
def wrapWithCommitments :
    (s : Oracle.Spec) → (roles : RoleDeco s) → (cd : CommitDeco m s) →
    (OutType : SharedTranscript s cd → Type) →
    FocalStrategy m s roles
      (fun tr => OutType (projectShared s cd tr)) →
    FocalStrategy m (bcsSpec s cd) (bcsRoleDeco s roles cd)
      (fun tr => OutType (bcsProjectShared s cd tr))
  | .done, _, _, _, strategy => strategy
  | .«public» _ rest, ⟨.sender, rRest⟩, cdRest, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitments (rest x) (rRest x) (cdRest x)
        (fun st => OutType ⟨x, st⟩) restStrategy⟩
  | .«public» _ rest, ⟨.receiver, rRest⟩, cdRest, OutType, strategy =>
      fun x => do
        let restStrategy ← strategy x
        return (wrapWithCommitments (rest x) (rRest x) (cdRest x)
          (fun st => OutType ⟨x, st⟩) restStrategy)
  | .«oracle» _ cont, roles, ⟨some nc, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      let ⟨cm, _⟩ ← nc.commit x
      return ⟨cm, wrapWithCommitments (cont ⟨⟩) roles cdRest OutType restStrategy⟩
  | .«oracle» _ cont, roles, ⟨none, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitments (cont ⟨⟩) roles cdRest
        (fun st => OutType ⟨x, st⟩) restStrategy⟩

/-- Extended BCS prover wrapping that also extracts committed oracle messages
as witness for the opening phase.

At committed `.oracle` nodes, the oracle message `x` and commitment witness
are extracted and paired into the output via `TwoParty.Focal.mapOutput`. -/
def wrapWithCommitmentsExt :
    (s : Oracle.Spec) → (roles : RoleDeco s) → (cd : CommitDeco m s) →
    (OutType : SharedTranscript s cd → Type) →
    FocalStrategy m s roles
      (fun tr => OutType (projectShared s cd tr)) →
    FocalStrategy m (bcsSpec s cd) (bcsRoleDeco s roles cd)
      (fun tr => OutType (bcsProjectShared s cd tr) ×
                 OracleWitness s cd (bcsProjectShared s cd tr))
  | .done, _, _, _, strategy => (strategy, ⟨⟩)
  | .«public» _ rest, ⟨.sender, rRest⟩, cdRest, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitmentsExt (rest x) (rRest x) (cdRest x)
        (fun st => OutType ⟨x, st⟩) restStrategy⟩
  | .«public» _ rest, ⟨.receiver, rRest⟩, cdRest, OutType, strategy =>
      fun x => do
        let restStrategy ← strategy x
        return (wrapWithCommitmentsExt (rest x) (rRest x) (cdRest x)
          (fun st => OutType ⟨x, st⟩) restStrategy)
  | .«oracle» _ cont, roles, ⟨some nc, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      let ⟨cm, cwit⟩ ← nc.commit x
      let bcsRest := wrapWithCommitmentsExt (cont ⟨⟩) roles cdRest OutType restStrategy
      return ⟨cm, Interaction.ShapeOver.mapOutput (pairedShapeOver m)
        (ctxs := toRuntimeRoles (bcsSpec (cont ⟨⟩) cdRest)
          (bcsRoleDeco (cont ⟨⟩) roles cdRest))
        (fun _ ⟨out, owit⟩ => (out, x, cwit, owit)) bcsRest⟩
  | .«oracle» _ cont, roles, ⟨none, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitmentsExt (cont ⟨⟩) roles cdRest
        (fun st => OutType ⟨x, st⟩) restStrategy⟩

end BCS

/-! ## Query bundle -/

/-- A finite collection of queries to a single oracle interface. Bundles the
number of queries with a query-selection function. -/
structure QueryBundle {X : Type} (oi : OracleInterface X) where
  numQueries : ℕ
  queries : Fin numQueries → oi.Query

/-! ## Oracle query and response decorations -/

section QueryResponse
variable {m : Type → Type}

/-- Oracle query decoration: one `QueryBundle` per committed `.oracle` node
along a `SharedTranscript`. At `.public` nodes, recurse into the subtree
determined by the message. At non-committed `.oracle` nodes, skip. -/
def OracleQueryDeco :
    (s : Oracle.Spec) → (od : OracleDeco s) → (cd : CommitDeco m s) →
    SharedTranscript s cd → Type
  | .done, _, _, _ => PUnit
  | .«public» _ rest, odRest, cdRest, ⟨x, st⟩ =>
      OracleQueryDeco (rest x) (odRest x) (cdRest x) st
  | .«oracle» _ _, ⟨oi, odRest⟩, ⟨some _, cdRest⟩, st =>
      QueryBundle oi × OracleQueryDeco _ odRest cdRest st
  | .«oracle» _ _, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, st⟩ =>
      OracleQueryDeco _ odRest cdRest st

/-- Oracle response decoration: for each committed `.oracle` node, a function
mapping each query in the `QueryBundle` to its response type. Mirrors
`OracleQueryDeco` structurally. -/
def OracleResponseDeco :
    (s : Oracle.Spec) → (od : OracleDeco s) → (cd : CommitDeco m s) →
    (st : SharedTranscript s cd) → OracleQueryDeco s od cd st → Type
  | .done, _, _, _, _ => PUnit
  | .«public» _ rest, odRest, cdRest, ⟨x, st⟩, qd =>
      OracleResponseDeco (rest x) (odRest x) (cdRest x) st qd
  | .oracle _ _, ⟨oi, odRest⟩, ⟨some _, cdRest⟩, st, ⟨qb, qdRest⟩ =>
      ((i : Fin qb.numQueries) → oi.Response (qb.queries i)) ×
      OracleResponseDeco _ odRest cdRest st qdRest
  | .oracle _ _, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, st⟩, qd =>
      OracleResponseDeco _ odRest cdRest st qd

end QueryResponse

/-! ## Public-query verifier decomposition -/

/-- A BCS-compatible verifier decomposed into three components that together
express the "public query" property:

1. `challenger`: a counterpart strategy on `bcsSpec` using `toMonadDecoration`
   with `bcsOracleDeco`. At receiver nodes, the verifier can query external
   oracles (`oSpec`), input oracle statements (`[OStmtIn]ₒ`), and non-committed
   message oracles, but NOT committed ones (committed nodes are `.public` in the
   BCS spec, so they don't contribute to oracle access).

2. `queryFn`: a deterministic function producing queries to committed oracles
   from the `SharedTranscript`. The "public query" property is implicit in
   the type: queries can only depend on publicly visible data.

3. `decide`: given the shared transcript and query responses, produces the
   verifier's output. Runs inside `OracleComp` with access to external
   oracles, input oracle statements, and non-committed oracle messages. -/
structure PublicQueryVerifier {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    (s : Oracle.Spec) (roles : RoleDeco s)
    (od : OracleDeco s) (cd : CommitDeco (OracleComp oSpec) s)
    (StmtIn : Type) (StmtOut : SharedTranscript s cd → Type) where
  challenger : StmtIn →
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      (bcsSpec s cd).toInteractionSpec
      (RoleDecoration.withMonads
        ((bcsSpec s cd).toSpecRoles (bcsRoleDeco s roles cd))
        ((bcsSpec s cd).toMonadDecoration oSpec OStmtIn
          (bcsRoleDeco s roles cd) (bcsOracleDeco s od cd) []ₒ))
      (fun _ => PUnit)
  queryFn : StmtIn → (st : SharedTranscript s cd) →
    OracleQueryDeco s od cd st
  decide : StmtIn →
    (bcsTr : FullTranscript (bcsSpec s cd)) →
    (qd : OracleQueryDeco s od cd (bcsProjectShared s cd bcsTr)) →
    OracleResponseDeco s od cd (bcsProjectShared s cd bcsTr) qd →
    OracleComp (oSpec + [OStmtIn]ₒ +
      (bcsSpec s cd).toOracleSpec (bcsOracleDeco s od cd)
        ((bcsSpec s cd).projectPublicFull bcsTr))
      (StmtOut (bcsProjectShared s cd bcsTr))

/-! ## Phase 1 helpers -/

section Phase1
variable {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]

/-- Phase 1 of BCS: the prover's strategy on `bcsSpec`, obtained from
`wrapWithCommitmentsExt`. Given an original native oracle prover strategy,
produces a native BCS strategy whose output includes both the original output
and the `OracleWitness`. -/
def bcsPhase1Prover
    (s : Oracle.Spec) (roles : RoleDeco s) (cd : CommitDeco (OracleComp oSpec) s)
    (OutType : SharedTranscript s cd → Type) :
    FocalStrategy (OracleComp oSpec) s roles
      (fun tr => OutType (projectShared s cd tr)) →
    FocalStrategy (OracleComp oSpec) (bcsSpec s cd) (bcsRoleDeco s roles cd)
      (fun tr => OutType (bcsProjectShared s cd tr) ×
                 OracleWitness s cd (bcsProjectShared s cd tr)) :=
  wrapWithCommitmentsExt s roles cd OutType

/-- Phase 1 verifier: extract the `challenger` from a `PublicQueryVerifier`. -/
def bcsPhase1Verifier
    {s : Oracle.Spec} {roles : RoleDeco s} {od : OracleDeco s}
    {cd : CommitDeco (OracleComp oSpec) s}
    {StmtIn : Type} {StmtOut : SharedTranscript s cd → Type}
    (pqv : PublicQueryVerifier oSpec OStmtIn s roles od cd StmtIn StmtOut)
    (stmt : StmtIn) :=
  pqv.challenger stmt

end Phase1

/-! ## Phase 2: answering committed oracle queries -/

section Phase2

/-- Answer committed oracle queries using the actual oracle messages from a
full transcript. At committed `.oracle` nodes, the message `x : X` is used via
`OracleInterface.answer` to compute query responses. At non-committed `.oracle`
and `.public` nodes, recurse structurally.

This is the core computation of BCS Phase 2: the honest prover opens committed
data by providing responses computed from the oracle messages. -/
def answerCommittedQueries :
    (s : Oracle.Spec) → (od : OracleDeco s) → {m : Type → Type} →
    (cd : CommitDeco m s) →
    (tr : FullTranscript s) →
    (qd : OracleQueryDeco s od cd (projectShared s cd tr)) →
    OracleResponseDeco s od cd (projectShared s cd tr) qd
  | .done, _, _, _, _, _ => ⟨⟩
  | .«public» _ rest, odRest, _, cdRest, ⟨x, tr⟩, qd =>
      answerCommittedQueries (rest x) (odRest x) (cdRest x) tr qd
  | .«oracle» _ cont, ⟨oi, odRest⟩, _, ⟨some _, cdRest⟩, ⟨x, tr⟩, ⟨qb, qdRest⟩ =>
      (fun i => (oi.toOC.impl (qb.queries i)).run x,
       answerCommittedQueries (cont ⟨⟩) odRest cdRest tr qdRest)
  | .«oracle» _ cont, ⟨_, odRest⟩, _, ⟨none, cdRest⟩, ⟨_x, tr⟩, qd =>
      answerCommittedQueries (cont ⟨⟩) odRest cdRest tr qd

variable {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]

/-- Phase 2 of BCS: produce the output statement from queries and responses.
Given the pre-computed queries and responses for committed oracle nodes,
evaluates the `PublicQueryVerifier.decide` function. -/
def bcsPhase2
    {s : Oracle.Spec} {roles : RoleDeco s} {od : OracleDeco s}
    {cd : CommitDeco (OracleComp oSpec) s}
    {StmtIn : Type} {StmtOut : SharedTranscript s cd → Type}
    (pqv : PublicQueryVerifier oSpec OStmtIn s roles od cd StmtIn StmtOut)
    (stmt : StmtIn)
    (bcsTr : FullTranscript (bcsSpec s cd))
    (qd : OracleQueryDeco s od cd (bcsProjectShared s cd bcsTr))
    (rd : OracleResponseDeco s od cd (bcsProjectShared s cd bcsTr) qd) :
    OracleComp (oSpec + [OStmtIn]ₒ +
      (bcsSpec s cd).toOracleSpec (bcsOracleDeco s od cd)
        ((bcsSpec s cd).projectPublicFull bcsTr))
      (StmtOut (bcsProjectShared s cd bcsTr)) :=
  pqv.decide stmt bcsTr qd rd

end Phase2

/-! ## Opening decoration -/

section Opening

/-- Opening protocol data for each committed `.oracle` node. At committed
nodes, stores a `Commitment.Interaction.Opening`-like proof that the prover
can demonstrate consistency between the committed value and query responses.

The `OpeningProof` type parameter abstracts over the specific opening proof
mechanism. For Merkle trees, this would be authentication paths; for other
commitment schemes, the appropriate opening argument.

Each committed node stores: the opening interaction spec, its role decoration,
and a `Proof` (prover + verifier pair) for the opening sub-protocol.

At non-committed `.oracle` nodes and `.public` nodes, recurse structurally. -/
def OpeningDeco {m : Type → Type}
    (OpeningProof : {X : Type} → OracleInterface X →
      {_ : NodeCommitment m X} → Type 1) :
    (s : Oracle.Spec) → (od : OracleDeco s) →
    CommitDeco m s → Type 1
  | .done, _, _ => PUnit
  | .«public» _ rest, odRest, cdRest =>
      (x : _) → OpeningDeco OpeningProof (rest x) (odRest x) (cdRest x)
  | .«oracle» _X cont, ⟨oi, odRest⟩, ⟨some nc, cdRest⟩ =>
      @OpeningProof _ oi nc × OpeningDeco OpeningProof (cont ⟨⟩) odRest cdRest
  | .«oracle» _ cont, ⟨_, odRest⟩, ⟨none, cdRest⟩ =>
      OpeningDeco OpeningProof (cont ⟨⟩) odRest cdRest

end Opening

end Spec

end Interaction.Oracle


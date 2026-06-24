/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Hash.DuplexSponge
import ArkLib.Interaction.FiatShamir.Transform

open Interaction.TwoParty

/-!
# Duplex Sponge Fiat-Shamir

The duplex sponge instantiation of the Fiat-Shamir transform for the
interaction-native formalization. The basic FS transform
(`PublicCoinReduction.fiatShamir`) is parametric in the `ReplayOracle`; this
module constructs a specific `ReplayOracle` from a duplex sponge with a
concrete permutation.

The construction threads a `CanonicalDuplexSponge U` through the interaction
tree:
- at sender nodes, the message is serialized and absorbed into the sponge;
- at receiver nodes, the sponge is squeezed and the output deserialized to
  obtain the challenge.

## Main definitions

- `SpongeAnnotation` — per-node serialization metadata matching the shape of a
  role-decorated `Spec`.
- `buildSpongeReplayOracle` — construct a `ReplayOracle` from a sponge state
  and annotation.
- `spongeReplayOracle` — initialize the sponge from the statement and build
  the replay oracle.
- `PublicCoinReduction.duplexSpongeFiatShamir` — the full duplex sponge FS
  transform, composing with the basic FS machinery.

## Design notes

The permutation is resolved concretely via `forwardPermutationOracleImpl`, so
all sponge operations are pure. This is appropriate for the construction; the
idealized oracle-model version (needed for security proofs) is deferred.
-/

universe u

namespace Interaction

open DuplexSponge

/-! ## Sponge annotation -/

/-- Per-node serialization metadata for duplex sponge Fiat-Shamir, mirroring
the shape of a role-decorated `Spec`.

At sender nodes: how to serialize the message into sponge units (`List U`).
At receiver nodes: how many units to squeeze and how to deserialize the
result into a challenge value. -/
def SpongeAnnotation (U : Type) :
    (spec : Spec.{u}) → RoleDecoration spec → Type u
  | .done, _ => PUnit.{u + 1}
  | .node X rest, ⟨.sender, rRest⟩ =>
      (X → List U) × ((x : X) → SpongeAnnotation U (rest x) (rRest x))
  | .node X rest, ⟨.receiver, rRest⟩ =>
      (len : Nat) × (Vector U len → X) × ((x : X) → SpongeAnnotation U (rest x) (rRest x))

namespace SpongeAnnotation

variable {U : Type}

/-- The serialization function at a sender node. -/
abbrev serialize
    {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (ann : SpongeAnnotation U (.node X rest) ⟨.sender, rRest⟩) :
    X → List U :=
  ann.1

/-- The continuation annotation past a sender node. -/
abbrev afterMessage
    {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (ann : SpongeAnnotation U (.node X rest) ⟨.sender, rRest⟩) (x : X) :
    SpongeAnnotation U (rest x) (rRest x) :=
  ann.2 x

/-- The squeeze length at a receiver node. -/
abbrev squeezeLen
    {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (ann : SpongeAnnotation U (.node X rest) ⟨.receiver, rRest⟩) :
    Nat :=
  ann.1

/-- The deserialization function at a receiver node. -/
abbrev deserialize
    {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (ann : SpongeAnnotation U (.node X rest) ⟨.receiver, rRest⟩) :
    Vector U ann.squeezeLen → X :=
  ann.2.1

/-- The continuation annotation past a receiver node. -/
abbrev afterChallenge
    {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (ann : SpongeAnnotation U (.node X rest) ⟨.receiver, rRest⟩)
    (x : X) : SpongeAnnotation U (rest x) (rRest x) :=
  ann.2.2 x

end SpongeAnnotation

/-! ## Building a ReplayOracle from a sponge -/

variable {U : Type} [SpongeUnit U] [SpongeSize]
  [Permute (CanonicalSpongeState U)]

/-- Construct a `ReplayOracle` by threading a `CanonicalDuplexSponge U`
through the interaction tree.

At sender nodes, the message is serialized (via the annotation) and absorbed
into the sponge. At receiver nodes, the sponge is squeezed and the output
deserialized to obtain the deterministic challenge. The permutation is
resolved concretely via `forwardPermutationOracleImpl`. -/
def buildSpongeReplayOracle :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    SpongeAnnotation U spec roles →
    CanonicalDuplexSponge U →
    ReplayOracle spec roles
  | .done, _, _, _ => PUnit.unit
  | .node _X rest, ⟨.sender, rRest⟩, ann, sponge =>
      fun x =>
        let newSponge := absorbUnchecked sponge (ann.serialize x).toArray
        buildSpongeReplayOracle (rest x) (rRest x) (ann.afterMessage x) newSponge
  | .node _X rest, ⟨.receiver, rRest⟩, ann, sponge =>
      let (squeezed, newSponge) :=
        Id.run <| simulateQ (forwardPermutationOracleImpl _) (squeeze sponge ann.squeezeLen)
      let x := ann.deserialize squeezed
      ⟨x, buildSpongeReplayOracle (rest x) (rRest x) (ann.afterChallenge x) newSponge⟩

/-! ## Statement initialization and the full transform -/

section DuplexSpongeFiatShamir

variable {m : Type u → Type u} [Monad m]
variable {StatementIn : Type u} {WitnessIn : Type u}
variable {Context : StatementIn → Spec.{u}}
variable {Roles : (s : StatementIn) → RoleDecoration (Context s)}
variable {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u}
variable {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type u}

/-- Initialize a sponge from the statement and build the corresponding
`ReplayOracle`. The `initSponge` parameter captures statement-dependent
sponge initialization (paralleling `DuplexSponge.start` with a concrete
start oracle). -/
def spongeReplayOracle
    (initSponge : StatementIn → CanonicalDuplexSponge U)
    (annotation : (s : StatementIn) → SpongeAnnotation U (Context s) (Roles s))
    (s : StatementIn) : ReplayOracle (Context s) (Roles s) :=
  buildSpongeReplayOracle (Context s) (Roles s) (annotation s) (initSponge s)

/-- Construct the `FSStatement` (original statement bundled with a sponge-derived
replay oracle) from an original statement. -/
def toFSStatement
    (initSponge : StatementIn → CanonicalDuplexSponge U)
    (annotation : (s : StatementIn) → SpongeAnnotation U (Context s) (Roles s))
    (s : StatementIn) : FSStatement StatementIn Context Roles :=
  ⟨s, spongeReplayOracle initSponge annotation s⟩

/-- The duplex sponge FS prover: constructs the replay oracle from the sponge,
then delegates to the basic `Prover.fiatShamir`. -/
def Prover.duplexSpongeFiatShamir
    (initSponge : StatementIn → CanonicalDuplexSponge U)
    (annotation : (s : StatementIn) → SpongeAnnotation U (Context s) (Roles s))
    (P : Prover m StatementIn Context Roles
      (fun _ => PUnit) (fun _ => WitnessIn) StatementOut WitnessOut) :
    Prover m StatementIn
      (fun s => fsContext Context Roles (toFSStatement initSponge annotation s))
      (fun s => fsRoles Context Roles (toFSStatement initSponge annotation s))
      (fun _ => PUnit) (fun _ => WitnessIn)
      (fun s => fsStatementOut Context Roles StatementOut (toFSStatement initSponge annotation s))
      (fun s => fsWitnessOut Context Roles WitnessOut (toFSStatement initSponge annotation s)) :=
  fun s _ wit => do
    let fs := toFSStatement initSponge annotation s
    let strategy ← P s PUnit.unit wit
    let ⟨msgs, out⟩ ←
      Strategy.runWithReplayOracle (Context s) (Roles s) fs.2 strategy
    pure <| pure ⟨msgs, out⟩

/-- The duplex sponge FS verifier: constructs the replay oracle from the sponge,
then delegates to `PublicCoinVerifier.fiatShamir`. -/
def PublicCoinVerifier.duplexSpongeFiatShamir
    (initSponge : StatementIn → CanonicalDuplexSponge U)
    (annotation : (s : StatementIn) → SpongeAnnotation U (Context s) (Roles s))
    (V : PublicCoinVerifier m StatementIn Context Roles
      (fun _ => PUnit) StatementOut) :
    Verifier m StatementIn
      (fun s => fsContext Context Roles (toFSStatement initSponge annotation s))
      (fun s => fsRoles Context Roles (toFSStatement initSponge annotation s))
      (fun _ => PUnit)
      (fun s => fsStatementOut Context Roles StatementOut
        (toFSStatement initSponge annotation s)) :=
  fun s _ msgs =>
    let fs := toFSStatement initSponge annotation s
    V.replay s PUnit.unit (MessagesOnly.deriveTranscript (Context s) (Roles s) fs.2 msgs)

/-- The full duplex sponge Fiat-Shamir transform for a public-coin reduction.

Given a sponge initialization function and per-node serialization annotations,
constructs a non-interactive reduction by:
1. Building a `ReplayOracle` from the duplex sponge.
2. Running the prover against it to produce a `MessagesOnly` proof.
3. Having the verifier reconstruct the transcript and replay through the
   original public-coin verifier. -/
def PublicCoinReduction.duplexSpongeFiatShamir
    (initSponge : StatementIn → CanonicalDuplexSponge U)
    (annotation : (s : StatementIn) → SpongeAnnotation U (Context s) (Roles s))
    (R : PublicCoinReduction m StatementIn Context Roles
      (fun _ => PUnit) (fun _ => WitnessIn) StatementOut WitnessOut) :
    Reduction m StatementIn
      (fun s => fsContext Context Roles (toFSStatement initSponge annotation s))
      (fun s => fsRoles Context Roles (toFSStatement initSponge annotation s))
      (fun _ => PUnit) (fun _ => WitnessIn)
      (fun s => fsStatementOut Context Roles StatementOut (toFSStatement initSponge annotation s))
      (fun s => fsWitnessOut Context Roles WitnessOut (toFSStatement initSponge annotation s)) where
  prover := Prover.duplexSpongeFiatShamir initSponge annotation R.prover
  verifier := PublicCoinVerifier.duplexSpongeFiatShamir initSponge annotation R.verifier

end DuplexSpongeFiatShamir

end Interaction


/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.FiatShamir.Basic
import ArkLib.Interaction.Reduction

open Interaction.TwoParty

/-!
# The Fiat-Shamir Transform

This module implements the basic Fiat-Shamir (FS) transform for the `Interaction`
core when the verifier is public-coin in the strong, replayable sense captured
by `PublicCoinCounterpart.syntax`. The construction works as follows:

1. Replacing the random verifier with a deterministic `ReplayOracle`, which is
   bundled into the statement.
2. The prover runs its strategy against the replay oracle, producing a
   `MessagesOnly` proof (sent as a single message).
3. The verifier receives `MessagesOnly`, reconstructs the full transcript
   via `deriveTranscript`, and replays that transcript through the original
   public-coin verifier.

## Main definitions

- `Strategy.runWithReplayOracle` — execute a prover strategy against a replay
  oracle, producing `MessagesOnly` and the strategy's output simultaneously.
- `fsContext`, `fsRoles` — the non-interactive protocol (single sender node).
- `PublicCoinVerifier.fiatShamir` — build the one-message verifier from a
  public-coin interactive verifier.
- `PublicCoinReduction.fiatShamir` — package the transformed prover and verifier.

## Design notes

The replay oracle is modeled as input data (part of the statement), not as an
additional oracle. This is the simplest formulation for the basic FS transform.
For security proofs in the random oracle model, the replay oracle would be
sampled from a random oracle — that oracle-level formulation is deferred.
-/

universe u

namespace Interaction

open Spec

/-! ## Running a strategy against a replay oracle -/

/-- Execute a prover strategy against a `ReplayOracle`, building the
`MessagesOnly` proof and the strategy output simultaneously. At sender
nodes the prover picks its move; at receiver nodes the challenge comes
from the replay oracle. -/
def Strategy.runWithReplayOracle {m : Type u → Type u} [Monad m] :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    (rho : ReplayOracle spec roles) →
    {Output : Transcript spec → Type u} →
    Spec.StrategyOver (pairedSyntax m) TwoParty.Participant.focal spec roles Output →
    m ((msgs : MessagesOnly spec roles rho) ×
       Output (MessagesOnly.deriveTranscript spec roles rho msgs))
  | .done, _, _, _, output => pure ⟨⟨⟩, output⟩
  | .node _X rest, ⟨.sender, rRest⟩, rho, _, send => do
      let ⟨x, next⟩ ← send
      let ⟨msgs, out⟩ ← runWithReplayOracle (rest x) (rRest x)
        (rho.afterMessage x) next
      return ⟨⟨x, msgs⟩, out⟩
  | .node _X rest, ⟨.receiver, rRest⟩, rho, _, respond => do
      let next ← respond rho.challenge
      let ⟨msgs, out⟩ ← runWithReplayOracle (rest rho.challenge) (rRest rho.challenge)
        rho.afterChallenge next
      return ⟨msgs, out⟩

/-! ## The non-interactive protocol -/

section FiatShamir

variable {m : Type u → Type u} [Monad m]
variable {StatementIn : Type u} {WitnessIn : Type u}
variable {Context : StatementIn → Spec.{u}}
variable {Roles : (s : StatementIn) → RoleDecoration (Context s)}
variable {StatementOut : (s : StatementIn) → Transcript (Context s) → Type u}
variable {WitnessOut : (s : StatementIn) → Transcript (Context s) → Type u}

/-- The FS statement bundles the original statement with a replay oracle. -/
abbrev FSStatement (StatementIn : Type u) (Context : StatementIn → Spec.{u})
    (Roles : (s : StatementIn) → RoleDecoration (Context s)) : Type u :=
  (s : StatementIn) × ReplayOracle (Context s) (Roles s)

/-- The FS protocol context: a single sender node whose message type is
`MessagesOnly` (the FS proof). -/
def fsContext (Context : StatementIn → Spec.{u})
    (Roles : (s : StatementIn) → RoleDecoration (Context s)) :
    FSStatement StatementIn Context Roles → Spec.{u} :=
  fun ⟨s, rho⟩ => .node (MessagesOnly (Context s) (Roles s) rho) (fun _ => .done)

/-- The FS role decoration: the single node is a sender. -/
def fsRoles (Context : StatementIn → Spec.{u})
    (Roles : (s : StatementIn) → RoleDecoration (Context s)) :
    (fs : FSStatement StatementIn Context Roles) →
    RoleDecoration (fsContext Context Roles fs) :=
  fun _ => ⟨.sender, fun _ => ⟨⟩⟩

/-- Transport statement output through the FS transcript. The FS transcript
is `(msgs : MessagesOnly, ⟨⟩)` and the original output is indexed by the
derived interactive transcript. -/
def fsStatementOut
    (Context : StatementIn → Spec.{u})
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (StatementOut : (s : StatementIn) → Transcript (Context s) → Type u) :
    (fs : FSStatement StatementIn Context Roles) →
    Transcript (fsContext Context Roles fs) → Type u :=
  fun ⟨s, rho⟩ ⟨msgs, _⟩ =>
    StatementOut s (MessagesOnly.deriveTranscript (Context s) (Roles s) rho msgs)

/-- Transport witness output through the FS transcript. -/
def fsWitnessOut
    (Context : StatementIn → Spec.{u})
    (Roles : (s : StatementIn) → RoleDecoration (Context s))
    (WitnessOut : (s : StatementIn) → Transcript (Context s) → Type u) :
    (fs : FSStatement StatementIn Context Roles) →
    Transcript (fsContext Context Roles fs) → Type u :=
  fun ⟨s, rho⟩ ⟨msgs, _⟩ =>
    WitnessOut s (MessagesOnly.deriveTranscript (Context s) (Roles s) rho msgs)

/-! ## The prover-side Fiat-Shamir transform -/

/-- The FS prover: given `(s, rho)` and witness, runs the original prover's
strategy against the replay oracle to produce a `MessagesOnly` proof. -/
def Prover.fiatShamir
    (P : Prover m StatementIn Context Roles
      (fun _ => PUnit) (fun _ => WitnessIn) StatementOut WitnessOut) :
    Prover m (FSStatement StatementIn Context Roles)
      (fsContext Context Roles) (fsRoles Context Roles)
      (fun _ => PUnit) (fun _ => WitnessIn)
      (fsStatementOut Context Roles StatementOut)
      (fsWitnessOut Context Roles WitnessOut) :=
  fun ⟨s, rho⟩ _ wit => do
    let strategy ← P s PUnit.unit wit
    let ⟨msgs, out⟩ ←
      Strategy.runWithReplayOracle (Context s) (Roles s) rho strategy
    pure <| pure ⟨msgs, out⟩

/-- The verifier-side basic Fiat-Shamir transform for a public-coin verifier.

The verifier receives a messages-only proof, reconstructs the corresponding
interactive transcript using the replay oracle bundled in the statement, and
then replays that transcript through the original public-coin verifier inside
the verifier monad. -/
def PublicCoinVerifier.fiatShamir
    (V : PublicCoinVerifier m StatementIn Context Roles
      (fun _ => PUnit) StatementOut) :
    Verifier m (FSStatement StatementIn Context Roles) (fsContext Context Roles)
      (fsRoles Context Roles) (fun _ => PUnit)
      (fsStatementOut Context Roles StatementOut) :=
  fun ⟨s, rho⟩ _ msgs =>
    V.replay s PUnit.unit (MessagesOnly.deriveTranscript (Context s) (Roles s) rho msgs)

/-- Package the basic Fiat-Shamir transform of a public-coin reduction.

The prover is run against the replay oracle to produce a messages-only proof,
and the verifier replays the reconstructed transcript through the original
public-coin verifier monadically. -/
def PublicCoinReduction.fiatShamir
    (R : PublicCoinReduction m StatementIn Context Roles
      (fun _ => PUnit) (fun _ => WitnessIn) StatementOut WitnessOut) :
    Reduction m (FSStatement StatementIn Context Roles)
      (fsContext Context Roles) (fsRoles Context Roles)
      (fun _ => PUnit) (fun _ => WitnessIn)
      (fsStatementOut Context Roles StatementOut)
      (fsWitnessOut Context Roles WitnessOut) where
  prover := Prover.fiatShamir R.prover
  verifier := R.verifier.fiatShamir

end FiatShamir

end Interaction


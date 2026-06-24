/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.TwoParty.Strategy

open Interaction.TwoParty

/-!
# Fiat-Shamir Basics: Replay Oracles and Messages-Only Proofs

The Fiat-Shamir (FS) transform replaces verifier challenges with deterministic
hash outputs, converting an interactive public-coin protocol into a
non-interactive one.

The key insight for the dependent-type setting: a `ReplayOracle` is a
deterministic counterpart strategy that observes sender messages and provides
challenges at receiver nodes. Given a fixed replay oracle, all challenge values
(and hence all subsequent types) are determined.

## Main definitions

- `ReplayOracle` — deterministic counterpart strategy with unit output. At
  sender nodes it observes a message; at receiver nodes it picks a challenge
  and continuation.
- `MessagesOnly` — the FS proof type. Only sender messages are stored; at
  receiver nodes the challenge is read from the replay oracle. This is the
  prover's output after the FS transform.
- `MessagesOnly.deriveTranscript` — reconstruct the full interactive `Transcript`
  from a messages-only proof and a replay oracle.
-/

universe u

namespace Interaction

/-- A `ReplayOracle` for the Fiat-Shamir transform is a deterministic
counterpart strategy: at sender nodes it observes any message, at receiver nodes
it provides a challenge.

This is a counterpart fiber of the paired two-party syntax over `Id`, which
unfolds to:
- `.done`: `PUnit`
- sender node: `(x : X) → ReplayOracle (rest x) (rRest x)` (observe)
- receiver node: `(x : X) × ReplayOracle (rest x) (rRest x)` (pick challenge) -/
abbrev ReplayOracle (spec : Spec.{u}) (roles : RoleDecoration spec) : Type u :=
  Spec.StrategyOver (pairedSyntax Id) TwoParty.Participant.counterpart
    spec roles (fun _ => PUnit)

namespace ReplayOracle

/-- The challenge picked at the current receiver node. -/
abbrev challenge {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (rho : ReplayOracle (.node X rest) ⟨.receiver, rRest⟩) : X :=
  rho.1

/-- The continuation replay oracle past the current receiver node. -/
abbrev afterChallenge {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (rho : ReplayOracle (.node X rest) ⟨.receiver, rRest⟩) :
    ReplayOracle (rest rho.challenge) (rRest rho.challenge) :=
  rho.2

/-- Restrict the replay oracle past a sender message. -/
abbrev afterMessage {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
    (rho : ReplayOracle (.node X rest) ⟨.sender, rRest⟩) (x : X) :
    ReplayOracle (rest x) (rRest x) :=
  rho x

end ReplayOracle

/-! ## Messages-only proofs -/

/-- The Fiat-Shamir proof type: only sender messages are stored. At receiver
nodes, the challenge is determined by the `ReplayOracle`, so no proof data
is needed — we recurse directly into the oracle-determined subtree.

This is the key dependent-typing insight: at a receiver node with
`rho : ReplayOracle`, the subtree is `rest rho.challenge`, and
`MessagesOnly` recurses into exactly that subtree. -/
def MessagesOnly :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    ReplayOracle spec roles → Type u
  | .done, _, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩, rho =>
      (x : X) × MessagesOnly (rest x) (rRest x) (rho.afterMessage x)
  | .node _X rest, ⟨.receiver, rRest⟩, rho =>
      MessagesOnly (rest rho.challenge) (rRest rho.challenge) rho.afterChallenge

namespace MessagesOnly

/-- Reconstruct the full interactive `Transcript` from a messages-only proof
and a replay oracle. Sender moves come from the proof; receiver challenges
come from the oracle. -/
def deriveTranscript :
    (spec : Spec.{u}) → (roles : RoleDecoration spec) →
    (rho : ReplayOracle spec roles) →
    MessagesOnly spec roles rho → Spec.Transcript spec
  | .done, _, _, _ => ⟨⟩
  | .node _X rest, ⟨.sender, rRest⟩, rho, ⟨x, tail⟩ =>
      ⟨x, deriveTranscript (rest x) (rRest x) (rho.afterMessage x) tail⟩
  | .node _X rest, ⟨.receiver, rRest⟩, rho, tail =>
      ⟨rho.challenge, deriveTranscript (rest rho.challenge) (rRest rho.challenge)
        rho.afterChallenge tail⟩

end MessagesOnly

end Interaction


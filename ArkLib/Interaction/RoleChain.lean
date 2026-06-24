/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.Replicate
import PolyFun.Interaction.TwoParty.Compose
import ArkLib.Interaction.Compat

open Interaction.TwoParty

/-!
# Decorated Two-Party Chains

A `Spec.RoleChain n` is a self-contained recipe for an `n`-round two-party
protocol. Each node carries:

* the current round `Spec`,
* the sender/receiver role decoration for that spec,
* a transcript-indexed continuation.

The chain fixes protocol shape and roles. Participant state is modeled
separately by the `Strategy.RoundSteps` and `Counterpart.RoundSteps` folds.
-/

universe u

namespace Interaction

namespace Spec

/-! ## Decorated chain -/

/-- A self-contained two-party chain: every round carries the local `Spec`,
the sender/receiver roles for that spec, and a transcript-indexed continuation. -/
def RoleChain : Nat → Type (u + 1)
  | 0 => PUnit
  | n + 1 => (spec : Spec.{u}) × RoleDecoration spec × (Transcript spec → RoleChain n)

namespace RoleChain

/-! ## Flattening -/

/-- Flatten a decorated chain into a concrete `Spec`. -/
def toSpec : (n : Nat) → RoleChain.{u} n → Spec.{u}
  | 0, _ => .done
  | n + 1, ⟨spec, _, cont⟩ => spec.append (fun tr => toSpec n (cont tr))

/-- Flatten the role decorations along a decorated chain. -/
def toRoles : (n : Nat) → (c : RoleChain.{u} n) → RoleDecoration (toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨_spec, roles, cont⟩ =>
      Spec.Decoration.append roles (fun tr => toRoles n (cont tr))

@[simp] theorem toSpec_zero (c : RoleChain.{u} 0) : toSpec 0 c = .done := rfl

theorem toSpec_succ {n : Nat} (spec : Spec.{u})
    (roles : RoleDecoration spec) (cont : Transcript spec → RoleChain.{u} n) :
    toSpec (n + 1) ⟨spec, roles, cont⟩ =
      spec.append (fun tr => toSpec n (cont tr)) := rfl

/-! ## Constant chains -/

/-- Constant decorated rounds: the same spec and roles at every level, with
continuation independent of the transcript. -/
def replicate (spec : Spec.{u}) (roles : RoleDecoration spec) : (n : Nat) → RoleChain.{u} n
  | 0 => ⟨⟩
  | n + 1 => ⟨spec, roles, fun _ => replicate spec roles n⟩

/-- Flattening a constant decorated chain recovers `Spec.replicate`. -/
@[simp]
theorem toSpec_replicate (spec : Spec.{u}) (roles : RoleDecoration spec) :
    (n : Nat) → toSpec n (replicate spec roles n) = spec.replicate n
  | 0 => rfl
  | n + 1 => by
      simp only [replicate, toSpec, Spec.replicate]
      congr 1
      funext _
      exact toSpec_replicate spec roles n

/-! ## Transcript operations -/

/-- Split a transcript of a flattened `(n+1)`-round decorated chain into the
first round transcript and the remainder. -/
def splitTranscript (n : Nat) (c : RoleChain.{u} (n + 1)) :
    Transcript (toSpec (n + 1) c) →
    (tr₁ : Transcript c.1) × Transcript (toSpec n (c.2.2 tr₁)) :=
  Transcript.split c.1 (fun tr => toSpec n (c.2.2 tr))

/-- Combine a first-round transcript with a suffix transcript. -/
def appendTranscript (n : Nat) (c : RoleChain.{u} (n + 1))
    (tr₁ : Transcript c.1) (tr₂ : Transcript (toSpec n (c.2.2 tr₁))) :
    Transcript (toSpec (n + 1) c) :=
  Transcript.append c.1 (fun tr => toSpec n (c.2.2 tr)) tr₁ tr₂

@[simp]
theorem splitTranscript_appendTranscript (n : Nat) (c : RoleChain.{u} (n + 1))
    (tr₁ : Transcript c.1) (tr₂ : Transcript (toSpec n (c.2.2 tr₁))) :
    splitTranscript n c (appendTranscript n c tr₁ tr₂) = ⟨tr₁, tr₂⟩ :=
  Transcript.split_append _ _ _ _

/-! ## Output family -/

/-- Lift a family on remaining decorated chains to a family on transcripts of
the flattened `Spec`. -/
def outputFamily
    (Family : {n : Nat} → RoleChain.{u} n → Type u) :
    (n : Nat) → (c : RoleChain.{u} n) → Transcript (toSpec n c) → Type u
  | 0, c, _ => Family c
  | n + 1, ⟨spec, _, cont⟩, tr =>
      Transcript.liftAppend spec (fun tr₁ => toSpec n (cont tr₁))
        (fun tr₁ tr₂ => outputFamily Family n (cont tr₁) tr₂)
        tr

end RoleChain

/-! ## Strategy composition -/

namespace Strategy

/-- Per-node prover handlers for one concrete `RoleChain`.

The handlers follow the actual continuation tree of `c`: a current-round
strategy plus, for every current transcript, handlers for the selected suffix. -/
def RoundSteps {m : Type u → Type u} [Monad m]
    (State : {k : Nat} → RoleChain.{u} k → Type u) :
    (n : Nat) → (c : RoleChain.{u} n) → Type (u + 1)
  | 0, _ => PUnit
  | n + 1, c =>
      ((state : State c) →
        m (_root_.Interaction.StrategyOver (pairedSyntax m) TwoParty.Participant.focal
          c.1 c.2.1 (fun (tr : PFunctor.FreeM.Path c.1) => State (c.2.2 tr)))) ×
      ((tr : Transcript c.1) →
        RoundSteps (m := m) State n (c.2.2 tr))

/-- Compose concrete-chain prover handlers into a full strategy. -/
def ofChain {m : Type u → Type u} [Monad m]
    (State : {k : Nat} → RoleChain.{u} k → Type u) :
    (n : Nat) → (c : RoleChain.{u} n) → State c →
      RoundSteps (m := m) State n c →
    m (_root_.Interaction.StrategyOver (pairedSyntax m) TwoParty.Participant.focal
      (RoleChain.toSpec n c) (RoleChain.toRoles n c)
      (fun (tr : PFunctor.FreeM.Path (RoleChain.toSpec n c)) => RoleChain.outputFamily State n c tr))
  | 0, _, state, _ => pure state
  | n + 1, ⟨spec, roles, cont⟩, state, steps => do
    let strat ← steps.1 state
    @StrategyOver.TwoParty.Focal.comp m _ spec (fun tr => RoleChain.toSpec n (cont tr))
      roles (fun tr => RoleChain.toRoles n (cont tr))
      (fun tr => State (cont tr))
      (fun tr₁ tr₂ => RoleChain.outputFamily State n (cont tr₁) tr₂)
      strat
      (fun tr state' =>
        ofChain State n (cont tr) state' (steps.2 tr))

end Strategy

/-! ## Counterpart composition -/

namespace Counterpart

/-- Per-node verifier counterparts for one concrete `RoleChain`. -/
def RoundSteps {m : Type u → Type u} [Monad m]
    (State : {k : Nat} → RoleChain.{u} k → Type u) :
    (n : Nat) → (c : RoleChain.{u} n) → Type (u + 1)
  | 0, _ => PUnit
  | n + 1, c =>
      ((state : State c) →
        _root_.Interaction.StrategyOver (pairedSyntax m) TwoParty.Participant.counterpart
          c.1 c.2.1 (fun (tr : PFunctor.FreeM.Path c.1) => State (c.2.2 tr))) ×
      ((tr : Transcript c.1) →
        RoundSteps (m := m) State n (c.2.2 tr))

/-- Compose concrete-chain verifier handlers into a full counterpart. -/
def ofChain {m : Type u → Type u} [Monad m]
    (State : {k : Nat} → RoleChain.{u} k → Type u) :
    (n : Nat) → (c : RoleChain.{u} n) → State c →
      RoundSteps (m := m) State n c →
    _root_.Interaction.StrategyOver (pairedSyntax m) TwoParty.Participant.counterpart
      (RoleChain.toSpec n c) (RoleChain.toRoles n c)
      (fun (tr : PFunctor.FreeM.Path (RoleChain.toSpec n c)) => RoleChain.outputFamily State n c tr)
  | 0, _, state, _ => state
  | n + 1, ⟨spec, roles, cont⟩, state, steps =>
    @StrategyOver.TwoParty.Counterpart.append m _ spec (fun tr => RoleChain.toSpec n (cont tr))
      roles (fun tr => RoleChain.toRoles n (cont tr))
      (fun tr => State (cont tr))
      (fun tr₁ tr₂ => RoleChain.outputFamily State n (cont tr₁) tr₂)
      (steps.1 state)
      (fun tr state' =>
        ofChain State n (cont tr) state' (steps.2 tr))

end Counterpart

end Spec

end Interaction


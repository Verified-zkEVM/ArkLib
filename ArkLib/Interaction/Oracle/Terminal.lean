/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.CoreRun

/-!
# Explicit protocol outcomes

Acceptance carries a claim, rejection is an ordinary returned result, and a fault carries the
model's named failure. These values do not account for missing runtime probability mass.
`ofOption` is the migration decoder for a verifier whose `none` means rejection.
-/

universe u v w

namespace Interaction.Oracle

/-- Returned protocol outcomes, separate from failure to return a runtime result. -/
inductive Terminal (Claim : Type u) (Fault : Type v) where
  /-- The verifier accepts the supplied claim. -/
  | accept : Claim → Terminal Claim Fault
  /-- The verifier rejects. -/
  | reject : Terminal Claim Fault
  /-- The model reports an explicit fault. -/
  | fault : Fault → Terminal Claim Fault
  deriving DecidableEq

namespace Terminal

variable {Claim : Type u} {Claim' : Type w} {Fault : Type v}

/-- Transform accepted claims, preserving rejection and faults. -/
def map (f : Claim → Claim') : Terminal Claim Fault → Terminal Claim' Fault
  | .accept claim => .accept (f claim)
  | .reject => .reject
  | .fault failure => .fault failure

/-- Continue only after acceptance. Rejection and faults short-circuit the continuation. -/
def bind (outcome : Terminal Claim Fault) (next : Claim → Terminal Claim' Fault) :
    Terminal Claim' Fault :=
  match outcome with
  | .accept claim => next claim
  | .reject => .reject
  | .fault failure => .fault failure

/-- Decode the optional-claim convention: absence is rejection, never a fault. -/
def ofOption : Option Claim → Terminal Claim Fault
  | some claim => .accept claim
  | none => .reject

@[simp]
theorem map_accept (f : Claim → Claim') (claim : Claim) :
    map f (.accept claim : Terminal Claim Fault) = .accept (f claim) := rfl

@[simp]
theorem map_reject (f : Claim → Claim') :
    map f (.reject : Terminal Claim Fault) = .reject := rfl

@[simp]
theorem map_fault (f : Claim → Claim') (fault : Fault) :
    map f (.fault fault : Terminal Claim Fault) = .fault fault := rfl

@[simp]
theorem bind_accept (claim : Claim) (next : Claim → Terminal Claim' Fault) :
    bind (.accept claim) next = next claim := rfl

@[simp]
theorem bind_reject (next : Claim → Terminal Claim' Fault) :
    bind .reject next = .reject := rfl

@[simp]
theorem bind_fault (fault : Fault) (next : Claim → Terminal Claim' Fault) :
    bind (.fault fault) next = .fault fault := rfl

@[simp]
theorem map_id (outcome : Terminal Claim Fault) : outcome.map id = outcome := by
  cases outcome <;> rfl

/-- Sequential outcome decoding is associative, including both short-circuit cases. -/
theorem bind_assoc {Claim'' : Type*} (outcome : Terminal Claim Fault)
    (first : Claim → Terminal Claim' Fault) (second : Claim' → Terminal Claim'' Fault) :
    (outcome.bind first).bind second = outcome.bind (fun claim => (first claim).bind second) := by
  cases outcome <;> rfl

@[simp]
theorem ofOption_eq_accept_iff (outcome : Option Claim) (claim : Claim) :
    (ofOption outcome : Terminal Claim Fault) = .accept claim ↔ outcome = some claim := by
  cases outcome <;> simp [ofOption]

@[simp]
theorem ofOption_eq_reject_iff (outcome : Option Claim) :
    (ofOption outcome : Terminal Claim Fault) = .reject ↔ outcome = none := by
  cases outcome <;> simp [ofOption]

@[simp]
theorem ofOption_ne_fault (outcome : Option Claim) (fault : Fault) :
    (ofOption outcome : Terminal Claim Fault) ≠ .fault fault := by
  cases outcome <;> simp [ofOption]

/-- Decoding and deterministic claim closing commute. -/
theorem ofOption_map (f : Claim → Claim') (outcome : Option Claim) :
    (ofOption (outcome.map f) : Terminal Claim' Fault) = (ofOption outcome).map f := by
  cases outcome <;> rfl

/-- Decode a missing runtime result only when the caller names its runtime fault.
The outer `none` is distinct from the optional-claim rejection decoded by `ofOption`. -/
def decodeRuntime (missingFault : Fault) : Option (Terminal Claim Fault) → Terminal Claim Fault
  | some outcome => outcome
  | none => .fault missingFault

@[simp]
theorem decodeRuntime_some (missingFault : Fault) (outcome : Terminal Claim Fault) :
    decodeRuntime missingFault (some outcome) = outcome := rfl

@[simp]
theorem decodeRuntime_none (missingFault : Fault) :
    decodeRuntime missingFault (none : Option (Terminal Claim Fault)) = .fault missingFault := rfl

/-- A decoded acceptance must have been returned by the protocol. -/
@[simp]
theorem decodeRuntime_eq_accept_iff (missingFault : Fault)
    (outcome : Option (Terminal Claim Fault)) (claim : Claim) :
    decodeRuntime missingFault outcome = .accept claim ↔ outcome = some (.accept claim) := by
  cases outcome <;> simp [decodeRuntime]

/-- Runtime missing mass cannot be decoded as verifier rejection. -/
@[simp]
theorem decodeRuntime_eq_reject_iff (missingFault : Fault)
    (outcome : Option (Terminal Claim Fault)) :
    decodeRuntime missingFault outcome = .reject ↔ outcome = some .reject := by
  cases outcome <;> simp [decodeRuntime]

end Terminal

namespace CoreRun

variable {protocol : Oracle.Protocol.{u}} {initial : PFunctor.{u, u}}
    {Stmt : protocol.tree.BranchPath → Type u}
    {Idx : protocol.tree.BranchPath → Type u}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type u}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type u}

/-- The optional outcome decoded after closing with this run's own resources. -/
def terminalClosed (Fault : Type v) (run : CoreRun protocol initial Stmt Out OutP) :
    Terminal (ClosedClaim (Stmt run.path.toBranchPath) (Out run.path.toBranchPath)) Fault :=
  Terminal.ofOption run.closed

/-- Closing a decoded core outcome uses exactly the resources paired by the core executor. -/
theorem terminalClosed_eq (Fault : Type v) (run : CoreRun protocol initial Stmt Out OutP) :
    run.terminalClosed Fault = (Terminal.ofOption run.outcome).map
      (fun claim => claim.closeWith
        (run.path.closingImpl protocol.oracles initial run.inputImpl)) :=
  Terminal.ofOption_map _ _

end CoreRun

end Interaction.Oracle

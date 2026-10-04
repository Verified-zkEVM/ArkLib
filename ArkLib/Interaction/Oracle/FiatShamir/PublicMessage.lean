/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestoration

/-!
# Public-message presentation of the fixed-round restoration fragment

The restoration certificate is phrased over oracle-message nodes. A Fiat–Shamir proof instead
contains public prover messages. These are distinct native protocol nodes: a public message is
retained in the branch history, whereas an oracle message contributes only a unit branch and its
payload is available through its declared oracle interface. This file gives the public protocol
and transports its *concrete execution path* to the certificate protocol's execution path.

The path equivalence by itself does not equate the two branch histories or grant a verifier access
to an oracle-message payload. A client transporting an observation or extractor must supply its
corresponding law explicitly.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- Alternating public prover messages and public verifier challenges. -/
def publicProtocol : List Round → Protocol
  | [] => .done
  | round :: rounds => .public .sender round.Message (fun _ =>
      .public .receiver round.Challenge (fun _ => publicProtocol rounds))

/-- Full public prover-message proof, without restoration's per-round salt fields. -/
def PublicMessages : List Round → Type
  | [] => PUnit
  | round :: rounds => round.Message × PublicMessages rounds

/-- Insert the trivial per-round restoration salt. A single global salt is part of the input. -/
def withUnitSalts : (rounds : List Round) → PublicMessages rounds → Messages PUnit rounds
  | [], _ => PUnit.unit
  | _ :: rounds, (message, messages) =>
      ⟨message, PUnit.unit, withUnitSalts rounds messages⟩

/-- Discard the trivial per-round restoration salts. -/
def withoutUnitSalts : (rounds : List Round) → Messages PUnit rounds → PublicMessages rounds
  | [], _ => PUnit.unit
  | _ :: rounds, (message, _, messages) =>
      ⟨message, withoutUnitSalts rounds messages⟩

@[simp]
theorem withoutUnitSalts_withUnitSalts (rounds : List Round)
    (messages : PublicMessages rounds) :
    withoutUnitSalts rounds (withUnitSalts rounds messages) = messages := by
  induction rounds with
  | nil => cases messages; rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, messages⟩
      simp only [withUnitSalts, withoutUnitSalts, ih]
      rfl

@[simp]
theorem withUnitSalts_withoutUnitSalts (rounds : List Round)
    (messages : Messages PUnit rounds) :
    withUnitSalts rounds (withoutUnitSalts rounds messages) = messages := by
  induction rounds with
  | nil => cases messages; rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, salt, messages⟩
      cases salt
      simp only [withUnitSalts, withoutUnitSalts, ih]
      rfl

/-- The concrete path forgets whether the message node was public or oracle-authored. -/
def toRestorationPath : (rounds : List Round) →
    (publicProtocol rounds).tree.ExecutionPath → (protocol rounds).tree.ExecutionPath
  | [], _ => PUnit.unit
  | _ :: rounds, path =>
      ⟨path.1, ⟨path.2.1, toRestorationPath rounds path.2.2⟩⟩

/-- Recover the same concrete public transcript from a restoration execution path. -/
def toPublicPath : (rounds : List Round) →
    (protocol rounds).tree.ExecutionPath → (publicProtocol rounds).tree.ExecutionPath
  | [], _ => PUnit.unit
  | _ :: rounds, path =>
      ⟨path.1, ⟨path.2.1, toPublicPath rounds path.2.2⟩⟩

@[simp]
theorem toPublicPath_toRestorationPath (rounds : List Round)
    (path : (publicProtocol rounds).tree.ExecutionPath) :
    toPublicPath rounds (toRestorationPath rounds path) = path := by
  induction rounds with
  | nil => cases path; rfl
  | cons round rounds ih =>
      rcases path with ⟨message, challenge, tail⟩
      simp only [toRestorationPath, toPublicPath, ih]
      rfl

@[simp]
theorem toRestorationPath_toPublicPath (rounds : List Round)
    (path : (protocol rounds).tree.ExecutionPath) :
    toRestorationPath rounds (toPublicPath rounds path) = path := by
  induction rounds with
  | nil => cases path; rfl
  | cons round rounds ih =>
      rcases path with ⟨message, challenge, tail⟩
      simp only [toPublicPath, toRestorationPath, ih]
      rfl

/-- A concrete transcript equivalence. Its branch-history projections remain distinct. -/
def pathEquiv (rounds : List Round) :
    (publicProtocol rounds).tree.ExecutionPath ≃ (protocol rounds).tree.ExecutionPath where
  toFun := toRestorationPath rounds
  invFun := toPublicPath rounds
  left_inv := toPublicPath_toRestorationPath rounds
  right_inv := toRestorationPath_toPublicPath rounds

end Interaction.Oracle.FiatShamir

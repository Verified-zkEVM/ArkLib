/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.Data.Hash.DuplexSponge.CapacityInitialization

/-!
# Duplex execution with a shared permutation

Functional equivalence uses one fixed function for all permutation calls. Neither
bijectivity nor a cryptographic security property is needed for this deterministic interpretation.
The command interpreter below uses ArkLib's chunk implementations, `absorbFast` and `squeezeInto`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace DuplexSponge.Deterministic

/-- Absorb and squeeze commands, including empty inputs and empty outputs. -/
inductive Command (U : Type) where
  | absorb (input : Array U)
  | squeeze (output : Array U)

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- Execute a finite schedule using ArkLib's existing chunk implementation. -/
def run (perm : CanonicalSpongeState U → CanonicalSpongeState U)
    (state : CanonicalDuplexSponge U) :
    List (Command U) → List (Array U) × CanonicalDuplexSponge U
  | [] => ([], state)
  | .absorb input :: commands => run perm (evalWithAnswerFn perm (state.absorbFast input)) commands
  | .squeeze output :: commands =>
    let (next, bytes) := evalWithAnswerFn perm (state.squeezeInto output)
    let (outputs, final) := run perm next commands
    (bytes :: outputs, final)

/-- Concatenating schedules composes their state transitions and output lists. -/
theorem run_append (perm : CanonicalSpongeState U → CanonicalSpongeState U)
    (commands suffix : List (Command U)) (state : CanonicalDuplexSponge U) :
    run perm state (commands ++ suffix) =
      let first := run perm state commands
      let second := run perm first.2 suffix
      (first.1 ++ second.1, second.2) := by
  induction commands generalizing state with
  | nil => simp [run]
  | cons command commands ih =>
    cases command with
    | absorb input => simp [run, ih]
    | squeeze output => simp [run, ih]

/-- With available rate output, a chunk is copied before recursing on the remaining buffer. -/
theorem squeezeInto_available
    (perm : CanonicalSpongeState U → CanonicalSpongeState U)
    (state : CanonicalDuplexSponge U) (output : Array U)
    (hEmpty : output.isEmpty = false) (hPos : state.squeezePos.val < SpongeSize.R) :
    evalWithAnswerFn perm (state.squeezeInto output) =
      let count := min output.size (SpongeSize.R - state.squeezePos.val)
      let next : CanonicalDuplexSponge U :=
        { state with
          absorbPos := 0
          squeezePos := state.squeezePos + ⟨count, by omega⟩ }
      let result := evalWithAnswerFn perm (next.squeezeInto (output.drop count))
      (result.1, (state.state.extract state.squeezePos.val
        (state.squeezePos.val + count)).toArray ++ result.2) := by
  rw [DuplexSponge.squeezeInto]
  simp [hEmpty, show state.squeezePos.val ≠ SpongeSize.R by omega,
    evalWithAnswerFn]
  rfl

/-- A full rate cursor causes exactly one shared permutation before the next output chunk. -/
theorem squeezeInto_full
    (perm : CanonicalSpongeState U → CanonicalSpongeState U)
    (state : CanonicalDuplexSponge U) (output : Array U)
    (hEmpty : output.isEmpty = false) (hPos : state.squeezePos.val = SpongeSize.R) :
    evalWithAnswerFn perm (state.squeezeInto output) =
      evalWithAnswerFn perm (({ state := perm state.state, absorbPos := 0, squeezePos := 0 } :
        CanonicalDuplexSponge U).squeezeInto output) := by
  rw [DuplexSponge.squeezeInto, DuplexSponge.squeezeInto]
  simp [hEmpty, hPos, evalWithAnswerFn, Nat.ne_of_lt SpongeSize.R_pos]
  rfl

end DuplexSponge.Deterministic

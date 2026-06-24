/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Spec

/-!
# Platonic chain primitive (`Oracle.Spec.Telescope`)

`Telescope round step` is the *initial algebra* of the segment functor that
extends an oracle protocol by one round whose spec depends on the current
state and then transitions to a new state determined by the round's
**public** transcript. This is the `Oracle.Spec` analogue of VCVio's
`Interaction.Spec.Telescope`, with the key adjustment that state transitions
are indexed by `PublicTranscript` rather than the full `Transcript`:
oracle-message values are not observable to the verifier and therefore
cannot influence the *shape* of subsequent rounds. State *contents* may
still depend on private prover data; that information is layered on top of
the bare telescope shape.

Given
* a state space `St : Type v`,
* a round assignment `round : St → Oracle.Spec`,
* a state transition `step : (s : St) → PublicTranscript (round s) → St`,

an inhabitant of `Telescope round step s₀` is a finite tree of `extend`
steps ending in `done`. The construction is well-founded by virtue of being
an inductive: there is no way to construct an infinite-depth instance, so
inhabitation is itself a constructive termination proof for the underlying
state machine.

## Universal property

`Telescope round step` is the carrier of the initial `(round, step)`-algebra
in the slice category over `St`: for any other `(round, step)`-algebra
`(P : St → Type _, alg)`, there is a unique structure-preserving map
`Telescope round step → P` given by structural recursion on the inductive.
`toSpec` is one such recursion, with target algebra
`(fun _ => Oracle.Spec, .done, fun s cont => (round s).append cont)`.

## Relationship to `Oracle.Spec.Chain`

`Spec.Chain n` (in `ArkLib/Interaction/Oracle/Chain.lean`) is the
specialisation `St := Nat`, with `step` ignoring the public transcript and
decrementing the depth, and decorations (`RoleDeco` / `OracleDeco`) baked
into the carrier at every level. Telescope is the underlying shape; chains
and similar constructions are decorated views of it.

## References

* Hancock–Setzer (2000), recursion over interaction interfaces.
* Spivak–Niu (2024), polynomial functors as the algebra of interaction.
-/

universe v

namespace Interaction.Oracle
namespace Spec

/-- State-machine telescopes of `Oracle.Spec`s observed through public
transcripts.

At each state `s : St`, an inhabitant either terminates (`.done s`) or
extends by running the round `round s : Oracle.Spec` and recursing into
`Telescope round step (step s pt)` for every public transcript
`pt : PublicTranscript (round s)`. As an inductive type, every inhabitant
is finite, so the existence of a `Telescope` term is a proof that the
underlying state machine terminates.

This is the oracle-specialized alias of `PFunctor.FreeM.TelescopeWith`; the
observation family is `PublicTranscript`, which keeps public choices and
keeps an explicit `PUnit` marker at each oracle-message node. -/
abbrev Telescope {St : Type v}
    (round : St → Oracle.Spec)
    (step : (s : St) → PublicTranscript (round s) → St) : St → Type v :=
  PFunctor.FreeM.TelescopeWith (P := basePFunctor)
    round (fun s => PublicTranscript (round s)) step

namespace Telescope

variable {St : Type v} {round : St → Oracle.Spec}
    {step : (s : St) → PublicTranscript (round s) → St}

/-- Constructor wrapper for terminating an oracle-spec telescope. -/
abbrev done (s : St) : Telescope round step s :=
  PFunctor.FreeM.TelescopeWith.done
    (round := round) (Obs := fun s => PublicTranscript (round s)) (step := step) s

/-- Constructor wrapper for extending an oracle-spec telescope. -/
abbrev extend (s : St)
    (cont :
      (pt : PublicTranscript (round s)) → Telescope round step (step s pt)) :
    Telescope round step s :=
  PFunctor.FreeM.TelescopeWith.extend
    (round := round) (Obs := fun s => PublicTranscript (round s)) (step := step) s cont

/-- Flatten a `Telescope` into a concrete `Oracle.Spec` by iterated
`Spec.append`. Each `extend` step contributes its round spec to the head,
with the tail expanding through the recursive continuation indexed by the
prefix's public transcript. -/
def toSpec : {s : St} → Telescope round step s → Oracle.Spec
  | _, .done _ => .done
  | _, .extend s cont => (round s).append fun pt => (cont pt).toSpec

@[simp]
theorem toSpec_done (s : St) :
    (Telescope.done (round := round) (step := step) s).toSpec = .done := rfl

@[simp]
theorem toSpec_extend (s : St)
    (cont :
      (pt : PublicTranscript (round s)) → Telescope round step (step s pt)) :
    (Telescope.extend s cont).toSpec =
      (round s).append (fun pt => (cont pt).toSpec) := rfl

/-- Constant-shape telescopes: every state runs the same round spec and the
state transition ignores the public transcript. -/
def replicate (spec : Oracle.Spec) (next : St → St) :
    (depth : Nat) → (s : St) →
      Telescope (round := fun _ => spec)
        (step := fun s _ => next s) s
  | 0, s => .done s
  | n + 1, s => .extend s (fun _ => replicate spec next n (next s))

@[simp]
theorem toSpec_replicate_zero (spec : Oracle.Spec) (next : St → St) (s : St) :
    (replicate (St := St) spec next 0 s).toSpec = .done := rfl

@[simp]
theorem toSpec_replicate_succ (spec : Oracle.Spec) (next : St → St) (n : Nat)
    (s : St) :
    (replicate (St := St) spec next (n + 1) s).toSpec =
      spec.append (fun _ => (replicate spec next n (next s)).toSpec) := rfl

/-! ## Decoration lifts

A telescope on its own carries no information about who controls each round
or what oracle interfaces are exposed. Decorations are layered on top by
specifying, for each state `s : St`, the role and oracle assignments for
that state's round spec. The lift functions then flatten state-indexed
decoration families along the telescope, threading them through
`Spec.RoleDeco.append` / `Spec.OracleDeco.append` at every `extend` step.

This per-state design is general enough for protocols whose decorations
depend only on the round shape (which is what the state already determines).
Path-dependent decorations are recovered by enriching the state space to
record the relevant prefix data. -/

/-- Lift a state-indexed `RoleDeco` family to a `RoleDeco` on the flattened
telescope. At each `.extend` step, the round's role decoration is appended
with the recursive role decorations of every continuation branch. -/
def toRoleDeco (rd : (s : St) → RoleDeco (round s)) :
    {s : St} → (t : Telescope round step s) → RoleDeco t.toSpec
  | _, .done _ => ⟨⟩
  | _, .extend s cont =>
      RoleDeco.append (round s) (fun pt => (cont pt).toSpec)
        (rd s) (fun pt => toRoleDeco rd (cont pt))

@[simp]
theorem toRoleDeco_done (rd : (s : St) → RoleDeco (round s)) (s : St) :
    toRoleDeco (step := step) rd (.done s) = ⟨⟩ := rfl

@[simp]
theorem toRoleDeco_extend (rd : (s : St) → RoleDeco (round s)) (s : St)
    (cont :
      (pt : PublicTranscript (round s)) → Telescope round step (step s pt)) :
    toRoleDeco rd (.extend s cont) =
      RoleDeco.append (round s) (fun pt => (cont pt).toSpec)
        (rd s) (fun pt => toRoleDeco rd (cont pt)) := rfl

/-- Lift a state-indexed `OracleDeco` family to an `OracleDeco` on the
flattened telescope. At each `.extend` step, the round's oracle decoration
is appended with the recursive oracle decorations of every continuation
branch. -/
def toOracleDeco (od : (s : St) → OracleDeco (round s)) :
    {s : St} → (t : Telescope round step s) → OracleDeco t.toSpec
  | _, .done _ => ⟨⟩
  | _, .extend s cont =>
      OracleDeco.append (round s) (fun pt => (cont pt).toSpec)
        (od s) (fun pt => toOracleDeco od (cont pt))

@[simp]
theorem toOracleDeco_done (od : (s : St) → OracleDeco (round s)) (s : St) :
    toOracleDeco (step := step) od (.done s) = ⟨⟩ := rfl

@[simp]
theorem toOracleDeco_extend (od : (s : St) → OracleDeco (round s)) (s : St)
    (cont :
      (pt : PublicTranscript (round s)) → Telescope round step (step s pt)) :
    toOracleDeco od (.extend s cont) =
      OracleDeco.append (round s) (fun pt => (cont pt).toSpec)
        (od s) (fun pt => toOracleDeco od (cont pt)) := rfl

end Telescope
end Spec
end Interaction.Oracle

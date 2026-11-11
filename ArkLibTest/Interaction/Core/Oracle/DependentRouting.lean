/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Composition

/-!
# A public message may change the final claim type

A prefix exports its input oracle unchanged. The prover then announces whether the exported
input is zero, and the suffix verifier checks the announcement with one query. That public
Boolean changes both the final statement type and the realization type of the final oracle
family: on `true` the statement is `()` and the final oracle is the input itself; on `false` the
statement is the input value and the final oracle is a pair answering its first component.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle OracleComp

namespace Interaction.Core.DependentRoutingTests

/-- No ambient oracle is ever queried. -/
abbrev ambient : OracleSpec Empty := Empty →ₒ Nat

/-- A natural number answers the unit query with itself. -/
@[reducible]
def natInterface : OracleInterface Nat where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := read

/-- A pair answers the unit query with its first component. -/
@[reducible]
def pairInterface : OracleInterface (Nat × Nat) where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read).1

/-- One natural-number input oracle. -/
@[instance_reducible]
def inputFamily : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩

/-- The prefix has no rounds. -/
abbrev done : OracleProtocol := .pure ⟨⟩

/-- The suffix receives one public Boolean from the prover. -/
abbrev suffix : OracleProtocol := .liftBind (.message Bool) (fun _ => .pure ⟨⟩)

/-- The composed protocol. -/
abbrev combined : OracleProtocol := done.append (fun _ => suffix)

/-- The final statement type: `Unit` after `true`, a natural number after `false`. -/
def finalStmt : Path suffix → Type
  | ⟨true, _⟩ => Unit
  | ⟨false, _⟩ => Nat

/-- The final oracle data: a natural number after `true`, a pair after `false`. -/
def finalData : (p : Path suffix) → Unit → Type
  | ⟨true, _⟩, _ => Nat
  | ⟨false, _⟩, _ => Nat × Nat

/-- The final oracle family, whose realization type depends on the public Boolean. -/
def finalFamily : (p : Path suffix) → OracleFamily Unit (finalData p)
  | ⟨true, _⟩ => ⟨fun _ => natInterface⟩
  | ⟨false, _⟩ => ⟨fun _ => pairInterface⟩

/-- The prefix accepts with `()` and exports its input oracle unchanged. -/
def exportInput : OracleVerifier ambient done Unit (fun _ => Unit) inputFamily
    (fun _ => inputFamily) where
  decide _ _ _ := pure ()
  outputMap _ _ _ := OracleMap.fst _ _

/-- The resources visible to the suffix at a completed suffix path. -/
abbrev suffixResources (p : Path suffix) := pathResources inputFamily suffix p

/-- Query the exported input through its interface. -/
def queryInput (p : Path suffix) :
    OptionT (OracleComp (ambient + (suffixResources p).spec)) Nat :=
  liftM ((ambient + (suffixResources p).spec).query (.inr (.inl ⟨(), ()⟩)))

/-- Route the final unit query to the input, which answers the input value. -/
def finalMap : (p : Path suffix) → OracleMap (suffixResources p) (finalFamily p)
  | ⟨true, ⟨⟩⟩ =>
    { f := fun x _ => x.1 ()
      impl := fun q =>
        liftM ((suffixResources ⟨true, ⟨⟩⟩).spec.query (.inl ⟨(), q.2⟩))
      law := fun _ _ => rfl }
  | ⟨false, ⟨⟩⟩ =>
    { f := fun x _ => (x.1 (), x.1 ())
      impl := fun q =>
        liftM ((suffixResources ⟨false, ⟨⟩⟩).spec.query (.inl ⟨(), q.2⟩))
      law := fun _ _ => rfl }

/-- The suffix checks the announced Boolean against one input query. It returns `()` after a
correct `true` and the queried value after a correct `false`. -/
def announce : OracleVerifier ambient suffix Unit finalStmt inputFamily finalFamily where
  decide _ p _ := by
    rcases p with ⟨_ | _, ⟨⟩⟩
    · exact do
        let answer ← queryInput ⟨false, ⟨⟩⟩
        if answer = 0 then failure else pure answer
    · exact do
        let answer ← queryInput ⟨true, ⟨⟩⟩
        if answer = 0 then pure () else failure
  outputMap _ p _ := finalMap p

/-- The prefix accepts only `()`, so its output map is compatible with the suffix's. -/
def compatible :
    OracleVerifier.OutputCompatibility exportInput (fun _ => announce) :=
  .ofStatement _ _ (fun _ _ _ => ()) fun _ _ _ _ _ _ => rfl

/-- The composed verifier. Its output statement and oracle family follow the public Boolean. -/
def composite := exportInput.append (fun _ => announce) compatible

/-- The prover announces whether its input is zero and keeps a branch-dependent private result.
-/
def prover (input : Nat) : Prover oracleSig ambient combined (fun _ => Nat) :=
  pure ⟨decide (input = 0), pure (if input = 0 then 13 else 29)⟩

/-- A prover that announces a fixed Boolean, whatever the input. -/
def announcer (b : Bool) : Prover oracleSig ambient combined (fun _ => Nat) :=
  pure ⟨b, pure 0⟩

/-- Read the statement (zero for the unit statement) and the final oracle's answer at the unit
query, through the family selected by the actual path. -/
def readClaim : (p : Path suffix) → finalStmt p × (∀ j, finalData p j) → Nat × Nat
  | ⟨true, ⟨⟩⟩, claim =>
    (0, (finalFamily ⟨true, ⟨⟩⟩).behaviorOfRealizations claim.2 ⟨(), ()⟩)
  | ⟨false, ⟨⟩⟩, claim =>
    (claim.1, (finalFamily ⟨false, ⟨⟩⟩).behaviorOfRealizations claim.2 ⟨(), ()⟩)

/-- The composed run never queries an oracle: the ambient spec is empty and there are no
challenges. -/
def noQueries : QueryImpl (ambient + challengeSpec oracleSig combined) Id
  | .inl e => e.elim
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, c⟩, _⟩ => c.elim

/-- Run the composed verifier on one input value and report the public Boolean, the prover's
private result, and the read-out of the accepted claim. -/
def observed (input : Nat) : Bool × Nat × Option (Nat × Nat) :=
  let obs := simulateQ noQueries (composite.run () (fun _ => input) (prover input))
  ((projectPathAlong oracleSig combined obs.1).1, obs.2.1,
    obs.2.2.map (readClaim (projectPathAlong oracleSig combined obs.1)))

/-- Zero selects the unit statement and the input itself as the final oracle. -/
example : observed 0 = (true, 13, some (0, 0)) := rfl

/-- A nonzero input selects the input value as the statement and a pair as the final oracle,
which answers the pair's first component. -/
example : observed 7 = (false, 29, some (7, 7)) := rfl

/-- On the `false` branch the materialized final oracle is the pair of input copies. -/
example : (simulateQ noQueries (composite.run () (fun _ => 7) (prover 7))).2.2.map
    (fun claim => (claim.2 () : Nat × Nat)) = some (7, 7) := rfl

/-- A prover that announces `false` for the zero input is rejected. -/
example : (simulateQ noQueries (composite.run () (fun _ => 0) (announcer false))).2.2.isNone =
    true := rfl

/-- A prover that announces `true` for a nonzero input is rejected. -/
example : (simulateQ noQueries (composite.run () (fun _ => 7) (announcer true))).2.2.isNone =
    true := rfl

run_cmd do
  unless observed 0 == (true, 13, some (0, 0)) do throwError "the true branch routes wrongly"
  unless observed 7 == (false, 29, some (7, 7)) do throwError "the false branch routes wrongly"

end Interaction.Core.DependentRoutingTests

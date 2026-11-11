/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.Routing
import ArkLib.Interaction.Core.Oracle.LoggedExecution
import ArkLibTest.Interaction.Core.Support
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-! Routed oracle access in a composition. The prefix receives one oracle and exports a view that
reads it twice. The suffix receives another oracle and its decision reads the export and its own
fresh slot. Availability is typing: the routed suffix decision is a program over the inputs and
the oracles of the completed composed path, and the prefix decision, routed into the composed run,
never reaches the suffix slot. Both routed reads of the export name the same prefix slot. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

universe uI uD wI wJ

namespace Interaction.Core.QueryBoundsTests

/-- Ambient queries carry tags. -/
abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

/-- No input oracles; also the empty output family. -/
def none' : OracleFamily PEmpty (fun i => PEmpty.elim i) :=
  ⟨fun i => i.elim⟩

/-- The empty input data. -/
def noData : ∀ i : PEmpty, PEmpty.elim i := fun i => i.elim

/-- One scalar oracle send; both components of the composition are this protocol. -/
def single : OracleProtocol :=
  .liftBind (.oracle Nat OracleInterface.instDefault) (fun _ => .pure ⟨⟩)

/-- The prefix send, then the suffix send. -/
abbrev combined : OracleProtocol := single.append (fun _ => single)

/-- The only shape path of `single`. -/
abbrev singlePath : Path single := ⟨⟨⟩, ⟨⟩⟩

/-- The only shape path of `combined`. -/
abbrev combinedPath : Path combined := ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- One exported scalar oracle. -/
def exported : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The prefix decision resources. -/
abbrev prefixResources := pathResources none' single singlePath

/-- The suffix decision resources. -/
abbrev suffixResources := pathResources exported single singlePath

/-- The resources of a decision on the composed path: the inputs and both sends. -/
abbrev rawResources := pathResources none' combined combinedPath

/-- Export twice the prefix message, reading the same prefix slot twice. -/
def view : OracleMap prefixResources exported where
  f x _ := (show Nat from x.2 (.inl ⟨⟩)) + (show Nat from x.2 (.inl ⟨⟩))
  impl _ := do
    let left : Nat ← liftM (prefixResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    let right : Nat ← liftM (prefixResources.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    pure (left + right)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The prefix decision accepts; its output map is `view`. -/
def prefixVerifier :
    OracleVerifier ambient single Unit (fun _ => Unit) none' (fun _ => exported) where
  decide _ _ _ := pure ()
  outputMap _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact view

/-- The suffix decision program: read the export, then the suffix's own slot, and add. -/
def suffixProgram : OracleComp (ambient + suffixResources.spec) Nat := do
  let old : Nat ← liftM ((ambient + suffixResources.spec).query (.inr (.inl ⟨(), ()⟩)))
  let fresh : Nat ← liftM ((ambient + suffixResources.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
  pure (old + fresh)

/-- The empty output map. -/
def noOutput (In : Resources.{0, uI, uD}) : OracleMap In none' where
  f _ i := i.elim
  impl q := q.1.elim
  law _ q := q.1.elim

/-- The suffix decision runs `suffixProgram`; it has no output oracles. -/
def suffixVerifier :
    OracleVerifier ambient single Unit (fun _ => Nat) exported (fun _ => none') where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact liftM suffixProgram
  outputMap _ _ _ := noOutput _

/-- No output oracles, so the composite output map is trivially compatible. -/
def compatible : OracleVerifier.OutputCompatibility prefixVerifier (fun _ => suffixVerifier) where
  outputMap _ _ _ := noOutput _
  agrees _ _ _ _ _ _ := funext fun i => i.elim

/-- The composed verifier. -/
def composed := prefixVerifier.append (fun _ => suffixVerifier) compatible

/-- The prover sends the answer to query `a`, then the answer to query `b`, and keeps their sum. -/
def prover (a b : Nat) : Prover oracleSig ambient combined (fun _ => Nat) :=
  Prover.append (s₂ := fun _ => single)
    (do
      let first : Nat ← liftM (ambient.query a)
      pure ⟨first, pure first⟩)
    (fun _ first => pure (do
      let second : Nat ← liftM (ambient.query b)
      pure ⟨second, pure (first + second)⟩))

/-- The prefix slot of the composed resources. -/
abbrev prefixSlot : rawResources.spec.Domain := (.inr ⟨.inl ⟨⟩, ()⟩)

/-- The suffix slot of the composed resources. -/
abbrev suffixSlot : rawResources.spec.Domain := (.inr ⟨.inr (.inl ⟨⟩), ()⟩)

/-- The prefix and suffix queries name distinct sent oracles. -/
theorem prefixSlot_ne_suffixSlot : prefixSlot ≠ suffixSlot := by
  intro h
  cases h

/-- The suffix route of the composition at a view of the composed path. -/
abbrev route (v : View combined combinedPath) :=
  (OracleVerifier.suffixRoute prefixVerifier () combinedPath v).withAmbient ambient

-- QueryBounds 4, restated: availability is typing. The suffix decision routed by `suffixRoute`
-- is a program over the ambient oracle and the resources of the completed composed path.
/-- The routed suffix decision. -/
def routedSuffix (v : View combined combinedPath) :
    OracleComp (ambient + rawResources.spec) Nat :=
  simulateQ (route v) suffixProgram

-- QueryBounds 7, restated: names are retired. Both routed reads of the export query the same
-- prefix slot of the composed resources; the suffix's own read queries the suffix slot, which is
-- distinct.
example (v : View combined combinedPath) :
    (OracleVerifier.suffixRoute prefixVerifier () combinedPath v).impl (.inl ⟨(), ()⟩) = (do
      let left : Nat ← liftM (rawResources.spec.query prefixSlot)
      let right : Nat ← liftM (rawResources.spec.query prefixSlot)
      pure (left + right)) := rfl

example (v : View combined combinedPath) :
    (OracleVerifier.suffixRoute prefixVerifier () combinedPath v).impl (.inr ⟨.inl ⟨⟩, ()⟩) =
      (liftM (rawResources.spec.query suffixSlot) : OracleComp rawResources.spec Nat) := rfl

example : prefixSlot ≠ suffixSlot := prefixSlot_ne_suffixSlot

/-- The route of the prefix decision into the composed run. -/
abbrev prefixRoute :=
  (OracleVerifier.prefixRoute (inputs := none') (s₁ := single) (s₂ := fun _ => single)
    combinedPath).withAmbient ambient

-- QueryBounds 6, restated: at the join, the prefix decision's resources are the inputs and the
-- prefix oracles, which have no index for the suffix send. Routed into the composed run, every
-- prefix decision program, whatever its cost, queries only ambient oracles and the prefix slot,
-- never the suffix slot. The budget clause of the frozen row is moot.
example : (PEmpty ⊕ oracleIdx single (Path.split single (fun _ => single) combinedPath).1) =
    (PEmpty.{1} ⊕ (PUnit.{1} ⊕ PEmpty.{1})) := rfl

example : True := by
  fail_if_success
    have _ : prefixResources.spec.Domain := (.inr ⟨.inr (.inl ⟨⟩), ()⟩)
  trivial

/-- Routing any prefix decision excludes the suffix oracle query. -/
theorem future_rejected {α : Type} (program : OracleComp (ambient + prefixResources.spec) α) :
    AllQueriesSatisfy (simulateQ prefixRoute program) (· ≠ .inr suffixSlot) := by
  refine (allQueriesSatisfy_of_forall (fun _ => True.intro) program).simulateQ fun q _ => ?_
  rcases q with q | (⟨i, q⟩ | ⟨⟨⟩ | i, q⟩)
  · exact (allQueriesSatisfy_query_iff _ _).mpr Sum.inl_ne_inr
  · exact i.elim
  · cases q
    refine (allQueriesSatisfy_query_iff (spec := ambient + rawResources.spec)
      (.inr prefixSlot) _).mpr ?_
    intro h
    exact prefixSlot_ne_suffixSlot (Sum.inr.inj h)
  · exact i.elim

-- QueryBounds 15, restated as row 6: the actual join is the prefix component of the only
-- composed path, and its routed queries never reach the suffix slot.
example {α : Type} (program : OracleComp (ambient + prefixResources.spec) α) :
    AllQueriesSatisfy (simulateQ prefixRoute program) (· ≠ .inr suffixSlot) :=
  future_rejected program

/-- Answer each ambient tag with itself; there are no challenges. -/
def tagHandler : QueryImpl (ambient + challengeSpec oracleSig combined) Id
  | .inl n => pure n
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- The composed run under `tagHandler`, with independent input index and query universes. -/
def observed.{vI, qI, qJ} (a b : Nat) :=
  simulateQ tagHandler (composed.{vI, 0, qI, qJ}.run () noData (prover a b))

-- QueryBounds 9 and 10, restated: phases are retired. For all tags `a` and `b`, the composed
-- run sends `a` then `b`, keeps `a + b` and accepts `2a + b`. Its transcript is the append of the
-- prefix transcript `⟨a⟩` and the suffix transcript `⟨b⟩`, and splitting its payloads gives the
-- prefix payload `a` (row 9) and the suffix payload `b` (row 10).
example (a b : Nat) :
    ((observed.{uI, wI, wJ} a b).1, (observed.{uI, wI, wJ} a b).2.1,
      (observed.{uI, wI, wJ} a b).2.2.map Prod.fst) =
    (PathAlong.append oracleSig single (fun _ => single) ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩, a + b,
      some (a + a + b)) := by
  unfold observed composed
  rw [OracleVerifier.run_append]
  kernel_rfl

example (a b : Nat) :=
  splitOracles_payloads single (fun _ => single) (⟨a, ⟨⟩⟩ : PathAlong oracleSig single)
    (⟨b, ⟨⟩⟩ : PathAlong oracleSig single)

example (a b : Nat) : (splitOracles single (fun _ => single) combinedPath).f
    (payloads combined (PathAlong.append oracleSig single (fun _ => single) ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩))
    (.inl (.inl ⟨⟩)) = a := rfl

example (a b : Nat) : (splitOracles single (fun _ => single) combinedPath).f
    (payloads combined (PathAlong.append oracleSig single (fun _ => single) ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩))
    (.inr (.inl ⟨⟩)) = b := rfl

-- The full decision log fixes input indices and queries to `Type`; output queries stay
-- independent. See interaction rebuild implementation note 18.
/-- Private output, verdict and every raw decision query of the composed logged run. -/
def loggedSummary.{qJ} (a b : Nat) :
    Nat × Option Nat × QueryLog (ambient + rawResources.spec) :=
  let result := simulateQ tagHandler
    (composed.{0, 0, 0, qJ}.runWithLog () noData (prover a b))
  (result.1.2.1, result.1.2.2.map Prod.fst, result.2.2)

/-- One exported query expands into two separately recorded prefix reads, then the suffix read.
The same run keeps the private sum and accepts with the doubled prefix plus the suffix. -/
theorem loggedSummary_eq (a b : Nat) :
    loggedSummary.{wJ} a b =
      (a + b, some (a + a + b),
        [⟨.inr prefixSlot, a⟩, ⟨.inr prefixSlot, a⟩, ⟨.inr suffixSlot, b⟩]) := by
  kernel_rfl

/-- Prefix value one and suffix value two recover the concrete repeated-read observation. -/
example : loggedSummary.{0} 1 2 =
    (3, some 4,
      [⟨.inr prefixSlot, (1 : Nat)⟩, ⟨.inr prefixSlot, (1 : Nat)⟩,
        ⟨.inr suffixSlot, (2 : Nat)⟩]) :=
  loggedSummary_eq 1 2

end Interaction.Core.QueryBoundsTests

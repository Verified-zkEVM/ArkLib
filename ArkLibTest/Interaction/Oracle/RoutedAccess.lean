/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Routing
import ArkLib.Interaction.Oracle.SentOracles
import ArkLibTest.Interaction.Support
import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-! Routed oracle access in a composition. The prefix receives one oracle and exports a view that
reads it twice. The suffix receives another oracle and its decision reads the export and its own
fresh oracle. Availability is typing. The routed suffix decision is a program over the inputs and
the oracles of the completed composed path. The prefix decision, routed into the composed run,
never reaches the suffix oracle. Both routed reads of the export name the same prefix oracle. -/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle Interaction.TwoParty.Lens
  OracleComp OracleSpec

universe uI uD wI wJ

namespace Interaction.RoutedAccessTests

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

/-- The only path of `single`. -/
abbrev singlePath : Path single := ⟨⟨⟩, ⟨⟩⟩

/-- The only path of `combined`. -/
abbrev combinedPath : Path combined := ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- One exported scalar oracle. -/
def exported : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The prefix decision bundle. -/
abbrev prefixBundle := pathBundle none' single singlePath

/-- The suffix decision bundle. -/
abbrev suffixBundle := pathBundle exported single singlePath

/-- The bundle of a decision on the composed path: the inputs and both sends. -/
abbrev rawBundle := pathBundle none' combined combinedPath

/-- Export twice the prefix message, reading the same prefix oracle twice. -/
def view : OracleMap prefixBundle exported where
  f x _ := (show Nat from x.2 (.inl ⟨⟩)) + (show Nat from x.2 (.inl ⟨⟩))
  impl.toFun _ := do
    let left : Nat ← liftM (prefixBundle.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
    let right : Nat ← liftM (prefixBundle.spec.query (.inr ⟨.inl ⟨⟩, ()⟩))
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

/-- The suffix decision program: read the export, then the suffix's own oracle, and add. -/
def suffixProgram : OracleComp (ambient + suffixBundle.spec) Nat := do
  let old : Nat ← liftM ((ambient + suffixBundle.spec).query (.inr (.inl ⟨(), ()⟩)))
  let fresh : Nat ← liftM ((ambient + suffixBundle.spec).query (.inr (.inr ⟨.inl ⟨⟩, ()⟩)))
  pure (old + fresh)

/-- The empty output map. -/
def noOutput (In : OracleBundle.{0, uI, uD}) : OracleMap In none' where
  f _ i := i.elim
  impl.toFun q := q.1.elim
  law _ q := q.1.elim

/-- The suffix decision runs `suffixProgram`; it has no output oracles. -/
def suffixVerifier :
    OracleVerifier ambient single Unit (fun _ => Nat) exported (fun _ => none') where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact liftM suffixProgram
  outputMap _ _ _ := noOutput _

/-- With no output oracles, the compatibility condition ranges over an empty index type. -/
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

/-- The query to the prefix oracle in the composed bundle. -/
abbrev prefixSlot : rawBundle.spec.Domain := (.inr ⟨.inl ⟨⟩, ()⟩)

/-- The query to the suffix oracle in the composed bundle. -/
abbrev suffixSlot : rawBundle.spec.Domain := (.inr ⟨.inr (.inl ⟨⟩), ()⟩)

/-- The prefix and suffix queries name distinct sent oracles. -/
theorem prefixSlot_ne_suffixSlot : prefixSlot ≠ suffixSlot := by
  intro h
  cases h

/-- The suffix route of the composition at a view of the composed path. -/
abbrev route (v : View combined combinedPath) :=
  (OracleVerifier.suffixRoute prefixVerifier () combinedPath v).withAmbient ambient

-- QueryBounds 4, restated: availability is typing. The suffix decision routed by `suffixRoute`
-- is a program over the ambient oracle and the bundle of the completed composed path.
/-- The routed suffix decision. -/
def routedSuffix (v : View combined combinedPath) :
    OracleComp (ambient + rawBundle.spec) Nat :=
  simulateQ (route v) suffixProgram

-- QueryBounds 7, restated: node names are removed. Both routed reads of the export query the same
-- prefix oracle of the composed bundle. The suffix's own read queries the suffix oracle, which is
-- distinct.
example (v : View combined combinedPath) :
    (OracleVerifier.suffixRoute prefixVerifier () combinedPath v).impl (.inl ⟨(), ()⟩) = (do
      let left : Nat ← liftM (rawBundle.spec.query prefixSlot)
      let right : Nat ← liftM (rawBundle.spec.query prefixSlot)
      pure (left + right)) := rfl

example (v : View combined combinedPath) :
    (OracleVerifier.suffixRoute prefixVerifier () combinedPath v).impl (.inr ⟨.inl ⟨⟩, ()⟩) =
      (liftM (rawBundle.spec.query suffixSlot) : OracleComp rawBundle.spec Nat) := rfl

example : prefixSlot ≠ suffixSlot := prefixSlot_ne_suffixSlot

/-- The route of the prefix decision into the composed run. -/
abbrev prefixRoute :=
  (OracleVerifier.prefixRoute (inputs := none') (s₁ := single) (s₂ := fun _ => single)
    combinedPath).withAmbient ambient

-- QueryBounds 6, restated: at the join, the prefix decision's bundle consists of the inputs and
-- the prefix oracles, which have no index for the suffix send. Routed into the composed run, every
-- prefix decision program, whatever its cost, queries only ambient oracles and the prefix
-- oracle, never the suffix oracle. The budget clause of the old-layer row is moot.
example :
    (PEmpty ⊕ OracleMessageIndex single (Path.split single (fun _ => single) combinedPath).1) =
    (PEmpty.{1} ⊕ (PUnit.{1} ⊕ PEmpty.{1})) := rfl

example : True := by
  fail_if_success
    have _ : prefixBundle.spec.Domain := (.inr ⟨.inr (.inl ⟨⟩), ()⟩)
  trivial

/-- Routing any prefix decision excludes the suffix oracle query. -/
theorem future_rejected {α : Type} (program : OracleComp (ambient + prefixBundle.spec) α) :
    AllQueriesSatisfy (simulateQ prefixRoute program) (· ≠ .inr suffixSlot) := by
  refine (allQueriesSatisfy_of_forall (fun _ => True.intro) program).simulateQ fun q _ => ?_
  rcases q with q | (⟨i, q⟩ | ⟨⟨⟩ | i, q⟩)
  · exact (allQueriesSatisfy_query_iff _ _).mpr Sum.inl_ne_inr
  · exact i.elim
  · cases q
    refine (allQueriesSatisfy_query_iff (spec := ambient + rawBundle.spec)
      (.inr prefixSlot) _).mpr ?_
    intro h
    exact prefixSlot_ne_suffixSlot (Sum.inr.inj h)
  · exact i.elim

-- QueryBounds 15, restated as row 6: the actual join is the prefix component of the only
-- composed path, and its routed queries never reach the suffix oracle.
example {α : Type} (program : OracleComp (ambient + prefixBundle.spec) α) :
    AllQueriesSatisfy (simulateQ prefixRoute program) (· ≠ .inr suffixSlot) :=
  future_rejected program

/-- Answer each ambient tag with itself; there are no challenges. -/
def tagHandler : QueryImpl (ambient + challengeSpec oracleSig combined) Id where
  toFun
  | .inl n => pure n
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- The composed run under `tagHandler`, with independent input index and query universes. -/
def observed.{vI, qI, qJ} (a b : Nat) :=
  simulateQ tagHandler (composed.{vI, qI, 0, qJ}.run () noData (prover a b))

-- Additional oracle message checks beside the produced partial-transcript assertions in
-- LoggedExecution. For all tags `a` and `b`, the composed
-- run sends `a` then `b`, keeps `a + b` and accepts `2a + b`. Its transcript is the append of the
-- prefix transcript `⟨a⟩` and the suffix transcript `⟨b⟩`. Splitting its oracle messages gives
-- the prefix oracle message `a` (row 9) and the suffix oracle message `b` (row 10).
example (a b : Nat) :
    ((observed.{uI, wI, wJ} a b).1, (observed.{uI, wI, wJ} a b).2.1,
      (observed.{uI, wI, wJ} a b).2.2.map Prod.fst) =
    (Transcript.append (l := oracleSig) single (fun _ => single) ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩, a + b,
      some (a + a + b)) := by
  unfold observed composed
  rw [OracleVerifier.run_append]
  kernel_rfl

example (a b : Nat) :=
  splitOracleMessages_oracleMessages single (fun _ => single)
    (⟨a, ⟨⟩⟩ : Transcript oracleSig single) (⟨b, ⟨⟩⟩ : Transcript oracleSig single)

example (a b : Nat) : (splitOracleMessages single (fun _ => single) combinedPath).f
    (oracleMessages combined
      (Transcript.append (l := oracleSig) single (fun _ => single) ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩))
    (.inl (.inl ⟨⟩)) = a := rfl

example (a b : Nat) : (splitOracleMessages single (fun _ => single) combinedPath).f
    (oracleMessages combined
      (Transcript.append (l := oracleSig) single (fun _ => single) ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩))
    (.inr (.inl ⟨⟩)) = b := rfl

-- The full decision log fixes input indices and queries to `Type`; output queries stay
-- independent. See interaction rebuild implementation note 18.
/-- Private output, verdict and every raw decision query of the composed logged run. -/
def loggedSummary.{qJ} (a b : Nat) :
    Nat × Option Nat × QueryLog (ambient + rawBundle.spec) :=
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

/-- Prefix value one and suffix value two recover the concrete repeated-read outcome. -/
example : loggedSummary.{0} 1 2 =
    (3, some 4,
      [⟨.inr prefixSlot, (1 : Nat)⟩, ⟨.inr prefixSlot, (1 : Nat)⟩,
        ⟨.inr suffixSlot, (2 : Nat)⟩]) :=
  loggedSummary_eq 1 2

/-- The composed verifier's queries by move for the same tag-answering execution. -/
def composedQueriesByMove (a b : Nat) :
    OracleVerifier.QueriesByMove composed.{0, 0, 0, 0} (fun _ => Nat) :=
  simulateQ tagHandler (composed.runWithQueriesByMove () noData (prover a b))

/-- The queries-by-move result records the same raw decision queries as the logged run: two reads
of the prefix oracle, then one read of the suffix oracle. -/
theorem composed_decisionQueries (a b : Nat) :
    (composedQueriesByMove a b).decisionQueries =
      [⟨.inr prefixSlot, a⟩, ⟨.inr prefixSlot, a⟩, ⟨.inr suffixSlot, b⟩] := by
  kernel_rfl

/-- A raw query has its node name among the nodes of the available bundle at the decision entry. -/
def rawAvailable (a b : Nat) (q : rawBundle.spec.Domain) : Prop :=
  ∃ i : ((composedQueriesByMove a b).decision.availableContext none').Index,
    PartialTranscript.queryNode none' (composedQueriesByMove a b).decision.before i =
      PartialTranscript.queryNode none'
        (PartialTranscript.ofTranscript (l := oracleSig) combined ⟨a, b, ⟨⟩⟩) q

/-- Every raw query names an oracle of the bundle available at the partial transcript of this
execution's decision entry. -/
theorem raw_available (a b : Nat) (q : rawBundle.spec.Domain) : rawAvailable a b q := by
  have decision_before_eq : (composedQueriesByMove a b).decision.before =
      PartialTranscript.ofTranscript (l := oracleSig) combined ⟨a, b, ⟨⟩⟩ := by kernel_rfl
  unfold rawAvailable
  generalize entry_eq : (composedQueriesByMove a b).decision = entry
  rw [entry_eq] at decision_before_eq
  dsimp only [QueriesAt.availableContext]
  rw [decision_before_eq]
  exact ⟨q, rfl⟩

/-- Ambient queries are unrestricted; bundle queries must name an oracle of the bundle available at
the decision entry. -/
def decisionAllowed (a b : Nat) : (ambient + rawBundle.spec).Domain → Prop
  | .inl _ => True
  | .inr q => rawAvailable a b q

/-- The same routed program used by the cost bound only queries the bundle available at the
decision entry. -/
theorem routed_available (a b : Nat) (v : View combined combinedPath) :
    AllQueriesSatisfy (routedSuffix v) (decisionAllowed a b) := by
  apply allQueriesSatisfy_of_forall
  intro q
  cases q with
  | inl _ => trivial
  | inr q => exact raw_available a b q

end Interaction.RoutedAccessTests

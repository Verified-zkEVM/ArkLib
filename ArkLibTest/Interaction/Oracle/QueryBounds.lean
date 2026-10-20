/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.OracleComp.QueryBounds
import ArkLib.Interaction.Oracle.Prefix
import ArkLib.Interaction.Oracle.SourceRouting
import ArkLib.Interaction.Oracle.PhasedRun

/-!
# Actual exported source access and weighted query cost

The native prefix receives an oracle and exports a view that reads it twice. The suffix receives
another oracle and queries the exported view and its own fresh slot. The actual logged execution
preserves multiplicity, slot identity, answers, the closed claim, and private prover memory.
The same symbolic route has a weighted budget of five; a future slot fails syntactic availability
before it is sent, regardless of its cost budget. The actual phase list supplies the join and
terminal prefixes, and its context inclusion retains earlier names.
-/

namespace Interaction.Oracle.QueryBoundsTest

open OracleComp OracleSpec
open PFunctor.FreeM.Displayed (Decoration)

abbrev ambient : OracleSpec Nat := Nat →ₒ Nat
abbrev initial : PFunctor := (Empty →ₒ Unit).toPFunctor
@[reducible] def interface : OracleInterface Nat where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := do return (← read)
abbrev firstProtocol : Protocol := .oracleWith Nat interface .done
abbrev secondProtocol : Protocol := .oracleWith Nat interface .done
abbrev combined : Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun _ => secondProtocol.tree),
    Decoration.append firstProtocol.roles (fun _ => secondProtocol.roles),
    Decoration.append firstProtocol.oracles (fun _ => secondProtocol.oracles)⟩
abbrev exported : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => interface⟩
abbrev output : OracleFamily Empty (fun _ => Unit) := ⟨Empty.elim⟩
abbrev prefixAccess := Access.extend initial interface
abbrev suffixAccess := Access.extend exported.spec.toPFunctor interface
abbrev finalAccess := Access.extend prefixAccess interface

/-- Two references to the same actual prefix slot, rather than two resource identities. -/
def view : VirtualOracle (ofPFunctor prefixAccess) exported := ⟨fun _ => do
  let left : Nat ← liftM ((ofPFunctor prefixAccess).query (.inr ()))
  let right : Nat ← liftM ((ofPFunctor prefixAccess).query (.inr ()))
  return left + right⟩

def suffixProgram : OracleComp (ofPFunctor suffixAccess) Nat := do
  let old : Nat ← liftM ((ofPFunctor suffixAccess).query (.inl ⟨(), ()⟩))
  let fresh : Nat ← liftM ((ofPFunctor suffixAccess).query (.inr ()))
  return old + fresh

def route : QueryImpl (ofPFunctor suffixAccess) (OracleComp (ofPFunctor finalAccess)) :=
  TypeTree.routeAfter secondProtocol.tree secondProtocol.oracles exported.spec.toPFunctor
    prefixAccess view.query ⟨PUnit.unit, PUnit.unit⟩

def firstVerifier : Verifier.Fragment ambient firstProtocol.tree firstProtocol.roles
    firstProtocol.oracles initial (fun _ => OpenClaim (ofPFunctor prefixAccess) Unit exported) :=
  pure ⟨(), view⟩

def secondVerifier (_ : firstProtocol.tree.BranchPath) (_ : Unit) :
    Verifier.Strategy ambient secondProtocol.tree secondProtocol.roles secondProtocol.oracles
      exported.spec.toPFunctor (fun _ => Option (OpenClaim (ofPFunctor suffixAccess) Nat output)) :=
  pure (do
    let value ← suffixProgram.liftComp (ambient + ofPFunctor suffixAccess)
    return some ⟨value, ⟨fun q => Empty.elim q.1⟩⟩)

def verifier : Verifier.Strategy ambient combined.tree combined.roles combined.oracles initial
    (TerminalClaim combined initial (fun _ => Nat) (fun _ => output)) :=
  Verifier.appendExported ambient firstProtocol.tree (fun _ => secondProtocol.tree)
    firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) initial
    (fun _ => Unit) (fun _ _ => Nat) (fun _ => exported)
    (fun _ => Nat) (fun _ _ => Unit) (fun _ => output) firstVerifier secondVerifier

/-- The actual residual prover retains the first ambient response in its private output. -/
def prover : Prover.Strategy ambient combined.tree combined.roles (fun _ => Nat) := do
  let first : Nat ← liftM (ambient.query 1)
  return ⟨first, do
    let second : Nat ← liftM (ambient.query 2)
    return ⟨second, first + second⟩⟩

def rawCost : CostModel (ofPFunctor finalAccess) Nat := ⟨fun q => match q with
  | .inl (.inl q) => Empty.elim q
  | .inl (.inr _) => 1
  | .inr _ => 3⟩

def sourceCost : CostModel (ofPFunctor suffixAccess) Nat := ⟨fun q => match q with
  | .inl _ => 2
  | .inr _ => 3⟩

theorem route_cost (q : (ofPFunctor suffixAccess).Domain) :
    WorstCaseCostBound (route q) rawCost (sourceCost.queryCost q) := by
  rcases q with (⟨⟨⟩, ⟨⟩⟩ | ⟨⟩)
  · change WorstCaseCostBound (do
      let left : Nat ← liftM ((ofPFunctor finalAccess).query (.inl (.inr ())))
      let right : Nat ← liftM ((ofPFunctor finalAccess).query (.inl (.inr ())))
      return left + right) rawCost 2
    apply worstCaseCostBound_bind _ _ rawCost 1 1
      (worstCaseCostBound_query _ rawCost)
    intro left
    apply worstCaseCostBound_bind _ _ rawCost 1 0
      (worstCaseCostBound_query _ rawCost)
    intro right result member
    change result ∈ support (costDist (pure (left + right)) rawCost) at member
    rw [costDist_pure, mem_support_pure_iff] at member
    subst result
    exact le_rfl
  · exact worstCaseCostBound_query (Sum.inr ()) rawCost


/-- The source program's nonuniform charges reserve the whole expansion. -/
theorem program_cost : WorstCaseCostBound suffixProgram sourceCost 5 := by
  apply worstCaseCostBound_bind _ _ sourceCost 2 3
    (worstCaseCostBound_query _ sourceCost)
  intro old
  apply worstCaseCostBound_bind _ _ sourceCost 3 0
    (worstCaseCostBound_query _ sourceCost)
  intro fresh result member
  change result ∈ support (costDist (pure (old + fresh)) sourceCost) at member
  rw [costDist_pure, mem_support_pure_iff] at member
  subst result
  exact le_rfl

/-- The actual exported route issues two old-slot calls and one fresh-slot call. -/
example : WorstCaseCostBound (simulateQ route suffixProgram) rawCost 5 :=
  worstCaseCostBound_simulateQ route suffixProgram sourceCost rawCost 5
    program_cost route_cost

open Interaction.Oracle.TypeTree PFunctor.FreeM in
/-- Concrete realizations of the two messages from the same native execution. -/
def afterBoth (first second : Nat) : ExecutionPrefix combined.tree :=
  ⟨Cursor.down (P := basePFunctor) (a := Position.oracle Nat)
    (next := fun _ => secondProtocol.tree) PUnit.unit
    (Cursor.down (P := basePFunctor) (a := Position.oracle Nat)
      (next := fun _ => TypeTree.done) PUnit.unit (Cursor.root TypeTree.done)),
    ⟨first, second, PUnit.unit⟩⟩

/-- The availability predicate uses the canonical name of each actual accumulated slot. -/
def rawAllowed (first second : Nat) (q : finalAccess.A) : Prop :=
  ∃ index : ((afterBoth first second).availableContext initial.A).Index,
    ((afterBoth first second).availableContext initial.A).name index =
      (afterBoth first second).queryName combined.oracles initial q

/-- Access is certified for the same route used by the cost theorem. -/
theorem routed_available (first second : Nat) :
    AllQueriesSatisfy (simulateQ route suffixProgram) (rawAllowed first second) := by
  apply allQueriesSatisfy_simulateQ route suffixProgram (fun _ => True)
    (rawAllowed first second)
  · induction suffixProgram using OracleComp.inductionOn with
    | pure value => exact allQueriesSatisfy_pure _ _
    | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, ih⟩
  · intro q _
    induction route q using OracleComp.inductionOn with
    | pure value => exact allQueriesSatisfy_pure _ _
    | query_bind raw next ih =>
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨(afterBoth first second).queryName_available combined.oracles initial raw, ih⟩

/-- The direct native logged executor observes repeated old answers and the fresh answer. -/
example :
    let result := simulateQ (fun tag => (tag : Id Nat))
      (executeStrategiesLogged ambient combined.tree combined.roles combined.oracles
        initial Empty.elim prover verifier)
    (result.proverOut, result.verifierOut.map (·.stmt),
      (result.sourceLog : QueryLog (ofPFunctor finalAccess))) =
      (3, some 4, [⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩,
        ⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩, ⟨Sum.inr (), (2 : Nat)⟩]) := by
  rfl


open Interaction.Oracle.TypeTree PFunctor.FreeM in
/-- Stop at the genuine join, before receiving the suffix message. -/
def afterFirst (first : Nat) : ExecutionPrefix combined.tree :=
  ⟨Cursor.down (P := basePFunctor) (a := Position.oracle Nat)
    (next := fun _ => secondProtocol.tree) PUnit.unit (Cursor.root secondProtocol.tree),
    ⟨first, PUnit.unit⟩⟩

/-- The future query has its exact canonical terminal name, not an arbitrary annotation. -/
theorem future_rejected (first second : Nat) (budget : Nat) :
    ¬ (AllQueriesSatisfy
      (liftM ((ofPFunctor finalAccess).query (.inr ())) : OracleComp (ofPFunctor finalAccess)
        ((ofPFunctor finalAccess).Range (.inr ())))
      (fun q => ∃ index : ((afterFirst first).availableContext initial.A).Index,
        ((afterFirst first).availableContext initial.A).name index =
          (afterBoth first second).queryName combined.oracles initial q) ∧
      WorstCaseCostBound
        (liftM ((ofPFunctor finalAccess).query (.inr ())) : OracleComp (ofPFunctor finalAccess)
          ((ofPFunctor finalAccess).Range (.inr ()))) rawCost budget) := by
  intro certificate
  obtain ⟨index, named⟩ := (allQueriesSatisfy_query_iff _ _).mp certificate.1
  have unavailable : ¬ (afterFirst first).Available (afterBoth first second).cursor := by
    intro available
    have length := (afterFirst first).available_length_le _ available
    change 2 ≤ 1 at length
    omega
  cases index with
  | inl input => exact Empty.elim input
  | inr available =>
    change Sum.inr available.1 = Sum.inr (afterBoth first second).cursor at named
    exact unavailable (Sum.inr.inj named ▸ available.2)


/-- Both expanded old calls share one canonical occurrence; the fresh occurrence is distinct. -/
example (first second : Nat) :
    (afterBoth first second).queryName combined.oracles initial (.inl (.inr ())) =
      (afterFirst first).queryName combined.oracles initial (.inr ()) ∧
    (afterBoth first second).queryName combined.oracles initial (.inl (.inr ())) ≠
      (afterBoth first second).queryName combined.oracles initial (.inr ()) := by
  constructor
  · rfl
  · intro equal
    have length := congrArg (fun name => match name with
      | Sum.inl _ => 0
      | Sum.inr cursor => cursor.length) equal
    change 1 = 2 at length
    omega


/-- Closing the actually returned claim preserves the same source log and private memory. -/
example :
    let result := simulateQ (fun tag => (tag : Id Nat))
      (executeStrategiesLoggedRun (protocol := combined) Empty.elim prover verifier)
    (result.core.proverOut, result.core.closed.map (·.stmt),
      (result.sourceLog : QueryLog (ofPFunctor finalAccess))) =
      (3, some 4, [⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩,
        ⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩, ⟨Sum.inr (), (2 : Nat)⟩]) := by
  rfl

end Interaction.Oracle.QueryBoundsTest

namespace Interaction.Oracle.QueryBoundsTest

open OracleComp OracleSpec

/-- The same native strategies are executed once by the phased adapter. -/
def phased := simulateQ (fun tag => (tag : Id Nat))
  (executePhases ambient combined.tree combined.roles combined.oracles initial Empty.elim
    (pure prover) verifier)

/-- Select the actual prefix verifier action, immediately after the first send. -/
def joinPhase : WorldPhase ambient combined.tree := phased.phases[2]'(by decide)

/-- Select the actual terminal verifier action after the second send. -/
def terminalPhase : WorldPhase ambient combined.tree := phased.phases[5]'(by decide)

example : joinPhase.prefix = afterFirst 1 := by rfl
example : terminalPhase.prefix = afterBoth 1 2 := by rfl

/-- Both selected boundaries are drawn from this execution's actual phase list. -/
theorem joinPhase_mem : joinPhase ∈ phased.phases := List.getElem_mem _

theorem terminalPhase_mem : terminalPhase ∈ phased.phases := List.getElem_mem _

end Interaction.Oracle.QueryBoundsTest

namespace Interaction.Oracle.QueryBoundsTest

open OracleComp OracleSpec

/-- The actual terminal phase supplies the canonical context for the same certified route. -/
example :
    AllQueriesSatisfy (simulateQ route suffixProgram) (fun q =>
      ∃ index : (terminalPhase.availableContext initial.A).Index,
        (terminalPhase.availableContext initial.A).name index =
          terminalPhase.prefix.queryName combined.oracles initial q) ∧
    WorstCaseCostBound (simulateQ route suffixProgram) rawCost 5 := by
  constructor
  · exact routed_available 1 2
  · exact worstCaseCostBound_simulateQ route suffixProgram sourceCost rawCost 5
      program_cost route_cost

/-- The old query's actual join name survives inclusion into this execution's terminal context. -/
example :
    let finalContext :=
      (TypeTree.ExecutionPrefix.ofExecutionPath phased.execution.path).availableContext initial.A
    finalContext.name ((phased.contextInclusion joinPhase joinPhase_mem initial.A).map
        (joinPhase.prefix.queryIndex combined.oracles initial (.inr ()))) =
      joinPhase.prefix.queryName combined.oracles initial (.inr ()) := by
  exact (phased.contextInclusion joinPhase joinPhase_mem initial.A).name_eq _

/-- The actual join cannot certify the future suffix slot, for any requested cost budget. -/
example (budget : Nat) :
    ¬ (AllQueriesSatisfy
      (liftM ((ofPFunctor finalAccess).query (.inr ())) : OracleComp (ofPFunctor finalAccess)
        ((ofPFunctor finalAccess).Range (.inr ())))
      (fun q => ∃ index : (joinPhase.availableContext initial.A).Index,
        (joinPhase.availableContext initial.A).name index =
          terminalPhase.prefix.queryName combined.oracles initial q) ∧
      WorstCaseCostBound
        (liftM ((ofPFunctor finalAccess).query (.inr ())) : OracleComp (ofPFunctor finalAccess)
          ((ofPFunctor finalAccess).Range (.inr ()))) rawCost budget) :=
  future_rejected 1 2 budget

/-- The phase adapter retains the exact source log through its ordinary logging correspondence.
WorldPhase.queries records ambient calls; it is not identified with this source log. -/
example : (phased.execution.sourceLog : QueryLog (ofPFunctor finalAccess)) =
    [⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩, ⟨Sum.inl (Sum.inr ()), (1 : Nat)⟩,
      ⟨Sum.inr (), (2 : Nat)⟩] := by
  change (phased.logView).1.2.2.2 = _
  have observed := executePhases_logView ambient combined.tree combined.roles combined.oracles
    initial Empty.elim (pure prover) verifier
  have interpreted := congrArg (fun program => simulateQ (fun tag => (tag : Id Nat)) program)
    observed
  have same := congrArg
    (fun result => (result.1.2.2.2 : QueryLog (ofPFunctor finalAccess))) interpreted
  rw [simulateQ_map] at same
  exact same.trans (by rfl)

end Interaction.Oracle.QueryBoundsTest

namespace Interaction.Oracle.QueryBoundsTest

open OracleComp OracleSpec

/-- An inhabited completed path charges the shared old slot twice, so four is insufficient. -/
example : ¬ WorstCaseCostBound (simulateQ route suffixProgram) rawCost 4 := by
  intro certificate
  have member : (0, Multiplicative.ofAdd 5) ∈
      support (costDist (simulateQ route suffixProgram) rawCost) := by
    change (0, Multiplicative.ofAdd 5) ∈ support (costDist (do
      let left : Nat ← liftM ((ofPFunctor finalAccess).query (.inl (.inr ())))
      let right : Nat ← liftM ((ofPFunctor finalAccess).query (.inl (.inr ())))
      let fresh : Nat ← liftM ((ofPFunctor finalAccess).query (.inr ()))
      return left + right + fresh) rawCost)
    have last : (0, Multiplicative.ofAdd 3) ∈ support (costDist (do
        let fresh : Nat ← liftM ((ofPFunctor finalAccess).query (.inr ()))
        return 0 + 0 + fresh) rawCost) :=
      mem_support_costDist_query_bind (spec := ofPFunctor finalAccess) (.inr ())
        (fun (fresh : Nat) => pure (0 + 0 + fresh)) (0 : Nat) rawCost (0, 1)
        (by rw [costDist_pure, mem_support_pure_iff])
    have middle : (0, Multiplicative.ofAdd 4) ∈ support (costDist (do
        let right : Nat ← liftM ((ofPFunctor finalAccess).query (.inl (.inr ())))
        let fresh : Nat ← liftM ((ofPFunctor finalAccess).query (.inr ()))
        return 0 + right + fresh) rawCost) :=
      mem_support_costDist_query_bind (spec := ofPFunctor finalAccess) (.inl (.inr ()))
        (fun (right : Nat) => do
          let fresh : Nat ← liftM ((ofPFunctor finalAccess).query (.inr ()))
          return 0 + right + fresh) (0 : Nat) rawCost (0, Multiplicative.ofAdd 3) last
    exact mem_support_costDist_query_bind (spec := ofPFunctor finalAccess) (.inl (.inr ()))
      (fun (left : Nat) => do
        let right : Nat ← liftM ((ofPFunctor finalAccess).query (.inl (.inr ())))
        let fresh : Nat ← liftM ((ofPFunctor finalAccess).query (.inr ()))
        return left + right + fresh) (0 : Nat) rawCost (0, Multiplicative.ofAdd 4) middle
  have bound := certificate (0, Multiplicative.ofAdd 5) member
  norm_num at bound

end Interaction.Oracle.QueryBoundsTest

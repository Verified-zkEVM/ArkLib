/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.LoggedExecution
import ArkLib.Interaction.Oracle.WorldSegments

/-!
# Executions with local world-query segments

The runner logs each participant's actual local action, after interpreting claim-resource reads.
The paired observation theorem compares this same execution with the source-logged runner and
its complete ambient query log. No trace replay or independently supplied phase evidence is used.
-/

namespace Interaction.Oracle

open OracleComp OracleSpec TwoParty

/-- The complete observation of the source-logged executor. -/
def LoggedObservation (tree : Oracle.TypeTree) (oracles : tree.OracleDecoration)
    (initial : PFunctor) (OutP : tree.ExecutionPath → Type)
    (OutV : tree.BranchPath → Type) :=
  (path : tree.ExecutionPath) × OutP path × OutV path.toBranchPath ×
    QueryLog (OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path.toBranchPath))

/-- Pair every source-logged observation before comparing instrumented executions. -/
def LoggedResult.observe {tree : Oracle.TypeTree} {oracles : tree.OracleDecoration}
    {initial : PFunctor} {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (result : LoggedResult tree oracles initial OutP OutV) :
    LoggedObservation tree oracles initial OutP OutV :=
  ⟨result.path, result.proverOut, result.verifierOut, result.deltaTrace⟩

/-- One runner's outputs, source log, and concrete-path-indexed local world segments. -/
structure PhasedResult {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor) (OutP : tree.ExecutionPath → Type) (OutV : tree.BranchPath → Type) where
  private mk ::
  /-- Actual concrete path. -/
  path : tree.ExecutionPath
  /-- Private prover output. -/
  proverOut : OutP path
  /-- Verifier terminal output. -/
  verifierOut : OutV path.toBranchPath
  /-- Ordered claim-resource observations, routed to final access. -/
  deltaTrace : QueryLog
    (OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path.toBranchPath))
  /-- Actual local-action world logs, with boundaries determined by `path`. -/
  world : WorldSegments ambient tree path

namespace PhasedResult

/-- Forget the world segmentation while retaining all source-run observations. -/
def observe {ι : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    {roles : tree.RoleDecoration} {oracles : tree.OracleDecoration} {initial : PFunctor}
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (result : PhasedResult ambient tree roles oracles initial OutP OutV) :
    LoggedObservation tree oracles initial OutP OutV :=
  ⟨result.path, result.proverOut, result.verifierOut, result.deltaTrace⟩

/-- Keep the complete chronological world log paired with the source-run observations. -/
def logView {ι : Type} {ambient : OracleSpec ι} {tree : Oracle.TypeTree}
    {roles : tree.RoleDecoration} {oracles : tree.OracleDecoration} {initial : PFunctor}
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (result : PhasedResult ambient tree roles oracles initial OutP OutV) :=
  (result.observe, result.world.flatten)

end PhasedResult

/-- Execute restricted strategies in the paired runner's ownership order, logging each verifier
local action once. Oracle receives extend behavior before executing the verifier action. -/
def executeStrategiesPhased {ι : Type} (ambient : OracleSpec ι) :
    (tree : Oracle.TypeTree) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    QueryImpl (OracleSpec.ofPFunctor initial) Id →
    {OutP : tree.ExecutionPath → Type} → {OutV : tree.BranchPath → Type} →
    Prover.Strategy ambient tree roles OutP →
    Verifier.Strategy ambient tree roles oracles initial OutV →
    OracleComp ambient (PhasedResult ambient tree roles oracles initial OutP OutV)
  | .done, _, _, initial, impl, _, _, prover, verifier => do
      let ⟨result, world⟩ ← ((simulateQ (Verifier.loggedReadImpl ambient initial impl)
        verifier).run).withQueryLog
      return ⟨⟨⟩, prover, result.1, result.2, world⟩
  | .public _ rest, ⟨.sender, roles⟩, oracles, initial, impl, OutP, OutV, prover, verifier => do
      let ⟨⟨move, nextP⟩, worldP⟩ ← prover.withQueryLog
      let ⟨nextV, worldV⟩ ←
        ((simulateQ (Verifier.loggedReadImpl ambient initial impl) (verifier
          move)).run).withQueryLog
      let result ← executeStrategiesPhased ambient (rest move) (roles move) (oracles.2 move)
        initial impl (OutP := fun path => OutP ⟨move, path⟩)
        (OutV := fun path => OutV ⟨move, path⟩) nextP nextV.1
      return ⟨⟨move, result.path⟩, result.proverOut, result.verifierOut,
        TypeTree.routeLog (rest move) (oracles.2 move) initial result.path.toBranchPath nextV.2 ++
          result.deltaTrace, ⟨worldP, worldV, result.world⟩⟩
  | .public _ rest, ⟨.receiver, roles⟩, oracles, initial, impl, OutP, OutV, prover, verifier => do
      let ⟨nextV, worldV⟩ ←
        ((simulateQ (Verifier.loggedReadImpl ambient initial impl) verifier).run).withQueryLog
      let ⟨nextP, worldP⟩ ← (prover nextV.1.1).withQueryLog
      let result ← executeStrategiesPhased ambient (rest nextV.1.1) (roles nextV.1.1)
        (oracles.2 nextV.1.1) initial impl (OutP := fun path => OutP ⟨nextV.1.1, path⟩)
        (OutV := fun path => OutV ⟨nextV.1.1, path⟩) nextP nextV.1.2
      return ⟨⟨nextV.1.1, result.path⟩, result.proverOut, result.verifierOut,
        TypeTree.routeLog (rest nextV.1.1) (oracles.2 nextV.1.1) initial
          result.path.toBranchPath nextV.2 ++ result.deltaTrace, ⟨worldV, worldP, result.world⟩⟩
  | .oracle _ rest, roles, oracles, initial, impl, OutP, OutV, prover, verifier => do
      let ⟨⟨message, nextP⟩, worldP⟩ ← prover.withQueryLog
      let extended := Access.extend initial oracles.1
      let extendedImpl := Access.extendImpl initial oracles.1 impl message
      let ⟨nextV, worldV⟩ ←
        ((simulateQ (Verifier.loggedReadImpl ambient extended extendedImpl)
          verifier).run).withQueryLog
      let result ← executeStrategiesPhased ambient (rest PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) extended extendedImpl (OutP := fun path => OutP ⟨message, path⟩)
        (OutV := fun path => OutV ⟨PUnit.unit, path⟩) nextP nextV.1
      return ⟨⟨message, result.path⟩, result.proverOut, result.verifierOut,
        TypeTree.routeLog (rest PUnit.unit) (oracles.2 PUnit.unit) extended
          result.path.toBranchPath nextV.2 ++ result.deltaTrace, ⟨worldP, worldV, result.world⟩⟩


set_option backward.isDefEq.respectTransparency false in
/-- Flattening the local world segments gives the complete world log of the same source-logged
execution, still paired with all outputs and source observations. -/
theorem executeStrategiesPhased_logView {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) :
    PhasedResult.logView <$> executeStrategiesPhased ambient tree roles oracles initial impl
        prover verifier =
      (fun result => (result.1.observe, result.2)) <$>
        (executeStrategiesLogged ambient tree roles oracles initial impl prover
          verifier).withQueryLog := by
  induction tree generalizing initial with
  | done =>
      simp only [executeStrategiesPhased, executeStrategiesLogged, OracleComp.withQueryLog_bind,
        PhasedResult.logView, PhasedResult.observe, LoggedResult.observe, WorldSegments.flatten,
          OracleComp.withQueryLog_pure,
        map_bind, map_pure,         Prod.map_apply, id_eq, List.append_nil, monad_norm]
  | «public» Moves rest ih =>
      rcases roles with ⟨role, roles⟩
      cases role with
      | sender =>
        simp only [executeStrategiesPhased, executeStrategiesLogged, OracleComp.withQueryLog_bind,
          PhasedResult.logView, PhasedResult.observe, LoggedResult.observe,
            WorldSegments.flatten, OracleComp.withQueryLog_pure,
          map_bind, map_pure,           Prod.map_apply, id_eq, List.append_nil,
            List.append_assoc, monad_norm]
        congr 1
        funext first
        congr 1
        funext second
        have h := ih first.1.1 (roles first.1.1) (oracles.2 first.1.1) initial impl
          (OutP := fun path => OutP ⟨first.1.1, path⟩)
          (OutV := fun path => OutV ⟨first.1.1, path⟩) first.1.2 second.1.1
        have lifted := congrArg (fun program =>
          (fun view : LoggedObservation (rest first.1.1)
              (oracles.2 first.1.1) (initial) (fun path => OutP ⟨first.1.1, path⟩)
              (fun path => OutV ⟨first.1.1, path⟩) × QueryLog ambient =>
            ((⟨⟨first.1.1, view.1.1⟩, view.1.2.1, view.1.2.2.1,
              TypeTree.routeLog (rest first.1.1) (oracles.2 first.1.1) (initial)
                view.1.1.toBranchPath second.1.2 ++ view.1.2.2.2⟩ :
              LoggedObservation (TypeTree.public Moves rest)
                oracles initial OutP OutV), first.2 ++ second.2 ++ view.2)) <$> program) h
        simpa [Functor.map_map, PhasedResult.logView, PhasedResult.observe,
          LoggedResult.observe, WorldSegments.flatten, monad_norm] using lifted
      | receiver =>
        simp only [executeStrategiesPhased, executeStrategiesLogged, OracleComp.withQueryLog_bind,
          PhasedResult.logView, PhasedResult.observe, LoggedResult.observe,
            WorldSegments.flatten, OracleComp.withQueryLog_pure,
          map_bind, map_pure,           Prod.map_apply, id_eq, List.append_nil,
            List.append_assoc, monad_norm]
        congr 1
        funext first
        congr 1
        funext second
        have h := ih first.1.1.1 (roles first.1.1.1) (oracles.2 first.1.1.1) initial impl
          (OutP := fun path => OutP ⟨first.1.1.1, path⟩)
          (OutV := fun path => OutV ⟨first.1.1.1, path⟩) second.1 first.1.1.2
        have lifted := congrArg (fun program =>
          (fun view : LoggedObservation (rest first.1.1.1)
              (oracles.2 first.1.1.1) (initial) (fun path => OutP ⟨first.1.1.1, path⟩)
              (fun path => OutV ⟨first.1.1.1, path⟩) × QueryLog ambient =>
            ((⟨⟨first.1.1.1, view.1.1⟩, view.1.2.1, view.1.2.2.1,
              TypeTree.routeLog (rest first.1.1.1) (oracles.2 first.1.1.1) (initial)
                view.1.1.toBranchPath first.1.2 ++ view.1.2.2.2⟩ :
              LoggedObservation (TypeTree.public Moves rest)
                oracles initial OutP OutV), first.2 ++ second.2 ++ view.2)) <$> program) h
        simpa [Functor.map_map, PhasedResult.logView, PhasedResult.observe,
          LoggedResult.observe, WorldSegments.flatten, monad_norm] using lifted
  | «oracle» Messages rest ih =>
      simp only [executeStrategiesPhased, executeStrategiesLogged, OracleComp.withQueryLog_bind,
        PhasedResult.logView, PhasedResult.observe, LoggedResult.observe, WorldSegments.flatten,
          OracleComp.withQueryLog_pure,
        map_bind, map_pure,         Prod.map_apply, id_eq, List.append_nil, List.append_assoc,
          monad_norm]
      congr 1
      funext first
      congr 1
      funext second
      have h := ih (roles.2 PUnit.unit) (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl first.1.1)
        (OutP := fun path => OutP ⟨first.1.1, path⟩)
        (OutV := fun path => OutV ⟨PUnit.unit, path⟩) first.1.2 second.1.1
      have lifted := congrArg (fun program =>
        (fun view : LoggedObservation (rest PUnit.unit)
            (oracles.2 PUnit.unit) (Access.extend initial oracles.1) (fun path => OutP
              ⟨first.1.1, path⟩)
            (fun path => OutV ⟨PUnit.unit, path⟩) × QueryLog ambient =>
          ((⟨⟨first.1.1, view.1.1⟩, view.1.2.1, view.1.2.2.1,
            TypeTree.routeLog (rest PUnit.unit) (oracles.2 PUnit.unit) (Access.extend initial
              oracles.1)
              view.1.1.toBranchPath second.1.2 ++ view.1.2.2.2⟩ :
            LoggedObservation (TypeTree.oracle Messages rest)
              oracles initial OutP OutV), first.2 ++ second.2 ++ view.2)) <$> program) h
      simpa [Functor.map_map, PhasedResult.logView, PhasedResult.observe,
        LoggedResult.observe, WorldSegments.flatten, monad_norm] using lifted

/-- Erasing world instrumentation preserves every output and source observation. -/
theorem executeStrategiesPhased_erase {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) :
    PhasedResult.observe <$> executeStrategiesPhased ambient tree roles oracles initial impl
        prover verifier =
      LoggedResult.observe <$>
        executeStrategiesLogged ambient tree roles oracles initial impl prover verifier := by
  have paired := congrArg (fun program => Prod.fst <$> program)
    (executeStrategiesPhased_logView ambient tree roles oracles initial impl prover verifier)
  have erase := loggingOracle.fst_map_run_simulateQ
    (executeStrategiesLogged ambient tree roles oracles initial impl prover verifier)
  have erased := congrArg (fun program => LoggedResult.observe <$> program) erase
  simp only [Functor.map_map] at paired erased
  simpa [PhasedResult.logView] using paired.trans erased

private theorem log_map {ι : Type} {ambient : OracleSpec ι} {α β : Type}
    (f : α → β) (program : OracleComp ambient α) :
    (f <$> program).withQueryLog = (fun result => (f result.1, result.2)) <$>
      program.withQueryLog := by
  simp [OracleComp.withQueryLog]

/-- On a supported execution, flattening the recorded local segments is exactly the world log
of that execution, rather than merely a log with the same marginal distribution. -/
theorem executeStrategiesPhased_world_eq {ι : Type} (ambient : OracleSpec ι)
    (tree : Oracle.TypeTree) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type} {OutV : tree.BranchPath → Type}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV)
    (result : PhasedResult ambient tree roles oracles initial OutP OutV) (trace : QueryLog ambient)
    (generated : (result, trace) ∈ support
      (executeStrategiesPhased ambient tree roles oracles initial impl prover
        verifier).withQueryLog) :
    result.world.flatten = trace := by
  have observed : (result.logView, trace) ∈ support
      (PhasedResult.logView <$>
        executeStrategiesPhased ambient tree roles oracles initial impl prover
          verifier).withQueryLog := by
    rw [log_map, support_map]
    exact ⟨(result, trace), generated, rfl⟩
  rw [executeStrategiesPhased_logView, log_map, support_map] at observed
  obtain ⟨⟨⟨original, inner⟩, outer⟩, supported, equal⟩ := observed
  have agree := OracleComp.withQueryLog_self_log_eq
    (executeStrategiesLogged ambient tree roles oracles initial impl prover verifier) supported
  have inner_eq : inner = result.world.flatten := congrArg (fun x => x.1.2) equal
  have outer_eq : outer = trace := congrArg Prod.snd equal
  exact inner_eq.symm.trans (agree.trans outer_eq)

end Interaction.Oracle

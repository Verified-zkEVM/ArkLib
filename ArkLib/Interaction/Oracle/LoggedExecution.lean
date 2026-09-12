/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.CoreRun
public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Ordered source logging

The restricted verifier's source queries are recorded as they execute. Earlier entries are
routed through each later signature extension, retaining their order and multiplicity.
Erasure is an equality of open ambient programs, before any world interpreter is chosen.
-/

@[expose] public section

universe u v w

namespace Interaction.Oracle

open OracleComp OracleSpec TwoParty


namespace TypeTree

/-- Route an earlier query/answer entry into the accumulated terminal signature. -/
def routeEntry : (tree : Oracle.TypeTree.{u}) → (oracles : tree.OracleDecoration) →
    (initial : PFunctor.{u, u}) → (path : tree.BranchPath) →
    ((q : initial.A) × initial.B q) →
    ((q : (accessAfter tree oracles initial path).A) ×
      (accessAfter tree oracles initial path).B q)
  | .done, _, _, _, entry => entry
  | .public _ rest, oracles, initial, path, entry =>
      routeEntry (rest path.1) (oracles.2 path.1) initial path.2 entry
  | .oracle _ rest, oracles, initial, path, entry =>
      routeEntry (rest path.1) (oracles.2 path.1) (Access.extend initial oracles.1) path.2
        ⟨Sum.inl entry.1, entry.2⟩

/-- Routing never deletes, duplicates, or reorders entries. -/
def routeLog (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (path : tree.BranchPath)
    (log : QueryLog (OracleSpec.ofPFunctor initial)) :
    QueryLog (OracleSpec.ofPFunctor (accessAfter tree oracles initial path)) :=
  log.map (routeEntry tree oracles initial path)

@[simp]
theorem routeLog_length (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (path : tree.BranchPath)
    (log : QueryLog (OracleSpec.ofPFunctor initial)) :
    (routeLog tree oracles initial path log).length = log.length := List.length_map ..

end TypeTree

namespace Verifier

/-- Interpret ambient queries unchanged and record source responses immediately after answering. -/
def loggedLiftAccessImpl {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (access : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor access) Id) :
    QueryImpl (ambient + OracleSpec.ofPFunctor access)
      (WriterT (QueryLog (OracleSpec.ofPFunctor access)) (OracleComp ambient)) :=
  (liftAccessImpl ambient access impl).withTraceAppend (fun q answer =>
    match q with
    | .inl _ => []
    | .inr query => [⟨query, answer⟩])

/-- Erasing one instrumented local action gives the original read interpreter. -/
theorem loggedLiftAccessImpl_erase {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (access : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor access) Id)
    {α : Type u} (program : OracleComp (ambient + OracleSpec.ofPFunctor access) α) :
    Prod.fst <$> (simulateQ (loggedLiftAccessImpl ambient access impl) program).run =
      simulateQ (liftAccessImpl ambient access impl) program :=
  QueryImpl.fst_map_run_withTraceAppend ..

end Verifier

/-- One generic execution's outputs and ordered source observations. The executor owns pairing. -/
structure LoggedResult (tree : Oracle.TypeTree.{u}) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (OutP : tree.ExecutionPath → Type u)
    (OutV : tree.BranchPath → Type u) where
  private mk ::
  /-- Actual concrete path. -/
  path : tree.ExecutionPath
  /-- Private prover output. -/
  proverOut : OutP path
  /-- Verifier terminal output. -/
  verifierOut : OutV path.toBranchPath
  /-- Source queries in execution order, routed to final access. -/
  sourceLog : QueryLog
    (OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path.toBranchPath))

/-- Forget instrumentation without changing path or either participant's output. -/
def LoggedResult.erase {tree : Oracle.TypeTree.{u}} {oracles : tree.OracleDecoration}
    {initial : PFunctor.{u, u}} {OutP : tree.ExecutionPath → Type u}
    {OutV : tree.BranchPath → Type u} (result : LoggedResult tree oracles initial OutP OutV) :
    (path : tree.ExecutionPath) × OutP path × OutV path.toBranchPath :=
  ⟨result.path, result.proverOut, result.verifierOut⟩

/-- Execute restricted strategies in the paired runner's ownership order, logging each verifier
local action once. Oracle receives extend behavior before executing the verifier action. -/
@[no_expose]
def executeStrategiesLogged {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor.{u, u}) →
    QueryImpl (OracleSpec.ofPFunctor initial) Id →
    {OutP : tree.ExecutionPath → Type u} → {OutV : tree.BranchPath → Type u} →
    Prover.Strategy ambient tree roles OutP →
    Verifier.Strategy ambient tree roles oracles initial OutV →
    OracleComp ambient (LoggedResult tree oracles initial OutP OutV)
  | .done, _, _, initial, impl, _, _, prover, verifier => do
      let result ← (simulateQ (Verifier.loggedLiftAccessImpl ambient initial impl) verifier).run
      return ⟨⟨⟩, prover, result.1, result.2⟩
  | .public _ rest, ⟨.sender, roles⟩, oracles, initial, impl, OutP, OutV, prover, verifier => do
      let ⟨move, nextP⟩ ← prover
      let nextV ←
        (simulateQ (Verifier.loggedLiftAccessImpl ambient initial impl) (verifier move)).run
      let result ← executeStrategiesLogged ambient (rest move) (roles move) (oracles.2 move)
        initial impl (OutP := fun path => OutP ⟨move, path⟩)
        (OutV := fun path => OutV ⟨move, path⟩) nextP nextV.1
      return ⟨⟨move, result.path⟩, result.proverOut, result.verifierOut,
        TypeTree.routeLog (rest move) (oracles.2 move) initial result.path.toBranchPath nextV.2 ++
          result.sourceLog⟩
  | .public _ rest, ⟨.receiver, roles⟩, oracles, initial, impl, OutP, OutV, prover,
      verifier => do
      let nextV ← (simulateQ (Verifier.loggedLiftAccessImpl ambient initial impl) verifier).run
      let nextP ← prover nextV.1.1
      let result ← executeStrategiesLogged ambient (rest nextV.1.1) (roles nextV.1.1)
        (oracles.2 nextV.1.1) initial impl (OutP := fun path => OutP ⟨nextV.1.1, path⟩)
        (OutV := fun path => OutV ⟨nextV.1.1, path⟩) nextP nextV.1.2
      return ⟨⟨nextV.1.1, result.path⟩, result.proverOut, result.verifierOut,
        TypeTree.routeLog (rest nextV.1.1) (oracles.2 nextV.1.1) initial
          result.path.toBranchPath nextV.2 ++ result.sourceLog⟩
  | .oracle _ rest, roles, oracles, initial, impl, OutP, OutV, prover, verifier => do
      let ⟨message, nextP⟩ ← prover
      let extended := Access.extend initial oracles.1
      let extendedImpl := Access.extendImpl initial oracles.1 impl message
      let nextV ←
        (simulateQ (Verifier.loggedLiftAccessImpl ambient extended extendedImpl) verifier).run
      let result ← executeStrategiesLogged ambient (rest PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) extended extendedImpl (OutP := fun path => OutP ⟨message, path⟩)
        (OutV := fun path => OutV ⟨PUnit.unit, path⟩) nextP nextV.1
      return ⟨⟨message, result.path⟩, result.proverOut, result.verifierOut,
        TypeTree.routeLog (rest PUnit.unit) (oracles.2 PUnit.unit) extended
          result.path.toBranchPath nextV.2 ++ result.sourceLog⟩

set_option backward.isDefEq.respectTransparency false in
/-- Instrumentation preserves the complete open execution program after log erasure. -/
theorem executeStrategiesLogged_erase {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    {OutP : tree.ExecutionPath → Type u} {OutV : tree.BranchPath → Type u}
    (prover : Prover.Strategy ambient tree roles OutP)
    (verifier : Verifier.Strategy ambient tree roles oracles initial OutV) :
    LoggedResult.erase <$> executeStrategiesLogged ambient tree roles oracles initial impl
        prover verifier =
      executeStrategies ambient tree roles oracles initial impl prover verifier := by
  induction tree generalizing initial with
  | done =>
      simp only [executeStrategiesLogged, executeStrategies, Verifier.toCounterpart,
        TypeTree.toTypeTree_done, TypeTree.RoleDecoration.toTypeTreeRoles_done, TwoParty.run_done,
        pure_bind, map_bind, map_pure, LoggedResult.erase]
      simp only [bind_pure_comp]
      change (fun a : OutV ⟨⟩ × QueryLog (OracleSpec.ofPFunctor initial) =>
        ⟨⟨⟩, prover, a.1⟩)
        <$> (simulateQ (Verifier.loggedLiftAccessImpl ambient initial impl) verifier).run =
          (fun out => (⟨⟨⟩, prover, out⟩ :
            (path : TypeTree.ExecutionPath .done) × OutP path × OutV path.toBranchPath))
            <$> simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier
      rw [← Verifier.loggedLiftAccessImpl_erase ambient initial impl verifier, Functor.map_map]
  | «public» Moves rest ih =>
      rcases roles with ⟨role, roles⟩
      cases role <;>
        simp only [executeStrategiesLogged, executeStrategies, Verifier.toCounterpart,
          TypeTree.toTypeTree_public, TypeTree.RoleDecoration.toTypeTreeRoles_public,
          map_bind, map_pure, LoggedResult.erase]
      · erw [TwoParty.run_sender]
        simp only [bind_assoc, pure_bind]
        congr 1
        funext nextP
        rw [← Verifier.loggedLiftAccessImpl_erase ambient initial impl (verifier nextP.1)]
        simp only [bind_map_left]
        congr 1
        funext nextV
        have h := ih nextP.1 (roles nextP.1) (oracles.2 nextP.1) initial impl
          (OutP := fun path => OutP ⟨nextP.1, path⟩)
          (OutV := fun path => OutV ⟨nextP.1, path⟩) nextP.2 nextV.1
        have lifted := congrArg (fun program =>
          (fun result => (⟨⟨nextP.1, result.1⟩, result.2⟩ :
            (path : (TypeTree.public Moves rest).ExecutionPath) ×
              OutP path × OutV path.toBranchPath))
            <$> program) h
        simp only [Functor.map_map, LoggedResult.erase, executeStrategies, map_bind,
          bind_pure_comp, TypeTree.ExecutionPath.ofTypeTreePath,
          PFunctor.FreeM.mapLensPathToPathAlong, TypeTree.runtimeLens, TypeTree.toTypeTree]
            at lifted ⊢
        exact lifted
      · erw [TwoParty.run_receiver]
        simp only [bind_assoc, pure_bind]
        rw [← Verifier.loggedLiftAccessImpl_erase ambient initial impl verifier]
        simp only [bind_map_left]
        congr 1
        funext nextV
        congr 1
        funext nextP
        have h := ih nextV.1.1 (roles nextV.1.1) (oracles.2 nextV.1.1) initial impl
          (OutP := fun path => OutP ⟨nextV.1.1, path⟩)
          (OutV := fun path => OutV ⟨nextV.1.1, path⟩) nextP nextV.1.2
        have lifted := congrArg (fun program =>
          (fun result => (⟨⟨nextV.1.1, result.1⟩, result.2⟩ :
            (path : (TypeTree.public Moves rest).ExecutionPath) ×
              OutP path × OutV path.toBranchPath))
            <$> program) h
        simp only [Functor.map_map, LoggedResult.erase, executeStrategies, map_bind,
          bind_pure_comp, TypeTree.ExecutionPath.ofTypeTreePath,
          PFunctor.FreeM.mapLensPathToPathAlong, TypeTree.runtimeLens, TypeTree.toTypeTree]
            at lifted ⊢
        exact lifted
  | «oracle» Messages rest ih =>
      simp only [executeStrategiesLogged, executeStrategies, Verifier.toCounterpart,
        TypeTree.toTypeTree_oracle, TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
        map_bind, map_pure, LoggedResult.erase]
      erw [TwoParty.run_sender]
      simp only [bind_assoc, pure_bind]
      congr 1
      funext nextP
      rw [← Verifier.loggedLiftAccessImpl_erase ambient (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl nextP.1) verifier]
      simp only [bind_map_left]
      congr 1
      funext nextV
      have h := ih (roles.2 PUnit.unit) (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl nextP.1)
        (OutP := fun path => OutP ⟨nextP.1, path⟩)
        (OutV := fun path => OutV ⟨PUnit.unit, path⟩) nextP.2 nextV.1
      have lifted := congrArg (fun program =>
        (fun result => (⟨⟨nextP.1, result.1⟩, result.2⟩ :
          (path : (TypeTree.oracle Messages rest).ExecutionPath) ×
            OutP path × OutV path.toBranchPath))
          <$> program) h
      simp only [Functor.map_map, LoggedResult.erase, executeStrategies, map_bind,
        bind_pure_comp, TypeTree.ExecutionPath.ofTypeTreePath,
          PFunctor.FreeM.mapLensPathToPathAlong, TypeTree.runtimeLens, TypeTree.toTypeTree]
            at lifted ⊢
      exact lifted

end Interaction.Oracle

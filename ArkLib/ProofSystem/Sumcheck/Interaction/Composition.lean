/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import all PolyFun.Interaction.TwoParty.Compose
public import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol
public import ArkLib.Interaction.Oracle.CompositionSoundness

/-!
# Native Sumcheck as exported oracle composition

The first round returns an ordinary claim over its retained original oracle. Successful public
branches continue with the existing verifier authored against that exported interface. Public
rejection keeps its existing terminal branch and the prover's response to it.
-/

@[expose] public section

open Interaction Interaction.Oracle OracleComp OracleSpec
namespace Interaction.Oracle
variable {ι I : Type} {ambient : OracleSpec ι} {protocol : Protocol} {initial : PFunctor}
  {Stmt : Type} {Data : I → Type} {Out : OracleFamily I Data}
  {OutP : protocol.tree.ExecutionPath → Type}
private theorem executeStrategiesCore_closed_eq_run
    (impl : QueryImpl (ofPFunctor initial) Id)
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial
      (TerminalClaim protocol initial (fun _ => Stmt) (fun _ => Out))) :
    (fun result => result.closed) <$> executeStrategiesCore impl prover verifier = (do
      let result ← TwoParty.run protocol.tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles protocol.tree protocol.roles) prover
        (Verifier.toCounterpartWith ambient protocol.tree protocol.roles protocol.oracles
          initial impl _ (fun _ => OracleComp ambient (Option (ClosedClaim Stmt Out)))
          (fun path actual action =>
            (fun out => out.map (fun claim => OpenClaim.closeWith claim actual)) <$>
              simulateQ (Verifier.liftAccessImpl ambient
                (TypeTree.accessAfter protocol.tree protocol.oracles initial path) actual) action)
          verifier)
      result.2.2) := by
  simp only [executeStrategiesCore, executeStrategies, CoreRun.closed,
    map_bind, map_pure, bind_assoc, pure_bind]
  simp only [Verifier.toCounterpart, Verifier.toCounterpartWith_finish_eq_mapOutput,
    run_counterpart_mapOutput, bind_map_left]
  simp only [map_eq_pure_bind]
end Interaction.Oracle

namespace Sumcheck.Interaction.Native
open SingleRound MultivariateRound
noncomputable section

variable (R : Type) [CommSemiring R] [DecidableEq R] (n deg : ℕ)
  {ι : Type} (ambient : OracleSpec ι)

/-- Rejection has no successor statement; success carries the next Sumcheck statement. -/
def midpointStatement (count start : ℕ) (finish : start + (count + 1) = n)
    (path : (firstRoundProtocol R deg).tree.BranchPath) : Type :=
  match path.2.1 with
  | none => Unit
  | some _ => Spec.StatementRound R n ⟨start + 1, by omega⟩

/-- Author one ordinary round, retaining the original view as its exported oracle. -/
def firstRoundFragment (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩) :
    Verifier.Fragment ambient (firstRoundProtocol R deg).tree (firstRoundProtocol R deg).roles
      (firstRoundProtocol R deg).oracles A (fun path => OpenClaim
        (ofPFunctor (TypeTree.accessAfter (firstRoundProtocol R deg).tree
          (firstRoundProtocol R deg).oracles A path))
        (midpointStatement R n deg count start finish path) (polynomialFamily R n deg)) := by
  unfold firstRoundProtocol midpointStatement
  exact do
    let total ← latestSum R deg ambient A domain
    return do
      if total = stmt.target then
        let r ← challenge.liftComp
          (ambient + ofPFunctor (Access.extend A (polynomialInterface R deg)))
        let value ← latest R deg ambient A r
        return ⟨some r, (⟨⟨value, Fin.snoc stmt.challenges r⟩,
          originalOracle.sumWeaken (polynomialInterface R deg).spec⟩ :
          OpenClaim (ofPFunctor (Access.extend A (polynomialInterface R deg)))
            (Spec.StatementRound R n ⟨start + 1, by omega⟩) (polynomialFamily R n deg))⟩
      else
        return ⟨none, (⟨(), originalOracle.sumWeaken (polynomialInterface R deg).spec⟩ :
          OpenClaim (ofPFunctor (Access.extend A (polynomialInterface R deg)))
            Unit (polynomialFamily R n deg))⟩
/-- Continue the same verifier over only the exported original-oracle interface. -/
def remainingVerifier (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n)
    (path : (firstRoundProtocol R deg).tree.BranchPath)
    (stmt : midpointStatement R n deg count start finish path) :
    Verifier.Strategy ambient (remainingProtocol R deg count path).tree
      (remainingProtocol R deg count path).roles (remainingProtocol R deg count path).oracles
      (polynomialFamily R n deg).spec.toPFunctor
      (TerminalClaim (remainingProtocol R deg count path)
        (polynomialFamily R n deg).spec.toPFunctor (fun _ => FinalStatement R n)
        (fun _ => polynomialFamily R n deg)) :=
  match path with
  | ⟨_, none, _⟩ => pure none
  | ⟨_, some _, _⟩ => verifier R n deg ambient challenge domain count (start + 1) (by omega)
      (polynomialFamily R n deg).spec.toPFunctor (VirtualOracle.id (polynomialFamily R n deg)) stmt

/-- Compose the first round with the remaining verifier using its exported original oracle. -/
def composedVerifier (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩) :=
  Verifier.appendExported ambient (firstRoundProtocol R deg).tree
    (fun p => (remainingProtocol R deg count p).tree) (firstRoundProtocol R deg).roles
    (fun p => (remainingProtocol R deg count p).roles) (firstRoundProtocol R deg).oracles
    (fun p => (remainingProtocol R deg count p).oracles) A
    (midpointStatement R n deg count start finish) (fun _ => Spec.OracleStatement R n deg)
    (fun _ => polynomialFamily R n deg) (fun _ => FinalStatement R n)
    (fun _ => Spec.OracleStatement R n deg) (fun _ => polynomialFamily R n deg)
    (firstRoundFragment R n deg ambient challenge domain count start finish A originalOracle stmt)
    (remainingVerifier R n deg ambient challenge domain count start finish)

omit [DecidableEq R] in
/-- Interpret the concrete first message while retaining the actual original source handler. -/
theorem firstRound_closingImpl (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    (q : Message R deg) (choice : Option R) :
    TypeTree.ExecutionPath.closingImpl (tree := (firstRoundProtocol R deg).tree)
      ⟨q, ⟨choice, PUnit.unit⟩⟩ (firstRoundProtocol R deg).oracles A impl =
      Access.extendImpl A (polynomialInterface R deg) impl q := by
  rfl

omit [DecidableEq R] in
private theorem firstRound_closingImpl_literal (A : PFunctor) (impl : QueryImpl (ofPFunctor A) Id)
    (q : Message R deg) (choice : Option R) :
    TypeTree.ExecutionPath.closingImpl
      (tree := TypeTree.oracle (Message R deg) fun _ =>
        TypeTree.public (Option R) fun _ => .done)
      ⟨q, ⟨choice, PUnit.unit⟩⟩
      ⟨polynomialInterface R deg, fun _ => ⟨PUnit.unit, fun _ => PUnit.unit⟩⟩ A impl =
      Access.extendImpl A (polynomialInterface R deg) impl q := by
  rfl

omit [DecidableEq R] in
private theorem onAppendedRuntime_native (count : ℕ)
    (prover : Prover.Strategy ambient (protocol R deg (count + 1)).tree
      (protocol R deg (count + 1)).roles (fun _ => Unit)) :
    onAppendedRuntime ambient TwoParty.Participant.focal (firstRoundProtocol R deg).tree
      (fun p => (remainingProtocol R deg count p).tree) (firstRoundProtocol R deg).roles
      (fun p => (remainingProtocol R deg count p).roles) (fun _ => Unit) prover = prover := by
  rfl

omit [DecidableEq R] in
private theorem splitPrefix_native (count : ℕ)
    (prover : Prover.Strategy ambient (protocol R deg (count + 1)).tree
      (protocol R deg (count + 1)).roles (fun _ => Unit)) :
    StrategyOver.TwoParty.Focal.splitPrefix
      (s₁ := (firstRoundProtocol R deg).tree.toTypeTree)
      (s₂ := fun p => (remainingProtocol R deg count
        (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).tree.toTypeTree)
      (r₁ := TypeTree.RoleDecoration.toTypeTreeRoles (firstRoundProtocol R deg).tree
        (firstRoundProtocol R deg).roles)
      (r₂ := fun p => TypeTree.RoleDecoration.toTypeTreeRoles
        (remainingProtocol R deg count (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).tree
        (remainingProtocol R deg count
          (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).roles)
      (Output := fun _ => Unit) prover = prover := by
  simp only [firstRoundProtocol, Core.firstRoundProtocol, Protocol.oracleWith_tree,
    Protocol.oracleWith_roles,
    Protocol.public_tree, Protocol.public_roles, Protocol.done_tree, Protocol.done_roles,
    TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public, TypeTree.toTypeTree_done,
    TypeTree.RoleDecoration.toTypeTreeRoles_oracle, TypeTree.RoleDecoration.toTypeTreeRoles_public,
    TypeTree.RoleDecoration.toTypeTreeRoles_done, Interaction.TypeTree.node,
    StrategyOver.TwoParty.Focal.splitPrefix]
  simp only [map_eq_pure_bind, bind_pure]
  simp only [Sigma.eta]
  exact id_map prover


set_option backward.isDefEq.respectTransparency false in
/-- The native prefix run returns its actual first-round path, exported claim, and continuation. -/
theorem exportedPrefixRun_firstRound (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩) (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R deg (count + 1)).tree
      (protocol R deg (count + 1)).roles (fun _ => Unit)) :
    exportedPrefixRun ambient (firstRoundProtocol R deg).tree
      (fun p => (remainingProtocol R deg count p).tree) (firstRoundProtocol R deg).roles
      (fun p => (remainingProtocol R deg count p).roles) (firstRoundProtocol R deg).oracles A impl
      (midpointStatement R n deg count start finish) (fun _ => Spec.OracleStatement R n deg)
      (fun _ => polynomialFamily R n deg) (fun _ => Unit) prover
      (firstRoundFragment R n deg ambient challenge domain count start finish A originalOracle stmt)
      = (do
        let chosen ← prover
        if (domain.map (fun x => chosen.1.val.eval x)).sum = stmt.target then
          let r ← challenge
          let next ← chosen.2 (some r)
          return ⟨⟨chosen.1, ⟨some r, PUnit.unit⟩⟩, next,
            ⟨⟨chosen.1.val.eval r, Fin.snoc stmt.challenges r⟩,
              originalOracle.sumWeaken (polynomialInterface R deg).spec⟩⟩
        else
          let next ← chosen.2 none
          return ⟨⟨chosen.1, ⟨none, PUnit.unit⟩⟩, next,
            ⟨(), originalOracle.sumWeaken (polynomialInterface R deg).spec⟩⟩) := by
  unfold exportedPrefixRun
  rw [onAppendedRuntime_native, splitPrefix_native]
  simp only [firstRoundProtocol, Core.firstRoundProtocol, Protocol.oracleWith_tree,
    Protocol.oracleWith_roles,
    Protocol.oracleWith_oracles, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles,
    TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public, TypeTree.toTypeTree_done,
    Interaction.TypeTree.node, TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
    TypeTree.RoleDecoration.toTypeTreeRoles_public, TypeTree.RoleDecoration.toTypeTreeRoles_done,
    Verifier.toCounterpartValue, Verifier.toCounterpartWith, firstRoundFragment]
  dsimp only [TwoParty.run, InteractionOver.runTypeTree,
    InteractionOver.TwoParty.pairedTypeTree, InteractionOver.TwoParty.paired,
    TwoParty.participantProfile, TwoParty.collectParticipantOutputs]
  simp only [simulateQ_bind, simulateQ_pure, simulate_latestSum, pure_bind, bind_assoc, id_eq]
  apply bind_congr
  rintro ⟨q, respond⟩
  change Message R deg at q
  by_cases hcheck : (domain.map (fun x => q.val.eval x)).sum = stmt.target
  · simp only [hcheck, ↓reduceIte, simulateQ_bind, simulateQ_pure]
    rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' ambient)
      (fun _ => rfl), simulateQ_id']
    simp only [simulate_latest, pure_bind, bind_assoc]
    rfl
  · simp only [hcheck, ↓reduceIte, simulateQ_pure, pure_bind]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Decompose the actual composed run into the first message, check, challenge, and response,
then execute the existing remaining verifier over the exported interface. -/
theorem execute_appendExported_succ (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R deg (count + 1)).tree
      (protocol R deg (count + 1)).roles (fun _ => Unit)) :
    (fun result => result.2.2.map (fun claim => OpenClaim.closeWith claim
      (result.1.closingImpl (protocol R deg (count + 1)).oracles A impl))) <$>
      executeStrategies ambient (protocol R deg (count + 1)).tree
        (protocol R deg (count + 1)).roles (protocol R deg (count + 1)).oracles A impl prover
        (composedVerifier R n deg ambient challenge domain count start finish A originalOracle
          stmt) =
    (do
      let chosen ← prover
      if (domain.map (fun x => chosen.1.val.eval x)).sum = stmt.target then
        let r ← challenge
        let next ← chosen.2 (some r)
        execute R n deg ambient challenge domain count (start + 1) (by omega)
          (polynomialFamily R n deg).spec.toPFunctor (VirtualOracle.id (polynomialFamily R n deg))
          ⟨chosen.1.val.eval r, Fin.snoc stmt.challenges r⟩ (originalOracle.eval impl) next
      else
        let _ ← chosen.2 none
        return none) := by
  have composed := congrArg (fun program => (fun result => result.2.2) <$> program)
    (executeStrategies_appendExported_close ambient (firstRoundProtocol R deg).tree
      (fun p => (remainingProtocol R deg count p).tree) (firstRoundProtocol R deg).roles
      (fun p => (remainingProtocol R deg count p).roles) (firstRoundProtocol R deg).oracles
      (fun p => (remainingProtocol R deg count p).oracles) A impl
      (midpointStatement R n deg count start finish) (fun _ => Spec.OracleStatement R n deg)
      (fun _ => polynomialFamily R n deg) (fun _ => FinalStatement R n)
      (fun _ => Spec.OracleStatement R n deg) (fun _ => polynomialFamily R n deg)
      (fun _ => Unit) prover
      (firstRoundFragment R n deg ambient challenge domain count start finish A originalOracle stmt)
      (remainingVerifier R n deg ambient challenge domain count start finish))
  simp only [Functor.map_map] at composed
  refine composed.trans ?_
  simp only [map_bind, map_pure]
  have firstRunEq := exportedPrefixRun_firstRound R n deg ambient challenge domain count
    start finish
    A originalOracle stmt impl prover
  unfold exportedPrefixRun at firstRunEq
  rw [firstRunEq]
  simp only [bind_assoc]
  apply bind_congr
  rintro ⟨q, respond⟩
  change Message R deg at q
  by_cases hcheck : (domain.map (fun x => q.val.eval x)).sum = stmt.target
  · simp only [hcheck, ↓reduceIte, pure_bind, bind_assoc]
    apply bind_congr
    intro r
    apply bind_congr
    intro next
    simp only [firstRoundProtocol, Core.firstRoundProtocol, Protocol.oracleWith_tree,
      Protocol.public_tree,
      Protocol.done_tree, Protocol.oracleWith_oracles, Protocol.public_oracles,
      Protocol.done_oracles]
    simp only [TypeTree.ExecutionPath.ofTypeTreePath,
      PFunctor.FreeM.mapLensPathToPathAlong,
      remainingProtocol, Core.remainingProtocol,
      remainingVerifier]
    dsimp only [TypeTree.ExecutionPath.toBranchPath, PFunctor.FreeM.projectPathAlong,
      PFunctor.FreeM.projectPathAlongLocalMap, PFunctor.FreeM.Displayed.LocalMap.toHom,
      PFunctor.FreeM.Displayed.LocalMap.toHomFun, TypeTree.oracle, TypeTree.public,
      Oracle.TypeTree.done, TypeTree.runtimeLens]
    simp only [cast_eq,
      StrategyOver.TwoParty.Counterpart.mapOutput_id]
    rw [firstRound_closingImpl_literal R deg A impl q (some r)]
    rw [VirtualOracle.eval_sumWeaken_extendImpl]
    change Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles (fun _ => Unit) at next
    have closed := executeStrategiesCore_closed_eq_run
      (protocol := protocol R deg count) (originalOracle.eval impl) next
      (verifier R n deg ambient challenge domain count (start + 1) (by omega)
        (polynomialFamily R n deg).spec.toPFunctor
        (VirtualOracle.id (polynomialFamily R n deg))
        ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩)
    simpa only [execute, Core.execute, protocol, verifier, FinalStatement, TwoParty.run,
      map_eq_pure_bind, bind_assoc, pure_bind, bind_pure,
      InteractionOver.TwoParty.pairedTypeTree, InteractionOver.TwoParty.paired, TerminalClaim]
      using closed.symm
  · simp only [hcheck, ↓reduceIte, pure_bind, bind_assoc]
    apply bind_congr
    intro next
    simp only [firstRoundProtocol, Core.firstRoundProtocol, Protocol.oracleWith_tree,
      Protocol.public_tree,
      Protocol.done_tree, Protocol.oracleWith_oracles, Protocol.public_oracles,
      Protocol.done_oracles]
    simp only [TypeTree.ExecutionPath.ofTypeTreePath,
      PFunctor.FreeM.mapLensPathToPathAlong,
      remainingProtocol, Core.remainingProtocol,
      remainingVerifier]
    dsimp only [TypeTree.ExecutionPath.toBranchPath, PFunctor.FreeM.projectPathAlong,
      PFunctor.FreeM.projectPathAlongLocalMap, PFunctor.FreeM.Displayed.LocalMap.toHom,
      PFunctor.FreeM.Displayed.LocalMap.toHomFun, TypeTree.oracle, TypeTree.public,
      Oracle.TypeTree.done, TypeTree.runtimeLens]
    simp only [cast_eq,
      StrategyOver.TwoParty.Counterpart.mapOutput_id]
    rw [firstRound_closingImpl_literal R deg A impl q none]
    rw [VirtualOracle.eval_sumWeaken_extendImpl]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The composed verifier has the same actual closed result as the existing native verifier,
for every whole prover, including its effectful response to rejection. -/
theorem execute_eq_appendExported (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy ambient (protocol R deg (count + 1)).tree
      (protocol R deg (count + 1)).roles (fun _ => Unit)) :
    execute R n deg ambient challenge domain (count + 1) start finish A originalOracle stmt
      impl prover =
    (fun result => result.2.2.map (fun claim => OpenClaim.closeWith claim
      (result.1.closingImpl (protocol R deg (count + 1)).oracles A impl))) <$>
      executeStrategies ambient (protocol R deg (count + 1)).tree
        (protocol R deg (count + 1)).roles (protocol R deg (count + 1)).oracles A impl prover
        (composedVerifier R n deg ambient challenge domain count start finish A originalOracle
          stmt) := by
  rw [execute_succ R n deg ambient challenge domain count start finish A originalOracle stmt
    impl prover]
  rw [execute_appendExported_succ]
  apply bind_congr
  rintro ⟨q, respond⟩
  change Message R deg at q
  by_cases hcheck : (domain.map (fun x => q.val.eval x)).sum = stmt.target
  · simp only [hcheck, ↓reduceIte]
    apply bind_congr
    intro r
    apply bind_congr
    intro next
    apply execute_eq_of_originalOracle_eq
    rw [VirtualOracle.eval_sumWeaken_extendImpl, VirtualOracle.eval_id]
  · simp only [hcheck, ↓reduceIte]

/-- Project the actual accepted suffix run to its closed native result. -/
theorem exportedSuffixRun_some (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (impl : QueryImpl (ofPFunctor A) Id) (q : Message R deg) (r : R)
    (next : Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles (fun _ => Unit))
    (mid : OpenClaim (ofPFunctor (Access.extend A (polynomialInterface R deg)))
      (Spec.StatementRound R n ⟨start + 1, by omega⟩) (polynomialFamily R n deg)) :
    (fun result => result.2) <$> exportedSuffixRun ambient (firstRoundProtocol R deg).tree
      (fun p => (remainingProtocol R deg count p).tree)
      (fun p => (remainingProtocol R deg count p).roles) (firstRoundProtocol R deg).oracles
      (fun p => (remainingProtocol R deg count p).oracles) A impl
      (midpointStatement R n deg count start finish) (fun _ => Spec.OracleStatement R n deg)
      (fun _ => polynomialFamily R n deg) (fun _ => FinalStatement R n)
      (fun _ => Spec.OracleStatement R n deg) (fun _ => polynomialFamily R n deg) (fun _ => Unit)
      (remainingVerifier R n deg ambient challenge domain count start finish)
      ⟨⟨q, ⟨some r, PUnit.unit⟩⟩, next, mid⟩ =
      execute R n deg ambient challenge domain count (start + 1) (by omega)
        (polynomialFamily R n deg).spec.toPFunctor (VirtualOracle.id (polynomialFamily R n deg))
        mid.stmt (mid.oracles.eval (Access.extendImpl A (polynomialInterface R deg) impl q))
        next := by
  have h := Interaction.Oracle.executeStrategiesCore_closed_eq_run
    (protocol := protocol R deg count)
    (mid.oracles.eval (Access.extendImpl A (polynomialInterface R deg) impl q)) next
    (verifier R n deg ambient challenge domain count (start + 1) (by omega)
      (polynomialFamily R n deg).spec.toPFunctor (VirtualOracle.id (polynomialFamily R n deg))
      mid.stmt)
  simp only [exportedSuffixRun, execute, map_bind, map_pure, bind_pure]
  exact h.symm
/-- An aborted public branch returns no final claim. -/
theorem exportedSuffixRun_none (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + (count + 1) = n) (A : PFunctor)
    (impl : QueryImpl (ofPFunctor A) Id) (q : Message R deg) (next : Unit)
    (mid : OpenClaim (ofPFunctor (Access.extend A (polynomialInterface R deg)))
      Unit (polynomialFamily R n deg)) :
    (fun result => result.2) <$> exportedSuffixRun ambient (firstRoundProtocol R deg).tree
      (fun p => (remainingProtocol R deg count p).tree)
      (fun p => (remainingProtocol R deg count p).roles) (firstRoundProtocol R deg).oracles
      (fun p => (remainingProtocol R deg count p).oracles) A impl
      (midpointStatement R n deg count start finish) (fun _ => Spec.OracleStatement R n deg)
      (fun _ => polynomialFamily R n deg) (fun _ => FinalStatement R n)
      (fun _ => Spec.OracleStatement R n deg) (fun _ => polynomialFamily R n deg) (fun _ => Unit)
      (remainingVerifier R n deg ambient challenge domain count start finish)
      ⟨⟨q, ⟨none, PUnit.unit⟩⟩, next, mid⟩ = pure none := by
  rfl

end
end Sumcheck.Interaction.Native

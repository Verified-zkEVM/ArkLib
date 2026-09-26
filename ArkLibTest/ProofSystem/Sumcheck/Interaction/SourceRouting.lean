/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.SourceRouting
import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol

/-! # Two Sumcheck rounds through an exported interface

The first round exports the slice of its original bivariate oracle plus the evaluation of its
actual first message. The prefix has the native optional challenge and abort shape; the second
round uses the existing sampled multivariate verifier over the exported univariate interface.
Its final relation observes that transformed oracle, including both actual prefix resources.
-/

namespace Sumcheck.Interaction.Native.SourceRoutingTest

open OracleComp OracleSpec Polynomial
open Interaction.Oracle
open SingleRound MultivariateRound

noncomputable section


abbrev ambient : OracleSpec Nat := Nat →ₒ Nat

def event (tag : Nat) : OracleComp ambient Nat := liftM (ambient.query tag)

def affine (a b : Nat) : SingleRound.Message Nat 1 :=
  ⟨C a * X + C b, Polynomial.mem_degreeLE.mpr
    (degree_add_le_of_degree_le (degree_C_mul_X_le a) (degree_C_le.trans zero_le_one))⟩

private theorem eval_affine (a b x : Nat) : (affine a b).val.eval x = a * x + b := by
  simp only [affine, eval_add, eval_mul, eval_C, eval_X]

private theorem answer_affine (a b x : Nat) :
    @OracleInterface.answer (SingleRound.Message Nat 1) (polynomialInterface Nat 1)
      (affine a b) x = a * x + b := by
  change (affine a b).val.eval x = _
  exact eval_affine a b x

abbrev firstProtocol := Interaction.Oracle.Protocol.oracleWith (SingleRound.Message Nat 1)
  (polynomialInterface Nat 1)
  (Interaction.Oracle.Protocol.public .receiver (Option Nat) fun _ => .done)

/-- The prefix has the full native verifier's one-round public abort shape. -/
example : protocol Nat 1 1 = firstProtocol := by
  unfold protocol
  congr 2
  funext choice
  cases choice <;> rfl
abbrev raw := (polynomialFamily Nat 2 1).spec.toPFunctor
abbrev exported := polynomialFamily Nat 1 1
abbrev prefixAccess := Access.extend raw (polynomialInterface Nat 1)

/-- The exported query combines original bivariate input with the actual prefix message. -/
def exportAt (r : Nat) : VirtualOracle (ofPFunctor prefixAccess) exported := ⟨fun query => do
  let old : Nat ← liftM ((ofPFunctor prefixAccess).query
    (.inl ⟨(), Fin.cons r query.2⟩))
  let sent : Nat ← liftM ((ofPFunctor prefixAccess).query (.inr r))
  return old + sent⟩

/-- The ordinary fragment checks its first Sumcheck sum and publishes a challenge or abort. -/
def firstVerifier (target : Nat) : Verifier.Fragment ambient firstProtocol.tree
    firstProtocol.roles firstProtocol.oracles raw (fun p =>
      OpenClaim (ofPFunctor (TypeTree.accessAfter firstProtocol.tree firstProtocol.oracles raw p))
        Nat exported) := by
  refine pure ?_
  exact do
    let total ← latestSum Nat 1 ambient raw [0, 1]
    if total = target then
      let r ← OracleComp.liftComp (event 1) (ambient + ofPFunctor prefixAccess)
      let value ← latest Nat 1 ambient raw r
      return ⟨some r, ⟨3 * value, exportAt r⟩⟩
    else return ⟨none, ⟨0, exportAt 0⟩⟩

def suffixProtocol (p : firstProtocol.tree.BranchPath) : Interaction.Oracle.Protocol :=
  match p.2.1 with
  | none => .done
  | some _ => SingleRound.protocol Nat 1


abbrev suffixTree (p : firstProtocol.tree.BranchPath) := (suffixProtocol p).tree

/-- The second verifier's authoring signature contains only the exported univariate oracle. -/
def secondVerifier (p : firstProtocol.tree.BranchPath) (target : Nat) :
    Verifier.Strategy ambient (suffixTree p) (suffixProtocol p).roles (suffixProtocol p).oracles
      exported.spec.toPFunctor (fun q => Option (OpenClaim
        (ofPFunctor (TypeTree.accessAfter (suffixTree p) (suffixProtocol p).oracles
          exported.spec.toPFunctor q)) (FinalStatement Nat 1) exported)) := by
  rcases p with ⟨_, choice, _⟩
  cases choice with
  | none => exact pure none
  | some r =>
    exact MultivariateRound.sampledVerifier Nat 1 1 ambient 0 ⟨target, Fin.elim0⟩
      [0, 1] (event 2)

/-- The ordinary whole prover keeps its first challenge in private memory for the second message. -/
def wholeProver (hidden : Nat) (bump : Nat := 0) : Prover.Strategy ambient
    (PFunctor.FreeM.append firstProtocol.tree suffixTree)
    (PFunctor.FreeM.Displayed.Decoration.append firstProtocol.roles
      (fun p => (suffixProtocol p).roles)) (fun _ => Nat) := by
  refine pure ⟨affine 2 1, ?_⟩
  intro choice
  cases choice with
  | none => exact do
    let tag ← event 3
    return hidden + tag
  | some r => exact do
    let tag ← event 3
    return pure ⟨affine 1 (3 * r + 1 + bump), fun _ => do
      let finish ← event 4
      return hidden + tag + finish⟩

/-- The input behavior is the nonconstant bivariate polynomial x + y. -/
def inputImpl : QueryImpl (ofPFunctor raw) Id := fun q => q.2 0 + q.2 1

def appended (target : Nat) := Verifier.appendExported ambient firstProtocol.tree suffixTree
  firstProtocol.roles (fun p => (suffixProtocol p).roles)
  firstProtocol.oracles (fun p => (suffixProtocol p).oracles) raw
  (fun _ => Nat) (fun _ => exported.Realization) (fun _ => exported)
  (fun _ => FinalStatement Nat 1) (fun _ => exported.Realization) (fun _ => exported)
  (firstVerifier target) secondVerifier

/-- Close only with the actual combined path's handler, retaining the private prover output. -/
def closed (target hidden : Nat) (bump : Nat := 0) :=
  (fun result => (result.2.1, result.2.2.map (fun claim => claim.closeWith
    (result.1.closingImpl (PFunctor.FreeM.Displayed.Decoration.append firstProtocol.oracles
      (fun p => (suffixProtocol p).oracles)) raw inputImpl)))) <$>
    executeStrategies ambient (PFunctor.FreeM.append firstProtocol.tree suffixTree)
      (PFunctor.FreeM.Displayed.Decoration.append firstProtocol.roles
        (fun p => (suffixProtocol p).roles))
      (PFunctor.FreeM.Displayed.Decoration.append firstProtocol.oracles
        (fun p => (suffixProtocol p).oracles)) raw inputImpl
      (wholeProver hidden bump) (appended target)

/-- The two public challenges and the two actual prover responses have different tags. -/
def record : QueryImpl ambient (StateM (List Nat)) := fun tag => do
  modify (fun seen => seen ++ [tag])
  return if tag = 1 then 2 else if tag = 2 then 3 else if tag = 3 then 50 else 60

def claimSummary (claim : ClosedClaim (FinalStatement Nat 1) exported) : Nat × Nat :=
  (claim.stmt.target, claim.oracles ⟨(), claim.stmt.challenges⟩)

def observed (target hidden : Nat) (bump : Nat := 0) :=
  (simulateQ record
  ((fun result => (result.1, result.2.map claimSummary)) <$>
      closed target hidden bump)).run []

set_option backward.isDefEq.respectTransparency false in
/-- Both actual Sumcheck rounds finish at the transformed oracle's claimed value. -/
theorem accepted (hidden : Nat) : observed 4 hidden =
    ((hidden + 50 + 60, some (10, 10)), [1, 3, 2, 4]) := by
  have execution := executeStrategies_appendExported_close ambient firstProtocol.tree suffixTree
    firstProtocol.roles (fun p => (suffixProtocol p).roles)
    firstProtocol.oracles (fun p => (suffixProtocol p).oracles) raw inputImpl
    (fun _ => Nat) (fun _ => exported.Realization) (fun _ => exported)
    (fun _ => FinalStatement Nat 1) (fun _ => exported.Realization) (fun _ => exported)
    (fun _ => Nat) (wholeProver hidden) (firstVerifier 4) secondVerifier
  have summary := congrArg (fun program => (simulateQ record
    ((fun result => (result.2.1, result.2.2.map claimSummary)) <$> program)).run []) execution
  simpa only [closed, observed, appended, Functor.map_map] using summary.trans (by
    simp only [firstVerifier, wholeProver, secondVerifier, suffixTree, suffixProtocol,
      firstProtocol, SingleRound.protocol, Interaction.Oracle.Protocol.oracleWith_tree,
      Interaction.Oracle.Protocol.public_tree, Interaction.Oracle.Protocol.done_tree,
      Interaction.Oracle.Protocol.oracleWith_roles, Interaction.Oracle.Protocol.public_roles,
      Interaction.Oracle.Protocol.done_roles, Interaction.Oracle.Protocol.oracleWith_oracles,
      Interaction.Oracle.Protocol.public_oracles, Interaction.Oracle.Protocol.done_oracles,
      TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public, TypeTree.toTypeTree_done,
      TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
      TypeTree.RoleDecoration.toTypeTreeRoles_public,
      TypeTree.RoleDecoration.toTypeTreeRoles_done, TypeTree.ExecutionPath.ofTypeTreePath,
      PFunctor.FreeM.mapLensPathToPathAlong, TypeTree.ExecutionPath.toBranchPath_oracle,
      TypeTree.ExecutionPath.toBranchPath_public, TypeTree.ExecutionPath.toBranchPath_done,
      TypeTree.runtimeLens, TypeTree.ExecutionPath.closingImpl_oracle,
      TypeTree.ExecutionPath.closingImpl_public, TypeTree.ExecutionPath.closingImpl_done,
      Interaction.InteractionOver.runTypeTree,
      Interaction.InteractionOver.TwoParty.pairedTypeTree,
      Interaction.InteractionOver.TwoParty.paired, Interaction.TwoParty.participantProfile,
      Interaction.TwoParty.collectParticipantOutputs, onAppendedRuntime, castRuntimeStrategy,
      Interaction.TwoParty.run, Interaction.StrategyOver.TwoParty.Focal.splitPrefix,
      Interaction.StrategyOver.TwoParty.Counterpart.mapOutput, Interaction.ShapeOver.mapOutput,
      Interaction.ShapeOver.TwoParty.pairedTypeTree, Interaction.ShapeOver.TwoParty.paired,
      PFunctor.Lens.id, Verifier.toCounterpartValue, Verifier.toCounterpartWith,
      MultivariateRound.sampledVerifier, MultivariateRound.simulate_challenge, eval_affine,
      exportAt, VirtualOracle.eval, simulate_latestSum, simulate_latest, simulateQ_bind,
      simulateQ_pure, map_bind, map_pure, pure_bind, bind_assoc, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceAdd,
      ite_true]
    simp only [event, Verifier.liftAccessImpl, Access.extendImpl, QueryImpl.compose,
      QueryImpl.add_eq_hAdd, simulateQ_liftM_query, QueryImpl.add, answer_affine, simulateQ_pure,
      simulateQ_bind, StateT.run_bind, StateT.run_pure]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- A wrong first sum takes the public abort branch and retains its actual prover response. -/
theorem abort (hidden : Nat) : observed 0 hidden =
    ((hidden + 50, none), [3]) := by
  have execution := executeStrategies_appendExported_close ambient firstProtocol.tree suffixTree
    firstProtocol.roles (fun p => (suffixProtocol p).roles)
    firstProtocol.oracles (fun p => (suffixProtocol p).oracles) raw inputImpl
    (fun _ => Nat) (fun _ => exported.Realization) (fun _ => exported)
    (fun _ => FinalStatement Nat 1) (fun _ => exported.Realization) (fun _ => exported)
    (fun _ => Nat) (wholeProver hidden) (firstVerifier 0) secondVerifier
  have summary := congrArg (fun program => (simulateQ record
    ((fun result => (result.2.1, result.2.2.map claimSummary)) <$> program)).run []) execution
  simpa only [closed, observed, appended, Functor.map_map] using summary.trans (by
    simp only [firstVerifier, wholeProver, secondVerifier, suffixTree, suffixProtocol,
      firstProtocol, SingleRound.protocol, Interaction.Oracle.Protocol.oracleWith_tree,
      Interaction.Oracle.Protocol.public_tree, Interaction.Oracle.Protocol.done_tree,
      Interaction.Oracle.Protocol.oracleWith_roles, Interaction.Oracle.Protocol.public_roles,
      Interaction.Oracle.Protocol.done_roles, Interaction.Oracle.Protocol.oracleWith_oracles,
      Interaction.Oracle.Protocol.public_oracles, Interaction.Oracle.Protocol.done_oracles,
      TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public, TypeTree.toTypeTree_done,
      TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
      TypeTree.RoleDecoration.toTypeTreeRoles_public,
      TypeTree.RoleDecoration.toTypeTreeRoles_done, TypeTree.ExecutionPath.ofTypeTreePath,
      PFunctor.FreeM.mapLensPathToPathAlong, TypeTree.ExecutionPath.toBranchPath_oracle,
      TypeTree.ExecutionPath.toBranchPath_public, TypeTree.ExecutionPath.toBranchPath_done,
      TypeTree.runtimeLens, TypeTree.ExecutionPath.closingImpl_oracle,
      TypeTree.ExecutionPath.closingImpl_public, TypeTree.ExecutionPath.closingImpl_done,
      Interaction.InteractionOver.runTypeTree,
      Interaction.InteractionOver.TwoParty.pairedTypeTree,
      Interaction.InteractionOver.TwoParty.paired, Interaction.TwoParty.participantProfile,
      Interaction.TwoParty.collectParticipantOutputs, onAppendedRuntime, castRuntimeStrategy,
      Interaction.TwoParty.run, Interaction.StrategyOver.TwoParty.Focal.splitPrefix,
      Interaction.StrategyOver.TwoParty.Counterpart.mapOutput, Interaction.ShapeOver.mapOutput,
      Interaction.ShapeOver.TwoParty.pairedTypeTree, Interaction.ShapeOver.TwoParty.paired,
      PFunctor.Lens.id, Verifier.toCounterpartValue, Verifier.toCounterpartWith,
      MultivariateRound.sampledVerifier, eval_affine, exportAt, VirtualOracle.eval,
      simulate_latestSum, simulateQ_bind, simulateQ_pure, map_bind, map_pure, pure_bind,
      bind_assoc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Nat.reduceAdd, Nat.reduceEqDiff, ite_false]
    simp only [event, Access.extendImpl, QueryImpl.add_eq_hAdd, simulateQ_liftM_query,
      answer_affine, StateT.run_bind, StateT.run_pure]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- A bad second message rejects after its challenge and actual prover response. -/
theorem suffix_rejected (hidden : Nat) : observed 4 hidden 1 =
    ((hidden + 50 + 60, none), [1, 3, 2, 4]) := by
  have execution := executeStrategies_appendExported_close ambient firstProtocol.tree suffixTree
    firstProtocol.roles (fun p => (suffixProtocol p).roles)
    firstProtocol.oracles (fun p => (suffixProtocol p).oracles) raw inputImpl
    (fun _ => Nat) (fun _ => exported.Realization) (fun _ => exported)
    (fun _ => FinalStatement Nat 1) (fun _ => exported.Realization) (fun _ => exported)
    (fun _ => Nat) (wholeProver hidden 1) (firstVerifier 4) secondVerifier
  have summary := congrArg (fun program => (simulateQ record
    ((fun result => (result.2.1, result.2.2.map claimSummary)) <$> program)).run []) execution
  simpa only [closed, observed, appended, Functor.map_map] using summary.trans (by
    simp only [firstVerifier, wholeProver, secondVerifier, suffixTree, suffixProtocol,
      firstProtocol, SingleRound.protocol, Interaction.Oracle.Protocol.oracleWith_tree,
      Interaction.Oracle.Protocol.public_tree, Interaction.Oracle.Protocol.done_tree,
      Interaction.Oracle.Protocol.oracleWith_roles, Interaction.Oracle.Protocol.public_roles,
      Interaction.Oracle.Protocol.done_roles, Interaction.Oracle.Protocol.oracleWith_oracles,
      Interaction.Oracle.Protocol.public_oracles, Interaction.Oracle.Protocol.done_oracles,
      TypeTree.toTypeTree_oracle, TypeTree.toTypeTree_public, TypeTree.toTypeTree_done,
      TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
      TypeTree.RoleDecoration.toTypeTreeRoles_public,
      TypeTree.RoleDecoration.toTypeTreeRoles_done, TypeTree.ExecutionPath.ofTypeTreePath,
      PFunctor.FreeM.mapLensPathToPathAlong, TypeTree.ExecutionPath.toBranchPath_oracle,
      TypeTree.ExecutionPath.toBranchPath_public, TypeTree.ExecutionPath.toBranchPath_done,
      TypeTree.runtimeLens, TypeTree.ExecutionPath.closingImpl_oracle,
      TypeTree.ExecutionPath.closingImpl_public, TypeTree.ExecutionPath.closingImpl_done,
      Interaction.InteractionOver.runTypeTree,
      Interaction.InteractionOver.TwoParty.pairedTypeTree,
      Interaction.InteractionOver.TwoParty.paired, Interaction.TwoParty.participantProfile,
      Interaction.TwoParty.collectParticipantOutputs, onAppendedRuntime, castRuntimeStrategy,
      Interaction.TwoParty.run, Interaction.StrategyOver.TwoParty.Focal.splitPrefix,
      Interaction.StrategyOver.TwoParty.Counterpart.mapOutput, Interaction.ShapeOver.mapOutput,
      Interaction.ShapeOver.TwoParty.pairedTypeTree, Interaction.ShapeOver.TwoParty.paired,
      PFunctor.Lens.id, Verifier.toCounterpartValue, Verifier.toCounterpartWith,
      MultivariateRound.sampledVerifier, MultivariateRound.simulate_challenge, eval_affine,
      exportAt, VirtualOracle.eval, simulate_latestSum, simulate_latest, simulateQ_bind,
      simulateQ_pure, map_bind, map_pure, pure_bind, bind_assoc, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceAdd,
      ite_true]
    simp only [event, Verifier.liftAccessImpl, Access.extendImpl, QueryImpl.compose,
      QueryImpl.add_eq_hAdd, simulateQ_liftM_query, QueryImpl.add, answer_affine, simulateQ_pure,
      simulateQ_bind, StateT.run_bind, StateT.run_pure]
    rfl)

/-- Every claim actually returned on success satisfies the existing native final relation. -/
theorem accepted_relation (hidden : Nat) (claim : ClosedClaim (FinalStatement Nat 1) exported)
    (hclaim : ((simulateQ record (closed 4 hidden)).run []).1.2 = some claim) :
    outputRelation Nat 1 1 claim := by
  have h := congrArg (fun result => result.1.2) (accepted hidden)
  simp only [observed, simulateQ_map, StateT.run_map] at h
  change Option.map claimSummary ((simulateQ record (closed 4 hidden)).run []).1.2 =
    some (10, 10) at h
  rw [hclaim] at h
  have values : claimSummary claim = (10, 10) := Option.some.inj h
  exact (congrArg Prod.snd values).trans (congrArg Prod.fst values).symm

end
end Sumcheck.Interaction.Native.SourceRoutingTest

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import all PolyFun.Interaction.Basic.StrategyOver

public import ArkLib.Interaction.Oracle.Security.KnowledgeAppend
public import ArkLib.Interaction.Oracle.Sequential
public import ArkLib.Interaction.Oracle.SourceRouting
public import VCVio.EvalDist.Monad.Support
public import ArkLib.Interaction.Oracle.Claim

/-!
# Sequential composition of local knowledge certificates

Dependent native append preserves the first stage's backward witness maps and its local
knowledge bounds, then continues with the certificate selected by the actual first-stage path.
The suffix tree is selected by the public structural path; its knowledge certificate may also
depend on the concrete messages and the closed middle claim of that execution.
-/

@[expose] public section

universe u v w

namespace Interaction.Oracle.Security

open Interaction.Oracle.TypeTree PFunctor.FreeM
open Interaction.TwoParty OracleComp OracleSpec

/-- Identify the composite terminal relation using the existing native path split. No witness
is selected: the named equivalence composes the two endpoint carrier identifications. -/
def TerminalRelation.append {tree : Oracle.TypeTree.{u}} {state : KnowledgeState.{w}}
    (first : RoundExtractor tree state) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (second : (path : tree.ExecutionPath) →
      RoundExtractor (suffix path.toBranchPath) (first.terminalState path))
    {Context : Type u} {family : ClaimFamily.{u, u} Context} (problem : Problem.{u, u, w} family)
    (context : (path : tree.ExecutionPath) → (suffix path.toBranchPath).ExecutionPath → Context)
    (claim : (path : tree.ExecutionPath) → (rest : (suffix path.toBranchPath).ExecutionPath) →
      family.Claim (context path rest))
    (terminal : ∀ path, TerminalRelation (second path) problem (context path) (claim path)) :
    TerminalRelation (first.append suffix second) problem
      (fun full => let parts := PathAlong.split TypeTree.runtimeLens tree suffix full
                   context parts.1 parts.2)
      (fun full => let parts := PathAlong.split TypeTree.runtimeLens tree suffix full
                   claim parts.1 parts.2) := by
  let sameState := fun (full : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) =>
    (congrArg (first.append suffix second).terminalState
      (PathAlong.append_split TypeTree.runtimeLens tree suffix full).symm).trans
      (RoundExtractor.terminalState_append first suffix second _ _)
  refine ⟨fun full => (Equiv.cast (congrArg KnowledgeState.Witness (sameState full))).trans
    ((terminal (PathAlong.split TypeTree.runtimeLens tree suffix full).1).witnessEquiv
      (PathAlong.split TypeTree.runtimeLens tree suffix full).2), ?_⟩
  intro full witness
  let parts := PathAlong.split TypeTree.runtimeLens tree suffix full
  have transport : ((first.append suffix second).terminalState full).holds witness ↔
      ((second parts.1).terminalState parts.2).holds
        ((Equiv.cast (congrArg KnowledgeState.Witness (sameState full))) witness) := by
    have law (a b : KnowledgeState.{w}) (h : a = b) (x : a.Witness) :
        a.holds x ↔ b.holds (cast (congrArg KnowledgeState.Witness h) x) := by
      cases h
      rfl
    exact law _ _ (sameState full) witness
  simpa using transport.trans ((terminal parts.1).knowledge_iff parts.2 _)

/-- Replace ordinary fragment leaves by a declared path-dependent value. All native node effects
and access restrictions are retained. -/
def withLeaf {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    {tree : Oracle.TypeTree.{u}} {roles : tree.RoleDecoration}
    {oracles : tree.OracleDecoration} {initial : PFunctor.{u, u}}
    {A B : tree.BranchPath → Type u}
    (leaf : (path : tree.BranchPath) → B path)
    (fragment : Verifier.Fragment ambient tree roles oracles initial A) :
    Verifier.Fragment ambient tree roles oracles initial B :=
  Verifier.Fragment.mapOutput ambient (fun path _ => leaf path) fragment

/-- The native value interpreter observes the replacement leaf at its actual concrete path. -/
theorem toCounterpartValue_withLeaf {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (A B : tree.BranchPath → Type u) (leaf : (path : tree.BranchPath) → B path)
    (fragment : Verifier.Fragment ambient tree roles oracles initial A) :
    Verifier.toCounterpartValue ambient tree roles oracles initial impl B
      (withLeaf ambient leaf fragment) =
      StrategyOver.TwoParty.Counterpart.mapOutput
        (fun path _ => leaf (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl A fragment) := by
  calc
    _ = Verifier.toCounterpartWith ambient tree roles oracles initial impl A B
        (fun path _ _ => leaf path) fragment :=
      Verifier.toCounterpartWith_mapOutput ambient tree roles oracles initial impl A B B
        (fun path _ => leaf path) (fun _ _ out => out) fragment
    _ = _ := Verifier.toCounterpartWith_finish_eq_mapOutput ambient tree roles oracles initial
      impl A B (fun path _ _ => leaf path) fragment

/-- The actual native runner returns exactly the declared leaf at its actual path. The prover's
private output, failed computations, and every node effect remain paired with that run. -/
theorem run_withLeaf {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (A B : tree.BranchPath → Type u) (leaf : (path : tree.BranchPath) → B path)
    (OutP : tree.ExecutionPath → Type u)
    (prover : Prover.Strategy ambient tree roles OutP)
    (fragment : Verifier.Fragment ambient tree roles oracles initial A) :
    TwoParty.run tree.toTypeTree (RoleDecoration.toTypeTreeRoles tree roles) prover
      (Verifier.toCounterpartValue ambient tree roles oracles initial impl B
        (withLeaf ambient leaf fragment)) =
    (fun result => ⟨result.1, result.2.1,
      leaf (TypeTree.ExecutionPath.ofTypeTreePath result.1).toBranchPath⟩) <$>
      TwoParty.run tree.toTypeTree (RoleDecoration.toTypeTreeRoles tree roles) prover
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl A fragment) := by
  rw [toCounterpartValue_withLeaf]
  exact run_counterpart_mapOutput _ prover _

/-- Complete a fragment with a pure path-dependent terminal observation. -/
def withOutput {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    {tree : Oracle.TypeTree.{u}} {roles : tree.RoleDecoration}
    {oracles : tree.OracleDecoration} {initial : PFunctor.{u, u}}
    {A B : tree.BranchPath → Type u} (output : (path : tree.BranchPath) → B path)
    (fragment : Verifier.Fragment ambient tree roles oracles initial A) :
    Verifier.Strategy ambient tree roles oracles initial B :=
  withLeaf ambient (fun path => pure (output path)) fragment

/-- The completed native verifier returns exactly the pure terminal observation at the path
produced by the same paired execution. This equation covers a pure terminal observation. -/
theorem executeStrategies_withOutput {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (A B : tree.BranchPath → Type u) (output : (path : tree.BranchPath) → B path)
    (OutP : tree.ExecutionPath → Type u)
    (prover : Prover.Strategy ambient tree roles OutP)
    (fragment : Verifier.Fragment ambient tree roles oracles initial A) :
    executeStrategies ambient tree roles oracles initial impl prover
      (withOutput ambient output fragment) =
    (fun result => ⟨TypeTree.ExecutionPath.ofTypeTreePath result.1, result.2.1,
      output (TypeTree.ExecutionPath.ofTypeTreePath result.1).toBranchPath⟩) <$>
      TwoParty.run tree.toTypeTree (RoleDecoration.toTypeTreeRoles tree roles) prover
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl A fragment) := by
  have interpreted : Verifier.toCounterpart ambient tree roles oracles initial impl B
      (withOutput ambient output fragment) =
      StrategyOver.TwoParty.Counterpart.mapOutput
        (fun path _ => (pure (output
          (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath) : OracleComp ambient _))
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl A fragment) := by
    unfold Verifier.toCounterpart withOutput withLeaf
    rw [Verifier.toCounterpartWith_mapOutput]
    simp only [simulateQ_pure]
    exact Verifier.toCounterpartWith_finish_eq_mapOutput ambient tree roles oracles initial
      impl A (fun p => OracleComp ambient (B p)) (fun path _ _ => pure (output path)) fragment
  rw [executeStrategies_eq_run, interpreted, run_counterpart_mapOutput]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro result
  rfl

/-- The native terminal interpreter closes a pure output with the same run's resources. -/
theorem toCounterpartWith_output {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (ofPFunctor initial) Id)
    (A B Out : tree.BranchPath → Type u) (output : (path : tree.BranchPath) → B path)
    (finish : (path : tree.BranchPath) →
      QueryImpl (ofPFunctor (TypeTree.accessAfter tree oracles initial path)) Id →
        B path → Out path)
    (fragment : Verifier.Fragment ambient tree roles oracles initial A) :
    Verifier.toCounterpartWith ambient tree roles oracles initial impl _
      (fun p => OracleComp ambient (Out p))
      (fun path actual action => finish path actual <$> simulateQ
        (Verifier.liftAccessImpl ambient
          (TypeTree.accessAfter tree oracles initial path) actual) action)
      (withOutput ambient output fragment) =
    StrategyOver.TwoParty.Counterpart.mapOutput (fun path _ =>
      (pure (finish (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath
        ((TypeTree.ExecutionPath.ofTypeTreePath path).closingImpl oracles initial impl)
        (output (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)) : OracleComp ambient _))
      (Verifier.toCounterpartValue ambient tree roles oracles initial impl A fragment) := by
  unfold withOutput withLeaf
  rw [Verifier.toCounterpartWith_mapOutput]
  simp only [simulateQ_pure]
  exact Verifier.toCounterpartWith_finish_eq_mapOutput ambient tree roles oracles initial impl
    A (fun p => OracleComp ambient (Out p))
    (fun path actual _ => pure (finish path actual (output path))) fragment

/-- Close the declared middle leaf using exactly the resources of its concrete native path. -/
def closedMiddle {I : Type u} (tree : Oracle.TypeTree.{u})
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (ofPFunctor initial) Id)
    (Stmt : tree.BranchPath → Type u) (Data : tree.BranchPath → I → Type u)
    (Export : (p : tree.BranchPath) → OracleFamily I (Data p))
    (leaf : (p : tree.BranchPath) →
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles initial p)) (Stmt p) (Export p))
    (path : tree.ExecutionPath) : ClosedClaim (Stmt path.toBranchPath) (Export path.toBranchPath) :=
  (leaf path.toBranchPath).closeWith (path.closingImpl oracles initial impl)

/-- The suffix oracle input is the behavior of the actual closed middle claim. -/
theorem closedMiddle_oracles {I : Type u} (tree : Oracle.TypeTree.{u})
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (ofPFunctor initial) Id)
    (Stmt : tree.BranchPath → Type u) (Data : tree.BranchPath → I → Type u)
    (Export : (p : tree.BranchPath) → OracleFamily I (Data p))
    (leaf : (p : tree.BranchPath) →
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles initial p)) (Stmt p) (Export p))
    (path : tree.ExecutionPath) :
    (closedMiddle tree oracles initial impl Stmt Data Export leaf path).oracles =
      (leaf path.toBranchPath).oracles.eval (path.closingImpl oracles initial impl) := rfl

/-- The actual prefix runner returns the same closed middle claim used by the certificate seam.
This equality retains the native private prover output and concrete path, and does not assume
that the middle claim is true or admissible. -/
theorem run_withLeaf_closedMiddle {ι I : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor.{u, u})
    (impl : QueryImpl (ofPFunctor initial) Id)
    (A Stmt : tree.BranchPath → Type u) (Data : tree.BranchPath → I → Type u)
    (Export : (p : tree.BranchPath) → OracleFamily I (Data p))
    (leaf : (p : tree.BranchPath) →
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles initial p)) (Stmt p) (Export p))
    (OutP : tree.ExecutionPath → Type u) (prover : Prover.Strategy ambient tree roles OutP)
    (fragment : Verifier.Fragment ambient tree roles oracles initial A) :
    (fun result => (⟨result.1, result.2.1,
      result.2.2.closeWith
        ((TypeTree.ExecutionPath.ofTypeTreePath result.1).closingImpl oracles initial impl)⟩ :
      (path : tree.toTypeTree.Path) × OutP (TypeTree.ExecutionPath.ofTypeTreePath path) ×
        ClosedClaim (Stmt (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
          (Export (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath))) <$>
      TwoParty.run tree.toTypeTree (RoleDecoration.toTypeTreeRoles tree roles) prover
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl _
          (withLeaf ambient leaf fragment)) =
    (fun result => (⟨result.1, result.2.1,
      closedMiddle tree oracles initial impl Stmt Data Export leaf
        (TypeTree.ExecutionPath.ofTypeTreePath result.1)⟩ :
      (path : tree.toTypeTree.Path) × OutP (TypeTree.ExecutionPath.ofTypeTreePath path) ×
        ClosedClaim (Stmt (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
          (Export (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath))) <$>
      TwoParty.run tree.toTypeTree (RoleDecoration.toTypeTreeRoles tree roles) prover
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl A fragment) := by
  rw [run_withLeaf, Functor.map_map]
  rfl

/-- The actual exported composite uses the declared first leaf at the actual prefix path,
retains its native private continuation, invokes the suffix with the actual closed middle
behavior, and closes its actual terminal result. This equation introduces no relation premise. -/
theorem executeStrategies_appendExported_withLeaf_close {ι I J : Type u}
    (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (ofPFunctor initial) Id)
    (Stmt : tree.BranchPath → Type u)
    (Data : tree.BranchPath → I → Type u)
    (Export : (p : tree.BranchPath) → OracleFamily.{u, u, u} I (Data p))
    (FinalStmt : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (FinalData : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → J → Type u)
    (Final : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      OracleFamily.{u, u, u} J (FinalData p))
    (OutP : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type u)
    (prover : Prover.Strategy ambient (PFunctor.FreeM.append tree suffix)
      (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles) OutP)
    (A : tree.BranchPath → Type u)
    (leaf : (p : tree.BranchPath) →
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree firstOracles initial p))
        (Stmt p) (Export p))
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial A)
    (second : (p : tree.BranchPath) → Stmt p → Verifier.Strategy ambient (suffix p)
      (secondRoles p) (secondOracles p) (Export p).spec.toPFunctor (fun q => Option
        (OpenClaim (ofPFunctor (TypeTree.accessAfter (suffix p) (secondOracles p)
          (Export p).spec.toPFunctor q))
          (FinalStmt (PFunctor.FreeM.Path.append tree suffix p q))
          (Final (PFunctor.FreeM.Path.append tree suffix p q))))) :
    (fun result => (⟨result.1, result.2.1,
      result.2.2.map (fun claim => claim.closeWith (result.1.closingImpl
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl))⟩ :
      (path : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) × OutP path ×
        Option (ClosedClaim (FinalStmt path.toBranchPath) (Final path.toBranchPath)))) <$>
      executeStrategies ambient (PFunctor.FreeM.append tree suffix)
        (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles)
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl prover
        (Verifier.appendExported ambient tree suffix firstRoles secondRoles
          firstOracles secondOracles
          initial Stmt Data Export FinalStmt FinalData Final
          (withLeaf ambient leaf first) second) = (do
      let ⟨path₁, continuation, _original⟩ ← TwoParty.run tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles tree firstRoles)
        (StrategyOver.TwoParty.Focal.splitPrefix
          (onAppendedRuntime ambient Participant.focal tree suffix firstRoles secondRoles OutP
            prover))
        (Verifier.toCounterpartValue ambient tree firstRoles firstOracles initial impl A first)
      let mid := leaf (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath
      let ⟨rest, outP, action⟩ ← TwoParty.run
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath).toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles
          (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
          (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath))
        continuation
        (StrategyOver.TwoParty.Counterpart.mapOutput (fun rest action =>
          cast (congrArg (fun branch => OracleComp ambient
            (Option (ClosedClaim (FinalStmt branch) (Final branch))))
            (runtimeBranch_append tree suffix path₁ rest).symm) action)
          (Verifier.toCounterpartWith ambient
            (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (Export (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath).spec.toPFunctor
            (mid.oracles.eval
              ((TypeTree.ExecutionPath.ofTypeTreePath path₁).closingImpl firstOracles initial impl))
            _ (fun q => OracleComp ambient (Option (ClosedClaim
              (FinalStmt (PFunctor.FreeM.Path.append tree suffix
                (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath q))
              (Final (PFunctor.FreeM.Path.append tree suffix
                (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath q)))))
            (fun q actual action => (fun result => result.map (fun claim =>
              claim.closeWith actual)) <$> simulateQ (Verifier.liftAccessImpl ambient
                (TypeTree.accessAfter
                  (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
                  (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
                  (OracleFamily.spec
                    (Export (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)).toPFunctor
                  q) actual) action)
            (second (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath mid.stmt)))
      let outV ← action
      return ⟨TypeTree.ExecutionPath.ofTypeTreePath
        (cast (congrArg Interaction.TypeTree.Path
          (TypeTree.toTypeTree_append tree suffix).symm)
          (PFunctor.FreeM.Path.append tree.toTypeTree
            (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
            path₁ rest)), outP, outV⟩) := by
  rw [executeStrategies_appendExported_close, toCounterpartValue_withLeaf,
    run_counterpart_mapOutput]
  simp only [bind_map_left]

namespace KnowledgeCertificate

/-- Compose certificates along a native suffix whose root is the actual first terminal state. -/
def append {tree : Oracle.TypeTree.{0}} {state : KnowledgeState.{w}}
    {firstRoles : tree.RoleDecoration} (first : KnowledgeCertificate tree firstRoles state)
    (suffix : tree.BranchPath → Oracle.TypeTree.{0})
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (second : (path : tree.ExecutionPath) → KnowledgeCertificate (suffix path.toBranchPath)
      (secondRoles path.toBranchPath) (first.extractor.terminalState path)) :
    KnowledgeCertificate (PFunctor.FreeM.append tree suffix)
      (Displayed.Decoration.append firstRoles secondRoles) state where
  extractor := first.extractor.append suffix (fun path => (second path).extractor)
  challenges := RoundExtractor.appendSchedule suffix firstRoles secondRoles first.challenges
    (fun path => (second path).challenges)
  prover_preserving := first.extractor.isProverPreserving_append suffix
    (fun path => (second path).extractor) firstRoles secondRoles first.prover_preserving
    (fun path => (second path).prover_preserving)
  local_bound := first.extractor.isLocallyBounded_append suffix
    (fun path => (second path).extractor)
    firstRoles secondRoles first.challenges (fun path => (second path).challenges)
    first.local_bound (fun path => (second path).local_bound)

section Sequential

variable {tree : Oracle.TypeTree.{0}} {state : KnowledgeState.{w}}
  {firstRoles : tree.RoleDecoration} (first : KnowledgeCertificate tree firstRoles state)
  (suffix : tree.BranchPath → Oracle.TypeTree.{0})
  (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
  {Context : Type} {family : ClaimFamily.{0, 0} Context} (middleProblem : Problem.{0, 0, w} family)
  (middleContext : tree.ExecutionPath → Context)
  (middleClaim : (path : tree.ExecutionPath) → family.Claim (middleContext path))
  (middle : TerminalRelation first.extractor middleProblem middleContext middleClaim)
  (second : (path : tree.ExecutionPath) → KnowledgeCertificate (suffix path.toBranchPath)
    (secondRoles path.toBranchPath)
    (KnowledgeState.ofProblem middleProblem (middleContext path) (middleClaim path)))

/-- Transport the suffix input through the actual middle relation's named witness identification.
The suffix covers every authored first path, even when that relation is false. -/
def sequentialSuffix (path : tree.ExecutionPath) :
    KnowledgeCertificate (suffix path.toBranchPath) (secondRoles path.toBranchPath)
      (first.extractor.terminalState path) :=
  (second path).changeInputState (first.extractor.terminalState path) (middle.witnessEquiv path)
    (middle.knowledge_iff path)

/-- Sequential composition preserves prover laws and every local bad-challenge bound across an
explicit middle witness relation. The suffix covers all authored boundaries; no middle witness
supplier, truth hypothesis, or admissibility restriction is introduced. -/
def sequential : KnowledgeCertificate (PFunctor.FreeM.append tree suffix)
    (Displayed.Decoration.append firstRoles secondRoles) state :=
  first.append suffix secondRoles
    (sequentialSuffix first suffix secondRoles middleProblem middleContext middleClaim
      middle second)

/-- The composite extractor first extracts the suffix witness, converts it through the actual
middle relation's named carrier equivalence, and then extracts the first input witness. -/
theorem extractWitness_sequential (path : tree.ExecutionPath)
    (rest : (suffix path.toBranchPath).ExecutionPath)
    (witness : ((sequentialSuffix first suffix secondRoles middleProblem middleContext middleClaim
      middle second path).extractor.terminalState rest).Witness) :
    (sequential first suffix secondRoles middleProblem middleContext middleClaim
      middle second).extractor.extractWitness
        (PathAlong.append TypeTree.runtimeLens tree suffix path rest)
        ((RoundExtractor.terminalState_append first.extractor suffix
          (fun p => (sequentialSuffix first suffix secondRoles middleProblem middleContext
            middleClaim
            middle second p).extractor) path rest).symm ▸ witness) =
    first.extractor.extractWitness path ((middle.witnessEquiv path).symm
      ((second path).extractor.extractWitness rest
        (RoundExtractor.terminalWitnessEquiv (second path).extractor
          (first.extractor.terminalState path) (middle.witnessEquiv path) rest witness))) := by
  refine (RoundExtractor.extractWitness_append first.extractor suffix
    (fun p => (sequentialSuffix first suffix secondRoles middleProblem middleContext
            middleClaim
      middle second p).extractor) path rest witness).trans ?_
  apply congrArg (first.extractor.extractWitness path)
  calc
    _ = (middle.witnessEquiv path).symm
        (middle.witnessEquiv path
          ((sequentialSuffix first suffix secondRoles middleProblem middleContext middleClaim
            middle second path).extractor.extractWitness rest witness)) :=
      ((middle.witnessEquiv path).symm_apply_apply _).symm
    _ = _ := congrArg (middle.witnessEquiv path).symm
      (RoundExtractor.extractWitness_changeInputState (second path).extractor
        (first.extractor.terminalState path) (middle.witnessEquiv path) rest witness)

/-- Exact final relation law after sequential composition, including an empty suffix. All carrier
identifications are explicit; this equivalence does not select or supply a terminal witness. -/
theorem terminalKnowledge_sequential_iff
    {FinalContext : Type} {finalFamily : ClaimFamily.{0, 0} FinalContext}
    (finalProblem : Problem.{0, 0, w} finalFamily)
    (finalContext : (path : tree.ExecutionPath) →
      (suffix path.toBranchPath).ExecutionPath → FinalContext)
    (finalClaim : (path : tree.ExecutionPath) → (rest : (suffix path.toBranchPath).ExecutionPath) →
      finalFamily.Claim (finalContext path rest))
    (finalRelation : ∀ path, TerminalRelation (second path).extractor finalProblem
      (finalContext path) (finalClaim path))
    (path : tree.ExecutionPath) (rest : (suffix path.toBranchPath).ExecutionPath)
    (witness : ((sequentialSuffix first suffix secondRoles middleProblem middleContext middleClaim
      middle second path).extractor.terminalState rest).Witness) :
    ((sequential first suffix secondRoles middleProblem middleContext middleClaim
      middle second).extractor.terminalState
       (PathAlong.append TypeTree.runtimeLens tree suffix path rest)).holds
      ((RoundExtractor.terminalState_append first.extractor suffix
        (fun p => (sequentialSuffix first suffix secondRoles middleProblem middleContext
            middleClaim
          middle second p).extractor) path rest).symm ▸ witness) ↔
    finalProblem.rel (finalContext path rest) (finalClaim path rest)
      ((finalRelation path).witnessEquiv rest
        (RoundExtractor.terminalWitnessEquiv (second path).extractor
          (first.extractor.terminalState path) (middle.witnessEquiv path) rest witness)) := by
  exact (KnowledgeState.holds_cast
    (RoundExtractor.terminalState_append first.extractor suffix
      (fun p => (sequentialSuffix first suffix secondRoles middleProblem middleContext
            middleClaim
        middle second p).extractor) path rest) witness).trans
    ((RoundExtractor.terminalKnowledge_changeInputState (second path).extractor
      (first.extractor.terminalState path) (middle.witnessEquiv path)
      (middle.knowledge_iff path) rest witness).trans
      ((finalRelation path).knowledge_iff rest _))

/-- The final relation on every actual composite path, split by the native dependent path API. -/
def sequentialTerminalRelation
    {FinalContext : Type} {finalFamily : ClaimFamily.{0, 0} FinalContext}
    (finalProblem : Problem.{0, 0, w} finalFamily)
    (finalContext : (path : tree.ExecutionPath) →
      (suffix path.toBranchPath).ExecutionPath → FinalContext)
    (finalClaim : (path : tree.ExecutionPath) → (rest : (suffix path.toBranchPath).ExecutionPath) →
      finalFamily.Claim (finalContext path rest))
    (finalRelation : ∀ path, TerminalRelation (second path).extractor finalProblem
      (finalContext path) (finalClaim path)) :
    TerminalRelation
      (sequential first suffix secondRoles middleProblem middleContext middleClaim
        middle second).extractor finalProblem
      (fun full => let parts := PathAlong.split TypeTree.runtimeLens tree suffix full
                   finalContext parts.1 parts.2)
      (fun full => let parts := PathAlong.split TypeTree.runtimeLens tree suffix full
                   finalClaim parts.1 parts.2) :=
  TerminalRelation.append first.extractor suffix
    (fun p => (sequentialSuffix first suffix secondRoles middleProblem middleContext
            middleClaim
      middle second p).extractor) finalProblem finalContext finalClaim
    (fun p => (finalRelation p).changeInputState (first.extractor.terminalState p)
      (middle.witnessEquiv p) (middle.knowledge_iff p))

end Sequential

/-- Compose knowledge certificates at the actual closed oracle claim returned by a deterministic
native first leaf. The suffix may depend on its statement and its concrete closed behavior,
while its native tree still depends only on the structural branch. The certificate is required
at every authored first path, including false and inadmissible middle claims. -/
def sequentialClosed {I : Type} {tree : Oracle.TypeTree.{0}} {state : KnowledgeState.{w}}
    {firstRoles : tree.RoleDecoration} (first : KnowledgeCertificate tree firstRoles state)
    (suffix : tree.BranchPath → Oracle.TypeTree.{0})
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id)
    (Stmt : tree.BranchPath → Type) (Data : tree.BranchPath → I → Type)
    (Export : (p : tree.BranchPath) → OracleFamily I (Data p))
    (leaf : (p : tree.BranchPath) →
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree firstOracles initial p)) (Stmt p) (Export p))
    (middleProblem : Problem.{0, 0, w} (ClaimFamily.closedOracle tree.BranchPath Stmt Export))
    (middle : TerminalRelation first.extractor middleProblem (fun path => path.toBranchPath)
      (closedMiddle tree firstOracles initial impl Stmt Data Export leaf))
    (second : (path : tree.ExecutionPath) → KnowledgeCertificate (suffix path.toBranchPath)
      (secondRoles path.toBranchPath) (KnowledgeState.ofProblem middleProblem path.toBranchPath
        (closedMiddle tree firstOracles initial impl Stmt Data Export leaf path))) :
    KnowledgeCertificate (PFunctor.FreeM.append tree suffix)
      (Displayed.Decoration.append firstRoles secondRoles) state :=
  first.sequential suffix secondRoles middleProblem (fun path => path.toBranchPath)
    (closedMiddle tree firstOracles initial impl Stmt Data Export leaf) middle second

end KnowledgeCertificate

/-- Actual interpreted native actions have the declared fresh challenge marginals. Receive
computations and every supported remaining verifier strategy are retained in this linkage. -/
def SamplesChallenges {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [MonadAttach m]
    (handler : QueryImpl ambient m) :
    (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    QueryImpl (ofPFunctor initial) Id → (Leaf : tree.BranchPath → Type) →
    Verifier.Fragment ambient tree roles oracles initial Leaf →
    RoundExtractor.ChallengeSchedule tree roles → Prop
  | .done, _, _, _, _, _, _, _ => True
  | .public _ next, ⟨.sender, roles⟩, oracles, initial, impl, Leaf, verifier, schedule =>
      ∀ move after, after ∈ support (simulateQ handler
        (simulateQ (Verifier.liftAccessImpl ambient initial impl) (verifier move))) →
        SamplesChallenges ambient handler (next move) (roles move) (oracles.2 move) initial impl
          (fun path => Leaf ⟨move, path⟩) after (schedule.2 move)
  | .public Moves next, ⟨.receiver, roles⟩, oracles, initial, impl, Leaf, verifier, schedule =>
      (∀ event : Moves → Prop,
        Pr{let chosen ← (simulateQ handler
          (simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier))}[event chosen.1] =
        Pr{let challenge ← schedule.1.1}[event challenge]) ∧
      ∀ chosen ∈ support (simulateQ handler
        (simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier)),
        SamplesChallenges ambient handler (next chosen.1) (roles chosen.1) (oracles.2 chosen.1)
          initial impl (fun path => Leaf ⟨chosen.1, path⟩) chosen.2 (schedule.2 chosen.1)
  | .oracle _ next, roles, oracles, initial, impl, Leaf, verifier, schedule =>
      ∀ message after, after ∈ support (simulateQ handler (simulateQ
        (Verifier.liftAccessImpl ambient (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)) verifier)) →
        SamplesChallenges ambient handler (next PUnit.unit) (roles.2 PUnit.unit)
          (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
          (Access.extendImpl initial oracles.1 impl message)
          (fun path => Leaf ⟨PUnit.unit, path⟩) after (schedule message)

/-- A certificate's local bound applies to the actual interpreted native receiver action.
The eventual witness remains existentially quantified inside that fresh-challenge probability. -/
theorem native_badChallenge_bound {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [MonadAttach m]
    (handler : QueryImpl ambient m) {Moves : Type} {next : Moves → Oracle.TypeTree.{0}}
    (roles : (move : Moves) → (next move).RoleDecoration)
    (oracles : (Oracle.TypeTree.public Moves next).OracleDecoration)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    (Leaf : (Oracle.TypeTree.public Moves next).BranchPath → Type)
    (verifier : Verifier.Fragment ambient (.public Moves next) ⟨.receiver, roles⟩
      oracles initial Leaf) {state : KnowledgeState.{w}}
    (certificate : KnowledgeCertificate (.public Moves next) ⟨.receiver, roles⟩ state)
    (fresh : SamplesChallenges ambient handler (.public Moves next) ⟨.receiver, roles⟩
      oracles initial impl Leaf verifier certificate.challenges) :
    Pr{let chosen ← (simulateQ handler
      (simulateQ (Verifier.liftAccessImpl ambient initial impl) verifier))}[
        certificate.extractor.badChallenge chosen.1] ≤ certificate.challenges.1.2 := by
  rw [fresh.1 certificate.extractor.badChallenge]
  exact ((_root_.RoundByRound.GameFamily.isBounded_iff _ _).mp certificate.local_bound.1) () ()

set_option backward.isDefEq.respectTransparency false in
/-- Replacing a fragment's deterministic leaf preserves all actual challenge marginals. -/
theorem samplesChallenges_mapOutput {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m) :
    (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    (impl : QueryImpl (ofPFunctor initial) Id) → (A B : tree.BranchPath → Type) →
    (f : (path : tree.BranchPath) → A path → B path) →
    (verifier : Verifier.Fragment ambient tree roles oracles initial A) →
    (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    SamplesChallenges ambient handler tree roles oracles initial impl A verifier schedule →
    SamplesChallenges ambient handler tree roles oracles initial impl B
      (Verifier.Fragment.mapOutput ambient f verifier) schedule
  | .done, _, _, _, _, _, _, _, _, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, oracles, initial, impl, A, B, f,
      verifier, schedule, fresh => by
      intro move after supported
      simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput,
        Verifier.localShape, Verifier.decorate, simulateQ_map] at supported
      rw [MonadAttach.support_map] at supported
      obtain ⟨original, horiginal, rfl⟩ := supported
      exact samplesChallenges_mapOutput ambient handler (next move) (roles move) (oracles.2 move)
        initial impl (fun p => A ⟨move, p⟩) (fun p => B ⟨move, p⟩)
        (fun p => f ⟨move, p⟩) original (schedule.2 move) (fresh move original horiginal)
  | .public _ next, ⟨.receiver, roles⟩, oracles, initial, impl, A, B, f,
      verifier, schedule, fresh => by
      constructor
      · intro event
        simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput,
          Verifier.localShape, Verifier.decorate, simulateQ_map, prEvent_map]
        exact fresh.1 event
      · intro chosen supported
        simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput,
          Verifier.localShape, Verifier.decorate, simulateQ_map] at supported
        rw [MonadAttach.support_map] at supported
        obtain ⟨original, horiginal, rfl⟩ := supported
        exact samplesChallenges_mapOutput ambient handler (next original.1) (roles original.1)
          (oracles.2 original.1) initial impl (fun p => A ⟨original.1, p⟩)
          (fun p => B ⟨original.1, p⟩) (fun p => f ⟨original.1, p⟩) original.2
          (schedule.2 original.1) (fresh.2 original horiginal)
  | .oracle _ next, roles, oracles, initial, impl, A, B, f,
      verifier, schedule, fresh => by
      intro message after supported
      simp only [Verifier.Fragment.mapOutput, ShapeOver.mapOutput,
        Verifier.localShape, Verifier.decorate, simulateQ_map] at supported
      rw [MonadAttach.support_map] at supported
      obtain ⟨original, horiginal, rfl⟩ := supported
      exact samplesChallenges_mapOutput ambient handler (next PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl message)
        (fun p => A ⟨PUnit.unit, p⟩) (fun p => B ⟨PUnit.unit, p⟩)
        (fun p => f ⟨PUnit.unit, p⟩) original (schedule message)
        (fresh message original horiginal)

set_option backward.isDefEq.respectTransparency false in
/-- Routing a fragment's declared source preserves its actual fresh challenge laws under the
composed input handler, including the same concrete messages received after routing. -/
theorem samplesChallenges_routeFragment {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m) :
    (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (source target : PFunctor) →
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target))) →
    (impl : QueryImpl (ofPFunctor target) Id) → (Leaf : tree.BranchPath → Type) →
    (verifier : Verifier.Fragment ambient tree roles oracles source Leaf) →
    (schedule : RoundExtractor.ChallengeSchedule tree roles) →
    SamplesChallenges ambient handler tree roles oracles source (QueryImpl.compose impl route)
      Leaf verifier schedule →
    SamplesChallenges ambient handler tree roles oracles target impl Leaf
      (Verifier.routeFragment ambient tree roles oracles source target route Leaf verifier) schedule
  | .done, _, _, _, _, _, _, _, _, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, oracles, source, target, route, impl, Leaf,
      verifier, schedule, fresh => by
      intro move after supported
      simp only [Verifier.routeFragment, ← map_eq_pure_bind, simulateQ_map,
        Verifier.simulateQ_routeProgram] at supported
      rw [MonadAttach.support_map] at supported
      obtain ⟨original, horiginal, rfl⟩ := supported
      exact samplesChallenges_routeFragment ambient handler (next move) (roles move)
        (oracles.2 move) source target route impl (fun p => Leaf ⟨move, p⟩) original
        (schedule.2 move) (fresh move original horiginal)
  | .public _ next, ⟨.receiver, roles⟩, oracles, source, target, route, impl, Leaf,
      verifier, schedule, fresh => by
      constructor
      · intro event
        simp only [Verifier.routeFragment, ← map_eq_pure_bind, simulateQ_map,
          Verifier.simulateQ_routeProgram, Functor.map_map]
        simpa only [← map_eq_pure_bind] using fresh.1 event
      · intro chosen supported
        simp only [Verifier.routeFragment, ← map_eq_pure_bind, simulateQ_map,
          Verifier.simulateQ_routeProgram] at supported
        rw [MonadAttach.support_map] at supported
        obtain ⟨original, horiginal, rfl⟩ := supported
        exact samplesChallenges_routeFragment ambient handler (next original.1) (roles original.1)
          (oracles.2 original.1) source target route impl (fun p => Leaf ⟨original.1, p⟩)
          original.2 (schedule.2 original.1) (fresh.2 original horiginal)
  | .oracle _ next, roles, oracles, source, target, route, impl, Leaf,
      verifier, schedule, fresh => by
      intro message after supported
      simp only [Verifier.routeFragment, ← map_eq_pure_bind, simulateQ_map,
        Verifier.simulateQ_routeProgram, Access.compose_extendRoute] at supported
      rw [MonadAttach.support_map] at supported
      obtain ⟨original, horiginal, rfl⟩ := supported
      have following := samplesChallenges_routeFragment ambient handler (next PUnit.unit)
        (roles.2 PUnit.unit) (oracles.2 PUnit.unit) (Access.extend source oracles.1)
        (Access.extend target oracles.1) (Access.extendRoute source target oracles.1 route)
        (Access.extendImpl target oracles.1 impl message) (fun p => Leaf ⟨PUnit.unit, p⟩)
        original (schedule message)
      apply following
      simpa only [Access.compose_extendRoute] using fresh message original horiginal

/-- Routing terminal actions also preserves actual node challenge laws. -/
theorem samplesChallenges_routeStrategy {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m)
    (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (source target : PFunctor)
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (impl : QueryImpl (ofPFunctor target) Id) (Out : tree.BranchPath → Type)
    (verifier : Verifier.Strategy ambient tree roles oracles source Out)
    (schedule : RoundExtractor.ChallengeSchedule tree roles)
    (fresh : SamplesChallenges ambient handler tree roles oracles source
      (QueryImpl.compose impl route) _ verifier schedule) :
    SamplesChallenges ambient handler tree roles oracles target impl _
      (Verifier.routeStrategy ambient tree roles oracles source target route Out verifier)
      schedule := by
  apply samplesChallenges_mapOutput
  exact samplesChallenges_routeFragment ambient handler tree roles oracles source target route
    impl _ verifier schedule fresh

/-- Routing an output claim preserves actual node challenge laws and its same-path source. -/
theorem samplesChallenges_routeClaimStrategy {ι I : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m)
    (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (source target : PFunctor)
    (route : QueryImpl (ofPFunctor source) (OracleComp (ofPFunctor target)))
    (impl : QueryImpl (ofPFunctor target) Id)
    (Stmt : tree.BranchPath → Type) (Data : tree.BranchPath → I → Type)
    (Out : (p : tree.BranchPath) → OracleFamily I (Data p))
    (verifier : Verifier.Strategy ambient tree roles oracles source (fun p => Option
      (OpenClaim (ofPFunctor (TypeTree.accessAfter tree oracles source p)) (Stmt p) (Out p))))
    (schedule : RoundExtractor.ChallengeSchedule tree roles)
    (fresh : SamplesChallenges ambient handler tree roles oracles source
      (QueryImpl.compose impl route) _ verifier schedule) :
    SamplesChallenges ambient handler tree roles oracles target impl _
      (Verifier.routeClaimStrategy ambient tree roles oracles source target route
        Stmt Data Out verifier) schedule := by
  apply samplesChallenges_mapOutput
  exact samplesChallenges_routeStrategy ambient handler tree roles oracles source target route
    impl _ verifier schedule fresh

/-- Replacing a deterministic leaf preserves the actual freshness laws. -/
theorem samplesChallenges_withLeaf {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m)
    (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (ofPFunctor initial) Id) (A B : tree.BranchPath → Type)
    (leaf : (path : tree.BranchPath) → B path)
    (verifier : Verifier.Fragment ambient tree roles oracles initial A)
    (schedule : RoundExtractor.ChallengeSchedule tree roles)
    (fresh : SamplesChallenges ambient handler tree roles oracles initial impl A
      verifier schedule) :
    SamplesChallenges ambient handler tree roles oracles initial impl B
      (withLeaf ambient leaf verifier) schedule :=
  samplesChallenges_mapOutput ambient handler tree roles oracles initial impl A B
    (fun path _ => leaf path) verifier schedule fresh

set_option backward.isDefEq.respectTransparency false in
/-- Native dependent append preserves the components' actual fresh challenge laws. The suffix
law is required at every authored concrete middle path and its same-path closing handler. -/
theorem samplesChallenges_append_withLeaf {ι : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m) :
    (tree : Oracle.TypeTree.{0}) → (suffix : tree.BranchPath → Oracle.TypeTree.{0}) →
    (firstRoles : tree.RoleDecoration) →
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration) →
    (firstOracles : tree.OracleDecoration) →
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration) →
    (initial : PFunctor) → (impl : QueryImpl (ofPFunctor initial) Id) →
    (A Mid : tree.BranchPath → Type) →
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type) →
    (leaf : (p : tree.BranchPath) → Mid p) →
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial A) →
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Fragment ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (Path.append tree suffix p q))) →
    (firstSchedule : RoundExtractor.ChallengeSchedule tree firstRoles) →
    (secondSchedule : (path : tree.ExecutionPath) →
      RoundExtractor.ChallengeSchedule (suffix path.toBranchPath) (secondRoles path.toBranchPath)) →
    SamplesChallenges ambient handler tree firstRoles firstOracles initial impl A first
      firstSchedule →
    (∀ path, SamplesChallenges ambient handler (suffix path.toBranchPath)
      (secondRoles path.toBranchPath) (secondOracles path.toBranchPath)
      (TypeTree.accessAfter tree firstOracles initial path.toBranchPath)
      (path.closingImpl firstOracles initial impl)
      (fun q => Out (Path.append tree suffix path.toBranchPath q))
      (second path.toBranchPath (leaf path.toBranchPath)) (secondSchedule path)) →
    SamplesChallenges ambient handler (PFunctor.FreeM.append tree suffix)
      (Displayed.Decoration.append firstRoles secondRoles)
      (Displayed.Decoration.append firstOracles secondOracles) initial impl Out
      (Verifier.appendFragment ambient tree suffix firstRoles secondRoles firstOracles secondOracles
        initial Mid Out (withLeaf ambient leaf first) second)
      (RoundExtractor.appendSchedule suffix firstRoles secondRoles firstSchedule secondSchedule)
  | .done, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, freshSuffix =>
      freshSuffix PUnit.unit
  | .public _ next, suffix, ⟨.sender, roles⟩, secondRoles, firstOracles, secondOracles,
      initial, impl, A, Mid, Out, leaf, first, second, firstSchedule, secondSchedule,
      fresh, freshSuffix => by
      intro move after supported
      simp only [Verifier.appendFragment, withLeaf, Verifier.Fragment.mapOutput,
        ShapeOver.mapOutput, Verifier.localShape, Verifier.decorate, simulateQ_map,
        Functor.map_map] at supported
      rw [MonadAttach.support_map] at supported
      obtain ⟨original, horiginal, rfl⟩ := supported
      exact samplesChallenges_append_withLeaf ambient handler (next move)
        (fun p => suffix ⟨move, p⟩) (roles move) (fun p => secondRoles ⟨move, p⟩)
        (firstOracles.2 move) (fun p => secondOracles ⟨move, p⟩) initial impl
        (fun p => A ⟨move, p⟩) (fun p => Mid ⟨move, p⟩) (fun p => Out ⟨move, p⟩)
        (fun p => leaf ⟨move, p⟩) original (fun p => second ⟨move, p⟩)
        (firstSchedule.2 move) (fun p => secondSchedule ⟨move, p⟩)
        (fresh move original horiginal) (fun p => freshSuffix ⟨move, p⟩)
  | .public _ next, suffix, ⟨.receiver, roles⟩, secondRoles, firstOracles, secondOracles,
      initial, impl, A, Mid, Out, leaf, first, second, firstSchedule, secondSchedule,
      fresh, freshSuffix => by
      constructor
      · intro event
        simp only [Verifier.appendFragment, withLeaf, Verifier.Fragment.mapOutput,
          ShapeOver.mapOutput, Verifier.localShape, Verifier.decorate, simulateQ_map,
          Functor.map_map, prEvent_map]
        exact fresh.1 event
      · intro chosen supported
        simp only [Verifier.appendFragment, withLeaf, Verifier.Fragment.mapOutput,
          ShapeOver.mapOutput, Verifier.localShape, Verifier.decorate, simulateQ_map,
          Functor.map_map] at supported
        rw [MonadAttach.support_map] at supported
        obtain ⟨original, horiginal, rfl⟩ := supported
        exact samplesChallenges_append_withLeaf ambient handler (next original.1)
          (fun p => suffix ⟨original.1, p⟩) (roles original.1)
          (fun p => secondRoles ⟨original.1, p⟩) (firstOracles.2 original.1)
          (fun p => secondOracles ⟨original.1, p⟩) initial impl
          (fun p => A ⟨original.1, p⟩) (fun p => Mid ⟨original.1, p⟩)
          (fun p => Out ⟨original.1, p⟩) (fun p => leaf ⟨original.1, p⟩) original.2
          (fun p => second ⟨original.1, p⟩) (firstSchedule.2 original.1)
          (fun p => secondSchedule ⟨original.1, p⟩) (fresh.2 original horiginal)
          (fun p => freshSuffix ⟨original.1, p⟩)
  | .oracle _ next, suffix, firstRoles, secondRoles, firstOracles, secondOracles,
      initial, impl, A, Mid, Out, leaf, first, second, firstSchedule, secondSchedule,
      fresh, freshSuffix => by
      intro message after supported
      simp only [Verifier.appendFragment, withLeaf, Verifier.Fragment.mapOutput,
        ShapeOver.mapOutput, Verifier.localShape, Verifier.decorate, simulateQ_map,
        Functor.map_map] at supported
      rw [MonadAttach.support_map] at supported
      obtain ⟨original, horiginal, rfl⟩ := supported
      exact samplesChallenges_append_withLeaf ambient handler (next PUnit.unit)
        (fun p => suffix ⟨PUnit.unit, p⟩) (firstRoles.2 PUnit.unit)
        (fun p => secondRoles ⟨PUnit.unit, p⟩) (firstOracles.2 PUnit.unit)
        (fun p => secondOracles ⟨PUnit.unit, p⟩) (Access.extend initial firstOracles.1)
        (Access.extendImpl initial firstOracles.1 impl message)
        (fun p => A ⟨PUnit.unit, p⟩) (fun p => Mid ⟨PUnit.unit, p⟩)
        (fun p => Out ⟨PUnit.unit, p⟩) (fun p => leaf ⟨PUnit.unit, p⟩) original
        (fun p => second ⟨PUnit.unit, p⟩) (firstSchedule message)
        (fun p => secondSchedule ⟨message, p⟩) (fresh message original horiginal)
        (fun p => freshSuffix ⟨message, p⟩)

/-- Native exported append preserves the fresh challenge laws supplied by both components.
The suffix is checked under the oracle behavior obtained by closing the actual middle leaf with
that same concrete first path; neither middle membership nor a supplied witness is assumed. -/
theorem samplesChallenges_appendExported_withLeaf {ι I J : Type} (ambient : OracleSpec ι)
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] [MonadAttach m] [ExactMonadAttach m]
    (handler : QueryImpl ambient m)
    (tree : Oracle.TypeTree.{0}) (suffix : tree.BranchPath → Oracle.TypeTree.{0})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
    (A Stmt : tree.BranchPath → Type) (Data : tree.BranchPath → I → Type)
    (Export : (p : tree.BranchPath) → OracleFamily I (Data p))
    (FinalStmt : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type)
    (FinalData : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → J → Type)
    (Final : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      OracleFamily J (FinalData p))
    (leaf : (p : tree.BranchPath) →
      OpenClaim (ofPFunctor (TypeTree.accessAfter tree firstOracles initial p))
        (Stmt p) (Export p))
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial A)
    (second : (p : tree.BranchPath) → Stmt p → Verifier.Strategy ambient (suffix p)
      (secondRoles p) (secondOracles p) (Export p).spec.toPFunctor (fun q => Option
        (OpenClaim (ofPFunctor (TypeTree.accessAfter (suffix p) (secondOracles p)
          (Export p).spec.toPFunctor q))
          (FinalStmt (Path.append tree suffix p q)) (Final (Path.append tree suffix p q)))))
    (firstSchedule : RoundExtractor.ChallengeSchedule tree firstRoles)
    (secondSchedule : (path : tree.ExecutionPath) →
      RoundExtractor.ChallengeSchedule (suffix path.toBranchPath) (secondRoles path.toBranchPath))
    (freshFirst : SamplesChallenges ambient handler tree firstRoles firstOracles initial impl
      A first firstSchedule)
    (freshSecond : ∀ path, SamplesChallenges ambient handler (suffix path.toBranchPath)
      (secondRoles path.toBranchPath) (secondOracles path.toBranchPath)
      (Export path.toBranchPath).spec.toPFunctor
      ((leaf path.toBranchPath).oracles.eval (path.closingImpl firstOracles initial impl))
      _ (second path.toBranchPath (leaf path.toBranchPath).stmt) (secondSchedule path)) :
    SamplesChallenges ambient handler (PFunctor.FreeM.append tree suffix)
      (Displayed.Decoration.append firstRoles secondRoles)
      (Displayed.Decoration.append firstOracles secondOracles) initial impl _
      (Verifier.appendExported ambient tree suffix firstRoles secondRoles
          firstOracles secondOracles
        initial Stmt Data Export FinalStmt FinalData Final (withLeaf ambient leaf first) second)
      (RoundExtractor.appendSchedule suffix firstRoles secondRoles
        firstSchedule secondSchedule) := by
  unfold Verifier.appendExported Verifier.append
  apply samplesChallenges_append_withLeaf
  · exact freshFirst
  · intro path
    apply samplesChallenges_mapOutput
    apply samplesChallenges_mapOutput
    apply samplesChallenges_routeClaimStrategy
    exact freshSecond path

end Interaction.Oracle.Security

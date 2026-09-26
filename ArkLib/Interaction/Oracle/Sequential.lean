/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import all PolyFun.Interaction.Basic.StrategyOver
import all PolyFun.Interaction.TwoParty.Strategy
import all PolyFun.Interaction.TwoParty.Compose

public import ArkLib.Interaction.Oracle.Execution
public import ArkLib.Interaction.Oracle.RunSources

/-!
# Sequential restricted verifier fragments

Fragment boundaries return ordinary values. Suffix shapes depend on public prefix branches;
resource handlers come from the same concrete prefix execution. Native prover strategies retain
all their private continuation data.
-/

@[expose] public section

universe u

namespace Interaction.Oracle

open OracleComp OracleSpec TwoParty
open PFunctor.FreeM.Displayed (Decoration)

/-- Transport an ordinary runtime strategy along a tree equality. The transport retains its
roles and dependent private output family; it performs no monadic action. -/
def castRuntimeStrategy {m : Type u → Type u} {who : Participant.{u}}
    {first second : Interaction.TypeTree.{u}} (h : first = second)
    (roles : TwoParty.RoleDecoration first) (Out : first.Path → Type u)
    (strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) who first roles Out) :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) who second
      (cast (congrArg TwoParty.RoleDecoration h) roles)
      (fun path => Out (cast (congrArg Interaction.TypeTree.Path h.symm) path)) := by
  cases h
  exact strategy

private theorem castRuntimeStrategy_typeEq {m : Type u → Type u} {who : Participant.{u}}
    {first second : Interaction.TypeTree.{u}} (h : first = second)
    (roles : TwoParty.RoleDecoration first) (Out : first.Path → Type u) :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) who first roles Out =
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) who second
        (cast (congrArg TwoParty.RoleDecoration h) roles)
        (fun path => Out (cast (congrArg Interaction.TypeTree.Path h.symm) path)) := by
  cases h
  rfl

private theorem oracleComp_bind_heq {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {A B C : Type u} (h : B = C) (program : OracleComp ambient A)
    (first : A → OracleComp ambient B) (second : A → OracleComp ambient C)
    (same : ∀ value, HEq (first value) (second value)) :
    HEq (program >>= first) (program >>= second) := by
  cases h
  exact heq_of_eq (bind_congr (fun value => eq_of_heq (same value)))

private theorem castRuntimeStrategy_heq {m : Type u → Type u} {who : Participant.{u}}
    {first second : Interaction.TypeTree.{u}} (h : first = second)
    (roles : TwoParty.RoleDecoration first) (Out : first.Path → Type u)
    (strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) who first roles Out) :
    HEq (castRuntimeStrategy h roles Out strategy) strategy := by
  cases h
  rfl

/-- View a runtime strategy on the erased appended tree. This only transports the
existing strategy along the proved tree and role equalities. It retains all private outputs
and effects. -/
def onAppendedRuntime {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (who : Participant.{u})
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (first : tree.RoleDecoration)
    (second : (path : tree.BranchPath) → (suffix path).RoleDecoration)
    (Out : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type u)
    (strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) who
      (TypeTree.toTypeTree (PFunctor.FreeM.append tree suffix))
      (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
        (Decoration.append first second))
      (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath path))) :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) who
      (PFunctor.FreeM.append tree.toTypeTree (fun path =>
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath).toTypeTree))
      (Decoration.append (TypeTree.RoleDecoration.toTypeTreeRoles tree first) (fun path =>
        TypeTree.RoleDecoration.toTypeTreeRoles
          (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
          (second (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)))
      (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath
        (cast (congrArg Interaction.TypeTree.Path
          (TypeTree.toTypeTree_append tree suffix).symm) path))) := by
  have hroles := TypeTree.RoleDecoration.toTypeTreeRoles_append tree suffix first second
  exact hroles ▸ castRuntimeStrategy (TypeTree.toTypeTree_append tree suffix)
    (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
      (Decoration.append first second)) _ strategy

private theorem onAppendedRuntime_heq {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (who : Participant.{u}) (tree : Oracle.TypeTree.{u})
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) (first : tree.RoleDecoration)
    (second : (path : tree.BranchPath) → (suffix path).RoleDecoration)
    (Out : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type u)
    (strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) who
      (TypeTree.toTypeTree (PFunctor.FreeM.append tree suffix))
      (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
        (Decoration.append first second))
      (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath path))) :
    HEq (onAppendedRuntime ambient who tree suffix first second Out strategy) strategy := by
  simp only [onAppendedRuntime, eqRec_heq_iff]
  exact castRuntimeStrategy_heq _ _ _ strategy

private theorem run_castRuntimeStrategy {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {first second : Interaction.TypeTree.{u}} (h : first = second)
    (roles : TwoParty.RoleDecoration first) (OutP OutV : first.Path → Type u)
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      first roles OutP)
    (verifier : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      first roles OutV) :
    (fun result => ⟨cast (congrArg Interaction.TypeTree.Path h.symm) result.1,
      result.2.1, result.2.2⟩) <$>
      TwoParty.run second (cast (congrArg TwoParty.RoleDecoration h) roles)
        (castRuntimeStrategy h roles OutP prover) (castRuntimeStrategy h roles OutV verifier) =
      TwoParty.run first roles prover verifier := by
  cases h
  simp [castRuntimeStrategy]

private theorem run_cast_roles {m : Type u → Type u} [Monad m]
    {tree : Interaction.TypeTree.{u}} {first second : RoleDecoration tree}
    (h : first = second) (OutP OutV : tree.Path → Type u)
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      tree first OutP)
    (verifier : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      tree first OutV) :
    TwoParty.run tree second (h ▸ prover) (h ▸ verifier) =
      TwoParty.run tree first prover verifier := by
  cases h
  rfl

private theorem run_onAppendedRuntime {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (first : tree.RoleDecoration)
    (second : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (OutP OutV : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type u)
    (prover : Prover.Strategy ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append first second) OutP)
    (verifier : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
      Participant.counterpart (TypeTree.toTypeTree (PFunctor.FreeM.append tree suffix))
      (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
        (Decoration.append first second))
      (fun p => OutV (TypeTree.ExecutionPath.ofTypeTreePath p))) :
    (fun result => ⟨cast (congrArg Interaction.TypeTree.Path
        (TypeTree.toTypeTree_append tree suffix).symm) result.1, result.2.1, result.2.2⟩) <$>
      TwoParty.run
        (PFunctor.FreeM.append tree.toTypeTree
          (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree))
        (Decoration.append (TypeTree.RoleDecoration.toTypeTreeRoles tree first)
          (fun p => TypeTree.RoleDecoration.toTypeTreeRoles
            (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath)
            (second (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath)))
        (onAppendedRuntime ambient Participant.focal tree suffix first second OutP prover)
        (onAppendedRuntime ambient Participant.counterpart tree suffix first second OutV verifier) =
      TwoParty.run (TypeTree.toTypeTree (PFunctor.FreeM.append tree suffix))
        (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
          (Decoration.append first second)) prover verifier := by
  unfold onAppendedRuntime
  rw [run_cast_roles]
  exact run_castRuntimeStrategy (TypeTree.toTypeTree_append tree suffix) _ _ _ prover verifier

/-- The public branch of a joined runtime path is the append of the two public branches. -/
theorem runtimeBranch_append (tree : Oracle.TypeTree.{u})
    (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (path : Interaction.TypeTree.Path tree.toTypeTree)
    (rest : Interaction.TypeTree.Path
      (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath).toTypeTree) :
    (TypeTree.ExecutionPath.ofTypeTreePath
      (cast (congrArg Interaction.TypeTree.Path
        (TypeTree.toTypeTree_append tree suffix).symm)
        (PFunctor.FreeM.Path.append tree.toTypeTree
          (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
          path rest))).toBranchPath =
      PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath
        (TypeTree.ExecutionPath.ofTypeTreePath rest).toBranchPath := by
  exact (congrArg TypeTree.ExecutionPath.toBranchPath
    (TypeTree.ExecutionPath.ofTypeTreePath_append tree suffix path rest)).trans
    (TypeTree.ExecutionPath.toBranchPath_append tree suffix
      (TypeTree.ExecutionPath.ofTypeTreePath path) (TypeTree.ExecutionPath.ofTypeTreePath rest))

/-- Append a value-returning fragment using a pure suffix constructor. Public prefix choices
select the suffix shape; the boundary value selects only its strategy. All query effects stay at
existing nodes. No terminal action is implicitly run at the boundary. -/
def Verifier.appendFragment {ι : Type u} (ambient : OracleSpec.{u, u} ι) :
    (tree : Oracle.TypeTree.{u}) → (suffix : tree.BranchPath → Oracle.TypeTree.{u}) →
    (firstRoles : tree.RoleDecoration) →
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration) →
    (firstOracles : tree.OracleDecoration) →
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration) →
    (initial : PFunctor.{u, u}) → (Mid : tree.BranchPath → Type u) →
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u) →
    Verifier.Fragment ambient tree firstRoles firstOracles initial Mid →
    ((p : tree.BranchPath) → Mid p →
      Verifier.Fragment ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (PFunctor.FreeM.Path.append tree suffix p q))) →
    Verifier.Fragment ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstRoles secondRoles) (Decoration.append firstOracles secondOracles)
      initial Out
  | .done, _, _, _, _, _, _, _, _, first, second => second PUnit.unit first
  | .public _ rest, suffix, ⟨.sender, roles⟩, secondRoles, firstOracles, secondOracles,
      initial, Mid, Out, first, second =>
      fun move => (Verifier.appendFragment ambient (rest move)
        (fun p => suffix ⟨move, p⟩) (roles move) (fun p => secondRoles ⟨move, p⟩)
        (firstOracles.2 move) (fun p => secondOracles ⟨move, p⟩) initial
        (fun p => Mid ⟨move, p⟩) (fun p => Out ⟨move, p⟩)
        · (fun p => second ⟨move, p⟩)) <$> first move
  | .public _ rest, suffix, ⟨.receiver, roles⟩, secondRoles, firstOracles, secondOracles,
      initial, Mid, Out, first, second =>
      (fun ⟨move, next⟩ => ⟨move, Verifier.appendFragment ambient (rest move)
        (fun p => suffix ⟨move, p⟩) (roles move) (fun p => secondRoles ⟨move, p⟩)
        (firstOracles.2 move) (fun p => secondOracles ⟨move, p⟩) initial
        (fun p => Mid ⟨move, p⟩) (fun p => Out ⟨move, p⟩)
        next (fun p => second ⟨move, p⟩)⟩) <$> first
  | .oracle _ rest, suffix, firstRoles, secondRoles, firstOracles, secondOracles,
      initial, Mid, Out, first, second =>
      (Verifier.appendFragment ambient (rest PUnit.unit)
        (fun p => suffix ⟨PUnit.unit, p⟩) (firstRoles.2 PUnit.unit)
        (fun p => secondRoles ⟨PUnit.unit, p⟩) (firstOracles.2 PUnit.unit)
        (fun p => secondOracles ⟨PUnit.unit, p⟩) (Access.extend initial firstOracles.1)
        (fun p => Mid ⟨PUnit.unit, p⟩) (fun p => Out ⟨PUnit.unit, p⟩)
        · (fun p => second ⟨PUnit.unit, p⟩)) <$> first

/-- Assemble ordinary runtime counterparts from value fragments. The suffix receives the
handler determined by the prefix's concrete path; native append retains the node schedules. -/
def Verifier.appendValueCounterpart {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Mid : tree.BranchPath → Type u)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial Mid)
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Fragment ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (PFunctor.FreeM.Path.append tree suffix p q))) :=
  StrategyOver.TwoParty.Counterpart.appendFlat
    (Output₂ := fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath
      (cast (congrArg Interaction.TypeTree.Path
        (TypeTree.toTypeTree_append tree suffix).symm) path)).toBranchPath)
    (Verifier.toCounterpartValue ambient tree firstRoles firstOracles initial impl Mid first)
    (fun path mid => StrategyOver.TwoParty.Counterpart.mapOutput
      (fun rest out => cast (congrArg Out (runtimeBranch_append tree suffix path rest).symm) out)
      (Verifier.toCounterpartValue ambient
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (TypeTree.accessAfter tree firstOracles initial
          (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        ((TypeTree.ExecutionPath.ofTypeTreePath path).closingImpl firstOracles initial impl)
        _ (second (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath mid)))

private theorem appendedRuntimeType_eq {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (who : Participant.{u}) (tree : Oracle.TypeTree.{u})
    (suffix : tree.BranchPath → Oracle.TypeTree.{u}) (first : tree.RoleDecoration)
    (second : (path : tree.BranchPath) → (suffix path).RoleDecoration)
    (Out : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type u) :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) who
      (TypeTree.toTypeTree (PFunctor.FreeM.append tree suffix))
      (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
        (Decoration.append first second))
      (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath path)) =
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) who
      (PFunctor.FreeM.append tree.toTypeTree (fun path =>
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath).toTypeTree))
      (Decoration.append (TypeTree.RoleDecoration.toTypeTreeRoles tree first) (fun path =>
        TypeTree.RoleDecoration.toTypeTreeRoles
          (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
          (second (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)))
      (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath
        (cast (congrArg Interaction.TypeTree.Path
          (TypeTree.toTypeTree_append tree suffix).symm) path))) := by
  have hroles := TypeTree.RoleDecoration.toTypeTreeRoles_append tree suffix first second
  exact hroles ▸ castRuntimeStrategy_typeEq (m := OracleComp ambient) (who := who)
    (TypeTree.toTypeTree_append tree suffix)
    (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
      (Decoration.append first second)) _

private def runtimeAppendBranch (tree : Oracle.TypeTree.{u})
    (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (path : Interaction.TypeTree.Path (PFunctor.FreeM.append tree.toTypeTree
      (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree))) :
    TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) :=
  let pieces := PFunctor.FreeM.Path.split tree.toTypeTree
    (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree) path
  PFunctor.FreeM.Path.append tree suffix
    (TypeTree.ExecutionPath.ofTypeTreePath pieces.1).toBranchPath
    (TypeTree.ExecutionPath.ofTypeTreePath pieces.2).toBranchPath

set_option backward.isDefEq.respectTransparency false in
private theorem runtimeAppendBranch_append (tree : Oracle.TypeTree.{u})
    (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (path : Interaction.TypeTree.Path tree.toTypeTree)
    (rest : Interaction.TypeTree.Path
      (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath).toTypeTree) :
    runtimeAppendBranch tree suffix (PFunctor.FreeM.Path.append tree.toTypeTree
      (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
      path rest) = PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath
        (TypeTree.ExecutionPath.ofTypeTreePath rest).toBranchPath := by
  let branches := fun pieces : (p : Interaction.TypeTree.Path tree.toTypeTree) ×
      Interaction.TypeTree.Path
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree =>
    PFunctor.FreeM.Path.append tree suffix
      (TypeTree.ExecutionPath.ofTypeTreePath pieces.1).toBranchPath
      (TypeTree.ExecutionPath.ofTypeTreePath pieces.2).toBranchPath
  exact congrArg branches (PFunctor.FreeM.Path.split_append tree.toTypeTree
    (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
    path rest)

private theorem runtimeAppendBranch_eq (tree : Oracle.TypeTree.{u})
    (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (path : Interaction.TypeTree.Path
      (PFunctor.FreeM.append tree.toTypeTree
        (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree))) :
    runtimeAppendBranch tree suffix path =
      (TypeTree.ExecutionPath.ofTypeTreePath
        (cast (congrArg Interaction.TypeTree.Path
          (TypeTree.toTypeTree_append tree suffix).symm) path)).toBranchPath := by
  let pieces := PFunctor.FreeM.Path.split tree.toTypeTree
    (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree) path
  have h := (runtimeBranch_append tree suffix pieces.1 pieces.2).symm
  simpa only [runtimeAppendBranch, pieces, PFunctor.FreeM.Path.append_split] using h

private def Verifier.appendNormalizedCounterpart {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Mid : tree.BranchPath → Type u)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial Mid)
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Fragment ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (PFunctor.FreeM.Path.append tree suffix p q))) :=
  StrategyOver.TwoParty.Counterpart.appendFlat
    (Output₂ := fun path => Out (runtimeAppendBranch tree suffix path))
    (Verifier.toCounterpartValue ambient tree firstRoles firstOracles initial impl Mid first)
    (fun path mid => StrategyOver.TwoParty.Counterpart.mapOutput
      (fun rest out =>
        cast (congrArg Out (runtimeAppendBranch_append tree suffix path rest).symm) out)
      (Verifier.toCounterpartValue ambient
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (TypeTree.accessAfter tree firstOracles initial
          (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        ((TypeTree.ExecutionPath.ofTypeTreePath path).closingImpl firstOracles initial impl)
        _ (second (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath mid)))

private theorem sigma_mk_heq {A : Type u} {B C : A → Type u}
    (h : B = C) (value : A) (first : B value) (second : C value) (same : HEq first second) :
    HEq (⟨value, first⟩ : Sigma B) (⟨value, second⟩ : Sigma C) := by
  cases h
  cases same
  rfl

private theorem oracleComp_pure_heq {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {A B : Type u} (h : A = B) (first : A) (second : B) (same : HEq first second) :
    HEq (pure first : OracleComp ambient A) (pure second : OracleComp ambient B) := by
  cases h
  exact heq_of_eq (congrArg pure (eq_of_heq same))

set_option backward.isDefEq.respectTransparency false in
private theorem normalizedRuntimeType_eq {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (first : tree.RoleDecoration)
    (second : (path : tree.BranchPath) → (suffix path).RoleDecoration)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u) :
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) Participant.counterpart
      (TypeTree.toTypeTree (PFunctor.FreeM.append tree suffix))
      (TypeTree.RoleDecoration.toTypeTreeRoles (PFunctor.FreeM.append tree suffix)
        (Decoration.append first second))
      (fun path => Out (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath) =
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient)) Participant.counterpart
      (PFunctor.FreeM.append tree.toTypeTree (fun path =>
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath).toTypeTree))
      (Decoration.append (TypeTree.RoleDecoration.toTypeTreeRoles tree first) (fun path =>
        TypeTree.RoleDecoration.toTypeTreeRoles
          (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
          (second (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)))
      (fun path => Out (runtimeAppendBranch tree suffix path)) := by
  refine (appendedRuntimeType_eq ambient Participant.counterpart tree suffix first second
    (fun path => Out path.toBranchPath)).trans ?_
  congr 1
  funext path
  exact congrArg Out (runtimeAppendBranch_eq tree suffix path).symm

set_option backward.isDefEq.respectTransparency false in
private theorem appendValue_heq {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Mid : tree.BranchPath → Type u)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial Mid)
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Fragment ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (PFunctor.FreeM.Path.append tree suffix p q))) :
    HEq (Verifier.toCounterpartValue ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstRoles secondRoles) (Decoration.append firstOracles secondOracles)
      initial impl Out (Verifier.appendFragment ambient tree suffix firstRoles secondRoles
        firstOracles secondOracles initial Mid Out first second))
      (Verifier.appendNormalizedCounterpart ambient tree suffix firstRoles secondRoles firstOracles
        secondOracles initial impl Mid Out first second) := by
  induction tree generalizing initial with
  | done =>
      let interpreted := Verifier.toCounterpartValue ambient (suffix PUnit.unit)
        (secondRoles PUnit.unit) (secondOracles PUnit.unit) initial impl Out
        (second PUnit.unit first)
      change HEq interpreted
        (StrategyOver.TwoParty.Counterpart.mapOutput (fun _ out => out) interpreted)
      rw [StrategyOver.TwoParty.Counterpart.mapOutput_id]
  | «public» Moves rest ih =>
      rcases firstRoles with ⟨role, roles⟩
      cases role with
      | sender =>
          apply Function.hfunext rfl
          intro move other same
          cases same
          change Moves at move
          simp only [Verifier.appendNormalizedCounterpart, Verifier.appendFragment,
            Verifier.toCounterpartValue, Verifier.toCounterpartWith,
            StrategyOver.TwoParty.Counterpart.appendFlat,
            TypeTree.toTypeTree_public, TypeTree.RoleDecoration.toTypeTreeRoles_public,
            PFunctor.FreeM.append, Decoration.append]
          rw [simulateQ_map, bind_map_left, bind_assoc]
          simp only [pure_bind]
          have types := normalizedRuntimeType_eq ambient (rest move)
            (fun p => suffix ⟨move, p⟩) (roles move) (fun p => secondRoles ⟨move, p⟩)
            (fun p => Out ⟨move, p⟩)
          apply oracleComp_bind_heq types
          intro next
          apply oracleComp_pure_heq types
          exact ih move (fun p => suffix ⟨move, p⟩) (roles move)
            (fun p => secondRoles ⟨move, p⟩) (firstOracles.2 move)
            (fun p => secondOracles ⟨move, p⟩) initial impl (fun p => Mid ⟨move, p⟩)
            (fun p => Out ⟨move, p⟩) next (fun p => second ⟨move, p⟩)
      | receiver =>
          simp only [Verifier.appendNormalizedCounterpart, Verifier.appendFragment,
            Verifier.toCounterpartValue, Verifier.toCounterpartWith,
            StrategyOver.TwoParty.Counterpart.appendFlat,
            TypeTree.toTypeTree_public, TypeTree.RoleDecoration.toTypeTreeRoles_public,
            PFunctor.FreeM.append, Decoration.append]
          rw [simulateQ_map, bind_map_left, bind_assoc]
          simp only [pure_bind]
          have families := funext (fun move => normalizedRuntimeType_eq ambient (rest move)
            (fun p => suffix ⟨move, p⟩) (roles move) (fun p => secondRoles ⟨move, p⟩)
            (fun p => Out ⟨move, p⟩))
          have types := congrArg (fun F : Moves → Type u => Sigma F) families
          apply oracleComp_bind_heq types
          intro ⟨move, next⟩
          apply oracleComp_pure_heq types
          apply sigma_mk_heq families
          exact ih move (fun p => suffix ⟨move, p⟩) (roles move)
            (fun p => secondRoles ⟨move, p⟩) (firstOracles.2 move)
            (fun p => secondOracles ⟨move, p⟩) initial impl (fun p => Mid ⟨move, p⟩)
            (fun p => Out ⟨move, p⟩) next (fun p => second ⟨move, p⟩)
  | oracle Messages rest ih =>
      apply Function.hfunext rfl
      intro message other same
      cases same
      change Messages at message
      simp only [Verifier.appendNormalizedCounterpart, Verifier.appendFragment,
        Verifier.toCounterpartValue, Verifier.toCounterpartWith,
        StrategyOver.TwoParty.Counterpart.appendFlat,
        TypeTree.toTypeTree_oracle, TypeTree.RoleDecoration.toTypeTreeRoles_oracle,
        PFunctor.FreeM.append]
      rw [simulateQ_map, bind_map_left, bind_assoc]
      simp only [pure_bind]
      have types := normalizedRuntimeType_eq ambient (rest PUnit.unit)
        (fun p => suffix ⟨PUnit.unit, p⟩) (firstRoles.2 PUnit.unit)
        (fun p => secondRoles ⟨PUnit.unit, p⟩) (fun p => Out ⟨PUnit.unit, p⟩)
      apply oracleComp_bind_heq types
      intro next
      apply oracleComp_pure_heq types
      exact ih (fun p => suffix ⟨PUnit.unit, p⟩) (firstRoles.2 PUnit.unit)
        (fun p => secondRoles ⟨PUnit.unit, p⟩) (firstOracles.2 PUnit.unit)
        (fun p => secondOracles ⟨PUnit.unit, p⟩) (Access.extend initial firstOracles.1)
        (Access.extendImpl initial firstOracles.1 impl message)
        (fun p => Mid ⟨PUnit.unit, p⟩) (fun p => Out ⟨PUnit.unit, p⟩) next
        (fun p => second ⟨PUnit.unit, p⟩)
private theorem counterpart_mapOutput_heq {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {tree : Interaction.TypeTree.{u}} {roles : TwoParty.RoleDecoration tree}
    {Source A B : tree.Path → Type u} (types : A = B)
    (first : (path : tree.Path) → Source path → A path)
    (second : (path : tree.Path) → Source path → B path)
    (same : ∀ path value, HEq (first path value) (second path value))
    (strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
      Participant.counterpart tree roles Source) :
    HEq (StrategyOver.TwoParty.Counterpart.mapOutput first strategy)
      (StrategyOver.TwoParty.Counterpart.mapOutput second strategy) := by
  cases types
  have maps : first = second := funext (fun path => funext (fun value =>
    eq_of_heq (same path value)))
  cases maps
  rfl

private theorem counterpart_appendFlat_heq {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {tree : Interaction.TypeTree.{u}} {suffix : tree.Path → Interaction.TypeTree.{u}}
    {roles : TwoParty.RoleDecoration tree}
    {moreRoles : (path : tree.Path) → TwoParty.RoleDecoration (suffix path)}
    {Mid : tree.Path → Type u} {A B : (PFunctor.FreeM.append tree suffix).Path → Type u}
    (types : A = B)
    (first : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
      Participant.counterpart tree roles Mid)
    (left : (path : tree.Path) → Mid path →
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
        Participant.counterpart (suffix path) (moreRoles path)
        (fun rest => A (PFunctor.FreeM.Path.append tree suffix path rest)))
    (right : (path : tree.Path) → Mid path →
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree (OracleComp ambient))
        Participant.counterpart (suffix path) (moreRoles path)
        (fun rest => B (PFunctor.FreeM.Path.append tree suffix path rest)))
    (same : ∀ path value, HEq (left path value) (right path value)) :
    HEq (StrategyOver.TwoParty.Counterpart.appendFlat first left)
      (StrategyOver.TwoParty.Counterpart.appendFlat first right) := by
  cases types
  have continuations : left = right := funext (fun path => funext (fun value =>
    eq_of_heq (same path value)))
  cases continuations
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem normalized_actual_heq {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Mid : tree.BranchPath → Type u)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial Mid)
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Fragment ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (PFunctor.FreeM.Path.append tree suffix p q))) :
    HEq (Verifier.appendNormalizedCounterpart ambient tree suffix firstRoles secondRoles
      firstOracles secondOracles initial impl Mid Out first second)
      (Verifier.appendValueCounterpart ambient tree suffix firstRoles secondRoles firstOracles
        secondOracles initial impl Mid Out first second) := by
  have types := funext (fun path => congrArg Out (runtimeAppendBranch_eq tree suffix path))
  unfold Verifier.appendNormalizedCounterpart Verifier.appendValueCounterpart
  apply counterpart_appendFlat_heq types
  intro path mid
  apply counterpart_mapOutput_heq
    (funext (fun rest => congrArg Out (runtimeAppendBranch_eq tree suffix
      (PFunctor.FreeM.Path.append tree.toTypeTree
        (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
        path rest))))
  intro rest out
  exact (cast_heq _ out).trans (cast_heq _ out).symm

/-- Interpreting appended value fragments agrees with native counterpart append. The suffix
uses the actual prefix's concrete resource handler, while the boundary remains an ordinary value. -/
theorem Verifier.toCounterpartValue_appendFragment {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Mid : tree.BranchPath → Type u)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial Mid)
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Fragment ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (PFunctor.FreeM.Path.append tree suffix p q))) :
    onAppendedRuntime ambient Participant.counterpart tree suffix firstRoles secondRoles
      (fun path => Out path.toBranchPath)
      (Verifier.toCounterpartValue ambient (PFunctor.FreeM.append tree suffix)
        (Decoration.append firstRoles secondRoles) (Decoration.append firstOracles secondOracles)
        initial impl Out (Verifier.appendFragment ambient tree suffix firstRoles secondRoles
          firstOracles secondOracles initial Mid Out first second)) =
      Verifier.appendValueCounterpart ambient tree suffix firstRoles secondRoles firstOracles
        secondOracles initial impl Mid Out first second := by
  apply eq_of_heq
  exact (onAppendedRuntime_heq ambient Participant.counterpart tree suffix firstRoles secondRoles
    (fun path => Out path.toBranchPath) _).trans
    ((appendValue_heq ambient tree suffix firstRoles secondRoles firstOracles secondOracles
      initial impl Mid Out first second).trans
      (normalized_actual_heq ambient tree suffix firstRoles secondRoles firstOracles secondOracles
        initial impl Mid Out first second))

/-- Compose a value fragment with completed verifiers. Only the suffix carries a terminal action;
the final action retains the actual combined execution's query signature. -/
def Verifier.append {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (Mid : tree.BranchPath → Type u)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial Mid)
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Strategy ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => Out (PFunctor.FreeM.Path.append tree suffix p q))) :
    Verifier.Strategy ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstRoles secondRoles) (Decoration.append firstOracles secondOracles)
      initial Out :=
  Verifier.appendFragment ambient tree suffix firstRoles secondRoles firstOracles secondOracles
    initial Mid _ first (fun p mid => Verifier.Fragment.mapOutput ambient
      (fun q action => cast (congrArg (fun access => OracleComp
        (ambient + OracleSpec.ofPFunctor access) (Out (PFunctor.FreeM.Path.append tree suffix p q)))
        (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial p q).symm)
        action) (second p mid))

private theorem simulateQ_access_heq {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    {first second : PFunctor.{u, u}} {A B : Type u} (access : first = second) (output : A = B)
    (left : QueryImpl (OracleSpec.ofPFunctor first) Id)
    (right : QueryImpl (OracleSpec.ofPFunctor second) Id)
    (sameHandler : HEq left right)
    (leftAction : OracleComp (ambient + OracleSpec.ofPFunctor first) A)
    (rightAction : OracleComp (ambient + OracleSpec.ofPFunctor second) B)
    (sameAction : HEq leftAction rightAction) :
    HEq (simulateQ (Verifier.liftAccessImpl ambient first left) leftAction)
      (simulateQ (Verifier.liftAccessImpl ambient second right) rightAction) := by
  cases access
  cases output
  cases sameHandler
  cases sameAction
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem finish_append_action {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Out : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (path : Interaction.TypeTree.Path tree.toTypeTree)
    (rest : Interaction.TypeTree.Path
      (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath).toTypeTree)
    (action : OracleComp (ambient + OracleSpec.ofPFunctor
      (TypeTree.accessAfter (suffix (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (TypeTree.accessAfter tree firstOracles initial
          (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
        (TypeTree.ExecutionPath.ofTypeTreePath rest).toBranchPath))
      (Out (PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath
        (TypeTree.ExecutionPath.ofTypeTreePath rest).toBranchPath))) :
    let firstPath := TypeTree.ExecutionPath.ofTypeTreePath path
    let secondPath := TypeTree.ExecutionPath.ofTypeTreePath rest
    let fullPath := TypeTree.ExecutionPath.ofTypeTreePath
      (cast (congrArg Interaction.TypeTree.Path (TypeTree.toTypeTree_append tree suffix).symm)
        (PFunctor.FreeM.Path.append tree.toTypeTree
          (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
          path rest))
    let Leaf := fun branch => OracleComp (ambient + OracleSpec.ofPFunctor
      (TypeTree.accessAfter (PFunctor.FreeM.append tree suffix)
        (Decoration.append firstOracles secondOracles) initial branch)) (Out branch)
    simulateQ (Verifier.liftAccessImpl ambient
      (TypeTree.accessAfter (PFunctor.FreeM.append tree suffix)
        (Decoration.append firstOracles secondOracles) initial fullPath.toBranchPath)
      (fullPath.closingImpl (Decoration.append firstOracles secondOracles) initial impl))
      (cast (congrArg Leaf (runtimeBranch_append tree suffix path rest).symm)
        (cast (congrArg (fun access => OracleComp (ambient + OracleSpec.ofPFunctor access)
          (Out (PFunctor.FreeM.Path.append tree suffix firstPath.toBranchPath
            secondPath.toBranchPath)))
          (TypeTree.accessAfter_append tree suffix firstOracles secondOracles initial
            firstPath.toBranchPath secondPath.toBranchPath).symm) action)) =
    cast (congrArg (fun branch => OracleComp ambient (Out branch))
      (runtimeBranch_append tree suffix path rest).symm)
      (simulateQ (Verifier.liftAccessImpl ambient
        (TypeTree.accessAfter (suffix firstPath.toBranchPath) (secondOracles firstPath.toBranchPath)
          (TypeTree.accessAfter tree firstOracles initial firstPath.toBranchPath)
          secondPath.toBranchPath)
        (secondPath.closingImpl (secondOracles firstPath.toBranchPath)
          (TypeTree.accessAfter tree firstOracles initial firstPath.toBranchPath)
          (firstPath.closingImpl firstOracles initial impl))) action) := by
  dsimp only
  have joined := TypeTree.ExecutionPath.ofTypeTreePath_append tree suffix path rest
  have access := (congrArg (fun p => TypeTree.accessAfter (PFunctor.FreeM.append tree suffix)
    (Decoration.append firstOracles secondOracles) initial p.toBranchPath) joined).trans
    (TypeTree.accessAfter_append_execution tree suffix firstOracles secondOracles initial
      (TypeTree.ExecutionPath.ofTypeTreePath path) (TypeTree.ExecutionPath.ofTypeTreePath rest))
  have handler := congr_arg_heq (fun p : TypeTree.ExecutionPath
    (PFunctor.FreeM.append tree suffix) =>
      p.closingImpl (Decoration.append firstOracles secondOracles) initial impl) joined
  have closing := TypeTree.ExecutionPath.closingImpl_append tree suffix firstOracles
    secondOracles initial (TypeTree.ExecutionPath.ofTypeTreePath path)
    (TypeTree.ExecutionPath.ofTypeTreePath rest) impl
  have sameHandler := handler.trans ((cast_heq _ _).symm.trans (heq_of_eq closing))
  apply eq_of_heq
  refine (simulateQ_access_heq ambient access
    (congrArg Out (runtimeBranch_append tree suffix path rest)) _ _ sameHandler _ action ?_).trans
    (cast_heq _ _).symm
  exact (cast_heq _ _).trans (cast_heq _ action)

private theorem run_counterpart_mapOutput {m : Type u → Type u} [Monad m] [LawfulMonad m]
    {tree : Interaction.TypeTree.{u}} {roles : TwoParty.RoleDecoration tree}
    {OutP A B : tree.Path → Type u}
    (f : (path : tree.Path) → A path → B path)
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      tree roles OutP)
    (verifier : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      tree roles A) :
    TwoParty.run tree roles prover (StrategyOver.TwoParty.Counterpart.mapOutput f verifier) =
      (fun result => ⟨result.1, result.2.1, f result.1 result.2.2⟩) <$>
        TwoParty.run tree roles prover verifier := by
  simpa only [StrategyOver.TwoParty.Focal.mapOutput_id] using
    (TwoParty.run_mapOutput_mapOutput (fun _ out => out) f prover verifier)

private theorem toCounterpartValue_mapOutput {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (A B : tree.BranchPath → Type u) (f : (path : tree.BranchPath) → A path → B path)
    (verifier : Verifier.Fragment ambient tree roles oracles initial A) :
    Verifier.toCounterpartValue ambient tree roles oracles initial impl B
      (Verifier.Fragment.mapOutput ambient f verifier) =
      StrategyOver.TwoParty.Counterpart.mapOutput
        (fun path out => f (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath out)
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl A verifier) := by
  calc
    _ = Verifier.toCounterpartWith ambient tree roles oracles initial impl A B
        (fun path _ out => f path out) verifier :=
      Verifier.toCounterpartWith_mapOutput ambient tree roles oracles initial impl A B B f
        (fun _ _ out => out) verifier
    _ = _ := Verifier.toCounterpartWith_finish_eq_mapOutput ambient tree roles oracles initial
      impl A B (fun path _ out => f path out) verifier

private theorem toCounterpart_eq_mapOutput_value {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (roles : tree.RoleDecoration) (oracles : tree.OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Out : tree.BranchPath → Type u)
    (verifier : Verifier.Strategy ambient tree roles oracles initial Out) :
    Verifier.toCounterpart ambient tree roles oracles initial impl Out verifier =
      StrategyOver.TwoParty.Counterpart.mapOutput (fun path action => simulateQ
        (Verifier.liftAccessImpl ambient
          (TypeTree.accessAfter tree oracles initial
            (TypeTree.ExecutionPath.ofTypeTreePath path).toBranchPath)
          ((TypeTree.ExecutionPath.ofTypeTreePath path).closingImpl oracles initial impl)) action)
        (Verifier.toCounterpartValue ambient tree roles oracles initial impl _ verifier) := by
  exact Verifier.toCounterpartWith_finish_eq_mapOutput ambient tree roles oracles initial impl
    _ _ _ verifier

set_option backward.isDefEq.respectTransparency false in
/-- Executing appended restricted fragments factors through the native prefix and its actual
returned prover continuation. The suffix uses the handler derived from the same concrete prefix
path. The final verifier action runs once, after both fragments; this equality holds before any
ambient interpretation and needs no commutativity or losslessness assumption. -/
theorem executeStrategies_append {ι : Type u} (ambient : OracleSpec.{u, u} ι)
    (tree : Oracle.TypeTree.{u}) (suffix : tree.BranchPath → Oracle.TypeTree.{u})
    (firstRoles : tree.RoleDecoration)
    (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
    (firstOracles : tree.OracleDecoration)
    (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
    (initial : PFunctor.{u, u}) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (Mid : tree.BranchPath → Type u)
    (OutP : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type u)
    (OutV : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type u)
    (prover : Prover.Strategy ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstRoles secondRoles) OutP)
    (first : Verifier.Fragment ambient tree firstRoles firstOracles initial Mid)
    (second : (p : tree.BranchPath) → Mid p →
      Verifier.Strategy ambient (suffix p) (secondRoles p) (secondOracles p)
        (TypeTree.accessAfter tree firstOracles initial p)
        (fun q => OutV (PFunctor.FreeM.Path.append tree suffix p q))) :
    executeStrategies ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstRoles secondRoles) (Decoration.append firstOracles secondOracles)
      initial impl prover
      (Verifier.append ambient tree suffix firstRoles secondRoles firstOracles secondOracles
        initial Mid OutV first second) = (do
      let ⟨path₁, continuation, mid⟩ ← TwoParty.run tree.toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles tree firstRoles)
        (StrategyOver.TwoParty.Focal.splitPrefix
          (onAppendedRuntime ambient Participant.focal tree suffix firstRoles secondRoles OutP
            prover))
        (Verifier.toCounterpartValue ambient tree firstRoles firstOracles initial impl Mid first)
      let ⟨rest, outP, action⟩ ← TwoParty.run
        (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath).toTypeTree
        (TypeTree.RoleDecoration.toTypeTreeRoles
          (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
          (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath))
        continuation
        (StrategyOver.TwoParty.Counterpart.mapOutput (fun rest action =>
          cast (congrArg (fun branch => OracleComp ambient (OutV branch))
            (runtimeBranch_append tree suffix path₁ rest).symm) action)
          (Verifier.toCounterpart ambient
            (suffix (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            (TypeTree.accessAfter tree firstOracles initial
              (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath)
            ((TypeTree.ExecutionPath.ofTypeTreePath path₁).closingImpl firstOracles initial impl)
            _ (second (TypeTree.ExecutionPath.ofTypeTreePath path₁).toBranchPath mid)))
      let outV ← action
      return ⟨TypeTree.ExecutionPath.ofTypeTreePath
        (cast (congrArg Interaction.TypeTree.Path
          (TypeTree.toTypeTree_append tree suffix).symm)
          (PFunctor.FreeM.Path.append tree.toTypeTree
            (fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
            path₁ rest)), outP, outV⟩) := by
  simp only [executeStrategies]
  rw [toCounterpart_eq_mapOutput_value, run_counterpart_mapOutput]
  simp only [bind_map_left]
  let Leaf := fun branch => OracleComp (ambient + OracleSpec.ofPFunctor
    (TypeTree.accessAfter (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstOracles secondOracles) initial branch)) (OutV branch)
  have transport := run_onAppendedRuntime ambient tree suffix firstRoles secondRoles OutP
    (fun path => Leaf path.toBranchPath) prover
    (Verifier.toCounterpartValue ambient (PFunctor.FreeM.append tree suffix)
      (Decoration.append firstRoles secondRoles) (Decoration.append firstOracles secondOracles)
      initial impl Leaf (Verifier.append ambient tree suffix firstRoles secondRoles
        firstOracles secondOracles initial Mid OutV first second))
  rw [← transport]
  simp only [bind_map_left, Verifier.append]
  rw [Verifier.toCounterpartValue_appendFragment]
  unfold Verifier.appendValueCounterpart
  rw [TwoParty.run_appendFlat_splitPrefix]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro ⟨path₁, continuation, mid⟩
  rw [toCounterpartValue_mapOutput, toCounterpart_eq_mapOutput_value]
  simp only [run_counterpart_mapOutput, bind_map_left]
  apply bind_congr
  intro ⟨rest, outP, action⟩
  dsimp only [Leaf]
  rw [finish_append_action]

end Interaction.Oracle

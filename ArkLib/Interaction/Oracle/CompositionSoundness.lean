/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.SourceRouting
public import ArkLib.Interaction.CompositionSoundness

/-!
# Soundness of exported oracle composition

The boundary contains the prefix's actual private continuation and returned open claim. Its
truth and admissibility are tested after closing that claim with the same prefix resources.
Suffix errors include the final verifier action and closing its returned claim. Distribution
bounds apply directly to the existing ambient oracle computation.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open Interaction.Oracle Interaction.Oracle.Verifier
namespace Interaction.Oracle
noncomputable section
variable {ι I J : Type} (ambient : OracleSpec ι)
  [EvalDistSemantics (OracleComp ambient)] [LawfulEvalDistSemantics (OracleComp ambient)]
  (tree : Oracle.TypeTree) (suffix : tree.BranchPath → Oracle.TypeTree)
  (firstRoles : tree.RoleDecoration)
  (secondRoles : (p : tree.BranchPath) → (suffix p).RoleDecoration)
  (firstOracles : tree.OracleDecoration)
  (secondOracles : (p : tree.BranchPath) → (suffix p).OracleDecoration)
  (initial : PFunctor) (impl : QueryImpl (ofPFunctor initial) Id)
  (Stmt : tree.BranchPath → Type) (Data : tree.BranchPath → I → Type)
  (Export : (p : tree.BranchPath) → OracleFamily I (Data p))
  (FinalStmt : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → Type)
  (FinalData : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix) → J → Type)
  (Final : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
    OracleFamily J (FinalData p))
  (OutP : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix) → Type)
  (prover : Prover.Strategy ambient (PFunctor.FreeM.append tree suffix)
    (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles) OutP)
  (first : Fragment ambient tree firstRoles firstOracles initial (fun p =>
    OpenClaim (ofPFunctor (TypeTree.accessAfter tree firstOracles initial p))
      (Stmt p) (Export p)))
  (second : (p : tree.BranchPath) → Stmt p → Strategy ambient (suffix p)
    (secondRoles p) (secondOracles p) (Export p).spec.toPFunctor (fun q => Option
      (OpenClaim (ofPFunctor (TypeTree.accessAfter (suffix p) (secondOracles p)
        (Export p).spec.toPFunctor q))
        (FinalStmt (PFunctor.FreeM.Path.append tree suffix p q))
        (Final (PFunctor.FreeM.Path.append tree suffix p q)))))

/-- The existing native append boundary retains its actual prefix path, private continuation,
and returned export claim. -/
abbrev ExportedBoundary := Interaction.TwoParty.AppendBoundary
  (m := OracleComp ambient) (s₁ := tree.toTypeTree)
  (s₂ := fun p => (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath).toTypeTree)
  (r₂ := fun p => TypeTree.RoleDecoration.toTypeTreeRoles
    (suffix (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath)
    (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath))
  (OutputP := fun p => OutP (TypeTree.ExecutionPath.ofTypeTreePath
    (cast (congrArg Interaction.TypeTree.Path (TypeTree.toTypeTree_append tree suffix).symm) p)))
  (MidC := fun p => OpenClaim (ofPFunctor (TypeTree.accessAfter tree firstOracles initial
    (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath))
    (Stmt (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath)
    (Export (TypeTree.ExecutionPath.ofTypeTreePath p).toBranchPath))

/-- Run the actual prefix of a whole prover and retain the continuation returned by it. -/
abbrev exportedPrefixRun := Interaction.TwoParty.run tree.toTypeTree
  (TypeTree.RoleDecoration.toTypeTreeRoles tree firstRoles)
  (Interaction.StrategyOver.TwoParty.Focal.splitPrefix
    (onAppendedRuntime ambient .focal tree suffix firstRoles secondRoles OutP prover))
  (toCounterpartValue ambient tree firstRoles firstOracles initial impl _ first)


/-- Continue the actual remaining prover using the exported oracle, then run the final verifier
action and close its claim. This abbreviates the same native run and shared interpreter. -/
abbrev exportedSuffixRun
    (b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial Stmt Data Export
      OutP) :
    OracleComp ambient
      ((q : (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath).BranchPath) ×
        Option (ClosedClaim
          (FinalStmt (PFunctor.FreeM.Path.append tree suffix
            (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q))
          (Final (PFunctor.FreeM.Path.append tree suffix
            (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q)))) :=
(do
  let ⟨rest, _outP, action⟩ ← Interaction.TwoParty.run
    (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath).toTypeTree
    (TypeTree.RoleDecoration.toTypeTreeRoles
      (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
      (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)) b.2.1
    (toCounterpartWith ambient
      (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
      (secondRoles (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
      (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
      (Export (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath).spec.toPFunctor
      (b.2.2.oracles.eval ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
        firstOracles initial impl)) (fun q => OracleComp
          (ambient + ofPFunctor (TypeTree.accessAfter
            (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
            (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
            (Export (TypeTree.ExecutionPath.ofTypeTreePath
              b.1).toBranchPath).spec.toPFunctor q))
          (Option (OpenClaim (ofPFunctor (TypeTree.accessAfter
            (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
            (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
            (Export (TypeTree.ExecutionPath.ofTypeTreePath
              b.1).toBranchPath).spec.toPFunctor q))
            (FinalStmt (PFunctor.FreeM.Path.append tree suffix
              (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q))
            (Final (PFunctor.FreeM.Path.append tree suffix
              (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q)))))
          (fun q => OracleComp ambient (Option
          (ClosedClaim
            (FinalStmt (PFunctor.FreeM.Path.append tree suffix
              (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q))
            (Final (PFunctor.FreeM.Path.append tree suffix
              (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q)))))
      (fun q actual action => (fun (result : Option
        (OpenClaim (ofPFunctor (TypeTree.accessAfter
          (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
          (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
          (Export (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath).spec.toPFunctor
            q))
          (FinalStmt (PFunctor.FreeM.Path.append tree suffix
            (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q))
          (Final (PFunctor.FreeM.Path.append tree suffix
            (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q)))) =>
          result.map (fun claim =>
        OpenClaim.closeWith claim actual)) <$> simulateQ (liftAccessImpl ambient
          (TypeTree.accessAfter
            (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
            (secondOracles (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath)
            (Export (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath).spec.toPFunctor
            q) actual) action)
      (second (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath b.2.2.stmt))
  let out ← action
  return (⟨(TypeTree.ExecutionPath.ofTypeTreePath rest).toBranchPath, out⟩ :
    (q : (suffix (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath).BranchPath) ×
      Option (ClosedClaim
        (FinalStmt (PFunctor.FreeM.Path.append tree suffix
          (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q))
        (Final (PFunctor.FreeM.Path.append tree suffix
          (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath q)))))

omit [EvalDistSemantics (OracleComp ambient)] [LawfulEvalDistSemantics (OracleComp ambient)] in
private theorem observe_truth_cast
    (TruthFinal : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      ClosedClaim (FinalStmt p) (Final p) → Prop)
    {p q : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)} (h : p = q)
    (action : OracleComp ambient (Option (ClosedClaim (FinalStmt p) (Final p)))) :
    (do
      let out ← cast (congrArg (fun branch => OracleComp ambient
        (Option (ClosedClaim (FinalStmt branch) (Final branch)))) h) action
      return out.map (TruthFinal q) = some True) = (do
      let out ← action
      return out.map (TruthFinal p) = some True) := by
  cases h
  rfl

omit [EvalDistSemantics (OracleComp ambient)] [LawfulEvalDistSemantics (OracleComp ambient)] in
set_option backward.isDefEq.respectTransparency false in
private theorem observe_appendExported
    (TruthFinal : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      ClosedClaim (FinalStmt p) (Final p) → Prop) :
    (fun result => result.2.2.map (fun claim => TruthFinal result.1.toBranchPath
      (OpenClaim.closeWith claim (result.1.closingImpl
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial
              impl))) =
      some True) <$> executeStrategies ambient (PFunctor.FreeM.append tree suffix)
        (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles)
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl prover
        (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
          initial Stmt Data Export FinalStmt FinalData Final first second) = (do
      let b ← exportedPrefixRun ambient tree suffix firstRoles secondRoles firstOracles initial impl
        Stmt Data Export OutP prover first
      let result ← exportedSuffixRun ambient tree suffix secondRoles firstOracles secondOracles
        initial impl Stmt Data Export FinalStmt FinalData Final OutP second b
      return result.2.map (TruthFinal (PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1)) = some True) := by
  let observe := fun (result :
      (path : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) × OutP path ×
        Option (ClosedClaim (FinalStmt path.toBranchPath) (Final path.toBranchPath))) =>
    result.2.2.map (TruthFinal result.1.toBranchPath) = some True
  have execution := congrArg (fun program => observe <$> program)
    (executeStrategies_appendExported_close ambient tree suffix firstRoles secondRoles
      firstOracles secondOracles initial impl Stmt Data Export FinalStmt FinalData Final OutP
      prover first second)
  simp only [Functor.map_map, observe, Option.map_map] at execution
  refine execution.trans ?_
  simp only [map_bind, map_pure, exportedPrefixRun]
  apply bind_congr
  rintro ⟨path, continuation, mid⟩
  rw [run_counterpart_mapOutput]
  simp only [bind_map_left, exportedSuffixRun, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨rest, outP, action⟩
  exact observe_truth_cast ambient tree suffix FinalStmt FinalData Final TruthFinal
    (runtimeBranch_append tree suffix path rest).symm action

/-- Bound true final claims by true midpoint claims, false inadmissible midpoints, and the
average suffix error on false admissible midpoints. Each claim is closed using the actual
resources of its path, after the final action. A false input premise belongs to the caller
that proves the midpoint truth bound. -/
theorem executeStrategies_appendExported_soundness_weighted_ae
    (TruthMid Admissible : (p : tree.BranchPath) → ClosedClaim (Stmt p) (Export p) → Prop)
    (TruthFinal : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      ClosedClaim (FinalStmt p) (Final p) → Prop)
    (error : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP →
      ENNReal) (εtruth εinvalid : ENNReal) :
    let prefixProgram := exportedPrefixRun ambient tree suffix firstRoles secondRoles
      firstOracles initial impl
      Stmt Data Export OutP prover first
    let trueMid := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP => TruthMid (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
        (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
          firstOracles initial impl))
    let admissible := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP => Admissible (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
        (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
          firstOracles initial impl))
    (Pr{b ← prefixProgram}[trueMid b] ≤ εtruth) →
    (Pr{b ← prefixProgram}[¬ trueMid b ∧ ¬ admissible b] ≤ εinvalid) →
    (letI : MeasurableSpace (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP) := ⊤;
      ∀ᵐ b ∂𝒟[prefixProgram], ¬ trueMid b → admissible b →
        Pr{result ← (exportedSuffixRun ambient tree suffix secondRoles firstOracles
          secondOracles initial impl Stmt Data Export FinalStmt FinalData Final OutP second b)}[
            result.2.map (TruthFinal (PFunctor.FreeM.Path.append tree suffix
              (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1)) = some True] ≤
          error b) →
    (let : MeasurableSpace (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP) := ⊤;
      Pr{result ← (executeStrategies ambient (PFunctor.FreeM.append tree suffix)
        (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles)
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl prover
        (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
          initial Stmt Data Export FinalStmt FinalData Final first second))}[
        result.2.2.map (fun claim => TruthFinal result.1.toBranchPath
          (OpenClaim.closeWith claim (result.1.closingImpl
            (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial
              impl))) =
          some True] ≤ εtruth + εinvalid +
        ∫⁻ b in {b | ¬ trueMid b ∧ admissible b}, error b ∂𝒟[prefixProgram]) := by
  classical
  let prefixProgram := exportedPrefixRun ambient tree suffix firstRoles secondRoles firstOracles
    initial impl Stmt Data Export OutP prover first
  let trueMid := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
    Stmt Data Export OutP => TruthMid (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
      (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
        firstOracles initial impl))
  let admissible := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
    Stmt Data Export OutP => Admissible (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
      (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
        firstOracles initial impl))
  change _ → _ → _ → _
  intro htruth hinvalid hsuffix
  let : MeasurableSpace (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
    Stmt Data Export OutP) := ⊤
  let next := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
    Stmt Data Export OutP => (fun result => result.2.map
      (TruthFinal (PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1)) = some True) <$>
      exportedSuffixRun ambient tree suffix secondRoles firstOracles secondOracles initial impl
        Stmt Data Export FinalStmt FinalData Final OutP second b
  have hnext : ∀ᵐ b ∂𝒟[prefixProgram], ¬ (trueMid b ∨ ¬ admissible b) →
      Pr{truth ← next b}[truth] ≤ error b := by
    apply hsuffix.mono
    intro b hb hg
    simpa only [next, map_eq_pure_bind] using hb (fun ht => hg (Or.inl ht))
      (not_not.mp (fun ha => hg (Or.inr ha)))
  have bound := prEvent_bind_le_prEvent_add_lintegral_ae prefixProgram next
    (fun b => trueMid b ∨ ¬ admissible b) (fun truth => truth) error
    (by simpa only [id_map'] using hnext)
  have hevent : Pr{b ← prefixProgram}[trueMid b ∨ ¬ admissible b] ≤
      εtruth + εinvalid := by
    have heq : (fun b => trueMid b ∨ ¬ admissible b) =
        (fun b => trueMid b ∨ (¬ trueMid b ∧ ¬ admissible b)) := by
      funext b
      exact propext (by tauto)
    rw [prEvent_congr prefixProgram _ _ (fun b => Iff.of_eq (congrFun heq b))]
    exact (prEvent_or_le prefixProgram trueMid (fun b => ¬ trueMid b ∧ ¬ admissible b)).trans
      (add_le_add htruth hinvalid)
  have observe := observe_appendExported ambient tree suffix firstRoles secondRoles firstOracles
    secondOracles initial impl Stmt Data Export FinalStmt FinalData Final OutP prover first
    second TruthFinal
  have hset : {b | ¬ (trueMid b ∨ ¬ admissible b)} =
      {b | ¬ trueMid b ∧ admissible b} := by
    ext b
    simp only [Set.mem_ofPred_eq, not_or, not_not]
  rw [hset] at bound
  rw [← prEvent_map _ _ (fun truth => truth), observe]
  simpa only [next, map_eq_pure_bind, prefixProgram] using
    bound.trans (add_le_add hevent le_rfl)

/-- A uniform suffix bound gives the sum of the truth, inadmissibility, and suffix errors.
Only almost-everywhere false admissible boundary results require suffix security. -/
theorem executeStrategies_appendExported_soundness_ae
    (TruthMid Admissible : (p : tree.BranchPath) → ClosedClaim (Stmt p) (Export p) → Prop)
    (TruthFinal : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      ClosedClaim (FinalStmt p) (Final p) → Prop)
    (εtruth εinvalid εsuffix : ENNReal) :
    let prefixProgram := exportedPrefixRun ambient tree suffix firstRoles secondRoles
      firstOracles initial impl
      Stmt Data Export OutP prover first
    let trueMid := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP => TruthMid (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
        (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
          firstOracles initial impl))
    let admissible := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP => Admissible (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath
        (b.2.2.closeWith ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl
          firstOracles initial impl))
    (Pr{b ← prefixProgram}[trueMid b] ≤ εtruth) →
    (Pr{b ← prefixProgram}[¬ trueMid b ∧ ¬ admissible b] ≤ εinvalid) →
    (letI : MeasurableSpace (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP) := ⊤;
      ∀ᵐ b ∂𝒟[prefixProgram], ¬ trueMid b → admissible b →
        Pr{result ← (exportedSuffixRun ambient tree suffix secondRoles firstOracles
          secondOracles initial impl Stmt Data Export FinalStmt FinalData Final OutP second b)}[
            result.2.map (TruthFinal (PFunctor.FreeM.Path.append tree suffix
              (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1)) = some True] ≤
          εsuffix) →
    (let : MeasurableSpace (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
      Stmt Data Export OutP) := ⊤;
      Pr{result ← (executeStrategies ambient (PFunctor.FreeM.append tree suffix)
        (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles)
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl prover
        (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
          initial Stmt Data Export FinalStmt FinalData Final first second))}[
        result.2.2.map (fun claim => TruthFinal result.1.toBranchPath
          (OpenClaim.closeWith claim (result.1.closingImpl
            (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial
              impl))) =
          some True] ≤ εtruth + εinvalid + εsuffix) := by
  classical
  dsimp only
  intro htruth hinvalid hsuffix
  let : MeasurableSpace (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
    Stmt Data Export OutP) := ⊤
  refine (executeStrategies_appendExported_soundness_weighted_ae ambient tree suffix firstRoles
    secondRoles firstOracles secondOracles initial impl Stmt Data Export FinalStmt FinalData Final
    OutP prover first second TruthMid Admissible TruthFinal (fun _ => εsuffix) εtruth εinvalid
    htruth hinvalid hsuffix).trans ?_
  refine add_le_add le_rfl ?_
  rw [setLIntegral_const]
  exact mul_le_of_le_one_right' ((measure_mono (Set.subset_univ _)).trans
    (evalDist_apply_univ_le_one _))

end
end Interaction.Oracle

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.CompositionSoundness
public import ArkLib.Interaction.Oracle.PhasedRun
public import ArkLib.Data.Probability.Sequential

/-! # Native composition soundness in a persistent runtime -/

@[expose] public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace OracleRuntime
variable {ι κ B X : Type} {imports : OracleSpec ι} {surface : OracleSpec κ}
  [EvalDistSemantics (OracleComp imports)] [LawfulEvalDistSemantics (OracleComp imports)]

/-- Average actual resumed success over the joint prefix result. The fixed authored continuation
receives only `B`; the runtime retains state and history internally. Analytic exceptional and error
predicates may inspect the full joint result. No independence or normalization is assumed. -/
theorem run_bind_success_le (runtime : OracleRuntime imports surface)
    (first : OracleComp surface B) (next : B → OracleComp surface X)
    (Exceptional : RunResult runtime B → Prop) (Success : X → Prop)
    (error : RunResult runtime B → ENNReal)
    (hsuffix : letI : MeasurableSpace (RunResult runtime B) := ⊤
      (∫⁻ b in {b | ¬ Exceptional b},
        Pr{let result ← runtime.resume b next}[Success result.output] ∂𝒟[runtime.run first]) ≤
      ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run first]) :
    let : MeasurableSpace (RunResult runtime B) := ⊤
    Pr{let result ← runtime.run (first >>= next)}[Success result.output] ≤
      Pr{let b ← runtime.run first}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run first] := by
  let : MeasurableSpace (RunResult runtime B) := ⊤
  rw [runtime.run_bind]
  exact (prEvent_bind_le_prEvent_add_lintegral_ae (runtime.run first)
    (fun b => runtime.resume b next) Exceptional (fun result => Success result.output)
    (fun b => Pr{let result ← runtime.resume b next}[Success result.output])
    (Filter.Eventually.of_forall (fun _ _ => le_rfl))).trans (add_le_add le_rfl hsuffix)
/-- A stronger pointwise almost-everywhere premise implies the joint average bound. -/
theorem run_bind_success_le_ae (runtime : OracleRuntime imports surface)
    (first : OracleComp surface B) (next : B → OracleComp surface X)
    (Exceptional : RunResult runtime B → Prop) (Success : X → Prop)
    (error : RunResult runtime B → ENNReal)
    (hsuffix : letI : MeasurableSpace (RunResult runtime B) := ⊤
      ∀ᵐ b ∂𝒟[runtime.run first], ¬ Exceptional b →
        Pr{let result ← runtime.resume b next}[Success result.output] ≤ error b) :
    let : MeasurableSpace (RunResult runtime B) := ⊤
    Pr{let result ← runtime.run (first >>= next)}[Success result.output] ≤
      Pr{let b ← runtime.run first}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run first] := by
  let : MeasurableSpace (RunResult runtime B) := ⊤
  rw [runtime.run_bind]
  exact prEvent_bind_le_prEvent_add_lintegral_ae (runtime.run first)
    (fun b => runtime.resume b next) Exceptional (fun result => Success result.output) error hsuffix

/-- A uniform actual-resume bound yields a uniform error term, even with missing mass. -/
theorem run_bind_success_le_uniform (runtime : OracleRuntime imports surface)
    (first : OracleComp surface B) (next : B → OracleComp surface X)
    (Exceptional : RunResult runtime B → Prop) (Success : X → Prop) (error : ENNReal)
    (hsuffix : letI : MeasurableSpace (RunResult runtime B) := ⊤
      ∀ᵐ b ∂𝒟[runtime.run first], ¬ Exceptional b →
        Pr{let result ← runtime.resume b next}[Success result.output] ≤ error) :
    Pr{let result ← runtime.run (first >>= next)}[Success result.output] ≤
      Pr{let b ← runtime.run first}[Exceptional b] + error := by
  let : MeasurableSpace (RunResult runtime B) := ⊤
  apply (runtime.run_bind_success_le_ae first next Exceptional Success (fun _ => error)
    hsuffix).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∫⁻ _, error ∂𝒟[runtime.run first] := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (f := fun _ => error)
          (μ := 𝒟[runtime.run first]) (Set.subset_univ {b | ¬ Exceptional b}))
    _ = error * 𝒟[runtime.run first] Set.univ := lintegral_const error
    _ ≤ error := mul_le_of_le_one_right' (evalDist_apply_univ_le_one (runtime.run first))

end OracleRuntime

namespace Interaction.Oracle

/-- Mapping an output preserves the same runtime state and ordered ambient history. -/
theorem runtime_run_map_observe {ι κ A B : Type}
    {imports : OracleSpec ι} {ambient : OracleSpec κ}
    (runtime : OracleRuntime imports ambient) (program : OracleComp ambient A) (f : A → B) :
    (fun result => (f result.output, result.state, result.trace)) <$> runtime.run program =
      (fun result => (result.output, result.state, result.trace)) <$>
        runtime.run (f <$> program) := by
  rw [OracleRuntime.run_eq, OracleRuntime.run_eq]
  simp only [map_bind]
  congr 1
  funext state
  have observed := congrArg (fun program =>
    (fun result => (f result.1, result.2.1, result.2.2)) <$> program)
    (runtime.runFrom_observe state program)
  calc
    _ = (fun result => (f result.1.1, result.2, result.1.2)) <$>
        runtime.handler.runState state program.withQueryLog := by
      simpa only [Functor.map_map] using observed
    _ = _ := by
      rw [runtime.runFrom_observe]
      simp [OracleComp.withQueryLog, QueryImpl.Stateful.runState, monad_norm]

/-- Erasing source instrumentation retains the actual concrete path, private output, paired input
behavior, terminal claim, final runtime state, and ordered ambient query history. -/
theorem executeStrategiesWithRuntime_core {ι κ : Type}
    {imports : OracleSpec ι} {ambient : OracleSpec κ} (runtime : OracleRuntime imports ambient)
    {protocol : Oracle.Protocol} {initial : PFunctor}
    {Stmt : protocol.tree.BranchPath → Type} {Idx : protocol.tree.BranchPath → Type}
    {Obj : (path : protocol.tree.BranchPath) → Idx path → Type}
    {Out : (path : protocol.tree.BranchPath) → OracleFamily (Idx path) (Obj path)}
    {OutP : protocol.tree.ExecutionPath → Type}
    (impl : QueryImpl (ofPFunctor initial) Id)
    (prover : Prover.Strategy ambient protocol.tree protocol.roles OutP)
    (verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles initial
      (TerminalClaim protocol initial Stmt Out)) :
    (fun result => (result.output.core, result.state, result.trace)) <$>
        executeStrategiesWithRuntime runtime impl prover verifier =
      (fun result => (result.output, result.state, result.trace)) <$>
        runtime.run (executeStrategiesCore impl prover verifier) := by
  unfold executeStrategiesWithRuntime
  rw [runtime_run_map_observe, executeStrategiesLoggedRun_erase]

open Interaction.Oracle.Verifier

section Native

variable {ι I J : Type} (ambient : OracleSpec ι)
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

/-- Casting a branch-dependent claim action preserves its paired branch and closed outcome. -/
private theorem pair_closed_cast
    {p q : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)} (h : p = q)
    (action : OracleComp ambient (Option (ClosedClaim (FinalStmt p) (Final p)))) :
    (fun out => (⟨q, out⟩ : (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
      Option (ClosedClaim (FinalStmt branch) (Final branch)))) <$>
        cast (congrArg (fun branch => OracleComp ambient
          (Option (ClosedClaim (FinalStmt branch) (Final branch)))) h) action =
      (fun out => (⟨p, out⟩ : (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
        Option (ClosedClaim (FinalStmt branch) (Final branch)))) <$> action := by
  cases h
  rfl

/-- The closed-output observation of a whole native prover splits at its actual continuation.
The claim is closed with the same execution's resources; this observation projects away private
output and concrete oracle payloads only after the existing executor has paired them. -/
theorem executeStrategies_appendExported_closedResult :
    (fun result => (⟨result.1.toBranchPath, result.2.2.map (fun claim =>
      claim.closeWith (result.1.closingImpl
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl))⟩ :
      (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
        Option (ClosedClaim (FinalStmt branch) (Final branch)))) <$>
      executeStrategies ambient (PFunctor.FreeM.append tree suffix)
        (PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles)
        (PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles) initial impl prover
        (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
          initial Stmt Data Export FinalStmt FinalData Final first second) = (do
      let b ← exportedPrefixRun ambient tree suffix firstRoles secondRoles firstOracles initial impl
        Stmt Data Export OutP prover first
      let result ← exportedSuffixRun ambient tree suffix secondRoles firstOracles secondOracles
        initial impl Stmt Data Export FinalStmt FinalData Final OutP second b
      return (⟨PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1, result.2⟩ :
        (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
          Option (ClosedClaim (FinalStmt branch) (Final branch)))) := by
  let observe := fun (result :
      (path : TypeTree.ExecutionPath (PFunctor.FreeM.append tree suffix)) × OutP path ×
        Option (ClosedClaim (FinalStmt path.toBranchPath) (Final path.toBranchPath))) =>
    (⟨result.1.toBranchPath, result.2.2⟩ :
      (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
        Option (ClosedClaim (FinalStmt branch) (Final branch)))
  have execution := congrArg (fun program => observe <$> program)
    (executeStrategies_appendExported_close ambient tree suffix firstRoles secondRoles
      firstOracles secondOracles initial impl Stmt Data Export FinalStmt FinalData Final OutP
      prover first second)
  simp only [Functor.map_map, observe] at execution
  refine execution.trans ?_
  simp only [map_bind, map_pure, exportedPrefixRun]
  apply bind_congr
  rintro ⟨path, continuation, mid⟩
  rw [run_counterpart_mapOutput]
  simp only [bind_map_left, exportedSuffixRun, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨rest, outP, action⟩
  simpa only [map_eq_pure_bind] using
    pair_closed_cast ambient tree suffix FinalStmt FinalData Final
      (runtimeBranch_append tree suffix path rest).symm action
/-- The native closed-output split preserves the actual final runtime state and ordered ambient
history. The complete core instrumentation is retained by `executeStrategiesWithRuntime_core`;
this theorem projects to the branch-dependent closed outcome used by security events. -/
theorem executeStrategiesWithRuntime_appendExported_closedResult
    {importIdx : Type} {imports : OracleSpec importIdx} (runtime : OracleRuntime imports ambient) :
    (fun result =>
      ((⟨result.output.core.path.toBranchPath, result.output.core.closed⟩ :
        (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
          Option (ClosedClaim (FinalStmt branch) (Final branch))), result.state, result.trace)) <$>
        executeStrategiesWithRuntime runtime
          (protocol := ⟨PFunctor.FreeM.append tree suffix,
            PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles,
            PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles⟩)
          (initial := initial) impl prover
          (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
            initial Stmt Data Export FinalStmt FinalData Final first second) =
      (fun result => (result.output, result.state, result.trace)) <$>
        runtime.run (do
          let b ← exportedPrefixRun ambient tree suffix firstRoles secondRoles firstOracles initial
            impl Stmt Data Export OutP prover first
          let result ← exportedSuffixRun ambient tree suffix secondRoles firstOracles secondOracles
            initial impl Stmt Data Export FinalStmt FinalData Final OutP second b
          return (⟨PFunctor.FreeM.Path.append tree suffix
            (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1, result.2⟩ :
            (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
              Option (ClosedClaim (FinalStmt branch) (Final branch)))) := by
  let protocol : Oracle.Protocol := ⟨PFunctor.FreeM.append tree suffix,
    PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles,
    PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles⟩
  let close := fun (core : CoreRun protocol initial FinalStmt Final OutP) =>
    (⟨core.path.toBranchPath, core.closed⟩ :
      (branch : protocol.tree.BranchPath) × Option (ClosedClaim (FinalStmt branch) (Final branch)))
  have erased := congrArg (fun program =>
    (fun result => (close result.1, result.2.1, result.2.2)) <$> program)
    (executeStrategiesWithRuntime_core runtime (protocol := protocol) impl prover
      (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
        initial Stmt Data Export FinalStmt FinalData Final first second))
  have ordinary := executeStrategies_appendExported_closedResult ambient tree suffix firstRoles
    secondRoles firstOracles secondOracles initial impl Stmt Data Export FinalStmt FinalData Final
    OutP prover first second
  calc
    _ = (fun result => (close result.output, result.state, result.trace)) <$>
        runtime.run (executeStrategiesCore (protocol := protocol) impl prover
          (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
            initial Stmt Data Export FinalStmt FinalData Final first second)) := by
      simpa only [Functor.map_map, close, protocol] using erased
    _ = _ := by
      rw [runtime_run_map_observe]
      have closed := congrArg runtime.run ordinary
      simpa [executeStrategiesCore, CoreRun.closed, close, protocol, monad_norm] using
        congrArg (fun program =>
          (fun result => (result.output, result.state, result.trace)) <$> program) closed

/-- A final closed-claim event has the same mass in the native runtime and its actual split.
This projects the paired closed-output/state/history equality while preserving its oracle relation.
-/
theorem executeStrategiesWithRuntime_appendExported_prEvent
    {importIdx : Type} {imports : OracleSpec importIdx}
    [EvalDistSemantics (OracleComp imports)] (runtime : OracleRuntime imports ambient)
    (TruthFinal : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      ClosedClaim (FinalStmt p) (Final p) → Prop) :
    Pr{let result ← executeStrategiesWithRuntime runtime
          (protocol := ⟨PFunctor.FreeM.append tree suffix,
            PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles,
            PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles⟩)
          (initial := initial) impl prover
          (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
            initial Stmt Data Export FinalStmt FinalData Final first second)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] =
    Pr{let result ← (runtime.run (do
      let b ← exportedPrefixRun ambient tree suffix firstRoles secondRoles firstOracles initial
        impl Stmt Data Export OutP prover first
      let result ← exportedSuffixRun ambient tree suffix secondRoles firstOracles secondOracles
        initial impl Stmt Data Export FinalStmt FinalData Final OutP second b
      return (⟨PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1, result.2⟩ :
        (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
          Option (ClosedClaim (FinalStmt branch) (Final branch)))))}[
      result.output.2.map (TruthFinal result.output.1) = some True] := by
  have observed := executeStrategiesWithRuntime_appendExported_closedResult ambient tree suffix
    firstRoles secondRoles firstOracles secondOracles initial impl Stmt Data Export FinalStmt
    FinalData Final OutP prover first second runtime
  have same := congrArg (fun program => Pr{let result ← program}[
    result.1.2.map (TruthFinal result.1.1) = some True]) observed
  simpa only [prEvent_map] using same

/-- Bound the actual native runtime experiment by an exceptional joint boundary event and the
average suffix error on its complement. The main premise is already averaged over the runtime's
actual state, native continuation, intermediate claim, and history distribution. It makes no
pointwise security requirement at each hidden state. The whole prover is fixed before setup;
only `runtime.resume` handles hidden state. Rejection is outside the accepted-claim event and
missing mass is left unnormalized. This theorem does not transfer security to arbitrary runtimes. -/
theorem executeStrategiesWithRuntime_appendExported_soundness
    {importIdx : Type} {imports : OracleSpec importIdx}
    [EvalDistSemantics (OracleComp imports)] [LawfulEvalDistSemantics (OracleComp imports)]
    (runtime : OracleRuntime imports ambient)
    (Exceptional : RunResult runtime
      (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
        Stmt Data Export OutP) → Prop)
    (TruthFinal : (p : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) →
      ClosedClaim (FinalStmt p) (Final p) → Prop)
    (error : RunResult runtime
      (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
        Stmt Data Export OutP) → ENNReal) :
    let prefixProgram := exportedPrefixRun ambient tree suffix firstRoles secondRoles
      firstOracles initial impl Stmt Data Export OutP prover first
    let next := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
        Stmt Data Export OutP =>
      (fun result => (⟨PFunctor.FreeM.Path.append tree suffix
        (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1, result.2⟩ :
        (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
          Option (ClosedClaim (FinalStmt branch) (Final branch)))) <$>
        exportedSuffixRun ambient tree suffix secondRoles firstOracles secondOracles initial impl
          Stmt Data Export FinalStmt FinalData Final OutP second b
    let Success := fun result :
        (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
          Option (ClosedClaim (FinalStmt branch) (Final branch)) =>
      result.2.map (TruthFinal result.1) = some True
    let : MeasurableSpace (RunResult runtime
      (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
        Stmt Data Export OutP)) := ⊤
    (∫⁻ b in {b | ¬ Exceptional b},
      Pr{let result ← runtime.resume b next}[Success result.output] ∂𝒟[runtime.run prefixProgram]) ≤
        ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run prefixProgram] →
    Pr{let result ← executeStrategiesWithRuntime runtime
          (protocol := ⟨PFunctor.FreeM.append tree suffix,
            PFunctor.FreeM.Displayed.Decoration.append firstRoles secondRoles,
            PFunctor.FreeM.Displayed.Decoration.append firstOracles secondOracles⟩)
          (initial := initial) impl prover
          (appendExported ambient tree suffix firstRoles secondRoles firstOracles secondOracles
            initial Stmt Data Export FinalStmt FinalData Final first second)}[
      result.output.core.closed.map (TruthFinal result.output.core.path.toBranchPath) = some True] ≤
        Pr{let b ← runtime.run prefixProgram}[Exceptional b] +
          ∫⁻ b in {b | ¬ Exceptional b}, error b ∂𝒟[runtime.run prefixProgram] := by
  dsimp only
  intro hsuffix
  let prefixProgram := exportedPrefixRun ambient tree suffix firstRoles secondRoles
    firstOracles initial impl Stmt Data Export OutP prover first
  let next := fun b : ExportedBoundary ambient tree suffix secondRoles firstOracles initial
        Stmt Data Export OutP =>
    (fun result => (⟨PFunctor.FreeM.Path.append tree suffix
      (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath result.1, result.2⟩ :
      (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
        Option (ClosedClaim (FinalStmt branch) (Final branch)))) <$>
      exportedSuffixRun ambient tree suffix secondRoles firstOracles secondOracles initial impl
        Stmt Data Export FinalStmt FinalData Final OutP second b
  let Success := fun result :
      (branch : TypeTree.BranchPath (PFunctor.FreeM.append tree suffix)) ×
        Option (ClosedClaim (FinalStmt branch) (Final branch)) =>
    result.2.map (TruthFinal result.1) = some True
  let : MeasurableSpace (RunResult runtime
    (ExportedBoundary ambient tree suffix secondRoles firstOracles initial
        Stmt Data Export OutP)) := ⊤
  have observed := executeStrategiesWithRuntime_appendExported_closedResult ambient tree suffix
    firstRoles secondRoles firstOracles secondOracles initial impl Stmt Data Export FinalStmt
    FinalData Final OutP prover first second runtime
  have same := congrArg (fun program =>
    Pr{let result ← program}[Success result.1]) observed
  simp only [prEvent_map] at same
  rw [same]
  simpa only [prefixProgram, next, map_eq_pure_bind, bind_assoc, pure_bind] using
    OracleRuntime.run_bind_success_le runtime prefixProgram next Exceptional Success error hsuffix


end Native

end Interaction.Oracle

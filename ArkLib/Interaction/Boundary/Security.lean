import ArkLib.Interaction.Boundary.Compatibility
import ArkLib.Interaction.Security.Completeness

open Interaction.TwoParty

/-!
# Interaction-Native Boundaries: Plain Security Transport

This file records the operational and security consequences of pulling back a
plain verifier or reduction along a boundary.

The key point of the projection-first boundary split is that the outer output
families remain explicit in theorem binders. This keeps the dense dependent
types visible in the statement, rather than hiding them behind record fields.

## Main results

- `Verifier.run_pullback`
- `Verifier.probAccept_pullback_le`
- `Reduction.execute_pullback`
- `Reduction.completeness_pullback`
-/

namespace Interaction
namespace Boundary

namespace Verifier

/-- Running a pulled-back verifier is the same as running the original inner
verifier on the projected input and then lifting only the final plain statement
output through the boundary. -/
theorem run_pullback
    {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (boundary : Statement projection InnerStmtOut OuterStmtOut)
    (verifier :
      Interaction.Verifier m
        InnerStmtIn
        InnerSpec
        InnerRoles
        (fun _ => PUnit)
        InnerStmtOut)
    (outer : OuterStmtIn)
    {OutputP : Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (prover :
      Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
        (InnerSpec (projection.proj outer))
        (InnerRoles (projection.proj outer))
        OutputP) :
    Interaction.Verifier.run
        (pullback boundary verifier)
        outer
        PUnit.unit
        prover =
      (fun z => ⟨z.1, z.2.1, boundary.lift outer z.1 z.2.2⟩) <$>
        Interaction.Verifier.run verifier (projection.proj outer) PUnit.unit prover := by
  simpa [Interaction.Verifier.run, pullback] using
    (TwoParty.run_mapOutput_mapOutput
      (fP := fun _ out => out)
      (fC := fun tr stmtOut => boundary.lift outer tr stmtOut)
      prover
      (verifier (projection.proj outer) PUnit.unit))

/-- Soundness for a pulled-back verifier reduces to soundness of the inner
verifier once accepting outer outputs are known to satisfy the boundary
compatibility predicate. -/
theorem probAccept_pullback_le
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (boundary : Statement projection InnerStmtOut OuterStmtOut)
    (verifier :
      Interaction.Verifier m
        InnerStmtIn
        InnerSpec
        InnerRoles
        (fun _ => PUnit)
        InnerStmtOut)
    (outerLangIn : Set OuterStmtIn)
    (innerLangIn : Set InnerStmtIn)
    (outerLangOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        Set (OuterStmtOut outer tr))
    (innerLangOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerSpec inner)) →
        Set (InnerStmtOut inner tr))
    (compat :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        InnerStmtOut (projection.proj outer) tr →
        Prop)
    (boundarySound :
      Statement.IsSound
        boundary
        outerLangIn
        innerLangIn
        outerLangOut
        innerLangOut
        compat)
    (compatOfAccept :
      ∀ outer tr innerStmtOut,
        boundary.lift outer tr innerStmtOut ∈ outerLangOut outer tr →
          compat outer tr innerStmtOut)
    (outer : OuterStmtIn)
    {OutputP : Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (prover :
      Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
        (InnerSpec (projection.proj outer))
        (InnerRoles (projection.proj outer))
        OutputP) :
    Pr[fun z => z.2.2 ∈ outerLangOut outer z.1 |
      Interaction.Verifier.run (pullback boundary verifier) outer PUnit.unit prover] ≤
      Pr[fun z => z.2.2 ∈ innerLangOut (projection.proj outer) z.1 |
        Interaction.Verifier.run verifier (projection.proj outer) PUnit.unit prover] := by
  rw [run_pullback, probEvent_map]
  apply probEvent_mono
  intro z hz hOuter
  by_contra hInner
  exact
    boundarySound.lift_sound
      outer
      z.1
      z.2.2
      (compatOfAccept outer z.1 z.2.2 hOuter)
      hInner
      hOuter

end Verifier

namespace Reduction

/-- Compatibility hypothesis used by `completeness_pullback`.

It says that whenever an honest outer input is valid and the inner execution
produces an output satisfying the inner relation, the boundary-specific
compatibility predicate also holds. -/
private abbrev CompletenessCompat
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (_boundary :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerSpec inner)) →
        InnerStmtOut inner tr →
        InnerWitOut inner tr →
        Prop)
    (compat :
      (outer : OuterStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        InnerStmtOut (projection.proj outer) tr →
        InnerWitOut (projection.proj outer) tr →
        Prop) : Prop :=
  (outerStmt : OuterStmtIn) →
    (outerWit : OuterWitIn) →
    (outerStmt, outerWit) ∈ outerRelIn →
    (tr : Spec.Transcript (InnerSpec (projection.proj outerStmt))) →
    (innerStmtOut : InnerStmtOut (projection.proj outerStmt) tr) →
    (innerWitOut : InnerWitOut (projection.proj outerStmt) tr) →
    innerRelOut
      (projection.proj outerStmt)
      tr
      innerStmtOut
      innerWitOut →
    compat outerStmt outerWit tr innerStmtOut innerWitOut

/-- Honest execution of a pulled-back reduction is just honest execution of the
inner reduction on projected inputs, followed by lifting the prover and
verifier outputs through the boundary. -/
theorem execute_pullback
    {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (boundary :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    (reduction :
      Interaction.Reduction m
        InnerStmtIn
        InnerSpec
        InnerRoles
        (fun _ => PUnit)
        (fun _ => InnerWitIn)
        InnerStmtOut
        InnerWitOut)
    (outerStmt : OuterStmtIn)
    (outerWit : OuterWitIn) :
    Interaction.Reduction.execute
        (pullback boundary reduction)
        outerStmt
        PUnit.unit
        outerWit =
      (fun z =>
        let out :=
          boundary.lift outerStmt outerWit z.1 z.2.1.stmt z.2.1.wit
        ⟨z.1, out, boundary.stmt.lift outerStmt z.1 z.2.2⟩) <$>
        Interaction.Reduction.execute
          reduction
          (projection.proj outerStmt)
          PUnit.unit
          (boundary.wit.proj outerStmt outerWit) := by
  simp [Interaction.Reduction.execute, pullback, Prover.pullback, Verifier.pullback,
    TwoParty.run_mapOutput_mapOutput]

section Completeness

variable
    {m : Type _ → Type _} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}

variable
    (boundary :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    (reduction :
      Interaction.Reduction m
        InnerStmtIn
        InnerSpec
        InnerRoles
        (fun _ => PUnit)
        (fun _ => InnerWitIn)
        InnerStmtOut
        InnerWitOut)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))

variable
    (outerRelOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        OuterStmtOut outer tr →
        OuterWitOut outer tr →
        Prop)
    (innerRelOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerSpec inner)) →
        InnerStmtOut inner tr →
        InnerWitOut inner tr →
        Prop)
    (compat :
      (outer : OuterStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        InnerStmtOut (projection.proj outer) tr →
        InnerWitOut (projection.proj outer) tr →
        Prop)

variable
    (eps : ENNReal)

/-- Completeness transports across a context boundary once:

- valid outer inputs project to valid inner inputs,
- successful inner outputs can be lifted back to successful outer outputs, and
- the compatibility witness required by that lifting is available. -/
theorem completeness_pullback
    (boundaryComplete :
      Boundary.Context.IsComplete
        boundary
        outerRelIn
        innerRelIn
        outerRelOut
        innerRelOut
        compat)
    (compatOfValid :
      CompletenessCompat boundary outerRelIn innerRelOut compat)
    (hComplete :
      reduction.completeness
        (fun inner _ wit => (inner, wit) ∈ innerRelIn)
        innerRelOut
        eps) :
    (pullback boundary reduction).completeness
      (fun outer _ wit => (outer, wit) ∈ outerRelIn)
      outerRelOut
      eps := by
  intro outerStmt _ outerWit hOuterIn
  have hInnerIn :
      (projection.proj outerStmt,
        boundary.wit.proj outerStmt outerWit) ∈ innerRelIn :=
    boundaryComplete.proj_complete outerStmt outerWit hOuterIn
  let innerGood :
      ((tr : Spec.Transcript (InnerSpec (projection.proj outerStmt))) ×
        HonestProverOutput
          (InnerStmtOut (projection.proj outerStmt) tr)
          (InnerWitOut (projection.proj outerStmt) tr) ×
        InnerStmtOut (projection.proj outerStmt) tr) →
      Prop :=
    fun z =>
      z.2.1.stmt = z.2.2 ∧
        innerRelOut
          (projection.proj outerStmt)
          z.1
          z.2.2
          z.2.1.wit
  let outerGood :
      ((tr : Spec.Transcript (InnerSpec (projection.proj outerStmt))) ×
        HonestProverOutput
          (OuterStmtOut outerStmt tr)
          (OuterWitOut outerStmt tr) ×
        OuterStmtOut outerStmt tr) →
      Prop :=
    fun z =>
      z.2.1.stmt = z.2.2 ∧
        outerRelOut outerStmt z.1 z.2.2 z.2.1.wit
  have hmono :
      Pr[innerGood |
        Interaction.Reduction.execute
          reduction
          (projection.proj outerStmt)
          PUnit.unit
          (boundary.wit.proj outerStmt outerWit)] ≤
        Pr[outerGood |
          Interaction.Reduction.execute
            (pullback boundary reduction)
            outerStmt
            PUnit.unit
            outerWit] := by
    rw [execute_pullback]
    rw [probEvent_map]
    apply probEvent_mono
    intro z hz hInnerGood
    rcases hInnerGood with ⟨hEq, hRel⟩
    constructor
    · simpa using congrArg (boundary.stmt.lift outerStmt z.1) hEq
    · have hCompat :
          compat outerStmt outerWit z.1 z.2.2 z.2.1.wit :=
        compatOfValid outerStmt outerWit hOuterIn z.1 z.2.2 z.2.1.wit hRel
      simpa [hEq] using
        (boundaryComplete.lift_complete
          outerStmt
          outerWit
          z.1
          z.2.2
          z.2.1.wit
          hCompat
          hOuterIn
          hRel)
  calc
    1 - eps ≤
        Pr[innerGood |
          Interaction.Reduction.execute
            reduction
            (projection.proj outerStmt)
            PUnit.unit
            (boundary.wit.proj outerStmt outerWit)] :=
      hComplete
        (projection.proj outerStmt)
        PUnit.unit
        (boundary.wit.proj outerStmt outerWit)
        hInnerIn
    _ ≤ Pr[outerGood |
          Interaction.Reduction.execute
            (pullback boundary reduction)
            outerStmt
            PUnit.unit
            outerWit] :=
      hmono

theorem perfectCompleteness_pullback
    (boundaryComplete :
      Boundary.Context.IsComplete
        boundary
        outerRelIn
        innerRelIn
        outerRelOut
        innerRelOut
        compat)
    (compatOfValid :
      CompletenessCompat boundary outerRelIn innerRelOut compat)
    (hPerfect :
      reduction.perfectCompleteness
        (fun inner _ wit => (inner, wit) ∈ innerRelIn)
        innerRelOut) :
    (pullback boundary reduction).perfectCompleteness
      (fun outer _ wit => (outer, wit) ∈ outerRelIn)
      outerRelOut := by
  exact
    completeness_pullback
      boundary
      reduction
      outerRelIn
      innerRelIn
      outerRelOut
      innerRelOut
      compat
      0
      boundaryComplete
      compatOfValid
      hPerfect

end Completeness

end Reduction

end Boundary
end Interaction


import ArkLib.Interaction.Boundary.Reification

/-!
# Interaction-Native Boundaries: Compatibility Predicates

This module defines the semantic predicates used to transport completeness and
soundness across plain and oracle boundaries.

The plain layer is stated directly over the projection-first boundary core:

- `Statement.IsSound`
- `Context.IsComplete`

The oracle layer is then reduced to the plain one by flattening oracle-aware
boundaries into ordinary boundaries on `StatementWithOracles`.
-/

namespace Interaction
namespace Boundary

private abbrev ConcreteInput
    (StmtIn : Type)
    {ιₛ : StmtIn → Type}
    (OStmt : (s : StmtIn) → ιₛ s → Type) :=
  Sigma fun s : StmtIn => Interaction.OracleStatement (OStmt s)

/-- A statement lifting is sound when:

1. invalid outer inputs project to invalid inner inputs, and
2. invalid inner outputs lift to invalid outer outputs, assuming the caller's
   compatibility predicate. -/
structure Statement.IsSound
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (boundary : Statement projection InnerStmtOut OuterStmtOut)
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
        Prop) where
  proj_sound :
    ∀ outer, outer ∉ outerLangIn → projection.proj outer ∉ innerLangIn
  lift_sound :
    ∀ outer tr innerStmtOut,
      compat outer tr innerStmtOut →
      innerStmtOut ∉ innerLangOut (projection.proj outer) tr →
      boundary.lift outer tr innerStmtOut ∉ outerLangOut outer tr

/-- A context lifting is complete when:

1. valid outer inputs project to valid inner inputs, and
2. valid inner outputs lift to valid outer outputs, assuming the caller's
   compatibility predicate. -/
structure Context.IsComplete
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
    (boundary : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
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
        Prop) where
  proj_complete :
    ∀ outerStmt outerWit,
      (outerStmt, outerWit) ∈ outerRelIn →
      (projection.proj outerStmt,
        boundary.wit.proj outerStmt outerWit) ∈ innerRelIn
  lift_complete :
    ∀ outerStmt outerWit tr innerStmtOut innerWitOut,
      compat outerStmt outerWit tr innerStmtOut innerWitOut →
      (outerStmt, outerWit) ∈ outerRelIn →
      innerRelOut
        (projection.proj outerStmt)
        tr
        innerStmtOut
        innerWitOut →
      let out := boundary.lift outerStmt outerWit tr innerStmtOut innerWitOut
      outerRelOut outerStmt tr out.1 out.2

namespace OracleStatement

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    {projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext}
    {InnerStmtOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type}
    {toStatement : OracleStatementLift projection InnerStmtOut OuterStmtOut}
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
        (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext s)) →
        Innerιₛₒ s pt →
        Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
        Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
        (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
        Outerιₛₒ outer pt →
        Type}
    [∀ s pt i, OracleInterface (InnerOStmtOut s pt i)]
    [∀ outer pt i, OracleInterface (OuterOStmtOut outer pt i)]

/-- Flatten an oracle statement boundary into a plain boundary on
`StatementWithOracles`, projecting full transcripts to public transcripts at
the boundary. -/
@[inline] def toConcreteStatement
    (boundary :
      OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) :
    Statement
      (StatementProjection.mk
        (OuterStmtIn := ConcreteInput OuterStmtIn OuterOStmtIn)
        (InnerStmtIn := ConcreteInput InnerStmtIn InnerOStmtIn)
        (InnerSpec := fun inner => (InnerContext inner.1).toInteractionSpec)
        (proj := fun outer =>
          ⟨projection.proj outer.1,
            (boundary.reification outer.1).materializeIn outer.2⟩))
      (fun inner tr =>
        let pt := (InnerContext inner.1).projectPublic tr
        StatementWithOracles
          (fun _ => InnerStmtOut inner.1 pt)
          (fun _ => InnerOStmtOut inner.1 pt)
          inner.1)
      (fun outer tr =>
        let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
        StatementWithOracles
          (fun _ => OuterStmtOut outer.1 pt)
          (fun _ => OuterOStmtOut outer.1 pt)
          outer.1) where
  lift := fun outer tr innerOut =>
    let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
    ⟨toStatement.lift outer.1 pt innerOut.stmt,
      (boundary.reification outer.1).materializeOut
        outer.2
        pt
        innerOut.oracleStmt⟩

/-- Soundness for an oracle statement boundary is the plain soundness predicate
applied to its flattened concrete view. -/
abbrev IsSound
    (boundary :
      OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerLangIn :
      Set (ConcreteInput OuterStmtIn OuterOStmtIn))
    (innerLangIn :
      Set (ConcreteInput InnerStmtIn InnerOStmtIn))
    (outerLangOut :
      (outer : ConcreteInput OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerContext (projection.proj outer.1)).toInteractionSpec) →
        Set
          (let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
           StatementWithOracles
            (fun _ => OuterStmtOut outer.1 pt)
            (fun _ => OuterOStmtOut outer.1 pt)
            outer.1))
    (innerLangOut :
      (inner : ConcreteInput InnerStmtIn InnerOStmtIn) →
        (tr : Spec.Transcript (InnerContext inner.1).toInteractionSpec) →
        Set
          (let pt := (InnerContext inner.1).projectPublic tr
           StatementWithOracles
            (fun _ => InnerStmtOut inner.1 pt)
            (fun _ => InnerOStmtOut inner.1 pt)
            inner.1))
    (compat :
      (outer : ConcreteInput OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerContext (projection.proj outer.1)).toInteractionSpec) →
        (let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
         StatementWithOracles
          (fun _ => InnerStmtOut (projection.proj outer.1) pt)
          (fun _ => InnerOStmtOut (projection.proj outer.1) pt)
          (projection.proj outer.1)) →
        Prop) :=
  Statement.IsSound
    boundary.toConcreteStatement
    outerLangIn
    innerLangIn
    outerLangOut
    innerLangOut
    compat

end OracleStatement

namespace OracleContext

variable
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    {projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext}
    {InnerStmtOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type}
    {toContext : OracleContextLift projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut}
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
        (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext s)) →
        Innerιₛₒ s pt →
        Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
        Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
        (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
        Outerιₛₒ outer pt →
        Type}
    [∀ s pt i, OracleInterface (InnerOStmtOut s pt i)]
    [∀ outer pt i, OracleInterface (OuterOStmtOut outer pt i)]

/-- Flatten an oracle context boundary into a plain context boundary on
`StatementWithOracles`, projecting full transcripts to public transcripts at
the boundary. -/
@[inline] def toConcreteContext
  (boundary :
      OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) :
    Context
      (StatementProjection.mk
        (OuterStmtIn := ConcreteInput OuterStmtIn OuterOStmtIn)
        (InnerStmtIn := ConcreteInput InnerStmtIn InnerOStmtIn)
        (InnerSpec := fun inner => (InnerContext inner.1).toInteractionSpec)
        (proj := fun outer =>
          ⟨projection.proj outer.1,
            (boundary.reification outer.1).materializeIn outer.2⟩))
      OuterWitIn
      InnerWitIn
      (fun inner tr =>
        let pt := (InnerContext inner.1).projectPublic tr
        StatementWithOracles
          (fun _ => InnerStmtOut inner.1 pt)
          (fun _ => InnerOStmtOut inner.1 pt)
          inner.1)
      (fun outer tr =>
        let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
        StatementWithOracles
          (fun _ => OuterStmtOut outer.1 pt)
          (fun _ => OuterOStmtOut outer.1 pt)
          outer.1)
      (fun inner tr => InnerWitOut inner.1 ((InnerContext inner.1).projectPublic tr))
      (fun outer tr =>
        OuterWitOut outer.1 ((InnerContext (projection.proj outer.1)).projectPublic tr)) where
  stmt := {
    lift := fun outer tr innerOut =>
      let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
      ⟨toContext.stmt.lift outer.1 pt innerOut.stmt,
        (boundary.reification outer.1).materializeOut
          outer.2
          pt
          innerOut.oracleStmt⟩
  }
  witProj := {
    proj := fun outer outerWit =>
      toContext.wit.proj outer.1 outerWit
  }
  wit := {
    lift := fun outer outerWit tr innerStmtOut innerWitOut =>
      let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
      toContext.wit.lift
        outer.1
        outerWit
        pt
        innerStmtOut.stmt
        innerWitOut
  }

/-- Completeness for an oracle context boundary is the plain completeness
predicate applied to its flattened concrete view. -/
abbrev IsComplete
    (boundary :
      OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerRelIn :
      Set
        (ConcreteInput OuterStmtIn OuterOStmtIn × OuterWitIn))
    (innerRelIn :
      Set
        (ConcreteInput InnerStmtIn InnerOStmtIn × InnerWitIn))
    (outerRelOut :
      (outer : ConcreteInput OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerContext (projection.proj outer.1)).toInteractionSpec) →
        (let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
         StatementWithOracles
          (fun _ => OuterStmtOut outer.1 pt)
          (fun _ => OuterOStmtOut outer.1 pt)
          outer.1) →
        OuterWitOut outer.1 ((InnerContext (projection.proj outer.1)).projectPublic tr) →
        Prop)
    (innerRelOut :
      (inner : ConcreteInput InnerStmtIn InnerOStmtIn) →
        (tr : Spec.Transcript (InnerContext inner.1).toInteractionSpec) →
        (let pt := (InnerContext inner.1).projectPublic tr
         StatementWithOracles
          (fun _ => InnerStmtOut inner.1 pt)
          (fun _ => InnerOStmtOut inner.1 pt)
          inner.1) →
        InnerWitOut inner.1 ((InnerContext inner.1).projectPublic tr) →
        Prop)
    (compat :
      (outer : ConcreteInput OuterStmtIn OuterOStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerContext (projection.proj outer.1)).toInteractionSpec) →
        (let pt := (InnerContext (projection.proj outer.1)).projectPublic tr
         StatementWithOracles
          (fun _ => InnerStmtOut (projection.proj outer.1) pt)
          (fun _ => InnerOStmtOut (projection.proj outer.1) pt)
          (projection.proj outer.1)) →
        InnerWitOut (projection.proj outer.1)
          ((InnerContext (projection.proj outer.1)).projectPublic tr) →
        Prop) :=
  Context.IsComplete
    boundary.toConcreteContext
    outerRelIn
    innerRelIn
    outerRelOut
    innerRelOut
    compat

end OracleContext

end Boundary
end Interaction

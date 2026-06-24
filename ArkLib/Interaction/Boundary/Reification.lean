import ArkLib.Interaction.Boundary.Oracle

open Interaction.TwoParty

/-!
# Boundary Reification for `Interaction.Oracle`

The access layer rewires verifier queries. This file adds the concrete
materialization data needed by honest provers and concrete execution:

* `materializeIn` turns an outer input oracle family into the projected inner
  input oracle family.
* `materializeOut` turns an inner output oracle family into the outer output
  oracle family.
* `Realizes` states that materialization and verifier-side simulation answer
  every query the same way.
-/

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

/-- Concrete oracle materialization for one projected statement. -/
structure OracleStatementReification
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ : Type} (OuterOStmtIn : Outerιₛᵢ → Type)
    {Innerιₛᵢ : Type} (InnerOStmtIn : Innerιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    (InnerOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Innerιₛₒ pt → Type)
    {Outerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    (OuterOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Outerιₛₒ pt → Type)
    [∀ pt i, OracleInterface (InnerOStmtOut pt i)]
    [∀ pt i, OracleInterface (OuterOStmtOut pt i)] where
  materializeIn :
    OracleStatement OuterOStmtIn →
      OracleStatement InnerOStmtIn
  materializeOut :
    OracleStatement OuterOStmtIn →
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      OracleStatement (InnerOStmtOut pt) →
      OracleStatement (OuterOStmtOut pt)

namespace OracleStatementReification

/-- Coherence between query simulation and concrete oracle materialization. -/
def Realizes
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {InnerOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Innerιₛₒ pt → Type}
    {Outerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {OuterOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Outerιₛₒ pt → Type}
    [∀ pt i, OracleInterface (InnerOStmtOut pt i)]
    [∀ pt i, OracleInterface (OuterOStmtOut pt i)]
    (access :
      OracleStatementAccess
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) : Prop :=
  (∀ oStmtIn i q,
      simulateQ
        (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
        (access.simulateIn ⟨i, q⟩) =
          pure
            (OracleInterface.answer
              (reification.materializeIn oStmtIn i)
              q)) ∧
    ∀ oStmtIn pt innerOStmtOut i q,
      simulateQ
        (QueryImpl.add
          (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
          (OracleInterface.simOracle0
            (InnerOStmtOut pt)
            innerOStmtOut))
        (access.simulateOut pt ⟨i, q⟩) =
          pure
            (OracleInterface.answer
              ((reification.materializeOut
                oStmtIn
                pt
                innerOStmtOut) i)
              q)

/-- Materialized input oracles realize the access-layer input simulation. -/
theorem realizes_materializeIn
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {InnerOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Innerιₛₒ pt → Type}
    {Outerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {OuterOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Outerιₛₒ pt → Type}
    [∀ pt i, OracleInterface (InnerOStmtOut pt i)]
    [∀ pt i, OracleInterface (OuterOStmtOut pt i)]
    {access :
      OracleStatementAccess
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    {reification :
      OracleStatementReification
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    (hRealizes : Realizes access reification)
    (oStmtIn : OracleStatement OuterOStmtIn) :
    ∀ q,
      simulateQ
        (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
        (access.simulateIn q) =
          pure
            ((OracleInterface.simOracle0
              InnerOStmtIn
              (reification.materializeIn oStmtIn)) q) := by
  intro q
  rcases q with ⟨i, q⟩
  simpa [OracleInterface.simOracle0] using hRealizes.1 oStmtIn i q

/-- Materialized output oracles realize the access-layer output simulation. -/
theorem realizes_materializeOut
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {InnerOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Innerιₛₒ pt → Type}
    {Outerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {OuterOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Outerιₛₒ pt → Type}
    [∀ pt i, OracleInterface (InnerOStmtOut pt i)]
    [∀ pt i, OracleInterface (OuterOStmtOut pt i)]
    {access :
      OracleStatementAccess
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    {reification :
      OracleStatementReification
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    (hRealizes : Realizes access reification)
    (oStmtIn : OracleStatement OuterOStmtIn)
    (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext)
    (innerOStmtOut : OracleStatement (InnerOStmtOut pt)) :
    ∀ q,
      simulateQ
        (QueryImpl.add
          (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
          (OracleInterface.simOracle0
            (InnerOStmtOut pt)
            innerOStmtOut))
        (access.simulateOut pt q) =
          pure
            ((OracleInterface.simOracle0
              (OuterOStmtOut pt)
              (reification.materializeOut oStmtIn pt innerOStmtOut)) q) := by
  intro q
  rcases q with ⟨i, q⟩
  simpa [OracleInterface.simOracle0] using
    hRealizes.2 oStmtIn pt innerOStmtOut i q

/-- Rerouting an inner output simulation across a realized boundary preserves
the concrete inner output oracle behavior. -/
theorem routeInnerOutputQueries_materialize
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {InnerOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Innerιₛₒ pt → Type}
    {Outerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {OuterOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Outerιₛₒ pt → Type}
    [∀ pt i, OracleInterface (InnerOStmtOut pt i)]
    [∀ pt i, OracleInterface (OuterOStmtOut pt i)]
    (access :
      OracleStatementAccess
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (hRealizes : Realizes access reification)
    (oStmtIn : OracleStatement OuterOStmtIn)
    {pt : Interaction.Oracle.Spec.PublicTranscript InnerContext}
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOStmtOut : OracleStatement (InnerOStmtOut pt))
    (simulateInner :
      QueryImpl [InnerOStmtOut pt]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add
              (OracleInterface.simOracle0
                InnerOStmtIn
                (reification.materializeIn oStmtIn))
              msgImpl)
            (simulateInner q) =
          pure
            ((OracleInterface.simOracle0
              (InnerOStmtOut pt)
              innerOStmtOut) q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add
            (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
            msgImpl)
          (OracleStatementAccess.routeInnerOutputQueries
            (access := access)
            (pt := pt)
            msgSpec
            simulateInner
            q) =
        pure
          ((OracleInterface.simOracle0
            (InnerOStmtOut pt)
            innerOStmtOut) q) := by
  intro q
  simpa using
    OracleStatementAccess.routeInnerOutputQueries_eval
      (access := access)
      (pt := pt)
      msgSpec
      (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
      (OracleInterface.simOracle0
        InnerOStmtIn
        (reification.materializeIn oStmtIn))
      msgImpl
      (OracleInterface.simOracle0
        (InnerOStmtOut pt)
        innerOStmtOut)
      simulateInner
      (realizes_materializeIn
        (hRealizes := hRealizes)
        oStmtIn)
      hInner
      q

/-- Materializing an inner output oracle across a realized boundary realizes the
pulled-back outer output simulation. -/
theorem pullbackSimulate_materialize
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {InnerOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Innerιₛₒ pt → Type}
    {Outerιₛₒ :
      Interaction.Oracle.Spec.PublicTranscript InnerContext → Type}
    {OuterOStmtOut :
      (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      Outerιₛₒ pt → Type}
    [∀ pt i, OracleInterface (InnerOStmtOut pt i)]
    [∀ pt i, OracleInterface (OuterOStmtOut pt i)]
    (access :
      OracleStatementAccess
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification
        (InnerContext := InnerContext)
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (hRealizes : Realizes access reification)
    (oStmtIn : OracleStatement OuterOStmtIn)
    (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext)
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOStmtOut : OracleStatement (InnerOStmtOut pt))
    (simulateInner :
      QueryImpl [InnerOStmtOut pt]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add
              (OracleInterface.simOracle0
                InnerOStmtIn
                (reification.materializeIn oStmtIn))
              msgImpl)
            (simulateInner q) =
          pure
            ((OracleInterface.simOracle0
              (InnerOStmtOut pt)
              innerOStmtOut) q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add
            (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
            msgImpl)
          (OracleStatementAccess.pullbackSimulate
            (access := access)
            pt
            msgSpec
            simulateInner
            q) =
        pure
          ((OracleInterface.simOracle0
            (OuterOStmtOut pt)
            (reification.materializeOut oStmtIn pt innerOStmtOut)) q) := by
  intro q
  simpa using
    OracleStatementAccess.pullbackSimulate_eval
      (access := access)
      pt
      msgSpec
      (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
      (OracleInterface.simOracle0
        InnerOStmtIn
        (reification.materializeIn oStmtIn))
      msgImpl
      (OracleInterface.simOracle0
        (InnerOStmtOut pt)
        innerOStmtOut)
      (OracleInterface.simOracle0
        (OuterOStmtOut pt)
        (reification.materializeOut oStmtIn pt innerOStmtOut))
      simulateInner
      (realizes_materializeIn
        (hRealizes := hRealizes)
        oStmtIn)
      hInner
      (realizes_materializeOut
        (hRealizes := hRealizes)
        oStmtIn
        pt
        innerOStmtOut)
      q

end OracleStatementReification

/-! ## Bundled oracle boundaries -/

/-- A bundled oracle statement boundary: statement lifting plus oracle access,
reification, and coherence. -/
structure OracleStatement
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    {projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext}
    {InnerStmtOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type}
    (toStatement : OracleStatementLift projection InnerStmtOut OuterStmtOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    (OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type)
    {Innerιₛᵢ : InnerStmtIn → Type}
    (InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type)
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext s)) →
      Innerιₛₒ s pt → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
      Outerιₛₒ outer pt → Type)
    [∀ s pt i, OracleInterface (InnerOStmtOut s pt i)]
    [∀ outer pt i, OracleInterface (OuterOStmtOut outer pt i)] where
  access :
    (outer : OuterStmtIn) →
      OracleStatementAccess
        (InnerContext := InnerContext (projection.proj outer))
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        (InnerOStmtOut (projection.proj outer))
        (OuterOStmtOut outer)
  reification :
    (outer : OuterStmtIn) →
      OracleStatementReification
        (InnerContext := InnerContext (projection.proj outer))
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        (InnerOStmtOut (projection.proj outer))
        (OuterOStmtOut outer)
  coherent :
    ∀ outer,
      OracleStatementReification.Realizes
        (access outer)
        (reification outer)

/-- A bundled oracle context boundary: context lifting plus oracle access,
reification, and coherence. -/
structure OracleContext
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
    (toContext :
      OracleContextLift projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    (OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type)
    {Innerιₛᵢ : InnerStmtIn → Type}
    (InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type)
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext s)) →
      Innerιₛₒ s pt → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
      Outerιₛₒ outer pt → Type)
    [∀ s pt i, OracleInterface (InnerOStmtOut s pt i)]
    [∀ outer pt i, OracleInterface (OuterOStmtOut outer pt i)] where
  access :
    (outer : OuterStmtIn) →
      OracleStatementAccess
        (InnerContext := InnerContext (projection.proj outer))
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        (InnerOStmtOut (projection.proj outer))
        (OuterOStmtOut outer)
  reification :
    (outer : OuterStmtIn) →
      OracleStatementReification
        (InnerContext := InnerContext (projection.proj outer))
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        (InnerOStmtOut (projection.proj outer))
        (OuterOStmtOut outer)
  coherent :
    ∀ outer,
      OracleStatementReification.Realizes
        (access outer)
        (reification outer)

/-- Forget witness transport and extract the statement-level oracle boundary. -/
def OracleContext.toOracleStatement
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
    {toContext :
      OracleContextLift projection
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
      Innerιₛₒ s pt → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
      Outerιₛₒ outer pt → Type}
    [∀ s pt i, OracleInterface (InnerOStmtOut s pt i)]
    [∀ outer pt i, OracleInterface (OuterOStmtOut outer pt i)]
    (oc : OracleContext toContext
      OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) :
    OracleStatement toContext.stmt
      OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut where
  access := oc.access
  reification := oc.reification
  coherent := oc.coherent

end Boundary

namespace Oracle
namespace Reduction

/-- Reinterpret an inner oracle reduction through a full oracle context
boundary. The shared input is projected; local statements are `PUnit`. -/
def pullback
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    {projection : Boundary.OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext}
    {InnerRoles : (s : InnerStmtIn) → Interaction.Oracle.Spec.RoleDeco (InnerContext s)}
    {InnerOracleDeco :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.OracleDeco (InnerContext s)}
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
    (toContext :
      Boundary.OracleContextLift projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
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
      Innerιₛₒ s pt → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
      Outerιₛₒ outer pt → Type}
    [∀ s pt i, OracleInterface (InnerOStmtOut s pt i)]
    [∀ outer pt i, OracleInterface (OuterOStmtOut outer pt i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reduction :
      Interaction.Oracle.Reduction oSpec
        InnerStmtIn InnerContext InnerRoles InnerOracleDeco
        (fun _ => PUnit)
        InnerOStmtIn
        (fun _ => InnerWitIn)
        InnerStmtOut InnerOStmtOut InnerWitOut) :
    Interaction.Oracle.Reduction oSpec
      OuterStmtIn
      (fun outer => InnerContext (projection.proj outer))
      (fun outer => InnerRoles (projection.proj outer))
      (fun outer => InnerOracleDeco (projection.proj outer))
      (fun _ => PUnit)
      OuterOStmtIn
      (fun _ => OuterWitIn)
      OuterStmtOut
      OuterOStmtOut
      OuterWitOut where
  prover outerStmt sWithOracles outerWit := do
    let outerOStmtIn := sWithOracles.oracleStmt
    let innerStmt := projection.proj outerStmt
    let innerOStmtIn :=
      (boundary.reification outerStmt).materializeIn outerOStmtIn
    let innerWit :=
      toContext.wit.proj outerStmt outerWit
    let strat ← reduction.prover innerStmt ⟨PUnit.unit, innerOStmtIn⟩ innerWit
    pure <| Interaction.Spec.ShapeOver.mapOutput focalMonadicShape
      (agent := PUnit.unit)
      (spec := (InnerContext innerStmt).toInteractionSpec)
      (ctxs := RoleDecoration.withMonads
        ((InnerContext innerStmt).toSpecRoles (InnerRoles innerStmt))
        ((InnerContext innerStmt).toProverMonadDecoration oSpec))
      (fun tr out =>
        let pt := (InnerContext innerStmt).projectPublic tr
        let innerStmtOut := out.stmt.stmt
        let innerOStmtOut := out.stmt.oracleStmt
        let outerStmtOut :=
          toContext.stmt.lift outerStmt pt innerStmtOut
        let outerOStmtOut :=
          (boundary.reification outerStmt).materializeOut
            outerOStmtIn
            pt
            innerOStmtOut
        let outerWitOut :=
          toContext.wit.lift
            outerStmt
            outerWit
            pt
            innerStmtOut
            out.wit
        ⟨⟨outerStmtOut, outerOStmtOut⟩, outerWitOut⟩)
      strat
  verifier :=
    Interaction.Oracle.Verifier.pullback
      toContext.stmt
      boundary.access
      reduction.verifier

end Reduction
end Oracle

end Interaction


import ArkLib.Interaction.Boundary.Compatibility
import ArkLib.Interaction.Oracle.Reification

/-!
# Security Transport Helpers for Oracle Boundaries

This file contains the security-facing consequences of the native oracle
boundary layer. The core fact is query-level: if the inner verifier's output
oracle simulation is realized by a concrete inner output oracle, then the
pulled-back outer simulation is realized by the materialized outer output
oracle.
-/

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

namespace OracleStatementReification

/-- Boundary pullback preserves concrete realization of output-oracle
simulations. This is the query-level lemma used by oracle completeness and
soundness transports. -/
theorem outputRealizes_pullbackSimulate
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
    (oStmtIn : Interaction.OracleStatement OuterOStmtIn)
    (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext)
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOStmtOut : Interaction.OracleStatement (InnerOStmtOut pt))
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
            (reification.materializeOut oStmtIn pt innerOStmtOut)) q) :=
  pullbackSimulate_materialize
    access
    reification
    hRealizes
    oStmtIn
    pt
    msgSpec
    msgImpl
    innerOStmtOut
    simulateInner
    hInner

end OracleStatementReification

namespace OracleStatement

open Interaction.Oracle

/-- A verifier reification transports through a realized oracle statement
boundary. The outer concrete oracle output is obtained by reifying the projected
inner input and then materializing that inner output back through the boundary. -/
def pullbackVerifierReification
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
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
    {toStatement :
      Boundary.OracleStatementLift projection InnerStmtOut OuterStmtOut}
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
      Boundary.OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (verifier :
      Interaction.Oracle.Verifier oSpec
        InnerStmtIn InnerContext InnerRoles InnerOracleDeco
        (fun _ => PUnit) InnerOStmtIn InnerStmtOut InnerOStmtOut)
    (innerReification :
      Interaction.Oracle.Verifier.Reification verifier) :
    Interaction.Oracle.Verifier.Reification
      (Interaction.Oracle.Verifier.pullback
        toStatement
        boundary.access
        verifier) where
  reify outer oStatementIn tr := do
    let innerOStatementOut ←
      innerReification.reify
        (projection.proj outer)
        ((boundary.reification outer).materializeIn oStatementIn)
        tr
    pure <|
      (boundary.reification outer).materializeOut
        oStatementIn
        ((InnerContext (projection.proj outer)).projectPublic tr)
        innerOStatementOut
  correct := by
    intro outer oStatementIn tr oStatementOut hReify
    cases hInner :
        innerReification.reify
          (projection.proj outer)
          ((boundary.reification outer).materializeIn oStatementIn)
          tr with
    | none =>
        rw [hInner] at hReify
        cases hReify
    | some innerOStatementOut =>
      rw [hInner] at hReify
      cases hReify
      rw [Interaction.Oracle.Verifier.simulatesConcrete_iff_outputRealizes]
      intro i q
      simpa [Interaction.Oracle.Verifier.pullback] using
        (Boundary.OracleStatementReification.outputRealizes_pullbackSimulate
            (boundary.access outer)
            (boundary.reification outer)
            (boundary.coherent outer)
            oStatementIn
            ((InnerContext (projection.proj outer)).projectPublic tr)
            ((InnerContext (projection.proj outer)).toOracleSpec
              (InnerOracleDeco (projection.proj outer))
              ((InnerContext (projection.proj outer)).projectPublic tr))
            (Interaction.Oracle.Spec.answerQuery
              (InnerContext (projection.proj outer))
              (InnerOracleDeco (projection.proj outer))
              tr)
            innerOStatementOut
            (verifier.simulate
              (projection.proj outer)
              ((InnerContext (projection.proj outer)).projectPublic tr))
            (by
              intro q
              rcases q with ⟨i, q⟩
              simpa [Interaction.Oracle.Verifier.SimulatesConcrete, OutputRealizes] using
                (innerReification.correct
                    (projection.proj outer)
                    ((boundary.reification outer).materializeIn oStatementIn)
                    tr
                    innerOStatementOut
                    hInner
                  i q))
            ⟨i, q⟩)

end OracleStatement

end Boundary
end Interaction

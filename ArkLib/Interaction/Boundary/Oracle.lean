import ArkLib.Interaction.Boundary.Core
import ArkLib.Interaction.Oracle.Execution

open Interaction.TwoParty

/-!
# Boundaries for `Interaction.Oracle`

This file contains the verifier-side half of oracle boundaries for the canonical
`Interaction.Oracle.Spec` layer. A boundary reinterprets an inner oracle
interaction through an outer statement interface without changing the protocol
tree.

The important indexing choice is that statement outputs and output oracle
families are indexed by `Oracle.Spec.PublicTranscript`, not by the full
interaction transcript. Full transcripts still appear when executing a concrete
prover, because they carry the actual oracle-message values used to answer
oracle queries.
-/

universe u

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

/-! ## Generic simulation lemmas -/

/-- Extensionality for oracle-query simulations. -/
theorem simulateQ_ext
    {ι : Type _} {spec : OracleSpec ι} {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    {impl₁ impl₂ : QueryImpl spec r}
    (himpl : ∀ q, impl₁ q = impl₂ q) :
    ∀ {α : Type _} (oa : OracleComp spec α), simulateQ impl₁ oa = simulateQ impl₂ oa := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [himpl t, ih]

/-- Simulating through one handler and then another is the same as simulating
once through their composed handler. -/
theorem simulateQ_compose
    {ι : Type _} {spec : OracleSpec ι}
    {ι' : Type _} {spec' : OracleSpec ι'}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    (impl' : QueryImpl spec' r)
    (impl : QueryImpl spec (OracleComp spec')) :
    ∀ {α : Type _} (oa : OracleComp spec α),
      simulateQ impl' (simulateQ impl oa) =
        simulateQ (fun q => simulateQ impl' (impl q)) oa := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [ih]

/-- Lifting an `Id`-valued handler into a larger oracle computation commutes
with `simulateQ`. -/
theorem simulateQ_liftId
    {ι : Type _} {spec : OracleSpec ι}
    {ι' : Type _} {superSpec : OracleSpec ι'}
    (impl : QueryImpl spec Id) :
    ∀ {α : Type _} (oa : OracleComp spec α),
      simulateQ
          (fun q => (liftM (n := OracleComp superSpec) (impl q) : OracleComp superSpec _))
          oa =
        (liftM (n := OracleComp superSpec) (simulateQ impl oa) : OracleComp superSpec α) := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t oa ih => simp [simulateQ_bind, ih, simulateQ_query]

/-- If a computation only queries the left summand of a sum oracle spec, then
evaluating it with the combined handler is the same as evaluating it with the
left handler alone. -/
theorem simulateQ_add_liftComp_left
    {ι₁ : Type _} {ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    (impl₁ : QueryImpl spec₁ r)
    (impl₂ : QueryImpl spec₂ r)
    {α : Type _}
    (oa : OracleComp spec₁ α) :
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (OracleComp.liftComp oa (spec₁ + spec₂)) =
      simulateQ impl₁ oa := by
  rw [OracleComp.liftComp_def, simulateQ_compose]
  apply simulateQ_ext
  intro q
  change
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (liftM ((spec₁ + spec₂).query (.inl q))) =
      impl₁ q
  simp [QueryImpl.add, simulateQ_query]

/-- If a computation only queries the right summand of a sum oracle spec, then
evaluating it with the combined handler is the same as evaluating it with the
right handler alone. -/
theorem simulateQ_add_liftComp_right
    {ι₁ : Type _} {ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    (impl₁ : QueryImpl spec₁ r)
    (impl₂ : QueryImpl spec₂ r)
    {α : Type _}
    (oa : OracleComp spec₂ α) :
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (OracleComp.liftComp oa (spec₁ + spec₂)) =
      simulateQ impl₂ oa := by
  rw [OracleComp.liftComp_def, simulateQ_compose]
  apply simulateQ_ext
  intro q
  change
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (liftM ((spec₁ + spec₂).query (.inr q))) =
      impl₂ q
  simp [QueryImpl.add, simulateQ_query]

/-! ## Public-transcript-indexed boundary data -/

/-- The projection half of an oracle statement boundary. -/
structure OracleStatementProjection
    (OuterStmtIn InnerStmtIn : Type)
    (InnerContext : InnerStmtIn → Interaction.Oracle.Spec) where
  proj : OuterStmtIn → InnerStmtIn

namespace OracleStatementProjection

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}

/-- The outer oracle context induced by a statement projection. -/
@[inline] abbrev context
    (projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext) :
    OuterStmtIn → Interaction.Oracle.Spec :=
  fun outer => InnerContext (projection.proj outer)

/-- Identity oracle statement projection. -/
@[inline, reducible] def id
    (StmtIn : Type)
    (InnerContext : StmtIn → Interaction.Oracle.Spec) :
    OracleStatementProjection StmtIn StmtIn InnerContext where
  proj := fun stmt => stmt

end OracleStatementProjection

/-- Statement-output lifting for an oracle boundary. Outputs are indexed by the
public transcript of the oracle protocol. -/
structure OracleStatementLift
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    (projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext)
    (InnerStmtOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type)
    (OuterStmtOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type) where
  lift :
    (outer : OuterStmtIn) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
      InnerStmtOut (projection.proj outer) pt →
      OuterStmtOut outer pt

namespace OracleStatementLift

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

/-- The input projection underlying a statement lifting. -/
@[inline] abbrev proj
    (_ : OracleStatementLift projection InnerStmtOut OuterStmtOut) :
    OuterStmtIn → InnerStmtIn :=
  projection.proj

/-- Identity statement lifting. -/
@[inline, reducible] def id
    (StmtIn : Type)
    (InnerContext : StmtIn → Interaction.Oracle.Spec)
    (StmtOut :
      (s : StmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type) :
    OracleStatementLift
      (OracleStatementProjection.id StmtIn InnerContext)
      StmtOut
      StmtOut where
  lift := fun _ _ stmtOut => stmtOut

end OracleStatementLift

/-- The projection half of an oracle witness boundary. -/
structure OracleWitnessProjection
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    (projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext)
    (OuterWitIn InnerWitIn : Type) where
  proj : (outer : OuterStmtIn) → OuterWitIn → InnerWitIn

/-- Witness-output lifting for an oracle boundary. -/
structure OracleWitnessLift
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    {projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext}
    {OuterWitIn InnerWitIn : Type}
    (witnessProjection : OracleWitnessProjection projection OuterWitIn InnerWitIn)
    (InnerStmtOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type)
    (InnerWitOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type)
    (OuterWitOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type) where
  lift :
    (outer : OuterStmtIn) →
      OuterWitIn →
      (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer))) →
      InnerStmtOut (projection.proj outer) pt →
      InnerWitOut (projection.proj outer) pt →
      OuterWitOut outer pt

namespace OracleWitnessLift

/-- The input witness projection underlying a witness lifting. -/
@[inline] abbrev proj
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    {projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext}
    {OuterWitIn InnerWitIn : Type}
    {witnessProjection : OracleWitnessProjection projection OuterWitIn InnerWitIn}
    {InnerStmtOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type}
    (_ : OracleWitnessLift witnessProjection InnerStmtOut InnerWitOut OuterWitOut) :
    (outer : OuterStmtIn) → OuterWitIn → InnerWitIn :=
  witnessProjection.proj

end OracleWitnessLift

/-- A full oracle boundary bundling statement and witness transport. -/
structure OracleContextLift
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    (projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext)
    (OuterWitIn InnerWitIn : Type)
    (InnerStmtOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type)
    (OuterStmtOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type)
    (InnerWitOut :
      (s : InnerStmtIn) → Interaction.Oracle.Spec.PublicTranscript (InnerContext s) → Type)
    (OuterWitOut :
      (outer : OuterStmtIn) →
        Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outer)) →
          Type) where
  witProj : OracleWitnessProjection projection OuterWitIn InnerWitIn
  stmt : OracleStatementLift projection InnerStmtOut OuterStmtOut
  wit : OracleWitnessLift witProj InnerStmtOut InnerWitOut OuterWitOut

namespace OracleContextLift

/-- Lift inner statement and witness outputs back to outer outputs. -/
@[inline] def lift
    {OuterStmtIn InnerStmtIn : Type}
    {InnerContext : InnerStmtIn → Interaction.Oracle.Spec}
    {projection : OracleStatementProjection OuterStmtIn InnerStmtIn InnerContext}
    {OuterWitIn InnerWitIn : Type}
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
    (boundary : OracleContextLift projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut)
    (outerStmt : OuterStmtIn) (outerWit : OuterWitIn)
    (pt : Interaction.Oracle.Spec.PublicTranscript (InnerContext (projection.proj outerStmt)))
    (stmtOut : InnerStmtOut (projection.proj outerStmt) pt)
    (witOut : InnerWitOut (projection.proj outerStmt) pt) :
    OuterStmtOut outerStmt pt × OuterWitOut outerStmt pt :=
  ⟨boundary.stmt.lift outerStmt pt stmtOut,
    boundary.wit.lift outerStmt outerWit pt stmtOut witOut⟩

end OracleContextLift

/-! ## Verifier-side oracle access -/

/-- Verifier-side oracle simulation for one projected statement.

`simulateIn` answers inner input-oracle queries using outer input-oracle
queries. `simulateOut` answers outer output-oracle queries using outer input
oracles and the inner output oracle. -/
structure OracleStatementAccess
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
  simulateIn :
    QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)
  simulateOut :
    (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext) →
      QueryImpl [OuterOStmtOut pt]ₒ
        (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut pt]ₒ))

namespace OracleStatementAccess

/-- Route inner input oracle queries through `simulateIn`, passing base oracles
and accumulated prover-message oracles through unchanged. -/
def routeInputQueries
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ ιₐ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (accSpec : OracleSpec ιₐ) :
    QueryImpl
      ((oSpec + [InnerOStmtIn]ₒ) + accSpec)
      (OracleComp ((oSpec + [OuterOStmtIn]ₒ) + accSpec))
  | .inl (.inl q) =>
      liftM <| oSpec.query q
  | .inl (.inr q) =>
      OracleComp.liftComp
        (superSpec := (oSpec + [OuterOStmtIn]ₒ) + accSpec)
        (simulateIn q)
  | .inr q =>
      liftM <| accSpec.query q

/-- Concrete evaluator route for the outer-input side of `routeInputQueries`. -/
def routeInputQueriesOuterEval
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ ιₐ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (accSpec : OracleSpec ιₐ)
    (accImpl : QueryImpl accSpec Id) :
    QueryImpl ((oSpec + [OuterOStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
  fun
  | .inl (.inl q) => liftM <| oSpec.query q
  | .inl (.inr q) =>
      (liftM (n := OracleComp oSpec) (outerInputImpl q) : OracleComp oSpec _)
  | .inr q =>
      (liftM (n := OracleComp oSpec) (accImpl q) : OracleComp oSpec _)

/-- Concrete evaluator route for the inner-input side of `routeInputQueries`. -/
def routeInputQueriesInnerEval
    {ι : Type} {oSpec : OracleSpec ι}
    {Innerιₛᵢ ιₐ : Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (accSpec : OracleSpec ιₐ)
    (accImpl : QueryImpl accSpec Id) :
    QueryImpl ((oSpec + [InnerOStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
  fun
  | .inl (.inl q) => liftM <| oSpec.query q
  | .inl (.inr q) =>
      (liftM (n := OracleComp oSpec) (innerInputImpl q) : OracleComp oSpec _)
  | .inr q =>
      (liftM (n := OracleComp oSpec) (accImpl q) : OracleComp oSpec _)

/-- Evaluating `routeInputQueries` against concrete outer input oracles agrees
with evaluating the original inner handler against the realized inner input
oracle. -/
theorem routeInputQueries_eval
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ ιₐ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (accSpec : OracleSpec ιₐ)
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (accImpl : QueryImpl accSpec Id)
    (hInput :
      ∀ q,
        simulateQ outerInputImpl (simulateIn q) =
          pure (innerInputImpl q)) :
    ∀ {α : Type _}
      (oa : OracleComp ((oSpec + [InnerOStmtIn]ₒ) + accSpec) α),
      simulateQ
          (routeInputQueriesOuterEval
            (oSpec := oSpec)
            outerInputImpl
            accSpec
            accImpl)
          (simulateQ
            (routeInputQueries (oSpec := oSpec) simulateIn accSpec)
            oa) =
        simulateQ
          (routeInputQueriesInnerEval
            (oSpec := oSpec)
            innerInputImpl
            accSpec
            accImpl)
          oa := by
  intro α oa
  rw [simulateQ_compose]
  apply simulateQ_ext
  intro q
  rcases q with (q | q) | q
  · dsimp [OracleStatementAccess.routeInputQueries]
    rfl
  · let outerRoute :
        QueryImpl [OuterOStmtIn]ₒ (OracleComp oSpec) :=
      fun q => (liftM (n := OracleComp oSpec) (outerInputImpl q) : OracleComp oSpec _)
    simpa [OracleStatementAccess.routeInputQueries, routeInputQueriesOuterEval] using
      (calc
      simulateQ
          (routeInputQueriesOuterEval
            (oSpec := oSpec)
            outerInputImpl
            accSpec
            accImpl)
          (OracleComp.liftComp
            (superSpec := (oSpec + [OuterOStmtIn]ₒ) + accSpec)
            (simulateIn q)) =
        simulateQ outerRoute (simulateIn q) := by
          rw [OracleComp.liftComp_def, simulateQ_compose]
          apply simulateQ_ext
          intro q'
          rfl
      _ =
        (liftM (n := OracleComp oSpec) (simulateQ outerInputImpl (simulateIn q)) :
          OracleComp oSpec _) := by
            simpa [outerRoute] using
              (simulateQ_liftId (superSpec := oSpec) outerInputImpl (simulateIn q))
      _ =
        (liftM (n := OracleComp oSpec) (innerInputImpl q) : OracleComp oSpec _) := by
          simpa using congrArg
            (fun x => (liftM (n := OracleComp oSpec) x : OracleComp oSpec _))
            (hInput q))
  · dsimp [OracleStatementAccess.routeInputQueries, routeInputQueriesOuterEval,
      routeInputQueriesInnerEval]
    rfl

/-- Given a simulation of an inner output oracle that issues inner input oracle
queries, compose it with `simulateIn` so it issues outer input oracle queries
instead. -/
def routeInnerOutputQueries
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    {pt : Interaction.Oracle.Spec.PublicTranscript InnerContext}
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (simulateInner :
      QueryImpl [InnerOStmtOut pt]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec))) :
    QueryImpl [InnerOStmtOut pt]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
  fun q =>
    let route :
        QueryImpl ([InnerOStmtIn]ₒ + msgSpec)
          (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
      fun
      | .inl qIn =>
          OracleComp.liftComp
            (superSpec := [OuterOStmtIn]ₒ + msgSpec)
            (access.simulateIn qIn)
      | .inr qMsg =>
          liftM <| msgSpec.query qMsg
    simulateQ route (simulateInner q)

/-- Evaluating `routeInnerOutputQueries` against concrete outer input oracles
agrees with evaluating the original inner output simulation against the
realized inner input oracles. -/
theorem routeInnerOutputQueries_eval
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    {pt : Interaction.Oracle.Spec.PublicTranscript InnerContext}
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOutputImpl : QueryImpl [InnerOStmtOut pt]ₒ Id)
    (simulateInner :
      QueryImpl [InnerOStmtOut pt]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInput :
      ∀ q,
        simulateQ outerInputImpl (access.simulateIn q) =
          pure (innerInputImpl q))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add innerInputImpl msgImpl)
            (simulateInner q) =
          pure (innerOutputImpl q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add outerInputImpl msgImpl)
          (routeInnerOutputQueries
            (access := access)
            (pt := pt)
            msgSpec
            simulateInner
            q) =
        pure (innerOutputImpl q) := by
  intro q
  dsimp [routeInnerOutputQueries]
  calc
    simulateQ
        (QueryImpl.add outerInputImpl msgImpl)
        (simulateQ
          (fun
            | .inl qIn =>
                OracleComp.liftComp
                  (superSpec := [OuterOStmtIn]ₒ + msgSpec)
                  (access.simulateIn qIn)
            | .inr qMsg =>
                liftM <| msgSpec.query qMsg)
          (simulateInner q)) =
      simulateQ
        (fun q =>
          simulateQ
            (QueryImpl.add outerInputImpl msgImpl)
            (match q with
            | .inl qIn =>
                OracleComp.liftComp
                  (superSpec := [OuterOStmtIn]ₒ + msgSpec)
                  (access.simulateIn qIn)
            | .inr qMsg =>
                liftM <| msgSpec.query qMsg))
        (simulateInner q) := by
        rw [simulateQ_compose]
    _ =
      simulateQ
        (QueryImpl.add innerInputImpl msgImpl)
        (simulateInner q) := by
          apply simulateQ_ext
          intro q'
          cases q' with
          | inl qIn =>
              calc
                simulateQ
                    (QueryImpl.add outerInputImpl msgImpl)
                    (OracleComp.liftComp
                      (access.simulateIn qIn)
                      ([OuterOStmtIn]ₒ + msgSpec)) =
                  simulateQ outerInputImpl (access.simulateIn qIn) := by
                    simpa using
                      simulateQ_add_liftComp_left
                        outerInputImpl
                        msgImpl
                        (access.simulateIn qIn)
                _ = pure (innerInputImpl qIn) :=
                  hInput qIn
          | inr qMsg =>
              calc
                simulateQ
                    (QueryImpl.add outerInputImpl msgImpl)
                    (OracleComp.liftComp
                      (liftM (msgSpec.query qMsg) : OracleComp msgSpec _)
                      ([OuterOStmtIn]ₒ + msgSpec)) =
                  simulateQ msgImpl
                    (liftM (msgSpec.query qMsg) : OracleComp msgSpec _) := by
                      simpa using
                        simulateQ_add_liftComp_right
                          outerInputImpl
                          msgImpl
                          (liftM (msgSpec.query qMsg) : OracleComp msgSpec _)
                _ = msgImpl qMsg := by
                  simp [simulateQ_query]
    _ = pure (innerOutputImpl q) :=
      hInner q

/-- Rewire an output oracle simulation through a statement boundary. -/
def pullbackSimulate
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext)
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (simulateInner :
      QueryImpl [InnerOStmtOut pt]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec))) :
    QueryImpl [OuterOStmtOut pt]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
  fun q =>
    let route :
        QueryImpl
          ([OuterOStmtIn]ₒ + [InnerOStmtOut pt]ₒ)
          (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
      fun
      | .inl qIn =>
          liftM <| ([OuterOStmtIn]ₒ).query qIn
      | .inr qOut =>
          routeInnerOutputQueries
            (access := access)
            (pt := pt)
            msgSpec
            simulateInner
            qOut
    simulateQ route (access.simulateOut pt q)

/-- Evaluating `pullbackSimulate` against concrete outer input oracles and a
concrete message oracle agrees with the intended concrete outer output oracle. -/
theorem pullbackSimulate_eval
    {InnerContext : Interaction.Oracle.Spec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    (pt : Interaction.Oracle.Spec.PublicTranscript InnerContext)
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOutputImpl : QueryImpl [InnerOStmtOut pt]ₒ Id)
    (outerOutputImpl : QueryImpl [OuterOStmtOut pt]ₒ Id)
    (simulateInner :
      QueryImpl [InnerOStmtOut pt]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInput :
      ∀ q,
        simulateQ outerInputImpl (access.simulateIn q) =
          pure (innerInputImpl q))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add innerInputImpl msgImpl)
            (simulateInner q) =
          pure (innerOutputImpl q))
    (hOuter :
      ∀ q,
        simulateQ
            (QueryImpl.add outerInputImpl innerOutputImpl)
            (access.simulateOut pt q) =
          pure (outerOutputImpl q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add outerInputImpl msgImpl)
          (pullbackSimulate
            (access := access)
            pt
            msgSpec
            simulateInner
            q) =
        pure (outerOutputImpl q) := by
  intro q
  dsimp [pullbackSimulate]
  calc
    simulateQ
        (QueryImpl.add outerInputImpl msgImpl)
        (simulateQ
          (fun
            | .inl qIn =>
                liftM <| ([OuterOStmtIn]ₒ).query qIn
            | .inr qOut =>
                routeInnerOutputQueries
                  (access := access)
                  (pt := pt)
                  msgSpec
                  simulateInner
                  qOut)
          (access.simulateOut pt q)) =
      simulateQ
        (fun q =>
          simulateQ
            (QueryImpl.add outerInputImpl msgImpl)
            (match q with
            | .inl qIn =>
                liftM <| ([OuterOStmtIn]ₒ).query qIn
            | .inr qOut =>
                routeInnerOutputQueries
                  (access := access)
                  (pt := pt)
                  msgSpec
                  simulateInner
                  qOut))
        (access.simulateOut pt q) := by
        rw [simulateQ_compose]
    _ =
      simulateQ
        (QueryImpl.add outerInputImpl innerOutputImpl)
        (access.simulateOut pt q) := by
          apply simulateQ_ext
          intro q'
          cases q' with
          | inl qIn =>
              calc
                simulateQ
                    (QueryImpl.add outerInputImpl msgImpl)
                    (OracleComp.liftComp
                      (liftM (([OuterOStmtIn]ₒ).query qIn) :
                        OracleComp [OuterOStmtIn]ₒ _)
                      ([OuterOStmtIn]ₒ + msgSpec)) =
                  simulateQ outerInputImpl
                    (liftM (([OuterOStmtIn]ₒ).query qIn) :
                      OracleComp [OuterOStmtIn]ₒ _) := by
                      simpa using
                        simulateQ_add_liftComp_left
                          outerInputImpl
                          msgImpl
                          (liftM (([OuterOStmtIn]ₒ).query qIn) :
                            OracleComp [OuterOStmtIn]ₒ _)
                _ = outerInputImpl qIn := by
                  simp [simulateQ_query]
          | inr qOut =>
              simpa [QueryImpl.add] using
                routeInnerOutputQueries_eval
                  (access := access)
                  (pt := pt)
                  msgSpec
                  outerInputImpl
                  innerInputImpl
                  msgImpl
                  innerOutputImpl
                  simulateInner
                  hInput
                  hInner
                  qOut
    _ = pure (outerOutputImpl q) :=
      hOuter q

end OracleStatementAccess

/-! ## Counterpart verifier pullback -/

/-- Rewire every receiver-node input-oracle query in a verifier counterpart
through `simulateIn`, while applying an output map `f`. -/
def pullbackCounterpart
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (spec : Interaction.Oracle.Spec)
    (roles : Interaction.Oracle.Spec.RoleDeco spec)
    (od : Interaction.Oracle.Spec.OracleDeco spec)
    {Output₁ Output₂ : Interaction.Spec.Transcript spec.toInteractionSpec → Type}
    (f : ∀ tr, Output₁ tr → Output₂ tr)
    {ιₐ : Type}
    (accSpec : OracleSpec ιₐ)
    (cpt :
      Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
        spec.toInteractionSpec
        (RoleDecoration.withMonads (spec.toSpecRoles roles)
          (spec.toMonadDecoration oSpec InnerOStmtIn roles od accSpec))
        Output₁) :
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      spec.toInteractionSpec
      (RoleDecoration.withMonads (spec.toSpecRoles roles)
        (spec.toMonadDecoration oSpec OuterOStmtIn roles od accSpec))
      Output₂ :=
  match spec, roles, od with
  | .done, _, _ =>
      f ⟨⟩ cpt
  | .public _ rest, ⟨.sender, rRest⟩, odRest =>
      fun x =>
        pullbackCounterpart
          (simulateIn := simulateIn)
          (rest x)
          (rRest x)
          (odRest x)
          (fun tr out => f ⟨x, tr⟩ out)
          accSpec
          (cpt x)
  | .public _ rest, ⟨.receiver, rRest⟩, odRest =>
      simulateQ
        (OracleStatementAccess.routeInputQueries
          (oSpec := oSpec)
          simulateIn
          accSpec) <| do
        let ⟨x, cptRest⟩ ← cpt
        pure ⟨x,
          pullbackCounterpart
            (simulateIn := simulateIn)
            (rest x)
            (rRest x)
            (odRest x)
            (fun tr out => f ⟨x, tr⟩ out)
            accSpec
            cptRest⟩
  | .«oracle» _ cont, roles, ⟨oi, odRest⟩ =>
      fun x =>
        pullbackCounterpart
          (simulateIn := simulateIn)
          (cont ⟨⟩)
          roles
          odRest
          (fun tr out => f ⟨x, tr⟩ out)
          (accSpec + @OracleInterface.spec _ oi)
          (cpt x)

end Boundary

namespace Oracle
namespace Verifier

/-- Reinterpret an inner oracle verifier through a statement boundary and oracle
access layer. The shared input is projected; local statements are `PUnit`. -/
def pullback
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
    (toStatement :
      Boundary.OracleStatementLift projection InnerStmtOut OuterStmtOut)
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
    (access :
      (outer : OuterStmtIn) →
        Boundary.OracleStatementAccess
          (InnerContext := InnerContext (projection.proj outer))
          (OuterOStmtIn outer)
          (InnerOStmtIn (projection.proj outer))
          (InnerOStmtOut (projection.proj outer))
          (OuterOStmtOut outer))
    (verifier :
      Interaction.Oracle.Verifier oSpec
        InnerStmtIn InnerContext InnerRoles InnerOracleDeco
        (fun _ => PUnit) InnerOStmtIn InnerStmtOut InnerOStmtOut) :
    Interaction.Oracle.Verifier oSpec
      OuterStmtIn
      (fun outer => InnerContext (projection.proj outer))
      (fun outer => InnerRoles (projection.proj outer))
      (fun outer => InnerOracleDeco (projection.proj outer))
      (fun _ => PUnit)
      OuterOStmtIn
      OuterStmtOut
      OuterOStmtOut where
  toFun outer _ :=
    Boundary.pullbackCounterpart
      (access outer).simulateIn
      (InnerContext (projection.proj outer))
      (InnerRoles (projection.proj outer))
      (InnerOracleDeco (projection.proj outer))
      (fun tr stmtOut =>
        toStatement.lift outer
          ((InnerContext (projection.proj outer)).projectPublic tr)
          stmtOut)
      []ₒ
      (verifier.toFun (projection.proj outer) PUnit.unit)
  simulate outer pt :=
    Boundary.OracleStatementAccess.pullbackSimulate
      (access := access outer)
      pt
      ((InnerContext (projection.proj outer)).toOracleSpec
        (InnerOracleDeco (projection.proj outer))
        pt)
      (verifier.simulate (projection.proj outer) pt)

end Verifier
end Oracle

end Interaction


import ArkLib.Interaction.Reduction

open Interaction.TwoParty

/-!
# Interaction-Native Boundaries: Core Layer

A *boundary* reinterprets an existing interaction through a different outer
statement/witness interface without changing the underlying transcript or round
structure. This is distinct from sequential composition (`Spec.append`,
`Reduction.comp`), which extends a protocol by appending new rounds.

## When to use a boundary vs. composition

A boundary is the right tool when:
- the `Spec`, transcript shape, and round structure are *unchanged*;
- you want to reinterpret the protocol at a different outer statement or witness;
- you are *not* appending more rounds.

Use composition when the protocol itself grows. Use a boundary when only the
interface changes. See `INTERACTION_BOUNDARIES.md` for detailed rationale and
examples (sumcheck single-round reuse, FRIBinius witness reinterpretation,
BatchedFRI batching boundary).

## Three structures, one idea

`Statement` carries the statement-level boundary data:
- `proj` maps the outer input statement to the inner one;
- `StmtOut` defines the outer output statement type;
- `lift` produces an outer output statement from an inner one.

`WitnessProjection` carries the input-witness projection.

`Witness` then adds the output-witness lifting half over a fixed witness
projection:
- `proj` maps the outer witness to the inner one;
- `lift` reconstructs the outer output witness.

`Context` bundles both into a single record.

## Pullback

Given a boundary `b` and an inner protocol participant (verifier, prover, or
reduction), `pullback b` produces an outer participant that:
1. projects its input through `b`,
2. runs the inner participant on the projected input,
3. lifts the inner output back through `b`.

The transcript is unchanged throughout. For verifier-only pullbacks, a
`Statement` boundary suffices. For prover or full reduction pullbacks, a
`Context` boundary is needed. At the oracle level, additional simulation /
materialization data is required — see `Boundary.Oracle` and
`Boundary.Reification`.

## See also

- `Boundary.Oracle` — adds verifier-side oracle simulation
- `Boundary.Reification` — adds concrete oracle materialization for provers
- `Boundary.Compatibility` — soundness/completeness predicates for boundaries
- `Boundary.Security` / `Boundary.OracleSecurity` — security transport theorems
-/

namespace Interaction
namespace Boundary

/-- The projection half of a statement boundary. -/
structure StatementProjection
    (OuterStmtIn InnerStmtIn : Type)
    (InnerSpec : InnerStmtIn → Spec) where
  proj : OuterStmtIn → InnerStmtIn

namespace StatementProjection

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}

/-- The outer protocol spec induced by a statement projection. -/
@[inline] abbrev spec
    (projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec) :
    OuterStmtIn → Spec :=
  fun outer => InnerSpec (projection.proj outer)

/-- Identity statement projection. -/
@[inline, reducible] def id
    (StmtIn : Type)
    (InnerSpec : StmtIn → Spec) :
    StatementProjection StmtIn StmtIn InnerSpec where
  proj := fun stmt => stmt

end StatementProjection

/-- The lifting half of a statement boundary over a fixed statement projection
and an explicit outer output statement family. -/
structure Statement
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    (projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec)
    (InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type)
    (OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type) where
  lift :
    (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      InnerStmtOut (projection.proj outer) tr →
      OuterStmtOut outer tr

namespace Statement

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}

/-- The input projection underlying a statement lifting. -/
@[inline] abbrev proj
    (_ : Statement projection InnerStmtOut OuterStmtOut) :
    OuterStmtIn → InnerStmtIn :=
  projection.proj

/-- The outer output family underlying a statement lifting. -/
@[inline] abbrev StmtOut
    (_ : Statement projection InnerStmtOut OuterStmtOut) :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerSpec (projection.proj outer)) → Type :=
  OuterStmtOut

/-- Identity statement boundary. -/
@[inline, reducible] def id
    (StmtIn : Type)
    (InnerSpec : StmtIn → Spec)
    (StmtOut : (s : StmtIn) → Spec.Transcript (InnerSpec s) → Type) :
    Statement
      (StatementProjection.id StmtIn InnerSpec)
      StmtOut
      StmtOut where
  lift := fun _ _ stmtOut => stmtOut

/-- Boundary that only changes the input statement; the output is passed through
unchanged. -/
@[inline] def ofInputOnly
    (projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec) :
    Statement
      projection
      InnerStmtOut
      (fun outer tr => InnerStmtOut (projection.proj outer) tr) where
  lift := fun _ _ stmtOut => stmtOut

/-- Boundary that only changes the output statement; the input is passed through
unchanged. -/
@[inline] def ofOutputOnly
    (StmtIn : Type)
    (InnerSpec : StmtIn → Spec)
    (InnerStmtOut OuterStmtOut :
      (s : StmtIn) → Spec.Transcript (InnerSpec s) → Type)
    (lift :
      (s : StmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      InnerStmtOut s tr →
      OuterStmtOut s tr) :
    Statement
      (StatementProjection.id StmtIn InnerSpec)
      InnerStmtOut
      OuterStmtOut where
  lift := lift

end Statement

/-- The projection half of a witness boundary. -/
structure WitnessProjection
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    (projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec)
    (OuterWitIn InnerWitIn : Type) where
  proj : (outer : OuterStmtIn) → OuterWitIn → InnerWitIn

namespace WitnessProjection

variable
    {StmtIn : Type}
    {WitIn : Type}
    {InnerSpec : StmtIn → Spec}

/-- Identity witness projection. -/
@[inline, reducible] def id :
    WitnessProjection
      (StatementProjection.id StmtIn InnerSpec)
      WitIn
      WitIn where
  proj := fun _ wit => wit

end WitnessProjection

/-- The lifting half of a witness boundary over a fixed witness projection and
an explicit outer output-witness family. -/
structure Witness
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {OuterWitIn InnerWitIn : Type}
    (witnessProjection : WitnessProjection projection OuterWitIn InnerWitIn)
    (InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type)
    (InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type)
    (OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type) where
  lift :
    (outer : OuterStmtIn) →
      OuterWitIn →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      InnerStmtOut (projection.proj outer) tr →
      InnerWitOut (projection.proj outer) tr →
      OuterWitOut outer tr

namespace Witness

variable
    {StmtIn : Type}
    {InnerSpec : StmtIn → Spec}
    {StmtOut : (s : StmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {WitIn : Type}
    {WitOutTy : (s : StmtIn) → Spec.Transcript (InnerSpec s) → Type}

/-- The input witness projection underlying a witness lifting. -/
@[inline] abbrev proj
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {OuterWitIn InnerWitIn : Type}
    {witnessProjection : WitnessProjection projection OuterWitIn InnerWitIn}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (_ : Witness witnessProjection InnerStmtOut InnerWitOut OuterWitOut) :
    (outer : OuterStmtIn) → OuterWitIn → InnerWitIn :=
  witnessProjection.proj

/-- The outer output witness family underlying a witness lifting. -/
@[inline] abbrev WitOut
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {OuterWitIn InnerWitIn : Type}
    {witnessProjection : WitnessProjection projection OuterWitIn InnerWitIn}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (_ : Witness witnessProjection InnerStmtOut InnerWitOut OuterWitOut) :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerSpec (projection.proj outer)) → Type :=
  OuterWitOut

/-- Identity witness boundary over the identity statement boundary. -/
@[inline, reducible] def id :
    Witness
      (WitnessProjection.id
        (StmtIn := StmtIn)
        (WitIn := WitIn)
        (InnerSpec := InnerSpec))
      StmtOut
      WitOutTy
      WitOutTy where
  lift := fun _ _ _ _ witOut => witOut

/-- Witness boundary that only changes the input witness; the output witness is
passed through unchanged. -/
@[inline] def ofInputOnly
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {OuterWitIn InnerWitIn : Type}
    (witnessProjection : WitnessProjection projection OuterWitIn InnerWitIn)
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    :
    Witness
      witnessProjection
      InnerStmtOut
      InnerWitOut
      (fun outer tr => InnerWitOut (projection.proj outer) tr) where
  lift := fun _ _ _ _ witOut => witOut

end Witness

/-- A full plain boundary bundling statement and witness transport.

Use `Context` when constructing a prover or full reduction pullback.
For verifier-only pullbacks, a `Statement` lifting suffices. -/
structure Context
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    (projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec)
    (OuterWitIn InnerWitIn : Type)
    (InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type)
    (OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type)
    (InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type)
    (OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type) where
  witProj : WitnessProjection projection OuterWitIn InnerWitIn
  stmt : Statement projection InnerStmtOut OuterStmtOut
  wit : Witness witProj InnerStmtOut InnerWitOut OuterWitOut

namespace Context

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {OuterWitIn InnerWitIn : Type}
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

/-- The outer output statement type, delegated to the context parameters. -/
@[inline] abbrev StmtOut
    (_ : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut) :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerSpec (projection.proj outer)) → Type :=
  OuterStmtOut

/-- The outer output witness type, delegated to the context parameters. -/
@[inline] abbrev WitOut
    (_ : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut) :
    (outer : OuterStmtIn) →
      Spec.Transcript (InnerSpec (projection.proj outer)) → Type :=
  OuterWitOut

/-- Project an outer `(stmt, wit)` pair to an inner `(stmt, wit)` pair. -/
@[inline] def proj
    (boundary : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn :=
  fun ⟨outerStmt, outerWit⟩ =>
    ⟨projection.proj outerStmt, boundary.wit.proj outerStmt outerWit⟩

/-- Lift inner outputs back to outer outputs, returning both statement and
witness components. -/
@[inline] def lift
    (boundary : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut)
    (outerStmt : OuterStmtIn) (outerWit : OuterWitIn)
    (tr : Spec.Transcript (InnerSpec (projection.proj outerStmt)))
    (stmtOut : InnerStmtOut (projection.proj outerStmt) tr)
    (witOut : InnerWitOut (projection.proj outerStmt) tr) :
    boundary.StmtOut outerStmt tr × boundary.WitOut outerStmt tr :=
  ⟨boundary.stmt.lift outerStmt tr stmtOut,
    boundary.wit.lift outerStmt outerWit tr stmtOut witOut⟩

/-- Identity context boundary. -/
@[inline, reducible] def id
    (StmtIn : Type)
    (WitIn : Type)
    (InnerSpec : StmtIn → Spec)
    (StmtOut WitOut :
      (s : StmtIn) → Spec.Transcript (InnerSpec s) → Type) :
    Context
      (StatementProjection.id StmtIn InnerSpec)
      WitIn WitIn
      StmtOut StmtOut
      WitOut WitOut where
  stmt := Statement.id StmtIn InnerSpec StmtOut
  witProj := WitnessProjection.id
  wit := Witness.id

/-- Context boundary that only changes the input statement and witness. -/
@[inline] def ofInputOnly
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    (projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec)
    (witProj :
      (outer : OuterStmtIn) →
      OuterWitIn →
      InnerWitIn) :
    Context
      projection
      OuterWitIn InnerWitIn
      InnerStmtOut
      (fun outer tr => InnerStmtOut (projection.proj outer) tr)
      InnerWitOut
      (fun outer tr => InnerWitOut (projection.proj outer) tr) where
  witProj := { proj := witProj }
  stmt := Statement.ofInputOnly projection
  wit := Witness.ofInputOnly
    (projection := projection)
    (witnessProjection := { proj := witProj })

end Context

namespace Verifier

/-- Reinterpret an inner verifier through an outer statement boundary. -/
def pullback {m : Type _ → Type _} [Functor m]
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
    (verifier : Verifier m InnerStmtIn InnerSpec InnerRoles (fun _ => PUnit) InnerStmtOut) :
    Verifier m OuterStmtIn
      (StatementProjection.spec projection)
      (fun outer => InnerRoles (projection.proj outer))
      (fun _ => PUnit)
      OuterStmtOut :=
  fun outer _ =>
    TwoParty.Counterpart.mapOutput
      (fun tr stmtOut => boundary.lift outer tr stmtOut)
      (verifier (projection.proj outer) PUnit.unit)

end Verifier

namespace Prover

/-- Reinterpret an inner prover through a full context boundary. -/
def pullback {m : Type _ → Type _} [Monad m]
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {OuterWitIn InnerWitIn : Type}
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
    (boundary : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut)
    (prover : Prover m InnerStmtIn InnerSpec InnerRoles
      (fun _ => PUnit) (fun _ => InnerWitIn) InnerStmtOut InnerWitOut) :
    Prover m OuterStmtIn
      (StatementProjection.spec projection)
      (fun outer => InnerRoles (projection.proj outer))
      (fun _ => PUnit) (fun _ => OuterWitIn)
      OuterStmtOut
      OuterWitOut :=
  fun outerStmt _ outerWit => do
    let strat ← prover
      (projection.proj outerStmt)
      PUnit.unit
      (boundary.wit.proj outerStmt outerWit)
    pure <| TwoParty.Focal.mapOutput
      (fun tr out =>
        boundary.lift outerStmt outerWit tr out.stmt out.wit)
      strat

end Prover

namespace Reduction

/-- Reinterpret an inner reduction through a full context boundary. -/
def pullback {m : Type _ → Type _} [Monad m] [Functor m]
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {OuterWitIn InnerWitIn : Type}
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
    (boundary : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut)
    (reduction : Reduction m InnerStmtIn InnerSpec InnerRoles
      (fun _ => PUnit) (fun _ => InnerWitIn) InnerStmtOut InnerWitOut) :
    Reduction m OuterStmtIn
      (StatementProjection.spec projection)
      (fun outer => InnerRoles (projection.proj outer))
      (fun _ => PUnit) (fun _ => OuterWitIn)
      OuterStmtOut
      OuterWitOut where
  prover := Prover.pullback boundary reduction.prover
  verifier := Verifier.pullback boundary.stmt reduction.verifier

end Reduction

end Boundary
end Interaction


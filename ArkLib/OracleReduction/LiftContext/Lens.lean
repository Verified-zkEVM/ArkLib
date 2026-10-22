/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import PolyFun.PFunctor.Lens.Basic

/-!
  ## Lens between Input and Output Contexts of (Oracle) Reductions

  This file defines the different lenses required for the transformation / lifting of context for an
  (oracle) reduction, and the properties required for the transformation / lift to be complete /
  sound / knowledge sound (including an extra lens for the transformation / lifting of the
  extractor).

  We also define simpler examples of lenses, when we don't need the full generality. For instance,
  lenses where we have (only) an equivalence between the statements / witnesses, or lenses where the
  witnesses are trivial.
-/

@[expose] public section

open OracleSpec OracleComp PFunctor

/-- A lens for transporting input and output statements for the verifier of a (non-oracle)
    reduction.

  Consists of two functions:
  - `proj : OuterStmtIn → InnerStmtIn` : Transport input statements from the outer context to
    the inner context
  - `lift : OuterStmtIn → InnerStmtOut → OuterStmtOut` : Transport output statements from the
    inner context to the outer context, additionally relying on the outer input statement.

  This is exactly the same as a `PFunctor.Lens` between two monomials defined by the input and
  output statements (from the outer to the inner context).
-/
@[inline, reducible]
def Statement.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type) :=
  PFunctor.Lens (OuterStmtIn X^ OuterStmtOut) (InnerStmtIn X^ InnerStmtOut)

namespace Statement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)

/-- Transport input statements from the outer context to the inner context -/
@[inline, reducible]
def proj : OuterStmtIn → InnerStmtIn :=
  lens.toFunA

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def lift : OuterStmtIn → InnerStmtOut → OuterStmtOut :=
  lens.toFunB

end Statement.Lens

/-- A lens for transporting input and output statements (both oracle and non-oracle) for the
  oracle verifier of an oracle reduction.

  TODO: figure out the right way to define this -/
@[inline, reducible]
def OracleStatement.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
    [∀ i, OracleInterface (InnerOStmtOut i)] :=
    Statement.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
                  (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
  -- TODO: fill in the extra conditions
  /- For a legacy embedded output, the lens must preserve the embedding into the input oracle
  statements and prover messages. Derived virtual outputs instead use `ExecutableLens`, which
  transports their query implementation and materialization-agreement proof.

  We also need to provide a `QueryImpl` instance for simulating the outer oracle verifier using
  the inner oracle verifier.
  -/

  -- simulateOutputQuery : QueryImpl [InnerOStmtIn]ₒ
  --   (ReaderT OuterStmtIn (OracleComp [OuterOStmtIn]ₒ))

  -- simOStmt_neverFails : ∀ i, ∀ t, ∀ outerStmtIn,
  --   ((simulateOutputQuery.impl (query i t)).run outerStmtIn).neverFails
  -- To get back an output oracle statement in the outer context, we may simulate it using the input
  -- (non-oracle) statement of the outer context, the output (non-oracle) statement of the inner
  -- context, along with oracle access to the inner output oracle statements

  -- liftOStmt : QueryImpl [OuterOStmtOut]ₒ
  --   (ReaderT (OuterStmtIn × InnerStmtOut) (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut]ₒ)))
  -- liftOStmt_neverFails : ∀ i, ∀ t, ∀ outerStmtIn, ∀ innerStmtOut,
  --   ((liftOStmt.impl (query i t)).run (outerStmtIn, innerStmtOut)).neverFails

namespace OracleStatement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
/-- Transport input statements from the outer context to the inner context

TODO: refactor etc. -/
@[inline, reducible]
def proj : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn × (∀ i, InnerOStmtIn i) :=
  lens.toFunA

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context.

  TODO: refactor etc. -/
@[inline, reducible]
def lift : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
    OuterStmtOut × (∀ i, OuterOStmtOut i) :=
  lens.toFunB

-- def toVerifierLens : Statement.Lens
--     (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
--     (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
--   := oStmtLens

end OracleStatement.Lens

/-! ### Executable oracle-statement lenses

The extensional `OracleStatement.Lens` above is sufficient for relation-level
reasoning, but it cannot by itself implement an oracle verifier: an arbitrary
function on whole oracle values need not be realizable by queries.  The
following structure records the query implementations and their pointwise
agreement with materialized oracle values. -/

/-- A query-realizable lens between oracle statements.

Input-oracle projection may depend on the explicit outer input statement.
Output-oracle lifting is deliberately statement-independent: this is the
condition needed for output-oracle simulations to remain composable without
materializing intermediate verifier statements. -/
structure OracleStatement.ExecutableLens
    (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type)
    [OuterOᵢ : ∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type)
    [OuterOₒ : ∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type)
    [InnerOᵢ : ∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
    [InnerOₒ : ∀ i, OracleInterface (InnerOStmtOut i)] where
  /-- Project the explicit input statement. -/
  projStmt : OuterStmtIn → InnerStmtIn
  /-- Materialized input-oracle projection, used by relation-facing semantics. -/
  materializeInput : OuterStmtIn →
    (∀ i, OuterOStmtIn i) → ∀ i, InnerOStmtIn i
  /-- Query-by-query implementation of the input-oracle projection. -/
  simulateInput : OuterStmtIn →
    QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)
  /-- The input query implementation agrees with the materialized projection. -/
  simulateInput_eq : ∀ outerStmt outerOStmt q,
    simulateQ (OracleInterface.simOracle0 OuterOStmtIn outerOStmt)
        (simulateInput outerStmt q) =
      (InnerOᵢ q.1).answer (materializeInput outerStmt outerOStmt q.1) q.2
  /-- Lift the explicit output statement. -/
  liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut
  /-- Materialized output-oracle lift, used by relation-facing semantics. -/
  materializeOutput : (∀ i, OuterOStmtIn i) →
    (∀ i, InnerOStmtOut i) → ∀ i, OuterOStmtOut i
  /-- Query-by-query implementation of the output-oracle lift. -/
  simulateOutput :
    QueryImpl [OuterOStmtOut]ₒ (OracleComp ([OuterOStmtIn]ₒ + [InnerOStmtOut]ₒ))
  /-- The output query implementation agrees with the materialized lift. -/
  simulateOutput_eq : ∀ outerOStmt innerOStmt q,
    simulateQ
        (QueryImpl.add (OracleInterface.simOracle0 OuterOStmtIn outerOStmt)
          (OracleInterface.simOracle0 InnerOStmtOut innerOStmt))
        (simulateOutput q) =
      (OuterOₒ q.1).answer (materializeOutput outerOStmt innerOStmt q.1) q.2

namespace OracleStatement.ExecutableLens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
    [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
    [∀ i, OracleInterface (InnerOStmtOut i)]

/-- Forget query implementations and retain the extensional statement lens. -/
@[reducible]
def toLens (lens : OracleStatement.ExecutableLens
    OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut where
  toFunA := fun ⟨stmt, oStmt⟩ ↦
    ⟨lens.projStmt stmt, lens.materializeInput stmt oStmt⟩
  toFunB := fun ⟨stmt, oStmt⟩ ⟨stmtOut, oStmtOut⟩ ↦
    ⟨lens.liftStmt stmt stmtOut, lens.materializeOutput oStmt oStmtOut⟩

end OracleStatement.ExecutableLens

/-- Lenses for transporting the input & output witnesses from an inner protocol to an outer
    protocol.

  It consists of two functions:
  - `projWit : OuterStmtIn × OuterWitIn → InnerWitIn`, which derives the inner input witness from
    the outer one, requiring also the outer input statement.
  - `liftWit : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut`, which
    derives the outer output witness from outer input witness & the inner output one, requiring
    also the associated statements.

  The inclusion of the statements are necessary when we consider the full view of the prover. In
  practice as well, oftentimes a lens between only witnesses are not enough. -/
@[inline, reducible]
def Witness.Lens
    (OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  PFunctor.Lens ((OuterStmtIn × OuterWitIn) X^ OuterWitOut)
    (InnerWitIn X^ (InnerStmtOut × InnerWitOut))

namespace Witness.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
/-- Transport input witness from the outer context to the inner context -/
@[inline, reducible]
def proj : OuterStmtIn × OuterWitIn → InnerWitIn :=
  lens.toFunA

/-- Transport output witness from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def lift : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut :=
  lens.toFunB

end Witness.Lens

/-- A structure collecting a lens for the prover, and a lens for the verifier, for transporting
  between the contexts of an outer reduction and an inner reduction. -/
structure Context.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  wit : Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace Context.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Projection of the context. -/
@[inline, reducible]
def proj : OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn :=
  fun ctxIn => ⟨lens.stmt.toFunA ctxIn.1, lens.wit.toFunA ctxIn⟩

/-- Lifting of the context. -/
@[inline, reducible]
def lift : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterStmtOut × OuterWitOut :=
  fun ctxIn ctxOut =>
    ⟨lens.stmt.toFunB ctxIn.1 ctxOut.1, lens.wit.toFunB ctxIn ctxOut⟩

end Context.Lens

/-- A structure collecting a lens for the prover, and a lens for the oracle verifier, for
  transporting between the contexts of an outer oracle reduction and an inner oracle reduction. -/
structure OracleContext.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                  OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  wit : Witness.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleContext.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
/-- Projection of the context. -/
@[inline, reducible]
def proj : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn :=
  fun ctxIn => ⟨lens.stmt.proj ctxIn.1, lens.wit.proj ctxIn⟩

/-- Lifting of the context. -/
@[inline, reducible]
def lift : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut →
    (OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut :=
  fun ctxIn ctxOut => ⟨lens.stmt.lift ctxIn.1 ctxOut.1, lens.wit.lift ctxIn ctxOut⟩

/-- Convert the oracle context lens to a context lens. -/
@[inline, reducible]
def toContext :
    Context.Lens (OuterStmtIn × (∀ i, OuterOStmtIn i)) (OuterStmtOut × (∀ i, OuterOStmtOut i))
                (InnerStmtIn × (∀ i, InnerOStmtIn i)) (InnerStmtOut × (∀ i, InnerOStmtOut i))
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut :=
  ⟨lens.stmt, lens.wit⟩

end OracleContext.Lens

/-- An oracle-context lens whose statement component is executable by
querying, together with the ordinary witness lens used by the prover. -/
structure OracleContext.ExecutableLens
    (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type)
    [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type)
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
    [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : OracleStatement.ExecutableLens
    OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  wit : Witness.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i)
    (InnerStmtOut × ∀ i, InnerOStmtOut i)
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleContext.ExecutableLens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
    [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
    [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

/-- Forget the executable implementations and retain the extensional oracle
context lens. -/
@[reducible]
def toLens (lens : OracleContext.ExecutableLens
    OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut where
  stmt := lens.stmt.toLens
  wit := lens.wit

end OracleContext.ExecutableLens

/-- Lens for lifting the witness extraction procedure from the inner reduction to the outer
  reduction.

This goes in the reverse direction (output to input) compared to the witness lens for the prover,
and requires in addition the outer input statement.
-/
@[inline, reducible]
def Witness.InvLens (OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  PFunctor.Lens ((OuterStmtIn × OuterWitOut) X^ OuterWitIn) (InnerWitOut X^ InnerWitIn)

namespace Witness.InvLens

variable {OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
  (lens : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Projection of the witness. -/
@[inline, reducible]
def proj : OuterStmtIn × OuterWitOut → InnerWitOut :=
  lens.toFunA

/-- Lifting of the witness. -/
@[inline, reducible]
def lift : OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn :=
  lens.toFunB

end Witness.InvLens

/-- Lens for lifting the extractor from the inner reduction to the outer reduction.

This consists of two components:
- `stmt` : the statement lens
- `wit` : the witness lens in the reverse direction, matching the input-output interface of the
  extractor, i.e. `StmtIn × WitOut → WitIn` (ignoring transcript and query logs)
-/
@[ext]
structure Extractor.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  stmt : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
  wit : Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace Extractor.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- Transport the tuple of (input statement, output witness) from the outer context to the inner
  context -/
@[inline, reducible]
def proj (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitOut → InnerStmtIn × InnerWitOut :=
  fun ⟨stmtIn, witOut⟩ => ⟨lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witOut)⟩

-- /-- Transport the inner input witness to the outer input witness, also relying on the tuple
-- (outer--   input statement, outer output witness) -/
-- @[inline, reducible]
-- def lift (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
--               OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
--     OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn :=
--   fun ⟨stmtIn, witOut⟩ innerWitIn =>
--     lens.wit.lift (stmtIn, witOut) innerWitIn

end Extractor.Lens

/-- Conditions for the lens / transformation to preserve completeness

For `lift`, we require compatibility relations between the outer input statement/witness and
the inner output statement/witness -/
class Context.Lens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compat : (OuterStmtIn × OuterWitIn) → (InnerStmtOut × InnerWitOut) → Prop)
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  proj_complete : ∀ stmtIn witIn,
    (stmtIn, witIn) ∈ outerRelIn →
    (lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witIn)) ∈ innerRelIn

  lift_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    compat (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) →
    (outerStmtIn, outerWitIn) ∈ outerRelIn →
    (innerStmtOut, innerWitOut) ∈ innerRelOut →
    (lens.stmt.lift outerStmtIn innerStmtOut,
    lens.wit.lift (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut)) ∈ outerRelOut

/-- The completeness condition for the oracle context lens is just the one for the underlying
  context lens -/
@[reducible, simp]
def OracleContext.Lens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set ((OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn))
    (innerRelIn : Set ((InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn))
    (outerRelOut : Set ((OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut))
    (innerRelOut : Set ((InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut))
    (compat : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
              (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut → Prop)
    (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :=
  Context.Lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut compat lens.toContext

/-- Conditions for the lens / transformation to preserve soundness -/
class Statement.Lens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn

  lift_sound : ∀ outerStmtIn innerStmtOut,
    compatStmt outerStmtIn innerStmtOut →
    innerStmtOut ∉ innerLangOut →
    lens.lift outerStmtIn innerStmtOut ∉ outerLangOut

/-- The soundness condition for the oracle statement lens is just the one for the underlying
  statement lens -/
@[reducible, simp]
def OracleStatement.Lens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (outerLangIn : Set (OuterStmtIn × (∀ i, OuterOStmtIn i)))
    (outerLangOut : Set (OuterStmtOut × (∀ i, OuterOStmtOut i)))
    (innerLangIn : Set (InnerStmtIn × (∀ i, InnerOStmtIn i)))
    (innerLangOut : Set (InnerStmtOut × (∀ i, InnerOStmtOut i)))
    (compatStmt :
      OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) → Prop)
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :=
  Statement.Lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut compatStmt lens

section StatementLensCompleteness

/-! ### Language-level completeness for a statement lens

`Statement.Lens.IsSound.proj_sound` says `outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉
innerLangIn`, which is the containment `lens.proj ⁻¹' innerLangIn ⊆ outerLangIn`.  The converse
containment `outerLangIn ⊆ lens.proj ⁻¹' innerLangIn` is not available anywhere in the API at the
*language* level: `Context.Lens.IsComplete.proj_complete` has the right shape but is stated at the
*relation* level (`Set (Stmt × Wit)`), so it cannot discharge a `Set Stmt` obligation.

The class below supplies exactly that missing containment.  Taken together the two conditions say

  `outerLangIn = lens.proj ⁻¹' innerLangIn`

(`Statement.Lens.eq_preimage_of_projSound_of_isComplete`): the outer language is the *pullback* of
the inner language along `proj`.  That is why `Verifier.StateFunction.liftContext`'s `toFun_empty`
— a biconditional — needs both classes: it is that set equation read pointwise
(`Statement.Lens.mem_iff_proj_mem`).

The two classes are *independent*: neither implies the other
(`Statement.Lens.isSound_not_implies_isComplete`, `Statement.Lens.isComplete_not_implies_isSound`).
-/

/-- Conditions for the statement lens to preserve language membership under projection.

This is the language-level analogue of `Context.Lens.IsComplete.proj_complete` (which is stated at
the relation level), and the converse direction to `Statement.Lens.IsSound.proj_sound`. -/
class Statement.Lens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (innerLangIn : Set InnerStmtIn)
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_complete : ∀ outerStmtIn,
    outerStmtIn ∈ outerLangIn → lens.proj outerStmtIn ∈ innerLangIn

namespace Statement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {outerLangIn : Set OuterStmtIn} {innerLangIn : Set InnerStmtIn}
    {lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}

/-- Completeness restated as a containment: the outer language sits inside the preimage. -/
theorem IsComplete.subset_preimage [h : IsComplete outerLangIn innerLangIn lens] :
    outerLangIn ⊆ lens.proj ⁻¹' innerLangIn :=
  fun s hs => h.proj_complete s hs

/-- Completeness built from the containment. -/
def IsComplete.ofSubsetPreimage (h : outerLangIn ⊆ lens.proj ⁻¹' innerLangIn) :
    IsComplete outerLangIn innerLangIn lens :=
  ⟨fun s hs => h hs⟩

/-- **The single classical step in the lifting layer.**  `proj_sound` is stated in negated form
(`∉ → ∉`), because soundness is naturally about statements *outside* the language.  Recovering the
positive containment `lens.proj ⁻¹' innerLangIn ⊆ outerLangIn` from it is a contraposition, which
constructively yields only `¬¬(· ∈ outerLangIn)`; the elimination needs classical logic (or
decidability of `outerLangIn`).

Isolating it in this one lemma keeps the classical content of `Verifier.StateFunction.liftContext`
auditable: every other lemma here is choice-free. -/
theorem preimage_subset_of_projSound
    (hSound : ∀ outerStmtIn, outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn) :
    lens.proj ⁻¹' innerLangIn ⊆ outerLangIn := by
  intro s hs
  by_contra hc
  exact hSound s hc hs

/-- **Soundness and completeness are one equation.**  Together, `proj_sound` and `proj_complete`
say precisely that the outer input language is the preimage of the inner input language along
`proj` — i.e. the language pair is a pullback square over the lens. -/
theorem eq_preimage_of_projSound_of_isComplete
    (hSound : ∀ outerStmtIn, outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn)
    [IsComplete outerLangIn innerLangIn lens] :
    outerLangIn = lens.proj ⁻¹' innerLangIn :=
  Set.Subset.antisymm IsComplete.subset_preimage (preimage_subset_of_projSound hSound)

/-- Conversely, the pullback equation supplies both conditions.  With the previous lemma this is a
complete characterisation: `proj_sound ∧ proj_complete ↔ outerLangIn = lens.proj ⁻¹' innerLangIn`. -/
theorem projSound_and_isComplete_of_eq_preimage
    (h : outerLangIn = lens.proj ⁻¹' innerLangIn) :
    (∀ outerStmtIn, outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn) ∧
      IsComplete outerLangIn innerLangIn lens :=
  ⟨fun s hs hmem => hs (h ▸ hmem), IsComplete.ofSubsetPreimage (h ▸ subset_rfl)⟩

/-- The pointwise form of the pullback equation.  This is exactly the shape consumed by
`Verifier.StateFunction.liftContext`'s `toFun_empty`, which is a biconditional. -/
theorem mem_iff_proj_mem
    (hSound : ∀ outerStmtIn, outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn)
    [hC : IsComplete outerLangIn innerLangIn lens] (outerStmtIn : OuterStmtIn) :
    outerStmtIn ∈ outerLangIn ↔ lens.proj outerStmtIn ∈ innerLangIn :=
  ⟨hC.proj_complete outerStmtIn, fun h => preimage_subset_of_projSound hSound h⟩

/-- Failure of completeness is exactly failure of the containment. -/
theorem not_isComplete_iff_not_subset_preimage :
    (IsComplete outerLangIn innerLangIn lens → False) ↔
      ¬ (outerLangIn ⊆ lens.proj ⁻¹' innerLangIn) :=
  ⟨fun hNo hSub => hNo (IsComplete.ofSubsetPreimage hSub),
   fun hNo hC => hNo (@IsComplete.subset_preimage _ _ _ _ _ _ _ hC)⟩

/-! #### Instances -/

/-- **The universal instance.**  Every statement lens is complete when the outer language is taken
to be the preimage of the inner one.  By `IsComplete.subset_preimage` every other complete pair
factors through this one, so the preimage language is the *largest* outer language for which the
lens is complete — the terminal object among completeness data over a fixed `innerLangIn`. -/
instance instIsCompletePreimage
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (innerLangIn : Set InnerStmtIn) :
    IsComplete (lens.proj ⁻¹' innerLangIn) innerLangIn lens :=
  ⟨fun _ h => h⟩

/-- Completeness is functorial: it composes along lens composition.  (Stated as a `def` rather than
an `instance` because the intermediate language cannot be inferred by unification.) -/
def IsComplete.comp {MidStmtIn MidStmtOut : Type} {midLangIn : Set MidStmtIn}
    (L : Statement.Lens OuterStmtIn OuterStmtOut MidStmtIn MidStmtOut)
    (M : Statement.Lens MidStmtIn MidStmtOut InnerStmtIn InnerStmtOut)
    (hL : IsComplete outerLangIn midLangIn L)
    (hM : IsComplete midLangIn innerLangIn M) :
    IsComplete outerLangIn innerLangIn (M ∘ₗ L) :=
  ⟨fun s hs => hM.proj_complete _ (hL.proj_complete s hs)⟩

/-! #### Independence of `IsSound` and `IsComplete`

The two classes are logically independent.  Both witnesses use the *identity* lens on `Bool`, which
makes the point sharply: the gap is in the **language pair**, not in any exotic lens geometry. -/

/-- Separating data: the identity lens on `Bool`. -/
def sepLens : Statement.Lens Bool Unit Bool Unit := ⟨id, fun _ _ => ()⟩

/-- With `outerLangIn = univ`, `proj_sound` holds vacuously (nothing is outside `univ`). -/
instance sepLens_isSound :
    IsSound (Set.univ : Set Bool) (Set.univ : Set Unit) ({true} : Set Bool)
      (Set.univ : Set Unit) (fun _ _ => True) sepLens where
  proj_sound := fun s hs => absurd (Set.mem_univ s) hs
  lift_sound := fun _ i _ hi => absurd (Set.mem_univ i) hi

/-- …but `proj_complete` fails on `false`, which is in `univ` and not in `{true}`. -/
theorem sepLens_not_isComplete :
    IsComplete (Set.univ : Set Bool) ({true} : Set Bool) sepLens → False := by
  intro h
  have hf := h.proj_complete false (Set.mem_univ false)
  -- `hf : sepLens.proj false ∈ ({true} : Set Bool)`, which is definitionally `false = true`.
  -- Spelled as a defeq ascription rather than `simp`, so it does not depend on `id` being
  -- unfolded by whichever simp set is in scope.
  exact Bool.false_ne_true (hf : (false : Bool) = true)

/-- **`IsSound` does not imply `IsComplete`.**  Without this the new class would be redundant
scaffolding: every `IsSound` lens would already satisfy it. -/
theorem isSound_not_implies_isComplete :
    ∃ (L : Statement.Lens Bool Unit Bool Unit)
      (oIn : Set Bool) (oOut : Set Unit) (iIn : Set Bool) (iOut : Set Unit)
      (compatStmt : Bool → Unit → Prop),
      IsSound oIn oOut iIn iOut compatStmt L ∧ ¬ Nonempty (IsComplete oIn iIn L) :=
  ⟨sepLens, Set.univ, Set.univ, {true}, Set.univ, fun _ _ => True,
    sepLens_isSound, fun h => sepLens_not_isComplete h.some⟩

/-- The mirror witness: `outerLangIn = {true}` inside `innerLangIn = univ`. -/
instance sepLens'_isComplete :
    IsComplete ({true} : Set Bool) (Set.univ : Set Bool) sepLens :=
  ⟨fun _ _ => Set.mem_univ _⟩

/-! #### A non-vacuous separation

`sepLens_isSound` above satisfies `proj_sound` *vacuously*: with `outerLangIn = univ` there is no
statement outside the outer language, so the quantifier is empty.  That is enough to refute
`IsSound → IsComplete`, but a reader may reasonably object that it separates the two classes only at
a degenerate point.  The witness below removes that objection: soundness is checked against a
statement that really is outside the outer language, and completeness still fails. -/

/-- The constant-`false` lens. -/
def sepLensNV : Statement.Lens Bool Unit Bool Unit := ⟨fun _ => false, fun _ _ => ()⟩

/-- Soundness here is **not** vacuous: `true` really is outside `outerLangIn = {false}`, so
`proj_sound` has a live instance to discharge rather than an empty quantifier. -/
theorem sepLensNV_soundness_is_nonvacuous : ∃ s : Bool, s ∉ ({false} : Set Bool) :=
  ⟨true, by simp⟩

instance sepLensNV_isSound :
    IsSound ({false} : Set Bool) (∅ : Set Unit) ({true} : Set Bool) (∅ : Set Unit)
      (fun _ _ => True) sepLensNV where
  proj_sound := fun _ _ => by simp [sepLensNV, Statement.Lens.proj]
  lift_sound := fun _ _ _ _ => by simp

theorem sepLensNV_not_isComplete :
    IsComplete ({false} : Set Bool) ({true} : Set Bool) sepLensNV → False := by
  intro h
  have hf := h.proj_complete false (by simp)
  simp [sepLensNV, Statement.Lens.proj] at hf

/-- **`IsSound` does not imply `IsComplete`, and not merely vacuously.**  Strengthens
`isSound_not_implies_isComplete`: here `outerLangIn = {false} ≠ univ`, so soundness is discharged
against a genuine out-of-language statement (`sepLensNV_soundness_is_nonvacuous`). -/
theorem isSound_not_implies_isComplete_nonvacuously :
    ∃ (L : Statement.Lens Bool Unit Bool Unit)
      (oIn : Set Bool) (oOut : Set Unit) (iIn : Set Bool) (iOut : Set Unit)
      (compatStmt : Bool → Unit → Prop),
      IsSound oIn oOut iIn iOut compatStmt L ∧ ¬ Nonempty (IsComplete oIn iIn L)
        ∧ oIn ≠ Set.univ :=
  ⟨sepLensNV, {false}, ∅, {true}, ∅, fun _ _ => True,
    sepLensNV_isSound, fun h => sepLensNV_not_isComplete h.some, by
      intro hc
      have : (true : Bool) ∈ ({false} : Set Bool) := hc ▸ Set.mem_univ true
      simp at this⟩

/-- **`IsComplete` does not imply `IsSound` either.**  `proj_sound` fails on `false`, which is
outside `{true}` but inside `univ`.  With `isSound_not_implies_isComplete` this makes the two
classes genuinely independent, not merely distinct in presentation. -/
theorem isComplete_not_implies_isSound :
    ∃ (L : Statement.Lens Bool Unit Bool Unit) (oIn iIn : Set Bool),
      Nonempty (IsComplete oIn iIn L) ∧
        ¬ (∀ outerStmtIn, outerStmtIn ∉ oIn → L.proj outerStmtIn ∉ iIn) := by
  refine ⟨sepLens, {true}, Set.univ, ⟨sepLens'_isComplete⟩, ?_⟩
  intro h
  exact h false (by simp) (Set.mem_univ _)

end Statement.Lens

/-- The completeness condition for the oracle statement lens is just the one for the underlying
  statement lens -/
@[reducible, simp]
def OracleStatement.Lens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (outerLangIn : Set (OuterStmtIn × (∀ i, OuterOStmtIn i)))
    (innerLangIn : Set (InnerStmtIn × (∀ i, InnerOStmtIn i)))
    (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :=
  Statement.Lens.IsComplete outerLangIn innerLangIn lens

end StatementLensCompleteness

/-- Conditions for the extractor lens to preserve knowledge soundness -/
class Extractor.Lens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  /-- outer_to_inner for output witness (note: for statements, it's `lift` in this condition) -/
  proj_knowledgeSound : ∀ outerStmtIn innerStmtOut outerWitOut,
    compatStmt outerStmtIn innerStmtOut →
    (lens.stmt.lift outerStmtIn innerStmtOut, outerWitOut) ∈ outerRelOut →
    (innerStmtOut, lens.wit.proj (outerStmtIn, outerWitOut)) ∈ innerRelOut

  /-- inner_to_outer for input witness (note: for statements, it's `proj` in this condition) -/
  lift_knowledgeSound : ∀ outerStmtIn outerWitOut innerWitIn,
    compatWit outerWitOut innerWitIn →
    (lens.stmt.proj outerStmtIn, innerWitIn) ∈ innerRelIn →
    (outerStmtIn, lens.wit.lift (outerStmtIn, outerWitOut) innerWitIn) ∈ outerRelIn

namespace Extractor.Lens.IsKnowledgeSound

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    {outerRelIn : Set (OuterStmtIn × OuterWitIn)}
    {innerRelIn : Set (InnerStmtIn × InnerWitIn)}
    {outerRelOut : Set (OuterStmtOut × OuterWitOut)}
    {innerRelOut : Set (InnerStmtOut × InnerWitOut)}
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lens : Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut)

/-- If an extractor lens is knowledge sound, then the associated statement lens is sound. -/
instance [Inhabited OuterWitOut]
    [instKS : lens.IsKnowledgeSound
                outerRelIn innerRelIn
                outerRelOut innerRelOut
                compatStmt (fun _ _ => True)] :
    lens.stmt.IsSound
      outerRelIn.language outerRelOut.language
      innerRelIn.language innerRelOut.language
      compatStmt where
  proj_sound := fun outerStmtIn hCompat => by
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      not_exists] at hCompat ⊢
    intro innerWitIn hRelIn
    contrapose! hCompat
    let outerWitIn := lens.wit.lift (outerStmtIn, default) innerWitIn
    have hOuterWitIn := instKS.lift_knowledgeSound outerStmtIn default innerWitIn (by simp) hRelIn
    exact ⟨outerWitIn, hOuterWitIn⟩
  lift_sound := fun outerStmtIn innerStmtOut hCompat hInnerRelOut => by
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      not_exists] at hCompat hInnerRelOut ⊢
    intro outerWitOut hOuterRelOut
    contrapose! hInnerRelOut
    let innerWitOut := lens.wit.proj (outerStmtIn, outerWitOut)
    have hInnerWitOut :=
      instKS.proj_knowledgeSound outerStmtIn innerStmtOut outerWitOut hCompat hOuterRelOut
    exact ⟨innerWitOut, hInnerWitOut⟩

end Extractor.Lens.IsKnowledgeSound

section SpecialCases

-- Plan (do not delete)

-- 1. When the lens is over the input context only (keeping the output the same)
-- 1.1. Over the input statement only
-- 1.1.1. When the map is an equivalence
-- 1.2. Over the input witness only
-- 1.2.1. When the map is an equivalence

-- TODO for oracle statements as we haven't figured it out

-- 2. When the lens is over the output context only (keeping the input the same)
-- 2.1. Over the output statement only
-- 2.1.1. When the map is an equivalence
-- 2.2. Over the output witness only
-- 2.2.1. When the map is an equivalence

-- When does this lead to secure protocols? Since one of input / output is trivial, this essentially
-- reduces to the security of the zero-round reduction (that is either the on the input or the
-- output context)

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

namespace Statement.Lens

/-- The identity lens for the statement, which acts as identity on the input and output. -/
@[inline, reducible]
protected def id :
    Statement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut :=
  PFunctor.Lens.id _

alias trivial := Statement.Lens.id

/-- The identity lens is complete for any language against itself.  (Stated here rather than beside
`Statement.Lens.IsComplete` because `Statement.Lens.id` is introduced in this section.) -/
instance instIsCompleteId {OuterStmtIn OuterStmtOut : Type} (L : Set OuterStmtIn) :
    Statement.Lens.IsComplete L L
      (Statement.Lens.id :
        Statement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut) :=
  ⟨fun _ h => h⟩

/-- Lens for the statement which keeps the output the same, and hence only requires a
  projection on the input. -/
@[inline]
def ofInputOnly (projStmt : OuterStmtIn → InnerStmtIn) :
    Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut :=
  ⟨projStmt, fun _ => id⟩

/-- Lens for the statement which keeps the input the same, and hence only requires a
  lift on the output. -/
@[inline]
def ofOutputOnly (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut) :
    Statement.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut :=
  ⟨id, liftStmt⟩

/-- **Every output-only lens is complete, for every language.**  Its projection is the identity,
so membership is preserved on the nose.  This covers the whole `ofOutputOnly` family at once
rather than one bespoke protocol lens. -/
instance instIsCompleteOfOutputOnly {OuterStmtIn OuterStmtOut InnerStmtOut : Type}
    (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut) (L : Set OuterStmtIn) :
    Statement.Lens.IsComplete L L (Statement.Lens.ofOutputOnly liftStmt) :=
  ⟨fun _ h => h⟩

/-- **Every input-only lens is complete for the preimage language.**  Together with
`Statement.Lens.eq_preimage_of_projSound_of_isComplete` this says the preimage is the *only*
outer language for which an input-only lens can be both sound and complete. -/
instance instIsCompleteOfInputOnly {OuterStmtIn OuterStmtOut InnerStmtIn : Type}
    (projStmt : OuterStmtIn → InnerStmtIn) (innerLangIn : Set InnerStmtIn) :
    Statement.Lens.IsComplete (projStmt ⁻¹' innerLangIn) innerLangIn
      (Statement.Lens.ofInputOnly (OuterStmtOut := OuterStmtOut) projStmt) :=
  ⟨fun _ h => h⟩

end Statement.Lens

namespace OracleStatement.Lens

-- TODO: replace with new definitions when we figure out the right definition for oracle statements
-- lens

/-- The identity lens for the statement, which acts as identity on the input and output. -/
@[inline, reducible]
protected def id :
    OracleStatement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                        OuterOStmtIn OuterOStmtOut OuterOStmtIn OuterOStmtOut :=
  PFunctor.Lens.id _

alias trivial := OracleStatement.Lens.id

/-- Lens for the statement which keeps the output the same, and hence only requires a
  projection on the input. -/
@[inline]
def ofInputOnly
    (projStmt : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn × (∀ i, InnerOStmtIn i)) :
    OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
                        OuterOStmtIn OuterOStmtOut InnerOStmtIn OuterOStmtOut :=
  ⟨projStmt, fun _ => id⟩

/-- Lens for the statement which keeps the input the same, and hence only requires a
  lift on the output. -/
@[inline]
def ofOutputOnly
    (liftStmt : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
                OuterStmtOut × (∀ i, OuterOStmtOut i)) :
    OracleStatement.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
                        OuterOStmtIn OuterOStmtOut OuterOStmtIn InnerOStmtOut :=
  ⟨id, liftStmt⟩

end OracleStatement.Lens

namespace Witness.Lens

/-- The identity lens for the witness, which acts as projection from the context (statement +
  witness) to the witness. -/
@[inline, reducible]
protected def id :
    Witness.Lens OuterStmtIn OuterStmtOut OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ⟨Prod.snd, fun _ => Prod.snd⟩

alias trivial := Witness.Lens.id

/-- Lens for the witness which keeps the output context (statement + witness) the same, and hence
  only requires a projection for the input witness. -/
@[inline]
def ofInputOnly (projWit : OuterStmtIn × OuterWitIn → InnerWitIn) :
    Witness.Lens OuterStmtIn OuterStmtOut OuterWitIn OuterWitOut InnerWitIn OuterWitOut :=
  ⟨projWit, fun _ => Prod.snd⟩

/-- Lens for the witness which keeps the input context (statement + witness) the same, and hence
  only requires a lift for the output witness. -/
@[inline]
def ofOutputOnly
    (liftWit : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut) :
    Witness.Lens OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut OuterWitIn InnerWitOut :=
  ⟨Prod.snd, liftWit⟩

end Witness.Lens

namespace Witness.InvLens

/-- The identity inverse lens for the witness, whose projection is product projection to the second
  component, and lifting is identity. -/
@[inline, reducible]
protected def id :
    Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ⟨Prod.snd, fun _ => id⟩

alias trivial := Witness.InvLens.id

/-- Inverse lens for the witness which is the identity on the input witness (inner to outer), and
  only requires a projection for the output witness (outer to inner). -/
@[inline]
def ofOutputOnly (projWit : OuterStmtIn × OuterWitOut → InnerWitOut) :
    Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut OuterWitIn InnerWitOut :=
  ⟨projWit, fun _ => id⟩

/-- Inverse lens for the witness which is the second projection on the output witness (outer to
  inner), and only requires a lift for the input witness (inner to outer). -/
@[inline]
def ofInputOnly
    (liftWit : OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn) :
    Witness.InvLens OuterStmtIn OuterWitIn OuterWitOut InnerWitIn OuterWitOut :=
  ⟨Prod.snd, liftWit⟩

end Witness.InvLens

namespace Context.Lens

/-- The identity lens for the context, which combines the identity statement and witness lenses. -/
@[inline, reducible]
protected def id :
    Context.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := Statement.Lens.id
  wit := Witness.Lens.id

alias trivial := Context.Lens.id

/-- Lens for the context which keeps the output contexts the same, and only requires projections on
  the statement & witness for the input. -/
@[inline]
def ofInputOnly
    (stmtProj : OuterStmtIn → InnerStmtIn)
    (witProj : OuterStmtIn × OuterWitIn → InnerWitIn) :
    Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
                OuterWitIn OuterWitOut InnerWitIn OuterWitOut where
  stmt := Statement.Lens.ofInputOnly stmtProj
  wit := Witness.Lens.ofInputOnly witProj

/-- Lens for the context which keeps the input contexts the same, and only requires lifts on the
  statement & witness for the output. -/
@[inline]
def ofOutputOnly
    (witLift :
      OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut)
    (stmtLift : OuterStmtIn → InnerStmtOut → OuterStmtOut) :
    Context.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
                OuterWitIn OuterWitOut OuterWitIn InnerWitOut where
  wit := Witness.Lens.ofOutputOnly witLift
  stmt := Statement.Lens.ofOutputOnly stmtLift

end Context.Lens

namespace OracleContext.Lens

/-- The identity lens for the context, which combines the identity statement and witness lenses. -/
@[inline, reducible]
protected def id :
    OracleContext.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterOStmtIn OuterOStmtOut OuterOStmtIn OuterOStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := OracleStatement.Lens.id
  wit := Witness.Lens.id

alias trivial := OracleContext.Lens.id

/-- Lens for the oracle context which keeps the output contexts the same, and only requires
  projections on the statement & witness for the input. -/
@[inline]
def ofInputOnly
    (stmtProj : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn × (∀ i, InnerOStmtIn i))
    (witProj : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn → InnerWitIn) :
    OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
                OuterOStmtIn OuterOStmtOut InnerOStmtIn OuterOStmtOut
                OuterWitIn OuterWitOut InnerWitIn OuterWitOut where
  stmt := OracleStatement.Lens.ofInputOnly stmtProj
  wit := Witness.Lens.ofInputOnly witProj

/-- Lens for the oracle context which keeps the input contexts the same, and only requires lifts on
  the statement & witness for the output. -/
@[inline]
def ofOutputOnly
    (stmtLift : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
                OuterStmtOut × (∀ i, OuterOStmtOut i))
    (witLift : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
               (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut → OuterWitOut) :
    OracleContext.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
                OuterOStmtIn OuterOStmtOut OuterOStmtIn InnerOStmtOut
                OuterWitIn OuterWitOut OuterWitIn InnerWitOut where
  stmt := OracleStatement.Lens.ofOutputOnly stmtLift
  wit := Witness.Lens.ofOutputOnly witLift

end OracleContext.Lens

namespace Extractor.Lens

/-- The identity lens for the extractor on the witness, given a statement lens. -/
@[inline, reducible]
def idWit {stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut} :
    Extractor.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := stmtLens
  wit := Witness.InvLens.id

alias trivialWit := Extractor.Lens.idWit

end Extractor.Lens

end SpecialCases

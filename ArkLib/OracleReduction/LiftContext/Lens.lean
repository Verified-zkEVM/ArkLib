/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ToMathlib.PFunctor.Lens.Basic

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
def Statement.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
  := PFunctor.Lens (OuterStmtIn X^ OuterStmtOut)
                   (InnerStmtIn X^ InnerStmtOut)

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
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
  :=
    Statement.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
                  (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
  -- TODO: fill in the extra conditions
  /- Basically, as we model the output oracle statement as a subset of the input oracle statement +
  the prover's messages, we need to make sure that this subset relation is satisfied in the
  statement lens mapping.

  We also need to provide a `QueryImpl` instance for simulating the outer oracle verifier using
  the inner oracle verifier.
  -/

  -- simOStmt : QueryImpl [InnerOStmtIn]ₒ
  --   (ReaderT OuterStmtIn (OracleComp [OuterOStmtIn]ₒ))

  -- simOStmt_neverFails : ∀ i, ∀ t, ∀ outerStmtIn,
  --   ((simOStmt.impl (query i t)).run outerStmtIn).neverFails
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
def Witness.Lens (OuterStmtIn InnerStmtOut OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    := PFunctor.Lens ((OuterStmtIn × OuterWitIn) X^ OuterWitOut)
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

/-- Lens for lifting the witness extraction procedure from the inner reduction to the outer
  reduction.

This goes in the reverse direction (output to input) compared to the witness lens for the prover,
and requires in addition the outer input statement.
-/
@[inline, reducible]
def Witness.InvLens (OuterStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    := PFunctor.Lens ((OuterStmtIn × OuterWitOut) X^ OuterWitIn)
                     (InnerWitOut X^ InnerWitIn)

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
    simp [Set.language] at hCompat ⊢
    intro innerWitIn hRelIn
    contrapose! hCompat
    let outerWitIn := lens.wit.lift (outerStmtIn, default) innerWitIn
    have hOuterWitIn := instKS.lift_knowledgeSound outerStmtIn default innerWitIn (by simp) hRelIn
    exact ⟨outerWitIn, hOuterWitIn⟩
  lift_sound := fun outerStmtIn innerStmtOut hCompat hInnerRelOut => by
    simp [Set.language] at hCompat hInnerRelOut ⊢
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

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ToMathlib.PFunctor.Basic

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

section find_home

/-- Applies a pair of binary functions component-wise to a pair of pairs.

TODO: move to mathlib, add supporting lemmas -/
def Prod.map₂ {α β γ α' β' γ' : Type*} (f : α → β → γ) (g : α' → β' → γ') :
    (α × α') → (β × β') → (γ × γ') :=
  fun ⟨a, a'⟩ ⟨b, b'⟩ => ⟨f a b, g a' b'⟩

end find_home

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
  := PFunctor.Lens (OuterStmtIn y^ OuterStmtOut) (InnerStmtIn y^ InnerStmtOut)

namespace Statement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}

/-- Transport input statements from the outer context to the inner context -/
@[inline, reducible]
def proj (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) :
    OuterStmtIn → InnerStmtIn :=
  lens.mapPos

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def lift (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) :
    OuterStmtIn → InnerStmtOut → OuterStmtOut :=
  lens.mapDir

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
  --   (ReaderT (OuterStmtIn × InnerStmtOut) (OracleComp ([OuterOStmtIn]ₒ ++ₒ [InnerOStmtOut]ₒ)))
  -- liftOStmt_neverFails : ∀ i, ∀ t, ∀ outerStmtIn, ∀ innerStmtOut,
  --   ((liftOStmt.impl (query i t)).run (outerStmtIn, innerStmtOut)).neverFails

namespace OracleStatement.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]

/-- Transport input statements from the outer context to the inner context

TODO: refactor etc. -/
@[inline, reducible]
def proj (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn × (∀ i, InnerOStmtIn i) :=
  lens.mapPos

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context.

  TODO: refactor etc. -/
@[inline, reducible]
def lift (lens : OracleStatement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
    OuterStmtOut × (∀ i, OuterOStmtOut i) :=
  lens.mapDir

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
    := PFunctor.Lens ((OuterStmtIn × OuterWitIn) y^ OuterWitOut)
                     (InnerWitIn y^ (InnerStmtOut × InnerWitOut))

namespace Witness.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

/-- Transport input witness from the outer context to the inner context -/
@[inline, reducible]
def proj (lens : Witness.Lens OuterStmtIn InnerStmtIn
                                OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerWitIn :=
  lens.mapPos

/-- Transport output witness from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def lift (lens : Witness.Lens OuterStmtIn InnerStmtOut
                                OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterWitOut :=
  lens.mapDir

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

/-- Projection of the context. -/
@[inline, reducible]
def proj (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn :=
  fun ⟨stmtIn, witIn⟩ => ⟨lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witIn)⟩

/-- Lifting of the context. -/
@[inline, reducible]
def lift (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterStmtOut × OuterWitOut :=
  fun ⟨stmtIn, witIn⟩ ⟨innerStmtOut, innerWitOut⟩ =>
    ⟨lens.stmt.lift stmtIn innerStmtOut, lens.wit.lift (stmtIn, witIn) (innerStmtOut, innerWitOut)⟩

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

/-- Projection of the context. -/
@[inline, reducible]
def proj (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn :=
  fun ⟨stmtIn, witIn⟩ =>
    ⟨lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witIn)⟩

/-- Lifting of the context. -/
@[inline, reducible]
def lift (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut →
    (OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut :=
  fun ⟨stmtIn, witIn⟩ ⟨innerStmtOut, innerWitOut⟩ =>
    ⟨lens.stmt.lift stmtIn innerStmtOut, lens.wit.lift (stmtIn, witIn) (innerStmtOut, innerWitOut)⟩

/-- Convert the oracle context lens to a context lens. -/
@[inline, reducible]
def toContext (lens : OracleContext.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    Context.Lens (OuterStmtIn × (∀ i, OuterOStmtIn i)) (OuterStmtOut × (∀ i, OuterOStmtOut i))
                (InnerStmtIn × (∀ i, InnerOStmtIn i)) (InnerStmtOut × (∀ i, InnerOStmtOut i))
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut :=
  ⟨lens.stmt, lens.wit⟩

end OracleContext.Lens

/-- Lens for lifting the extractor from the inner reduction to the outer reduction.

Given that the extractor's input-output interface is of the form `StmtIn × WitOut → WitIn` (ignoring
transcript and query logs), this is essentially the same as a lens for the prover, except the
exchange of the input and output witness, and the omission of the output statement.
-/
@[inline, reducible]
def Extractor.Lens (OuterStmtIn InnerStmtIn
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    := PFunctor.Lens ((OuterStmtIn × OuterWitOut) y^ OuterWitIn)
                     ((InnerStmtIn × InnerWitOut) y^ InnerWitIn)

namespace Extractor.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

/-- Transport the tuple of (input statement, output witness) from the outer context to the inner
  context -/
@[inline, reducible]
def proj (lens : Extractor.Lens OuterStmtIn InnerStmtIn
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitOut → InnerStmtIn × InnerWitOut :=
  lens.mapPos

/-- Transport the inner input witness to the outer input witness, also relying on the tuple (outer
  input statement, outer output witness) -/
@[inline, reducible]
def lift (lens : Extractor.Lens OuterStmtIn InnerStmtIn
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitOut → InnerWitIn → OuterWitIn :=
  lens.mapDir

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
    (compatRel : Set ((OuterStmtIn × OuterWitIn) × (InnerStmtOut × InnerWitOut)))
    (lens : Context.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  proj_complete : ∀ stmtIn witIn,
    (stmtIn, witIn) ∈ outerRelIn →
    (lens.stmt.proj stmtIn, lens.wit.proj (stmtIn, witIn)) ∈ innerRelIn

  lift_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    ((outerStmtIn, outerWitIn), (innerStmtOut, innerWitOut)) ∈ compatRel →
    (outerStmtIn, outerWitIn) ∈ outerRelIn →
    (innerStmtOut, innerWitOut) ∈ innerRelOut →
    (lens.stmt.lift outerStmtIn innerStmtOut,
    lens.wit.lift (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut)) ∈ outerRelOut

/-- Conditions for the lens / transformation to preserve soundness -/
class Statement.Lens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compatRel : Set (OuterStmtIn × InnerStmtOut))
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.proj outerStmtIn ∉ innerLangIn

  lift_sound : ∀ outerStmtIn innerStmtOut,
    (outerStmtIn, innerStmtOut) ∈ compatRel →
    outerStmtIn ∉ outerLangIn →
    innerStmtOut ∉ innerLangOut →
    lens.lift outerStmtIn innerStmtOut ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve round-by-round soundness

This is nearly identical to the `IsSound` condition, _except_ that we do not require
`outerStmtIn ∉ outerLangIn` in the `lift_sound` condition.

(we need to relax that condition to prove `toFun_full` of the lifted state function) -/
class Statement.Lens.IsRBRSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compatRel : Set (OuterStmtIn × InnerStmtOut))
    (stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  -- inner_to_outer for input
  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → stmtLens.proj outerStmtIn ∉ innerLangIn

  -- outer_to_inner for output
  lift_sound : ∀ outerStmtIn innerStmtOut,
    (outerStmtIn, innerStmtOut) ∈ compatRel →
    innerStmtOut ∉ innerLangOut →
    stmtLens.lift outerStmtIn innerStmtOut ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve knowledge soundness

Note that we do _not_ require a witness lens in the input -> output direction, since we don't need
to do anything with the (honest) prover -/
class Statement.Lens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compatStmt : Set (OuterStmtIn × InnerStmtOut))
    (compatWit : Set (OuterWitOut × InnerWitIn))
    (lensE : Extractor.Lens OuterStmtIn InnerStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensV : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  -- outer_to_inner for output
  out_to_in : ∀ outerStmtIn innerStmtOut outerWitOut,
    (outerStmtIn, innerStmtOut) ∈ compatStmt →
    (lensV.lift outerStmtIn innerStmtOut, outerWitOut) ∈ outerRelOut →
    (innerStmtOut, (lensE.proj (outerStmtIn, outerWitOut)).2) ∈ innerRelOut

  -- inner_to_outer for input
  in_to_out : ∀ outerStmtIn outerWitOut innerWitIn,
    (outerWitOut, innerWitIn) ∈ compatWit →
    (lensV.proj outerStmtIn, innerWitIn) ∈ innerRelIn →
    (outerStmtIn, lensE.lift (outerStmtIn, outerWitOut) innerWitIn) ∈ outerRelIn

namespace Statement.Lens.IsKnowledgeSound

-- Convert knowledge soundness into soundness

end Statement.Lens.IsKnowledgeSound

class Statement.Lens.IsRBRKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compatStmt : Set (OuterStmtIn × InnerStmtOut))
    (compatWit : Set (OuterWitOut × InnerWitIn))
    (lensE : Extractor.Lens OuterStmtIn InnerStmtIn OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensV : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
  -- TODO: double-check if we need any extra conditions
  extends Statement.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
        compatStmt compatWit lensE lensV where

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

/-- The trivial lens for the statement, which acts as identity on the input and output. -/
@[inline, reducible]
def trivial :
    Statement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut :=
  ⟨id, fun _ => id⟩

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

/-- The trivial lens for the statement, which acts as identity on the input and output. -/
@[inline, reducible]
def trivial :
    OracleStatement.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                        OuterOStmtIn OuterOStmtOut OuterOStmtIn OuterOStmtOut :=
  ⟨id, fun _ => id⟩

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

/-- The trivial lens for the witness, which acts as projection from the context (statement +
  witness) to the witness. -/
@[inline, reducible]
def trivial :
    Witness.Lens OuterStmtIn OuterStmtOut OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ⟨Prod.snd, fun _ => Prod.snd⟩

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

namespace Context.Lens

/-- The trivial lens for the context, which combines the trivial statement and witness lenses. -/
@[inline, reducible]
def trivial :
    Context.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut where
  stmt := Statement.Lens.trivial
  wit := Witness.Lens.trivial

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

end SpecialCases

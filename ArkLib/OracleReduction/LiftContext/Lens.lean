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

TODO: move to mathlib -/
def Prod.map₂ {α β γ α' β' γ' : Type*} (f : α → β → γ) (g : α' → β' → γ') :
    (α × α') → (β × β') → (γ × γ') :=
  fun ⟨a, a'⟩ ⟨b, b'⟩ => ⟨f a b, g a' b'⟩

end find_home

open OracleSpec OracleComp PFunctor

/-- A lens for transporting input and output statements for the verifier of a (non-oracle)
  reduction.

  Consists of two functions:
  - `projStmt` : Transport input statements from the outer context to the inner context
  - `liftStmt` : Transport output statements from the inner context to the outer context,
    additionally relying on the input statements of the outer context.

  This is exactly the same as a `PFunctor.Lens` between two monomials defined by the input and
  output statements (from the outer to the inner context).
-/
@[inline, reducible]
def Verifier.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
  := PFunctor.Lens (OuterStmtIn y^ OuterStmtOut) (InnerStmtIn y^ InnerStmtOut)

namespace Verifier.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}

/-- Transport input statements from the outer context to the inner context -/
@[inline, reducible]
def projStmt (lens : Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) :
    OuterStmtIn → InnerStmtIn :=
  lens.mapPos

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def liftStmt (lens : Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) :
    OuterStmtIn → InnerStmtOut → OuterStmtOut :=
  lens.mapDir

end Verifier.Lens

/-- A lens for transporting input and output statements (both oracle and non-oracle) for the
  oracle verifier of an oracle reduction.

  TODO: figure out the right way to define this -/
@[inline, reducible]
def OracleVerifier.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
  :=
    Verifier.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
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

namespace OracleVerifier.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]

/-- Transport input statements from the outer context to the inner context

TODO: refactor etc. -/
@[inline, reducible]
def projStmt (lens : OracleVerifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn × (∀ i, InnerOStmtIn i) :=
  lens.mapPos

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context.

  TODO: refactor etc. -/
@[inline, reducible]
def liftStmt (lens : OracleVerifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) :
    OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
    OuterStmtOut × (∀ i, OuterOStmtOut i) :=
  lens.mapDir

-- def toVerifierLens : Verifier.Lens
--     (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
--     (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
--   := oStmtLens

end OracleVerifier.Lens

/-- A lens for transporting the input and output contexts (statements + witnesses) for the prover
  of a (non-oracle) reduction. -/
@[inline, reducible]
def Prover.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    := PFunctor.Lens ((OuterStmtIn × OuterWitIn) y^ (OuterStmtOut × OuterWitOut))
                     ((InnerStmtIn × InnerWitIn) y^ (InnerStmtOut × InnerWitOut))

namespace Prover.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

/-- Transport input statements from the outer context to the inner context -/
@[inline, reducible]
def projCtx (lens : Prover.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn :=
  lens.mapPos

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def liftCtx (lens : Prover.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterStmtOut × OuterWitOut :=
  lens.mapDir

end Prover.Lens

/-- A lens for transporting the input and output contexts (statements + witnesses) for the prover
  of an oracle reduction.

  Since the prover in an oracle reduction is the same as for the associated non-oracle reduction
  (oracle-ness only applies to the verifier), we can just use the prover lens for the non-oracle
  reduction. -/
@[inline, reducible]
def OracleProver.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  Prover.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
             (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
             OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleProver.Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}

/-- Transport input statements from the outer context to the inner context -/
@[inline, reducible]
def projStmt (lens : OracleProver.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtIn × (∀ i, InnerOStmtIn i)) × InnerWitIn :=
  lens.mapPos

/-- Transport output statements from the inner context to the outer context,
  additionally relying on the input statements of the outer context. -/
@[inline, reducible]
def liftStmt (lens : OracleProver.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut) :
    (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut →
    (OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut :=
  lens.mapDir

end OracleProver.Lens

/-- A structure collecting a lens for the prover, and a lens for the verifier, for transporting
  between the contexts of an outer reduction and an inner reduction. -/
@[ext]
structure Reduction.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  prover : Prover.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut
  verifier : Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut

/-- A structure collecting a lens for the prover, and a lens for the oracle verifier, for
  transporting between the contexts of an outer oracle reduction and an inner oracle reduction. -/
@[ext]
structure OracleReduction.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  prover : OracleProver.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
              OuterWitIn OuterWitOut InnerWitIn InnerWitOut
  verifier : OracleVerifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                       OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut

/-
  Recall the interface of an extractor:
  - Takes in `WitOut`, `StmtIn`, `Transcript`, `QueryLog`
  (note: no need for `StmtOut` as it can be derived from `StmtIn`, `Transcript`, and `QueryLog`)
  - Returns `WitIn`

  We need a lens for the extractor as well.

  Assume we have an inner extractor
    `E : InnerWitOut → InnerStmtIn → Transcript → QueryLog → InnerWitIn`

  We need to derive an outer extractor
    `E' : OuterWitOut → OuterStmtIn → Transcript → QueryLog → OuterWitIn`

  Note that `Transcript` and `QueryLog` are the same due to the lens only changing the
  input-output interface, and not the inside (oracle) reduction.

  So, `E' outerWitOut outerStmtIn transcript queryLog` needs to call
    `E (map to innerWitOut) (projStmt outerStmtIn) transcript queryLog`
  and then post-process the result, which is some `innerWitIn`, to get some `outerWitIn`.

  This processing is exactly the same as a lens in the opposite direction between the outer and
  inner witness types.
-/

/-- Inverse lens between outer and inner witnesses (going the other direction with respect to
  input-output), for extractors / knowledge soundness.
-/
@[inline, reducible]
def Extractor.Lens (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  PFunctor.Lens (OuterWitOut y^ OuterWitIn) (InnerWitOut y^ InnerWitIn)

-- structure Reduction.LensInv (OuterStmtOut InnerStmtOut : Type)
--     (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) extends
--       WitnessLens OuterWitOut OuterWitIn InnerWitOut InnerWitIn where
--   projStmt : OuterStmtOut → InnerStmtOut
  -- projWitInv : InnerWitOut → OuterWitOut
  -- liftWitInv : InnerWitIn × OuterWitOut → OuterWitIn

/-- For round-by-round knowledge soundness, we require an _equivalence_ on the input witness
  (inner <=> outer). Otherwise, we cannot extract.

  (imagine a reduction from R1 x R2 => R3 x R4, that is the sequential composition of R1 => R3 and
  then R2 => R4. This reduction is not round-by-round knowledge sound, since if we are in the
  R1 => R3 rounds, we have no way of invoking the second extractor for recovering the witness for
  R2.)
-/
class RBRWitnessLensInv (OuterWitIn InnerWitIn : Type) where
  liftWit : InnerWitIn → OuterWitIn

/-- Conditions for the lens / transformation to preserve completeness

For `lift`, we require compatibility relations between the outer input statement/witness and
the inner output statement/witness -/
class Reduction.Lens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut : Set (OuterStmtOut × OuterWitOut))
    (innerRelOut : Set (InnerStmtOut × InnerWitOut))
    (compatRel : Set ((OuterStmtIn × OuterWitIn) × (InnerStmtOut × InnerWitOut)))
    (lens : Reduction.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  proj_compat : ∀ stmtIn witIn,
    (lens.prover.projCtx (stmtIn, witIn)).fst = lens.verifier.projStmt stmtIn

  proj_complete : ∀ stmtIn witIn,
    (stmtIn, witIn) ∈ outerRelIn →
    (lens.prover.projCtx (stmtIn, witIn)) ∈ innerRelIn

  lift_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    ((outerStmtIn, outerWitIn), (innerStmtOut, innerWitOut)) ∈ compatRel →
    (outerStmtIn, outerWitIn) ∈ outerRelIn →
    (innerStmtOut, innerWitOut) ∈ innerRelOut →
    lens.prover.liftCtx (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) ∈ outerRelOut

/-- Conditions for the lens / transformation to preserve soundness -/
class Verifier.Lens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compatRel : Set (OuterStmtIn × InnerStmtOut))
    (lens : Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.projStmt outerStmtIn ∉ innerLangIn

  lift_sound : ∀ outerStmtIn innerStmtOut,
    (outerStmtIn, innerStmtOut) ∈ compatRel →
    outerStmtIn ∉ outerLangIn →
    innerStmtOut ∉ innerLangOut →
    lens.liftStmt outerStmtIn innerStmtOut ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve round-by-round soundness

This is nearly identical to the `IsSound` condition, _except_ that we do not require
`outerStmtIn ∉ outerLangIn` in the `lift_sound` condition.

(we need to relax that condition to prove `toFun_full` of the lifted state function) -/
class Verifier.Lens.IsRBRSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compatRel : Set (OuterStmtIn × InnerStmtOut))
    (lens : Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  -- inner_to_outer for input
  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.projStmt outerStmtIn ∉ innerLangIn

  -- outer_to_inner for output
  lift_sound : ∀ outerStmtIn innerStmtOut,
    (outerStmtIn, innerStmtOut) ∈ compatRel →
    innerStmtOut ∉ innerLangOut →
    lens.liftStmt outerStmtIn innerStmtOut ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve knowledge soundness

Note that we do _not_ require a witness lens in the input -> output direction, since we don't need
to do anything with the (honest) prover -/
class Verifier.Lens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lensE : Extractor.Lens OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensV : Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  -- outer_to_inner for output
  out_to_in : ∀ outerStmtIn innerStmtOut outerWitOut,
    compatStmt outerStmtIn innerStmtOut →
    outerRelOut (lensV.liftStmt outerStmtIn innerStmtOut) outerWitOut →
    innerRelOut innerStmtOut (lensE.projWit outerWitOut)

  -- inner_to_outer for input
  in_to_out : ∀ outerStmtIn outerWitOut innerWitIn,
    compatWit outerWitOut innerWitIn →
    innerRelIn (lensV.projStmt outerStmtIn) innerWitIn →
    outerRelIn outerStmtIn (lensE.liftWit (outerWitOut, innerWitIn))

namespace Verifier.Lens.IsKnowledgeSound

-- Convert knowledge soundness into soundness

end Verifier.Lens.IsKnowledgeSound

class Verifier.Lens.IsRBRKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lensE : Extractor.Lens OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lensV : Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
  -- TODO: double-check if we need any extra conditions
  extends Verifier.Lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
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

namespace Verifier.Lens

/-- The trivial lens for the verifier, which acts as identity on the input and output statements. -/
@[inline, reducible, simp]
def trivial :
    Verifier.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut :=
  ⟨id, fun _ => id⟩

/-- Lens for the verifier which keeps the output statements the same, and hence only requires a
  projection on the input statements. -/
@[inline]
def ofInputOnly (projStmt : OuterStmtIn → InnerStmtIn) :
    Verifier.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut :=
  ⟨projStmt, fun _ => id⟩

/-- Lens for the verifier which keeps the input statements the same, and hence only requires a
  lift on the output statements. -/
@[inline]
def ofOutputOnly (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut) :
    Verifier.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut :=
  ⟨id, liftStmt⟩

end Verifier.Lens

namespace Prover.Lens

/-- The trivial lens for the prover, which acts as identity on the input and output contexts. -/
@[inline, reducible, simp]
def trivial :
    Prover.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ⟨id, fun _ => id⟩

/-- Lens for the prover which keeps the output context (statements + witnesses) the same, and hence
  only requires a projection on the input context (statements + witnesses). -/
@[inline]
def ofInputOnly (projCtx : OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn) :
    Prover.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
                OuterWitIn OuterWitOut InnerWitIn OuterWitOut :=
  ⟨projCtx, fun _ => id⟩

/-- Lens for the prover which keeps the input context (statements + witnesses) the same, and hence
  only requires a lift on the output context (statements + witnesses). -/
@[inline]
def ofOutputOnly
    (liftCtx : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterStmtOut × OuterWitOut) :
    Prover.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
                OuterWitIn OuterWitOut OuterWitIn InnerWitOut :=
  ⟨id, liftCtx⟩

/-- Lens for the prover which separates the mappings between the statements and the witnesses. -/
def ofSeparateStmtWit
    (projStmt : OuterStmtIn → InnerStmtIn) (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut)
    (projWit : OuterWitIn → InnerWitIn) (liftWit : OuterWitIn → InnerWitOut → OuterWitOut) :
    Prover.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut :=
  ⟨Prod.map projStmt projWit, Prod.map₂ liftStmt liftWit⟩

/-- Lens for the prover which keeps the witnesses the same, and hence only requires a projection
  on the statements. -/
@[inline]
def ofStmtOnly
    (projStmt : OuterStmtIn → InnerStmtIn) (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut) :
    Prover.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ofSeparateStmtWit projStmt liftStmt id (fun _ => id)

/-- Lens for the prover which keeps the statements the same, and hence only requires a lift on
  the witnesses. -/
@[inline]
def ofWitOnly
    (projWit : OuterWitIn → InnerWitIn) (liftWit : OuterWitIn → InnerWitOut → OuterWitOut) :
    Prover.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut :=
  ofSeparateStmtWit id (fun _ => id) projWit liftWit

/-- Lens for the prover which keeps the witnesses the same, and also the output statements the same,
  hence only requires a projection on the input statements. -/
@[inline]
def ofInputStmtOnly (projStmt : OuterStmtIn → InnerStmtIn) :
    Prover.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ofStmtOnly projStmt (fun _ => id)

/-- Lens for the prover which keeps the witnesses the same, and also the input statements the same,
  hence only requires a lift on the output statements. -/
@[inline]
def ofOutputStmtOnly (liftStmt : OuterStmtIn → InnerStmtOut → OuterStmtOut) :
    Prover.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
                OuterWitIn OuterWitOut OuterWitIn OuterWitOut :=
  ofStmtOnly id liftStmt

/-- Lens for the prover which keeps the statements the same, and also the output witnesses the same,
  hence only requires a projection on the input witnesses. -/
@[inline]
def ofInputWitOnly (projWit : OuterWitIn → InnerWitIn) :
    Prover.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterWitIn OuterWitOut InnerWitIn OuterWitOut :=
  ofWitOnly projWit (fun _ => id)

/-- Lens for the prover which keeps the witnesses the same, and also the input statements the same,
  hence only requires a lift on the output statements. -/
@[inline]
def ofOutputWitOnly (liftWit : OuterWitIn → InnerWitOut → OuterWitOut) :
    Prover.Lens OuterStmtIn OuterStmtOut OuterStmtIn OuterStmtOut
                OuterWitIn OuterWitOut OuterWitIn InnerWitOut :=
  ofWitOnly id liftWit

end Prover.Lens

namespace Reduction.Lens

@[inline]
def ofInputOnly
    (proverProj : OuterStmtIn × OuterWitIn → InnerStmtIn × InnerWitIn)
    (verifierProj : OuterStmtIn → InnerStmtIn) :
    Reduction.Lens OuterStmtIn OuterStmtOut InnerStmtIn OuterStmtOut
                OuterWitIn OuterWitOut InnerWitIn OuterWitOut where
  prover := Prover.Lens.ofInputOnly proverProj
  verifier := Verifier.Lens.ofInputOnly verifierProj

@[inline]
def ofOutputOnly
    (proverLift :
      OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → OuterStmtOut × OuterWitOut)
    (verifierLift : OuterStmtIn → InnerStmtOut → OuterStmtOut) :
    Reduction.Lens OuterStmtIn OuterStmtOut OuterStmtIn InnerStmtOut
                OuterWitIn OuterWitOut OuterWitIn InnerWitOut where
  prover := Prover.Lens.ofOutputOnly proverLift
  verifier := Verifier.Lens.ofOutputOnly verifierLift

-- @[inline]
-- def ofInputStmtOnly (OuterStmtIn InnerStmtIn StmtOut WitIn WitOut : Type)
--     (projStmt : OuterStmtIn → InnerStmtIn) :
--     Reduction.Lens OuterStmtIn StmtOut InnerStmtIn StmtOut
--                 WitIn WitOut WitIn WitOut where
--   toStatementLens := StatementLens.ofInputOnly OuterStmtIn InnerStmtIn StmtOut projStmt
--   toWitnessLens := WitnessLens.trivial WitIn WitOut

-- @[inline]
-- def ofOutputStmtOnly (StmtIn OuterStmtOut InnerStmtOut WitIn WitOut : Type)
--     (liftStmt : InnerStmtOut → OuterStmtOut) :
--     Reduction.Lens StmtIn OuterStmtOut StmtIn InnerStmtOut
--                 WitIn WitOut WitIn WitOut where
--   toStatementLens := StatementLens.ofOutputOnly StmtIn OuterStmtOut InnerStmtOut liftStmt
--   toWitnessLens := WitnessLens.trivial WitIn WitOut

-- @[inline]
-- def ofInputWitOnly (StmtIn StmtOut OuterWitIn InnerWitIn WitOut : Type)
--     (projWit : OuterWitIn → InnerWitIn) :
--     Reduction.Lens StmtIn StmtOut StmtIn StmtOut
--                 OuterWitIn WitOut InnerWitIn WitOut where
--   toStatementLens := StatementLens.trivial StmtIn StmtOut
--   toWitnessLens := WitnessLens.ofInputOnly OuterWitIn InnerWitIn WitOut projWit

-- @[inline]
-- def ofOutputWitOnly (StmtIn StmtOut WitIn OuterWitOut InnerWitOut : Type)
--     (liftWit : InnerWitOut → OuterWitOut) :
--     Reduction.Lens StmtIn StmtOut StmtIn StmtOut
--                 WitIn OuterWitOut WitIn InnerWitOut where
--   toStatementLens := StatementLens.trivial StmtIn StmtOut
--   toWitnessLens := WitnessLens.ofOutputOnly WitIn OuterWitOut InnerWitOut liftWit

end Reduction.Lens

end SpecialCases

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic
import ToMathlib.PFunctor.Basic

/-!
  ## Lens between (Oracle) Statements and between Witnesses

  This file defines the different lenses required for the transformation / lifting of context for an
  (oracle) reduction, and the properties required for the transformation / lift to be complete /
  sound / knowledge sound.

  We also define simpler examples of lenses, when we don't need the full generality. For instance,
  lenses where we have (only) an equivalence between the statements / witnesses, or lenses where the
  witnesses are trivial.
-/

open OracleSpec OracleComp

/-- A lens for transporting (non-oracle) statements between outer and inner contexts -/
class StatementLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type) where
  projStmt : OuterStmtIn → InnerStmtIn
  liftStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut

/-- A lens for transporting both oracle and non-oracle statements between outer and inner contexts

We require both a lens of the underlying (combined) statements (via the conversion from oracle
reduction => reduction), but also simulation of oracle statements in terms of other values. -/
class OStatementLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
  extends
    StatementLens (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
                  (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
  where
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

namespace OStatementLens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
    (oStmtLens : OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)

instance instStatementLens : StatementLens
    (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
    (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
  := inferInstance

end OStatementLens

/-- A lens for transporting witnesses between outer and inner contexts -/
class WitnessLens (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  projWit : OuterWitIn → InnerWitIn
  liftWit : OuterWitIn × InnerWitOut → OuterWitOut

/-- A lens for transporting between outer and inner contexts of a (non-oracle) reduction -/
class ContextLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    extends StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut,
      WitnessLens OuterWitIn OuterWitOut InnerWitIn InnerWitOut

/-- A lens for transporting between outer and inner contexts of an oracle reduction -/
class OracleContextLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) extends
      OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                    OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut,
      WitnessLens OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleContextLens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
  {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
  {oLens : OracleContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}

/-- Converting an oracle context lens to a non-oracle context lens, via moving oracle statements
into non-oracle statements -/
instance instContextLens : ContextLens
    (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
    (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut where
  -- projStmt := oLens.projStmt
  -- liftStmt := oLens.liftStmt
  -- projWit := oLens.projWit
  -- liftWit := oLens.liftWit

end OracleContextLens


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
@[reducible]
def WitnessLensInv (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  WitnessLens OuterWitOut OuterWitIn InnerWitOut InnerWitIn
-- structure ContextLensInv (OuterStmtOut InnerStmtOut : Type)
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
class ContextLens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compat : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → Prop)
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  proj_complete : ∀ stmtIn witIn,
    outerRelIn stmtIn witIn →
    innerRelIn (lens.projStmt stmtIn) (lens.projWit witIn)

  lift_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    compat (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) →
    outerRelIn outerStmtIn outerWitIn →
    innerRelOut innerStmtOut innerWitOut →
    outerRelOut (lens.liftStmt (outerStmtIn, innerStmtOut))
                (lens.liftWit (outerWitIn, innerWitOut))

/-- Conditions for the lens / transformation to preserve soundness -/
class StatementLens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compat : OuterStmtIn → InnerStmtOut → Prop)
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.projStmt outerStmtIn ∉ innerLangIn

  lift_sound : ∀ outerStmtIn innerStmtOut,
    compat outerStmtIn innerStmtOut →
    outerStmtIn ∉ outerLangIn →
    innerStmtOut ∉ innerLangOut →
      lens.liftStmt (outerStmtIn, innerStmtOut) ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve round-by-round soundness

This is nearly identical to the `IsSound` condition, _except_ that we do not require
`outerStmtIn ∉ outerLangIn` in the `lift_sound` condition.

(we need to relax that condition to prove `toFun_full` of the lifted state function) -/
class StatementLens.IsRBRSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compat : OuterStmtIn → InnerStmtOut → Prop)
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  -- inner_to_outer for input
  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → lens.projStmt outerStmtIn ∉ innerLangIn

  -- outer_to_inner for output
  lift_sound : ∀ outerStmtIn innerStmtOut,
    compat outerStmtIn innerStmtOut →
    innerStmtOut ∉ innerLangOut →
    lens.liftStmt (outerStmtIn, innerStmtOut) ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve knowledge soundness

Note that we do _not_ require a witness lens in the input -> output direction, since we don't need
to do anything with the (honest) prover -/
class StatementLens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  -- outer_to_inner for output
  out_to_in : ∀ outerStmtIn innerStmtOut outerWitOut,
    compatStmt outerStmtIn innerStmtOut →
    outerRelOut (lens.liftStmt (outerStmtIn, innerStmtOut)) outerWitOut →
    innerRelOut innerStmtOut (lensInv.projWit outerWitOut)

  -- inner_to_outer for input
  in_to_out : ∀ outerStmtIn outerWitOut innerWitIn,
    compatWit outerWitOut innerWitIn →
    innerRelIn (lens.projStmt outerStmtIn) innerWitIn →
    outerRelIn outerStmtIn (lensInv.liftWit (outerWitOut, innerWitIn))

namespace ContextLens.IsKnowledgeSound

-- Convert knowledge soundness into soundness

end ContextLens.IsKnowledgeSound

class StatementLens.IsRBRKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop)
    (compatWit : OuterWitOut → InnerWitIn → Prop)
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
  -- TODO: double-check if we need any extra conditions
  extends StatementLens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
        compatStmt compatWit lensInv lens where

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

@[inline, reducible, simp]
def StatementLens.trivial (StmtIn StmtOut : Type) :
    StatementLens StmtIn StmtOut StmtIn StmtOut where
  projStmt := id
  liftStmt := Prod.snd

@[inline, reducible, simp]
def WitnessLens.trivial (WitIn WitOut : Type) : WitnessLens WitIn WitOut WitIn WitOut where
  projWit := id
  liftWit := Prod.snd

@[inline]
def StatementLens.ofInputOnly (OuterStmtIn InnerStmtIn StmtOut : Type)
    (projStmt : OuterStmtIn → InnerStmtIn) :
    StatementLens OuterStmtIn StmtOut InnerStmtIn StmtOut where
  projStmt := projStmt
  liftStmt := Prod.snd

@[inline]
def StatementLens.ofOutputOnly (StmtIn OuterStmtOut InnerStmtOut : Type)
    (liftStmt : InnerStmtOut → OuterStmtOut) :
    StatementLens StmtIn OuterStmtOut StmtIn InnerStmtOut where
  projStmt := id
  liftStmt := liftStmt ∘ Prod.snd

@[inline]
def WitnessLens.ofInputOnly (OuterWitIn InnerWitIn WitOut : Type)
    (projWit : OuterWitIn → InnerWitIn) :
    WitnessLens OuterWitIn WitOut InnerWitIn WitOut where
  projWit := projWit
  liftWit := Prod.snd

@[inline]
def WitnessLens.ofOutputOnly (WitIn OuterWitOut InnerWitOut : Type)
    (liftWit : InnerWitOut → OuterWitOut) :
    WitnessLens WitIn OuterWitOut WitIn InnerWitOut where
  projWit := id
  liftWit := liftWit ∘ Prod.snd

@[inline]
def ContextLens.ofInputOnly (OuterStmtIn InnerStmtIn StmtOut : Type)
    (OuterWitIn InnerWitIn WitOut : Type)
    (projStmt : OuterStmtIn → InnerStmtIn)
    (projWit : OuterWitIn → InnerWitIn) :
    ContextLens OuterStmtIn StmtOut InnerStmtIn StmtOut
                OuterWitIn WitOut InnerWitIn WitOut where
  toStatementLens := StatementLens.ofInputOnly OuterStmtIn InnerStmtIn StmtOut projStmt
  toWitnessLens := WitnessLens.ofInputOnly OuterWitIn InnerWitIn WitOut projWit

@[inline]
def ContextLens.ofOutputOnly (StmtIn OuterStmtOut InnerStmtOut WitIn OuterWitOut InnerWitOut : Type)
    (liftStmt : InnerStmtOut → OuterStmtOut)
    (liftWit : InnerWitOut → OuterWitOut) :
    ContextLens StmtIn OuterStmtOut StmtIn InnerStmtOut
                WitIn OuterWitOut WitIn InnerWitOut where
  toStatementLens := StatementLens.ofOutputOnly StmtIn OuterStmtOut InnerStmtOut liftStmt
  toWitnessLens := WitnessLens.ofOutputOnly WitIn OuterWitOut InnerWitOut liftWit

@[inline]
def ContextLens.ofInputStmtOnly (OuterStmtIn InnerStmtIn StmtOut WitIn WitOut : Type)
    (projStmt : OuterStmtIn → InnerStmtIn) :
    ContextLens OuterStmtIn StmtOut InnerStmtIn StmtOut
                WitIn WitOut WitIn WitOut where
  toStatementLens := StatementLens.ofInputOnly OuterStmtIn InnerStmtIn StmtOut projStmt
  toWitnessLens := WitnessLens.trivial WitIn WitOut

@[inline]
def ContextLens.ofOutputStmtOnly (StmtIn OuterStmtOut InnerStmtOut WitIn WitOut : Type)
    (liftStmt : InnerStmtOut → OuterStmtOut) :
    ContextLens StmtIn OuterStmtOut StmtIn InnerStmtOut
                WitIn WitOut WitIn WitOut where
  toStatementLens := StatementLens.ofOutputOnly StmtIn OuterStmtOut InnerStmtOut liftStmt
  toWitnessLens := WitnessLens.trivial WitIn WitOut

@[inline]
def ContextLens.ofInputWitOnly (StmtIn StmtOut OuterWitIn InnerWitIn WitOut : Type)
    (projWit : OuterWitIn → InnerWitIn) :
    ContextLens StmtIn StmtOut StmtIn StmtOut
                OuterWitIn WitOut InnerWitIn WitOut where
  toStatementLens := StatementLens.trivial StmtIn StmtOut
  toWitnessLens := WitnessLens.ofInputOnly OuterWitIn InnerWitIn WitOut projWit

@[inline]
def ContextLens.ofOutputWitOnly (StmtIn StmtOut WitIn OuterWitOut InnerWitOut : Type)
    (liftWit : InnerWitOut → OuterWitOut) :
    ContextLens StmtIn StmtOut StmtIn StmtOut
                WitIn OuterWitOut WitIn InnerWitOut where
  toStatementLens := StatementLens.trivial StmtIn StmtOut
  toWitnessLens := WitnessLens.ofOutputOnly WitIn OuterWitOut InnerWitOut liftWit



end SpecialCases

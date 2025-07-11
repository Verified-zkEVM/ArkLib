/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Lens
import ArkLib.ToVCVio.Oracle

/-!
  # Lenses for Oracle Reductions

  This file defines the `OracleStatement.Lens` and `OracleContext.Lens` that are necessary to lift
  the context of oracle reductions.

  Defining lenses in this setting is more complicated than in the non-oracle setting, because we
  need to provide two separate components, mappings on the underlying data and oracle simulations on
  the oracle interfaces. We also need those two components to be compatible with each other.
-/

open OracleSpec OracleComp OracleInterface

namespace OracleStatement

variable (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
  {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type)
  [Outer_Oₛᵢ : ∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type)
  [Outer_Oₛₒ : ∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type)
  [Inner_Oₛᵢ : ∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
  [Inner_Oₛₒ : ∀ i, OracleInterface (InnerOStmtOut i)]

namespace Lens

/-- A lens for transporting input and output statements (both oracle and non-oracle) for the
    prover of an oracle reduction. This operates on the underlying data. -/
@[inline, reducible]
def Prover :=
    Statement.Lens (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
                  (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)

namespace Prover

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
  (lensP : Prover OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                  OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)

/-- Projection for the main statement part for the prover's lens. -/
@[inline, reducible]
def projStmt : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtIn :=
  Prod.fst ∘ lensP.proj

/-- Projection for the oracle statement part for the prover's lens. -/
@[inline, reducible]
def projOStmt : OuterStmtIn × (∀ i, OuterOStmtIn i) → ∀ i, InnerOStmtIn i :=
  Prod.snd ∘ lensP.proj

/-- Lifting for the main statement part for the prover's lens. -/
@[inline, reducible]
def liftStmt : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
    OuterStmtOut :=
  fun a b => (lensP.lift a b).1

/-- Lifting for the oracle statement part for the prover's lens. -/
@[inline, reducible]
def liftOStmt : OuterStmtIn × (∀ i, OuterOStmtIn i) → InnerStmtOut × (∀ i, InnerOStmtOut i) →
    ∀ i, OuterOStmtOut i :=
  fun a b => (lensP.lift a b).2

end Prover

/-- The lens for transporting the oracle statements for the oracle verifier.

Unlike the one for the prover, this only has the simulation for the oracles corresponding to the
oracle statements, and not actual functions returning the underlying data.

We will define a compatibility condition between the two (map on data and oracle simulation). -/
structure Verifier where
  /-- Projection of the outer statement to the inner statement, with oracle access to the input
    oracle statement. -/
  projStmt : OuterStmtIn → OracleComp [OuterOStmtIn]ₒ InnerStmtIn

  /-- Projection of the outer oracle statement to the inner oracle statement, which takes in the
    outer input (non-oracle) statement and returns a simulation of the inner oracle statement in
    terms of the outer oracle statement. -/
  projOStmt : OuterStmtIn → QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)

  /-- Lifting of the outer statement to the inner statement, with oracle access to the input
    oracle statement. -/
  liftStmt : OuterStmtIn → InnerStmtOut →
    OracleComp ([OuterOStmtIn]ₒ ++ₒ [InnerOStmtOut]ₒ) OuterStmtOut

  liftOStmt : OuterStmtIn → InnerStmtOut → QueryImpl [OuterOStmtOut]ₒ
    (OracleComp ([OuterOStmtIn]ₒ ++ₒ [InnerOStmtOut]ₒ))

/-- The oracle statement lenses for the prover and verifier are **compatible** if the verifier's
oracle-based "simulation" of the statement transformation matches the prover's data-level
"reification" when the oracles are instantiated with the prover's data.

This is broken down into four conditions:

- `projStmt_compatible`: The verifier's simulated projection of the main statement, when run with
  the actual outer oracle data, must produce the same inner statement as the prover's direct
  data-level projection.

- `projOStmt_compatible`: Querying the verifier's *simulated* inner oracle statement must yield the
  same response as querying the *actual* inner oracle data produced by the prover's lens.

- `liftStmt_compatible`: The verifier's simulated lift of the main statement, when run with the
  actual outer input and inner output oracle data, must produce the same outer output statement as
  the prover's direct data-level lift.

- `liftOStmt_compatible`: Querying the verifier's *simulated* outer output oracle statement must
  yield the same response as querying the *actual* outer output oracle data produced by the prover's
  lens. -/
class IsCompatible
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
    [Outer_Oₛᵢ : ∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
    [Outer_Oₛₒ : ∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
    [Inner_Oₛᵢ : ∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
    [Inner_Oₛₒ : ∀ i, OracleInterface (InnerOStmtOut i)]
    (lensP : Prover OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)
    (lensV : Verifier OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                          OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut) where

  projStmt : ∀ outerStmtIn outerOStmtIn,
    runWithOracle (fun i => oracle (outerOStmtIn i)) (lensV.projStmt outerStmtIn)
      = some (lensP.projStmt ⟨outerStmtIn, outerOStmtIn⟩)

  projOStmt : ∀ outerStmtIn outerOStmtIn i t,
    runWithOracle (fun i => oracle (outerOStmtIn i))
      (simulateQ (lensV.projOStmt outerStmtIn) (query (spec := [InnerOStmtIn]ₒ) i t))
      = some ((Inner_Oₛᵢ i).oracle ((lensP.projOStmt ⟨outerStmtIn, outerOStmtIn⟩) i) t)

  liftStmt : ∀ outerStmtIn outerOStmtIn innerStmtOut innerOStmtOut,
    runWithOracle
      (fun i => match i with
        | .inl j => oracle (outerOStmtIn j)
        | .inr j => oracle (innerOStmtOut j))
      (lensV.liftStmt outerStmtIn innerStmtOut)
      = some (lensP.liftStmt ⟨outerStmtIn, outerOStmtIn⟩ ⟨innerStmtOut, innerOStmtOut⟩)

  liftOStmt : ∀ outerStmtIn outerOStmtIn innerStmtOut innerOStmtOut i t,
    runWithOracle (fun i => match i with
      | .inl j => oracle (outerOStmtIn j)
      | .inr j => oracle (innerOStmtOut j))
        (simulateQ (lensV.liftOStmt outerStmtIn innerStmtOut)
          (query (spec := [OuterOStmtOut]ₒ) i t))
      = some
        ((Outer_Oₛₒ i).oracle
          ((lensP.liftOStmt ⟨outerStmtIn, outerOStmtIn⟩ ⟨innerStmtOut, innerOStmtOut⟩) i) t)

end Lens

structure Lens where
  prover : Lens.Prover OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  verifier : Lens.Verifier OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
  [is_compatible : Lens.IsCompatible prover verifier]

attribute [instance] Lens.is_compatible

namespace Lens

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type}
  [Outer_Oₛᵢ : ∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type}
  [Outer_Oₛₒ : ∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type}
  [Inner_Oₛᵢ : ∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type}
  [Inner_Oₛₒ : ∀ i, OracleInterface (InnerOStmtOut i)]
  (lens : Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut)

/-- Convert the oracle statement lens to a statement lens. -/
@[inline, reducible]
def toStatement : Statement.Lens
    (OuterStmtIn × (∀ i, OuterOStmtIn i)) (OuterStmtOut × (∀ i, OuterOStmtOut i))
    (InnerStmtIn × (∀ i, InnerOStmtIn i)) (InnerStmtOut × (∀ i, InnerOStmtOut i)) :=
  lens.prover

end Lens

end OracleStatement

/-- A structure collecting a lens for the prover, and a lens for the oracle verifier, for
  transporting between the contexts of an outer oracle reduction and an inner oracle reduction. -/
structure OracleContext.Lens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type)
    [Outer_Oₛᵢ : ∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type)
    [Outer_Oₛₒ : ∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type)
    [Inner_Oₛᵢ : ∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type)
    [Inner_Oₛₒ : ∀ i, OracleInterface (InnerOStmtOut i)]
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
  fun ctxIn => ⟨lens.stmt.prover.proj ctxIn.1, lens.wit.proj ctxIn⟩

/-- Lifting of the context. -/
@[inline, reducible]
def lift : (OuterStmtIn × (∀ i, OuterOStmtIn i)) × OuterWitIn →
    (InnerStmtOut × (∀ i, InnerOStmtOut i)) × InnerWitOut →
    (OuterStmtOut × (∀ i, OuterOStmtOut i)) × OuterWitOut :=
  fun ctxIn ctxOut => ⟨lens.stmt.prover.lift ctxIn.1 ctxOut.1, lens.wit.lift ctxIn ctxOut⟩

/-- Convert the oracle context lens to a context lens. -/
@[inline, reducible]
def toContext :
    Context.Lens (OuterStmtIn × (∀ i, OuterOStmtIn i)) (OuterStmtOut × (∀ i, OuterOStmtOut i))
                (InnerStmtIn × (∀ i, InnerOStmtIn i)) (InnerStmtOut × (∀ i, InnerOStmtOut i))
                OuterWitIn OuterWitOut InnerWitIn InnerWitOut :=
  ⟨lens.stmt.prover, lens.wit⟩

end OracleContext.Lens

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
  Statement.Lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut compatStmt lens.prover

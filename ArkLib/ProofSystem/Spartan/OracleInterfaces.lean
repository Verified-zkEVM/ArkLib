/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Types
import ArkLib.Data.MvPolynomial.Multilinear

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

section OracleInterfaces

variable (R : Type) [BEq R] [CommRing R] [IsDomain R] [Fintype R] [LawfulBEq R]
  [Nontrivial R] (pp : PublicParams)

/-- Matrix oracles are queried by evaluating their multilinear extensions at a
constraint point and a variable point. -/
instance instOracleInterfaceInputOracleFamily :
    ∀ i, OracleInterface (InputOracleFamily R pp i) :=
  fun _ => {
    Query := (Fin pp.ℓ_m → R) × (Fin pp.ℓ_n → R)
    toOC.spec := fun _ => R
    toOC.impl := fun ⟨x, y⟩ => do
      return MvPolynomial.eval y (MvPolynomial.eval (MvPolynomial.C ∘ x) (← read).toMLE)
  }

/-- The witness oracle is queried by evaluating the witness multilinear
extension. -/
instance instOracleInterfaceWitness :
    OracleInterface (Witness R pp) where
  Query := Fin pp.ℓ_w → R
  toOC.spec := fun _ => R
  toOC.impl := fun evalPoint => do
    return (MLE ((← read) ∘ finFunctionFinEquiv)) ⸨evalPoint⸩

/-- Oracle interface for the combined matrix-plus-witness oracle family. -/
instance instOracleInterfaceWithWitnessOracleFamily :
    ∀ i, OracleInterface (WithWitnessOracleFamily R pp i)
  | .inl i => instOracleInterfaceInputOracleFamily R pp i
  | .inr _ => instOracleInterfaceWitness R pp

/-- The virtual first sum-check oracle is queried by evaluation point. -/
instance instOracleInterfaceFirstSumcheckOracleFamily :
    ∀ i, OracleInterface (FirstSumcheckOracleFamily R pp i) :=
  fun _ => inferInstance

/-- The virtual second sum-check oracle is queried by evaluation point. -/
instance instOracleInterfaceSecondSumcheckOracleFamily :
    ∀ i, OracleInterface (SecondSumcheckOracleFamily R pp i) :=
  fun _ => inferInstance

end OracleInterfaces

end

end OracleLayer

end Spartan

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Algebra.Identities
import ArkLib.ProofSystem.Spartan.Algebra.Layout
import Mathlib.Data.ZMod.Basic

/-! Small-field checks of rectangular R1CS embedding and Spartan's polynomial boundary. -/

namespace SpartanTest

open MvPolynomial Spartan

/-- Five public variables and one witness variable, with three constraints. -/
abbrev sourceSize : R1CS.Size := ⟨3, 6, 1, by decide⟩

/-- Six public variables and two witness variables, with four constraints. -/
abbrev params : PublicParams := ⟨2, 3, 1, by decide⟩

def input : R1CS.Statement (ZMod 5) sourceSize := ![2, 1, 0, 0, 0]

def matrices : ∀ i, R1CS.OracleStatement (ZMod 5) sourceSize i
  | .A => fun _ j => if j = 0 then 1 else 0
  | .B => fun _ j => if j = 5 then 1 else 0
  | .C => fun _ j => if j = 1 then 1 else 0

def witness : R1CS.Witness (ZMod 5) sourceSize := ![3]

abbrev paddedInput := R1CS.embedStatement (ZMod 5) sourceSize params.toSizeR1CS input

abbrev paddedMatrices := R1CS.embedMatrices (ZMod 5) sourceSize params.toSizeR1CS matrices

/-- The unused witness coordinate may be nonzero. -/
def paddedWitness : R1CS.Witness (ZMod 5) params.toSizeR1CS := ![3, 4]

def badWitness : R1CS.Witness (ZMod 5) params.toSizeR1CS := ![2, 4]

example : R1CS.relation (ZMod 5) sourceSize input matrices witness := by decide

example : R1CS.pullbackWitness (ZMod 5) sourceSize params.toSizeR1CS (by decide)
    paddedWitness = witness := by decide

example : R1CS.relation (ZMod 5) params.toSizeR1CS
    paddedInput paddedMatrices paddedWitness := by
  apply (R1CS.relation_embed_iff (ZMod 5) sourceSize params.toSizeR1CS
    (by decide) (by decide) (by decide) input matrices paddedWitness).mpr
  decide

example : ¬ R1CS.relation (ZMod 5) params.toSizeR1CS
    paddedInput paddedMatrices badWitness := by
  rw [R1CS.relation_embed_iff (ZMod 5) sourceSize params.toSizeR1CS
    (by decide) (by decide) (by decide) input matrices badWitness]
  decide

example : ∀ b : Fin 2 → Fin 2,
    eval (b : Fin 2 → ZMod 5)
      (Algebra.residual paddedMatrices (R1CS.𝕫 paddedInput paddedWitness)) = 0 := by
  apply (Algebra.residual_zero_iff_r1cs 2 (by decide)
    paddedInput paddedMatrices paddedWitness).mpr
  decide

example : Algebra.residualMLE paddedMatrices (R1CS.𝕫 paddedInput paddedWitness) = 0 := by
  apply (Algebra.residualMLE_zero_iff_r1cs 2 (by decide)
    paddedInput paddedMatrices paddedWitness).mpr
  decide

example : Algebra.residualMLE paddedMatrices (R1CS.𝕫 paddedInput badWitness) ≠ 0 := by
  intro h
  have hs := (Algebra.residualMLE_zero_iff_r1cs 2 (by decide)
    paddedInput paddedMatrices badWitness).mp h
  revert hs
  decide

example : R1CS.relation (ZMod 5) (PublicParams.forSize sourceSize).toSizeR1CS
    (Spartan.embedStatement sourceSize input) (Spartan.embedMatrices sourceSize matrices)
    (Spartan.embedWitness sourceSize witness) := by
  rw [Spartan.embedding_preserves_relation]
  decide

example : Spartan.pullbackWitness sourceSize (Spartan.embedWitness sourceSize witness) =
    witness := Spartan.pullback_embedWitness _ _

-- Execution exercises column relocation and the witness pullback.
/-- info: true -/
#guard_msgs in
#eval (paddedMatrices .B (0 : Fin 4) (6 : Fin 8) : ZMod 5) == 1
/-- info: true -/
#guard_msgs in
#eval (paddedMatrices .B (0 : Fin 4) (5 : Fin 8) : ZMod 5) == 0
/-- info: true -/
#guard_msgs in
#eval (R1CS.embedWitness (ZMod 5) sourceSize params.toSizeR1CS witness (1 : Fin 2) : ZMod 5) == 0
/-- info: true -/
#guard_msgs in
#eval (R1CS.pullbackWitness (ZMod 5) sourceSize params.toSizeR1CS (by decide)
  paddedWitness 0 : ZMod 5) == 3

end SpartanTest

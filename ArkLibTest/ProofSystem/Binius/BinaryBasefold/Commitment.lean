/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
import ArkLib.ProofSystem.Binius.FRIBinius.Prelude

/-!
# Initial oracle binding and coordinate order

Injectivity covers arbitrary admissible encodings. The two-coordinate fixture additionally
pins the least-significant-bit-first evaluation map, which distinguishes X₀ and X₁ at index 1.
-/

open Binius.BinaryBasefold MvPolynomial

example : MvPolynomial.eval (bitsOfIndex (L := ZMod 2) (n := 2) 1) (X (0 : Fin 2)) = 1 := by
  norm_num [bitsOfIndex]

example : MvPolynomial.eval (bitsOfIndex (L := ZMod 2) (n := 2) 1) (X (1 : Fin 2)) = 0 := by
  norm_num [bitsOfIndex, show Nat.testBit 1 1 = false by decide]

example : (Binius.FRIBinius.hypercubeEquivFin 2).symm (1 : Fin 4) (0 : Fin 2) = 1 := by
  decide

example : (Binius.FRIBinius.hypercubeEquivFin 2).symm (1 : Fin 4) (1 : Fin 2) = 0 := by
  decide

/--
info: 'Binius.BinaryBasefold.firstOracleWitnessConsistent_functional' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms firstOracleWitnessConsistent_functional

/--
info: 'Binius.BinaryBasefold.firstOracleEncoding_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms firstOracleEncoding_injective

/--
info: 'Binius.FRIBinius.binaryBasefold_initialCompatibility_functional' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Binius.FRIBinius.binaryBasefold_initialCompatibility_functional

namespace InitialEncodingControls

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)] [Algebra K L]
variable (β : Fin r → L) [Fact (LinearIndependent K β)] (h_rate : 0 + 0 < r)

/-- Constant-source encoding is injective at source dimension and rate zero. -/
theorem zero_dimension_zero_rate_encoding_injective :
    Function.Injective (firstOracleEncoding K β (ℓ := 0) (𝓡 := 0)
      (h_ℓ_add_R_rate := h_rate)) :=
  firstOracleEncoding_injective K β

/-- An exact constant encoding satisfies compatibility at dimension and rate zero. -/
example (t : MultilinearPoly L 0) :
    FirstOracleWitnessConsistent K β (h_ℓ_add_R_rate := h_rate) t
      (firstOracleEncoding K β (ℓ := 0) (𝓡 := 0) (h_ℓ_add_R_rate := h_rate) t) :=
  firstOracleWitnessConsistent_firstOracleEncoding K β t

/--
info: 'InitialEncodingControls.zero_dimension_zero_rate_encoding_injective' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms zero_dimension_zero_rate_encoding_injective

end InitialEncodingControls

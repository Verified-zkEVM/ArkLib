/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
  # The BLS12-381 scalar prime field

  The 253-bit prime number that divides the order of the BLS12-381 curve.

  This prime has 2-adicity 47.

  ## References

  This is `r` in (https://electriccoin.co/blog/new-snark-curve/).

  See also (https://github.com/ProvableHQ/snarkOS/tree/c9e5f823b8493f8c3a6c43e6f4dfd16173b99957/curves).

-/

namespace BLS12_381

@[reducible]
def scalarFieldSize : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

abbrev ScalarField := ZMod scalarFieldSize

theorem ScalarField_is_prime : Nat.Prime scalarFieldSize := by
  unfold scalarFieldSize
  refine PrattCertificate'.out (p := scalarFieldSize) ⟨7, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 32, 3, 11, 19, 10177, 125527, 859267, 906349 ^ 2, 2508409, 2529403, 52437899,
    254760293 ^ 2] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 32 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 19 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 10177 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 125527 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 859267 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 906349 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 2508409 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 2529403 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 52437899 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 254760293 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

instance : Fact (Nat.Prime scalarFieldSize) := ⟨ScalarField_is_prime⟩

instance : Field ScalarField := ZMod.instField scalarFieldSize

end BLS12_381

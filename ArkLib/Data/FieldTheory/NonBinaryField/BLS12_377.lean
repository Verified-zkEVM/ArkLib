/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
  # The BLS12-377 scalar prime field

  The 253-bit prime number that divides the order of the BLS12-377 curve.

  This prime has 2-adicity 47.

  ## References

  This is called `r` in (https://eprint.iacr.org/2018/962.pdf).

  See also (https://github.com/ProvableHQ/snarkOS/tree/c9e5f823b8493f8c3a6c43e6f4dfd16173b99957/curves).

-/

namespace BLS12_377

@[reducible]
def scalarFieldSize : Nat :=
  8444461749428370424248824938781546531375899335154063827935233455917409239041

abbrev ScalarField := ZMod scalarFieldSize

theorem ScalarField_is_prime : Nat.Prime scalarFieldSize := by
  unfold scalarFieldSize
  refine PrattCertificate'.out (p := scalarFieldSize) ⟨22, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 47, 3, 5, 7, 13, 499, 958612291309063373, 9586122913090633729 ^ 2]
    (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 47 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 7 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 499 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 958612291309063373 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 9586122913090633729 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

instance : Fact (Nat.Prime scalarFieldSize) := ⟨ScalarField_is_prime⟩

instance : Field ScalarField := ZMod.instField scalarFieldSize

end BLS12_377

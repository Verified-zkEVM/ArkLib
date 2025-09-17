/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate


/-!
  # The BN254 scalar prime field
-/

namespace BN254

@[reducible]
def scalarFieldSize : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

abbrev ScalarField := ZMod scalarFieldSize

theorem ScalarField_is_prime : Nat.Prime scalarFieldSize := by
  unfold scalarFieldSize
  refine PrattCertificate'.out (p := scalarFieldSize) ⟨5, (by reduce_mod_char), ?_⟩
  refine .split [2 ^ 28, 3 ^ 2, 13, 29, 983, 11003, 237073, 405928799, 1670836401704629,
    13818364434197438864469338081] (fun r hr => ?_) (by norm_num)
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 28 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 29 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 983 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11003 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 237073 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 405928799 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 1670836401704629 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
    · refine PrattCertificate'.out ⟨2, by reduce_mod_char, ?_⟩
      refine .split [2 ^ 2, 3 ^ 4, 5156902474397] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr <;> rw [hr]
      · exact .prime 2 2 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 4 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 5156902474397 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 13818364434197438864469338081 1 _ ?_ (by reduce_mod_char; decide)
      (by norm_num)
    · refine PrattCertificate'.out ⟨3, by reduce_mod_char, ?_⟩
      refine .split [2 ^ 5, 5, 823, 1593227, 65865678001877903] (fun r hr => ?_) (by norm_num)
      simp at hr
      rcases hr with hr | hr | hr | hr | hr <;> rw [hr]
      · exact .prime 2 5 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 5 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 823 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 1593227 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · refine .prime 65865678001877903 1 _ ?_ (by reduce_mod_char; decide) (by norm_num)
        · refine PrattCertificate'.out ⟨5, by reduce_mod_char, ?_⟩
          refine .split [2, 83, 379, 1637, 639533339] (fun r hr => ?_) (by norm_num)
          simp at hr
          rcases hr with hr | hr | hr | hr | hr <;> rw [hr]
          · exact .prime 2 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 83 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 379 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 1637 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)
          · exact .prime 639533339 1 _ (by pratt) (by reduce_mod_char; decide) (by norm_num)

instance : Fact (Nat.Prime scalarFieldSize) := ⟨ScalarField_is_prime⟩

instance : Field ScalarField := ZMod.instField scalarFieldSize

end BN254

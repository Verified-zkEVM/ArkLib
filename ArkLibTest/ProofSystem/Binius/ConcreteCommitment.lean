/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.FRIBinius.Commitment
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# A concrete FRI-Binius commitment over the field of sixteen elements

All field, basis, rate, and oracle-count parameters are constructed: the binary base is `ZMod 2`,
the packing field is `GaloisField 2 4`, the basis has rank four, and the retained dimension, rate
exponent, and commitment period are respectively two, one, and one. The production commitment
relation has honest witnesses and binds the two nonconstant coordinate polynomials distinctly.
-/

noncomputable section

namespace Binius.ConcreteCommitment

open MvPolynomial Module Sumcheck.Structured

/-- The actual field of sixteen elements used by this acceptance fixture. -/
abbrev PackedField := GaloisField 2 4

local instance : Fintype PackedField := Fintype.ofFinite PackedField
local instance : DecidableEq PackedField := Classical.decEq PackedField
local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨by simpa only [ZMod.ringChar_zmod_n] using Nat.prime_two⟩
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩
local instance : Fact (1 ∣ 2) := ⟨one_dvd 2⟩

/-- A rank-four binary basis, constructed from the proven degree of this finite field. -/
def binaryBasis : Basis (Fin (2 ^ 2)) (ZMod 2) PackedField :=
  Module.finBasisOfFinrankEq _ _ (GaloisField.finrank (p := 2) (by decide))

/-- The concrete field has sixteen elements. -/
theorem field_card : Fintype.card PackedField = 16 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 4 (by decide)

/-- The unchanged production relation, at fully constructed valid parameters. -/
abbrev commitment :=
  FRIBinius.BinaryBasefoldAbstractOStmtIn 2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide)

/-- The production initial oracle family for these parameters. -/
abbrev InitialOracles := ∀ j, commitment.OStmtIn j

/-- The two coordinate polynomials supply distinct nonconstant packed witnesses. -/
def coordinate (j : Fin 2) : MultilinearPoly PackedField 2 :=
  ⟨X j, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    rw [degreeOf_X]
    split <;> omega⟩

/-- A concrete Boolean point separating the two coordinate claims. -/
def separatingPoint (j : Fin 2) : PackedField := if j = 0 then 1 else 0

/-- At the same point the first source claims one and the second source claims zero. -/
theorem coordinate_claims :
    (coordinate 0).val.eval separatingPoint = 1 ∧
      (coordinate 1).val.eval separatingPoint = 0 := by
  simp [coordinate, separatingPoint]

/-- The concrete coordinate polynomials are unequal. -/
theorem coordinates_distinct : coordinate 0 ≠ coordinate 1 := by
  intro h
  have he := congrArg (fun t : MultilinearPoly PackedField 2 => t.val.eval separatingPoint) h
  rw [coordinate_claims.1, coordinate_claims.2] at he
  exact one_ne_zero he

/-- The actual FRI-Binius commitment relation is functional at these concrete parameters. -/
theorem functionality (o : InitialOracles) (t u : MultilinearPoly PackedField 2)
    (ht : commitment.initialCompatibility (t, o))
    (hu : commitment.initialCompatibility (u, o)) : t = u :=
  FRIBinius.binaryBasefold_initialCompatibility_functional
    2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide) o t u ht hu

/-- Every packed polynomial has an honest production oracle family at these parameters. -/
theorem coverage (t : MultilinearPoly PackedField 2) :
    ∃ o : InitialOracles, commitment.initialCompatibility (t, o) :=
  FRIBinius.binaryBasefold_initialCompatibility_coverage
    2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide) t

/-- Construct the actual honest initial oracle family, not an identity commitment. -/
def honestOracle (t : MultilinearPoly PackedField 2) : InitialOracles :=
  FRIBinius.honestPackedOracle 2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide) t

/-- The constructed honest family satisfies the exact production relation. -/
theorem honestOracle_compatible (t : MultilinearPoly PackedField 2) :
    commitment.initialCompatibility (t, honestOracle t) :=
  FRIBinius.honestPackedOracle_compatible 2 PackedField (ZMod 2) binaryBasis 2 1 1 (by decide) t

/-- The two concrete nonconstant polynomials produce different novel-basis codewords. -/
theorem codewords_distinct :
    BinaryBasefold.firstOracleEncoding (ZMod 2) binaryBasis
      (h_ℓ_add_R_rate := show 2 + 1 < 2 ^ 2 by decide) (coordinate 0) ≠
    BinaryBasefold.firstOracleEncoding (ZMod 2) binaryBasis
      (h_ℓ_add_R_rate := show 2 + 1 < 2 ^ 2 by decide) (coordinate 1) :=
  fun h => coordinates_distinct
    (BinaryBasefold.firstOracleEncoding_injective (ZMod 2) binaryBasis h)

/-- The honest commitment to the first nonconstant source cannot also commit to the second. -/
theorem honestOracle_rejects_other_coordinate :
    ¬ commitment.initialCompatibility (coordinate 1, honestOracle (coordinate 0)) := by
  intro h
  exact coordinates_distinct
    (functionality _ _ _ (honestOracle_compatible (coordinate 0)) h)

/-- Both concrete nonconstant sources have honest production commitments. -/
theorem both_coordinates_covered :
    commitment.initialCompatibility (coordinate 0, honestOracle (coordinate 0)) ∧
      commitment.initialCompatibility (coordinate 1, honestOracle (coordinate 1)) :=
  ⟨honestOracle_compatible _, honestOracle_compatible _⟩

/--
info: 'Binius.ConcreteCommitment.functionality'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms functionality

/--
info: 'Binius.ConcreteCommitment.coverage'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coverage

/--
info: 'Binius.ConcreteCommitment.codewords_distinct'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms codewords_distinct

/--
info: 'Binius.ConcreteCommitment.both_coordinates_covered'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms both_coordinates_covered

end Binius.ConcreteCommitment

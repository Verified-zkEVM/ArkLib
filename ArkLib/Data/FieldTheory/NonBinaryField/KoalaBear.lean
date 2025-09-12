/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FieldTheory.NonBinaryField.Basic
import ArkLib.ToMathlib.NumberTheory.PrattCertificate
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
  # KoalaBear Field `2^{31} - 2^{24} + 1`

  This is the field used for lean Ethereum spec.
-/

namespace KoalaBear

@[reducible]
def fieldSize : Nat := 2 ^ 31 - 2 ^ 24 + 1

-- 2130706433
-- #eval fieldSize

abbrev Field := ZMod fieldSize

theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

/-!
  ## Constants

  These are convenience constants to match the Python module:
  - `pBits = 31`
  - `twoAdicity = 24` with `fieldSize - 1 = 2^24 * 127`
-/

@[reducible]
def pBits : Nat := 31

@[reducible]
def twoAdicity : Nat := 24

/-!
  Provide instances so `KoalaBear.Field = ZMod fieldSize` is available as a `Field`
  and as a `NonBinaryField` (char ≠ 2).
-/

instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

instance : _root_.Field Field := ZMod.instField fieldSize

instance : NonBinaryField Field where
  char_neq_2 := by
    -- `decide` can discharge this concrete ZMod equality.
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 31 - 2 ^ 24 + 1)) ≠ 0)

/-!
  ## Two-adicity and roots of unity table

  We record the factorization of `fieldSize - 1` and provide a precomputed table
  of `2^n`-th roots of unity for `0 ≤ n ≤ twoAdicity`.
-/

lemma fieldSize_sub_one_factorization : fieldSize - 1 = 2 ^ twoAdicity * 127 := by
  unfold fieldSize twoAdicity
  decide

/-!
  A table of `2^n`-th roots of unity. The element at index `n` generates the
  multiplicative subgroup of order `2^n`.

  The first entry n = 0 is 1.
-/
def twoAdicGenerators : List Field :=
  [
    (0x1 : Field),
    (0x7F000000 : Field),
    (0x7E010002 : Field),
    (0x6832FE4A : Field),
    (0x8DBD69C : Field),
    (0xA28F031 : Field),
    (0x5C4A5B99 : Field),
    (0x29B75A80 : Field),
    (0x17668B8A : Field),
    (0x27AD539B : Field),
    (0x334D48C7 : Field),
    (0x7744959C : Field),
    (0x768FC6FA : Field),
    (0x303964B2 : Field),
    (0x3E687D4D : Field),
    (0x45A60E61 : Field),
    (0x6E2F4D7A : Field),
    (0x163BD499 : Field),
    (0x6C4A8A45 : Field),
    (0x143EF899 : Field),
    (0x514DDCAD : Field),
    (0x484EF19B : Field),
    (0x205D63C3 : Field),
    (0x68E7DD49 : Field),
    (0x6AC49F88 : Field)
  ]

@[simp] lemma twoAdicGenerators_length : twoAdicGenerators.length = twoAdicity + 1 := by decide

@[simp] lemma twoAdicGenerators_succ_square_eq' (idx : Fin twoAdicity) :
    twoAdicGenerators[idx.val + 1] ^ 2 = twoAdicGenerators[idx] := by
  fin_cases idx
  <;> simp [twoAdicGenerators] <;> decide

@[simp] lemma twoAdicGenerators_succ_square_eq (idx : Nat) (h : idx < twoAdicity) :
    haveI : idx + 1 < twoAdicGenerators.length := by simp [twoAdicGenerators_length, h]
    twoAdicGenerators[idx + 1] ^ 2 = twoAdicGenerators[idx] :=
  twoAdicGenerators_succ_square_eq' ⟨idx, h⟩

/-! Statements requested by the Python spec translation. We leave them with `sorry` proofs
    to be filled later. -/

/-- Fermat-style inversion in `ZMod fieldSize`. -/
lemma inv_eq_pow (a : Field) (ha : a ≠ 0) : a⁻¹ = a ^ (fieldSize - 2) := by
  sorry

/-- Bijectivity of the cube map on the unit group, using `gcd(3, fieldSize-1)=1`. -/
lemma cube_map_bijective :
    Function.Bijective (fun x : (Field)ˣ => x ^ (3 : Nat)) := by
  sorry

/-! The cube map x ↦ x^3 is an automorphism on the multiplicative group because
    `Nat.coprime 3 (fieldSize - 1)` holds. We record the coprimality here. -/
lemma coprime_three_fieldSize_sub_one : Nat.Coprime 3 (fieldSize - 1) := by
  -- Using the explicit factorization and concrete numerals
  simpa [fieldSize_sub_one_factorization, twoAdicity] using
    (by decide : Nat.Coprime 3 (2 ^ 24 * 127))

/-!
  Additional statements matching the Python spec API, left as `sorry` per request.
-/

/-- `twoAdicity` is maximal: `2^(twoAdicity+1)` does not divide `fieldSize - 1`. -/
lemma twoAdicity_maximal : ¬ (2 ^ (twoAdicity + 1)) ∣ (fieldSize - 1) := by
  decide

/-- The precomputed element at index `bits` is a primitive `2^bits`-th root of unity. -/
lemma isPrimitiveRoot_twoAdicGenerator (bits : Fin (twoAdicity + 1)) :
    IsPrimitiveRoot (twoAdicGenerators[bits]) (2 ^ (bits : Nat)) := by
  sorry

/-- As a unit, the precomputed element is a member of `rootsOfUnity (2^bits)`. -/
lemma twoAdicGenerator_unit_mem_rootsOfUnity
    (bits : Fin (twoAdicity + 1)) (h : twoAdicGenerators[bits] ≠ 0) :
    Units.mk0 (twoAdicGenerators[bits]) h ∈ rootsOfUnity (2 ^ (bits : Nat)) (Field) := by
  sorry

/-- The power `(twoAdicGenerators[bits])^(2^bits) = 1`. -/
lemma twoAdicGenerators_pow_twoPow_eq_one (bits : Fin (twoAdicity + 1)) :
    (twoAdicGenerators[bits]) ^ (2 ^ (bits : Nat)) = (1 : Field) := by
  sorry

/-- If `m < bits`, then `(twoAdicGenerators[bits])^(2^m) ≠ 1`. -/
lemma twoAdicGenerators_pow_twoPow_ne_one_of_lt
    {bits : Fin (twoAdicity + 1)} {m : Nat} (hm : m < bits) :
    (twoAdicGenerators[bits]) ^ (2 ^ m) ≠ (1 : Field) := by
  sorry

/-- The order of `twoAdicGenerators[bits]` equals `2^bits`. -/
lemma twoAdicGenerators_order (bits : Fin (twoAdicity + 1)) :
    orderOf (twoAdicGenerators[bits]) = 2 ^ (bits : Nat) := by
  rw [orderOf_eq_of_pow_and_pow_div_prime]
  · simp
  · exact twoAdicGenerators_pow_twoPow_eq_one bits
  · intro m hm hm'
    have : m = 2 := sorry
    rw [this]
    sorry
    -- exact twoAdicGenerators_pow_twoPow_ne_one_of_lt (by sorry)

end KoalaBear

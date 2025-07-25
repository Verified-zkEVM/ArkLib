/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.OracleComp

/-! # The Algebraic Group Model (With Oblivious Sampling)

We attempt to define the algebraic group model. Our mechanization follows recent papers of Jaeger &
 Mohan [JM24](https://link.springer.com/content/pdf/10.1007/978-3-031-68388-6_2) and Lipmaa,
 Parisella, and Siim [LPS24](https://eprint.iacr.org/2024/994.pdf). -/

section AGM

/-- A type is **serializable** if it can be encoded and decoded to a bit string.

This is highly similar but inequivalent to other type classes like `ToString` or `Repr`.

A special case of `Encodable` except that we require all encodings have the same bit-length, and do
not require decoding. -/
class Serializable (α : Type*) where
  len : ℕ
  toBitVec : α → BitVec len

/-- A type is **deserializable** if it can be decoded from a bit string of a given length. -/
class Deserializable (α : Type*) where
  len : ℕ
  fromBitVec : BitVec len → Option α

-- #check LinearMap.mk₂'

-- #check LinearMap.BilinForm.linMulLin

-- #check isCyclic_of_prime_card

-- These imply a finite cyclic group of prime order `p`
variable {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)] (h : Nat.card G = p)

@[ext]
structure GroupRepresentation (prev : List G) (target : G) where
  exponents : List (ZMod p)
  hEq : (prev.zipWith (fun g a => g ^ a.val) exponents).prod = target

-- #print GroupRepresentation

/-- An adversary in the Algebraic Group Model (AGM) may only access group elements via handles.

To formalize this, we let the handles be natural numbers, and assume that they are indices into an
(infinite) array storing potential group elements. -/
def GroupValTable (G : Type*) := Nat → Option G

local instance {α : Type*} : Zero (Option α) where
  zero := none

-- This might be a better abstraction since the type is finite
-- We put `DFinsupp` since it's computable, not sure if really needed (if not we use `Finsupp`)
def GroupVal (G : Type*) := Π₀ _ : Nat, Option G

-- This allows an adversary to perform the group operation on group elements stored at the indices
-- `i` and `j` (if they are both defined), storing the result at index `k`.
def GroupOpOracle : OracleSpec Unit := fun _ => (Nat × Nat × Nat, Unit)

/-- This oracle interface allows an adversary to get the bit encoding of a group element. -/
def GroupEncodeOracle (bitLength : ℕ) : OracleSpec Unit := fun _ => (Nat, BitVec bitLength)

/-- This oracle interface allows an adversary to get the bit encoding of a group element. -/
def GroupDecodeOracle (bitLength : ℕ) (G : Type) : OracleSpec Unit :=
  fun _ => (BitVec bitLength, Option G)

/-- An adversary in the Algebraic Group Model (AGM), given a single group `G` with elements having
    representation size `bitLength`, is a stateful oracle computation with oracle access to the
    `GroupOp` and `GroupEncode` oracles, and the state being the array of group elements (accessed
    via handles).

  How to make the adversary truly independent of the group description? It could have had `G`
  hardwired. Perhaps we need to enforce parametricity, i.e. it should be of type
  `∀ G, Group G → AGMAdversary G bitLength α`? -/
def AGMAdversary (G : Type) (bitLength : ℕ) : Type → Type _ :=
  fun α => StateT (GroupVal G) (OracleComp (GroupOpOracle ++ₒ GroupEncodeOracle bitLength)) α

end AGM

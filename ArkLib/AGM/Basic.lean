/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.Data.GroupTheory.PrimeOrder
import ArkLib.Data.Classes.Serde

/-! # The Algebraic Group Model (With Oblivious Sampling)

We attempt to define the algebraic group model. Our mechanization follows recent papers of Jaeger &
 Mohan [JM24] and Lipmaa, Parisella, and Siim [LPS24].

## References

* [Jaeger, J. and Mohan, D.I., *Generic and algebraic computation models: When AGM proofs transfer
    to the GGM*][JM24]
* [Lipmaa, H., Parisella, R., and Siim, J., *On Knowledge-Soundness of Plonk in ROM from
    Falsifiable Assumptions*][LPS24]
-/

open OracleComp OracleSpec

namespace AGM

@[ext]
structure GroupRepresentation {G : Type*} [Group G] {p : ℕ} (prev : List G) (target : G) where
  exponents : List (ZMod p)
  hEq : (prev.zipWith (fun g a => g ^ a.val) exponents).prod = target

local instance {α : Type*} : Zero (Option α) where
  zero := none

/-- A table of group elements, indexed by `ι`. We allow the table to be partially defined, i.e.
  some indices may not have a group element yet. We also mandate that the table must be finitely
  supported, e.g. via `Finsupp` or `DFinsupp`.

  Note that we use `DFinsupp` for now since it's computable, unlike `Finsupp`. This is just a
  historical incident of mathlib, and we can switch to `Finsupp` if needed. -/
@[reducible]
def GroupValTable (ι : Type*) (G : Type*) := Π₀ _ : ι, Option G

section OracleSpec

variable (ι : Type) (p : ℕ)

/-- The group operation oracle allows an adversary to perform the group operation on group elements
  stored at the indices `i` and `j` (if they are both defined), storing the result at index `k`. -/
@[reducible]
def GroupOpOracle : OracleSpec (ι × ι × ι) := fun _ => Unit

/-- The group exponent oracle allows an adversary to compute the group element at the index `i`
  raised to the power `a`, storing the result at index `j`.

  Technically, this oracle can be implemented with just the group operation oracle, but we allow
  this for faster implementation. -/
@[reducible]
def GroupExpOracle : OracleSpec (ι × ZMod p × ι) := fun _ => Unit

/-- The group equality oracle allows an adversary to check if the group elements stored at the
  indices `i` and `j` are equal. -/
@[reducible]
def GroupEqOracle : OracleSpec (ι × ι) := fun _ => Bool

variable (bitLength : ℕ)

/-- The group encoding oracle allows an adversary to get the bit encoding of a group element. -/
@[reducible]
def GroupEncodeOracle : OracleSpec ι := fun _ => BitVec bitLength

/-- The group decoding oracle allows an adversary to insert a group element corresponding to a
  bit encoding into the table, if the bit encoding is valid. -/
@[reducible]
def GroupDecodeOracle : OracleSpec (BitVec bitLength × ι) := fun _ => Unit

end OracleSpec

section impl

variable {ι : Type} [DecidableEq ι] {G : Type} [Group G] {p : ℕ}

/-- Implementation of the group operation oracle, which changes some underlying table of group
  elements, using the group operation `op`. If the indices `i` and `j` does not contain group
  elements yet, the oracle will fail. -/
def implGroupOpOracle : QueryImpl (GroupOpOracle ι) (StateT (GroupValTable ι G) Option) :=
  fun | ⟨i, j, k⟩ => fun table =>
    match table i, table j with
    | some g₁, some g₂ => some ((), table.update k (some (g₁ * g₂)))
    | _, _ => none

/-- Implementation of the group exponent oracle, which computes the group element at the index `i`
  raised to the power `a`, storing the result at index `j`. This will fail if the index `i` does
  not contain a group element yet. -/
def implGroupExpOracle : QueryImpl (GroupExpOracle ι p) (StateT (GroupValTable ι G) Option) :=
  fun | ⟨i, a, j⟩ => fun table =>
    match table i with
    | some g => some ((), table.update j (some (g ^ a.val)))
    | none => none

/-- Implementation of the group equality oracle, which checks if the group elements at the indices
  `i` and `j` are equal, and leave the table unchanged. -/
def implGroupEqOracle [BEq G] :
    QueryImpl (GroupEqOracle ι) (StateT (GroupValTable ι G) Option) :=
  fun | ⟨i, j⟩ => fun table =>
    match table i, table j with
    | some g₁, some g₂ => some (g₁ == g₂, table)
    | _, _ => none

variable {bitLength : ℕ}

/-- Implementation of the group encoding oracle, which returns the bit encoding of the group element
  at the index `i`, leaving the table unchanged. This will fail if the index `i` does not contain
  a group element yet. -/
def implGroupEncodeOracle [Serialize G (BitVec bitLength)] :
    QueryImpl (GroupEncodeOracle ι bitLength) (StateT (GroupValTable ι G) Option) :=
  fun | i => fun table =>
    match table i with
    | some g => some (serialize g, table)
    | none => none

/-- Implementation of the group decoding oracle, which inserts a group element corresponding to a
  bit encoding into the table, if the bit encoding is valid. This will fail if the bit encoding
  is invalid. -/
def implGroupDecodeOracle [DeserializeOption G (BitVec bitLength)] :
    QueryImpl (GroupDecodeOracle ι bitLength) (StateT (GroupValTable ι G) Option) :=
  fun | (b, i) => fun table =>
    match DeserializeOption.deserialize b with
    | some g => some ((), table.update i (some g))
    | none => none

end impl

/-- An adversary in the Algebraic Group Model (AGM) is defined as follows:

- It is given knowledge of the initial configuration of the group table
- It may use any of the group oracles, including for group operation, group exponentiation, group
  equality testing, and returning group encoding (no decoding of group elements allowed)
- It returns a list of handles specifying the group elements it is supposed to output, and a
  non-group-element result of type `α`

Note: even if the adversary knows the initial group table, it can only output group elements
implicitly, via indices in the table. This means the group element outputs can only be computed via
utilizing the oracles.

TODO: need to be sure this definition is correct.
-/
def Adversary (ι : Type) (G : Type) (p : ℕ) (bitLength : ℕ) (α : Type) : Type _ :=
  ReaderT (GroupValTable ι G)
    (OracleComp (GroupOpOracle ι + GroupExpOracle ι p +
      GroupEqOracle ι + GroupEncodeOracle ι bitLength))
    (List ι × α)

namespace Adversary

variable {ι : Type} [DecidableEq ι] {G : Type} [Group G] [DecidableEq G]
    {p : ℕ} {bitLength : ℕ}
    [Serialize G (BitVec bitLength)] [DeserializeOption G (BitVec bitLength)]
    (α : Type)

/-- Running the adversary on a given table, returning the list of group elements it is supposed to
  output, and the non-group-element result. -/
def run (adversary : Adversary ι G p bitLength α) (table : GroupValTable ι G) : List G × α :=
  sorry

end Adversary

-- How to make the adversary truly independent of the group description? It could have had `G`
-- hardwired.

-- Perhaps we need to enforce parametricity, i.e. it should be of type `∀ G, Group G →
-- AGMAdversary G bitLength α`?

-- TODO: talk about AGM in the pairing setting

end AGM

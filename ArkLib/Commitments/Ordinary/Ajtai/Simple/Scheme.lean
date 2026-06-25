/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.ModuleSIS
import VCVio

/-!
# Simple Ajtai Commitment Scheme

The simple non-hiding Ajtai [Ajt96] commitment over the computable cyclotomic ring `Rq Φ`:
the commitment to a message vector `s` under a public matrix `A` is the matrix–vector
product `A *ᵥ s`. An opening carries no auxiliary data; verification recomputes the
product and, in the bundled `CommitmentScheme`, checks the short-vector predicate `isShort`.

## References

* [Ajtai, M., *Generating Hard Instances of Lattice Problems*][Ajt96]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai.Simple

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- Public parameters: the Ajtai matrix `A`. -/
abbrev PublicParams (rows cols : Nat) := PolyMatrix (Rq Φ) rows cols

/-- Messages: column vectors over `Rq Φ`. -/
abbrev Message (cols : Nat) := PolyVec (Rq Φ) cols

/-- Commitments: row vectors over `Rq Φ`. -/
abbrev Commitment (rows : Nat) := PolyVec (Rq Φ) rows

/-- Deterministically commit by multiplying the public matrix by the message vector. -/
def commit {rows cols : Nat} (A : PublicParams Φ rows cols) (s : Message Φ cols) :
    Commitment Φ rows :=
  A *ᵥ s

/-- The simple Ajtai commitment has no auxiliary opening data. -/
abbrev Opening := Unit

/-- Verify a simple Ajtai opening by checking the matrix product. -/
def verify {rows cols : Nat} [DecidableEq (Commitment Φ rows)]
    (A : PublicParams Φ rows cols) (s : Message Φ cols)
    (c : Commitment Φ rows) (_opening : Opening) : Bool :=
  decide (commit Φ A s = c)

/-- The simple Ajtai commitment as a `CommitmentScheme`.

An opening is accepted only when the message satisfies the short-vector predicate
`isShort` (needed for the binding reduction to Module-SIS): verification checks both
shortness and the matrix product. -/
def commitmentScheme (rows cols : Nat) (isShort : Message Φ cols → Bool)
    [SampleableType (PublicParams Φ rows cols)] [DecidableEq (Commitment Φ rows)] :
    CommitmentScheme (PublicParams Φ rows cols) (Message Φ cols) (Commitment Φ rows) Opening where
  setup := $ᵗ (PublicParams Φ rows cols)
  commit A s := pure (commit Φ A s, ())
  verify A s c opening := isShort s && verify Φ A s c opening

end ArkLib.Lattices.Ajtai.Simple

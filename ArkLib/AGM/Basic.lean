/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.GroupTheory.PrimeOrder

/-! # Algebraic group representations

In a group of prime order `p`, a `GroupRepresentation` of a target element over a finite basis
assigns one `ZMod p` scalar to each basis index such that the product of the basis elements raised
to those scalars is the target. An algebraic adversary reports such a representation alongside each
group element it outputs, as in the algebraic group model of Jaeger and Mohan [JM24] and of
Lipmaa, Parisella, and Siim [LPS24].

## References

* [Jaeger, J. and Mohan, D.I., *Generic and algebraic computation models: When AGM proofs transfer
    to the GGM*][JM24]
* [Lipmaa, H., Parisella, R., and Siim, J., *On Knowledge-Soundness of Plonk in ROM from
    Falsifiable Assumptions*][LPS24]
-/

@[expose] public section

namespace AGM

/-- A representation has exactly one scalar per basis index in a group of prime order `p`.
The order hypothesis makes natural lifts of `ZMod p` scalars respect modular arithmetic;
it also supplies commutativity, so the finite product does not depend on an enumeration. -/
@[ext]
structure GroupRepresentation {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)]
    [PrimeOrderWith G p] {ι : Type*} [Fintype ι] (basis : ι → G) (target : G) where
  exponents : ι → ZMod p
  hEq : (∏ i, basis i ^ (exponents i).val) = target

namespace GroupRepresentation

variable {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)] [PrimeOrderWith G p]

/-- Every group element, including the identity, respects addition of modular scalars. -/
theorem pow_val_add (g : G) (a b : ZMod p) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  have hpow : g ^ ((a.val + b.val) % p) = g ^ (a.val + b.val) := by
    simpa only [PrimeOrderWith.hCard (G := G)] using pow_mod_natCard g (a.val + b.val)
  rw [ZMod.val_add, hpow, pow_add]

/-- A representation's modulus is positive; the `ZMod 0` integer case is excluded. -/
theorem modulus_pos {ι : Type*} [Fintype ι] {basis : ι → G} {target : G}
    (_ : GroupRepresentation (p := p) basis target) : 0 < p :=
  (Fact.out : Nat.Prime p).pos

end GroupRepresentation

end AGM

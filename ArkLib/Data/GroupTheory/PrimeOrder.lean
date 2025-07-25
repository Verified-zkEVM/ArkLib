/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Prime Order Groups

This file defines the `PrimeOrder` type class, which asserts that a group has some prime order `p`.

We also define the unbundled version, `PrimeOrderWith`, which has the prime order `p` as an explicit
output parameter. -/

/-- Type class for a group with an (implicit) prime order `p`. -/
class PrimeOrder (G : Type*) [Group G] where
  p : ℕ
  [hPrime : Fact (Nat.Prime p)]
  hCard : Nat.card G = p

namespace PrimeOrder

variable {G : Type*} [Group G] [PrimeOrder G]

instance : Fact (Nat.Prime (PrimeOrder.p G)) :=
  PrimeOrder.hPrime

instance : IsCyclic G :=
  isCyclic_of_prime_card PrimeOrder.hCard

instance : CommGroup G := IsCyclic.commGroup

end PrimeOrder

/-- Type class for a group with a prime order `p` as an explicit output parameter. -/
class PrimeOrderWith (G : Type*) [Group G] (p : outParam ℕ) [Fact (Nat.Prime p)] where
  hCard : Nat.card G = p

namespace PrimeOrderWith

variable {G : Type*} [Group G] {p : outParam ℕ} [Fact (Nat.Prime p)] [PrimeOrderWith G p]

instance : PrimeOrder G where
  p := p
  hCard := PrimeOrderWith.hCard

end PrimeOrderWith

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Prime Order Groups

This file defines the `PrimeOrder` type class, which asserts that a group has some prime order `p`.

Note: this is just a wrapper around `isCyclic_of_prime_card` -/

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

end PrimeOrder

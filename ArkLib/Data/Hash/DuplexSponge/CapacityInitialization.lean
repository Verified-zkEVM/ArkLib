/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.Data.Hash.DuplexSponge.Initialization

/-!
# Capacity-seeded initialization

This layout places an encoded session identifier at the start of the capacity and fills the rate
and remaining capacity with zeros. Callers supply the encoding and prove that it fits in the
capacity. The ideal hash-oracle `start` and rate-absorbing `absorbInitialObject` are separate
initializers.
-/

@[expose] public section

namespace DuplexSponge

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- Seed the capacity with an encoded session identifier. -/
def capacityInit (encoded : List U) (_fits : encoded.length ≤ SpongeSize.C) :
    CanonicalDuplexSponge U where
  state := Vector.ofFn fun i =>
    if SpongeSize.R ≤ i.val then encoded[i.val - SpongeSize.R]?.getD 0 else 0
  absorbPos := 0
  squeezePos := Fin.last SpongeSize.R

/-- Initialization does not absorb any rate elements. -/
@[simp] theorem capacityInit_absorbPos (encoded : List U)
    (fits : encoded.length ≤ SpongeSize.C) :
    (capacityInit encoded fits).absorbPos.val = 0 := rfl

/-- The first nonempty squeeze must evaluate the permutation. -/
@[simp] theorem capacityInit_squeezePos (encoded : List U)
    (fits : encoded.length ≤ SpongeSize.C) :
    (capacityInit encoded fits).squeezePos.val = SpongeSize.R := rfl

/-- Every rate element is initially zero. -/
theorem capacityInit_rate_zero (encoded : List U) (fits : encoded.length ≤ SpongeSize.C)
    (i : Nat) (hi : i < SpongeSize.R) :
    (capacityInit encoded fits).state[i]'(by have := SpongeSize.R_lt_N; omega) = 0 := by
  simp [capacityInit, Nat.not_le.mpr hi]

/-- The encoded identifier occupies the prefix of the capacity. -/
theorem capacityInit_encoded (encoded : List U) (fits : encoded.length ≤ SpongeSize.C)
    (i : Nat) (hi : i < encoded.length) :
    (capacityInit encoded fits).state[SpongeSize.R + i]'(by
      have := SpongeSize.R_plus_C_eq_N; omega) = encoded[i] := by
  simp [capacityInit, List.getElem?_eq_getElem hi]

/-- Capacity elements after the encoding remain zero. -/
theorem capacityInit_unused_zero (encoded : List U) (fits : encoded.length ≤ SpongeSize.C)
    (i : Nat) (hi : i < SpongeSize.N) (hAfter : SpongeSize.R + encoded.length ≤ i) :
    (capacityInit encoded fits).state[i] = 0 := by
  have hRate : SpongeSize.R ≤ i := by omega
  have hLen : encoded.length ≤ i - SpongeSize.R := by omega
  simp [capacityInit, hRate, List.getElem?_eq_none hLen]

end DuplexSponge

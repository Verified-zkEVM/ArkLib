/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ProfileCoordinates

/-!
# Profile inverse laws exclude collapsed carriers

A finite profile carrier has exactly `|L| ^ (2 ^ κ)` elements. So no profile of positive rank
over a finite nontrivial `L` uses `L` itself as its carrier: an automorphism or trace switch
with `A = L` cannot satisfy the inverse laws, however its coordinate maps are chosen.
-/

open RingSwitching

namespace ArkLibTest.RingSwitchingProfileCoordinates

/-- A nontrivial finite `L` is never its own positive-rank profile carrier. -/
theorem no_collapsed_carrier {B L : Type} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
    [Finite L] [Nontrivial L] (P : RingSwitchingProfile B L (κ + 1))
    (e : P.A ≃ L) : False := by
  have : Fintype L := Fintype.ofFinite L
  let : Fintype P.A := Fintype.ofEquiv L e.symm
  have hcard := P.card_A
  rw [Fintype.card_congr e] at hcard
  have h1 : 1 < Fintype.card L := Fintype.one_lt_card
  have h2 : 1 < 2 ^ (κ + 1) := Nat.one_lt_two_pow (Nat.succ_ne_zero κ)
  have := Nat.pow_lt_pow_right h1 h2
  rw [pow_one] at this
  omega

end ArkLibTest.RingSwitchingProfileCoordinates

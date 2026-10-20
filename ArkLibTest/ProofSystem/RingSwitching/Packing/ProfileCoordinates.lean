/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ProfileCoordinates
import ArkLib.ProofSystem.RingSwitching.Packing.Algebra

/-!
# Profile inverse laws exclude collapsed carriers

A finite profile carrier has exactly `|L| ^ (2 ^ κ)` elements. So no profile of positive rank
over a finite nontrivial `L` uses `L` itself as its carrier: an automorphism or trace switch
with `A = L` cannot satisfy the inverse laws, however its coordinate maps are chosen.
-/

open Module TensorProduct RingSwitching

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

noncomputable section

/-- Non-domain coefficients and a genuine rank-two extension need no field instances. -/
private def nonDomainProfile : RingSwitchingProfile (ZMod 4) (Fin 2 → ZMod 4) 1 :=
  tensorProductProfile 1 (ZMod 4) (Fin 2 → ZMod 4)
    ((Pi.basisFun (ZMod 4) (Fin 2)).reindex (Equiv.funUnique (Fin 1) (Fin 2)).symm)

example : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) * 2 = 0 := by decide

/-- The presentation map respects the left factor over a ring with zero divisors. -/
example (x : Fin 2 → ZMod 4) :
    nonDomainProfile.tensorEquiv (x ⊗ₜ[ZMod 4] 1) = nonDomainProfile.φ₀ x := by
  simp

/-- The presentation map respects the distinct right factor as well. -/
example (y : Fin 2 → ZMod 4) :
    nonDomainProfile.tensorEquiv (1 ⊗ₜ[ZMod 4] y) = nonDomainProfile.φ₁ y := by
  simp

/-- Rank one (`κ = 0`) also admits the tensor presentation, over any commutative ring. -/
example (B : Type) [CommRing B] : RingSwitchingProfile B B 0 :=
  tensorProductProfile 0 B B
    ((Basis.singleton Unit B).reindex (Equiv.ofUnique Unit (Fin 0 → Fin 2)))

/-- The abstract isomorphism preserves arbitrary finite sums of pure tensors. -/
example {B L : Type} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
    (P : RingSwitchingProfile B L κ) {ι : Type} (s : Finset ι) (x y : ι → L) :
    P.tensorEquiv (∑ i ∈ s, x i ⊗ₜ[B] y i) = ∑ i ∈ s, P.φ₀ (x i) * P.φ₁ (y i) := by
  simp

end

end ArkLibTest.RingSwitchingProfileCoordinates

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.SystemEnumeration
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Number of emitted square systems

The paper tries every r-element selection from n agreement rows and K-k coefficient tails.
Coincident rows may produce the same system, so the executable family has at most the binomial
number of selections. When K ≤ n this is at most (2n)^r. This counts systems only; it does not
assert an arithmetic cost for constructing or solving them.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

/-- Deduplication can only decrease the number of r-subset systems. -/
theorem card_enumerateSquareSystems_le_choose {P ι : Type*}
    [DecidableEq P] [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) :
    (enumerateSquareSystems r initial pool).card ≤ (Fintype.card ι).choose r := by
  unfold enumerateSquareSystems
  calc
    _ ≤ (rowSubsets ι r).attach.card := Finset.card_image_le
    _ = (Fintype.card ι).choose r := by simp [rowSubsets]

/-- A coarser power bound suitable for later size estimates. -/
theorem card_enumerateSquareSystems_le_pow {P ι : Type*}
    [DecidableEq P] [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) :
    (enumerateSquareSystems r initial pool).card ≤ (Fintype.card ι) ^ r :=
  (card_enumerateSquareSystems_le_choose r initial pool).trans (Nat.choose_le_pow _ _)

local instance sumFinOrderForCardinality (a b : ℕ) : LinearOrder (Fin a ⊕ Fin b) :=
  finSumFinEquiv.linearOrder

/-- The full agreement-and-tail pool contains at most 2n labels when K ≤ n. -/
theorem card_fullPoolSystems_le {P : Type*} [DecidableEq P]
    (r n K k : ℕ) (hK : K ≤ n) (initial : P) (pool : Fin n ⊕ Fin (K - k) → P) :
    (enumerateSquareSystems r initial pool).card ≤ (2 * n) ^ r := by
  apply (card_enumerateSquareSystems_le_pow r initial pool).trans
  apply Nat.pow_le_pow_left
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end ReedSolomon.HiddenDerivative.SquareSystems

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import ArkLib.Data.CodingTheory.ListDecodability.PairAgreementBound
import ArkLib.Data.CodingTheory.ListDecodability.SymbolMap
import Mathlib.Data.ZMod.Basic

open Code

namespace ListDecodabilityTest

example : (δᵣ((fun _ : Fin 4 ↦ true), ![true, true, true, false]) : ℝ) ≤ 1 / 4 := by
  have h : 3 ≤ agree ![true, true, true, false] (fun _ : Fin 4 ↦ true) := by decide
  have := relHammingDist_le_one_sub_div_of_le_agree h
  norm_num at this
  exact this

example :
    (({![true, true, true]} : Finset (Fin 3 → Bool)).card : ℝ) *
        (((3 : ℕ) : ℝ) ^ 2 - (Fintype.card (Fin 3) : ℝ) * ((0 : ℕ) : ℝ)) ≤
      (Fintype.card (Fin 3) : ℝ) * ((Fintype.card (Fin 3) : ℝ) - ((0 : ℕ) : ℝ)) :=
  card_mul_sq_minAgreement_sub_pairAgreement_le ![true, true, true] {![true, true, true]} 3 0
    (by decide) (by decide) (by decide)

example : ({![true, false, true]} : Finset (Fin 3 → Bool)).card ≤ 1 :=
  card_le_one_of_pairwise_agree_le ![true, false, true] {![true, false, true]} 3 1
    (by decide) (by decide) (by decide)

example :
    ({![true, true, true], ![false, false, false]} : Finset (Fin 3 → Bool)).card * 1 ≤
      Fintype.card (Fin 3) :=
  card_mul_minAgreement_le_of_pairwise_agree_eq_zero ![true, false, true] _ 1
    (by decide) (by decide)

end ListDecodabilityTest

namespace SymbolMapTest

/-- The inclusion of `Bool` into `ZMod 3` as `0, 1`. -/
def boolToZMod3 : Bool → ZMod 3 := fun b ↦ if b then 1 else 0

theorem boolToZMod3_injective : Function.Injective boolToZMod3 := by decide

example :
    (closeCodewordsRel (Set.univ : Set (Fin 1 → Bool)) (fun _ ↦ false) 1).encard ≤
      (closeCodewordsRel (Set.univ : Set (Fin 1 → ZMod 3))
        (boolToZMod3 ∘ fun _ ↦ false) 1).encard :=
  encard_closeCodewordsRel_le_of_injective_comp boolToZMod3_injective
    (fun _ _ ↦ Set.mem_univ _) _ _

example :
    Lambda (Set.univ : Set (Fin 1 → Bool)) 1 ≤ Lambda (Set.univ : Set (Fin 1 → ZMod 3)) 1 :=
  Lambda_le_of_injective_comp boolToZMod3_injective (fun _ _ ↦ Set.mem_univ _) 1

end SymbolMapTest

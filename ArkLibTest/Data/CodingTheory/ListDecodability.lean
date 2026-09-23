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

private def radiusWord : Fin 2 → Bool := ![true, false]

private def radiusCode : Set (Fin 2 → Bool) := {radiusWord}

example : (δᵣ((fun _ : Fin 4 ↦ true), ![true, true, true, false]) : ℝ) ≤ 1 / 4 := by
  have h : 3 ≤ agree ![true, true, true, false] (fun _ : Fin 4 ↦ true) := by decide
  have := relHammingDist_le_one_sub_div_of_le_agree h
  norm_num at this
  exact this

example :
    (δᵣ(radiusWord, radiusWord) : ℝ) ≤ 1 - (2 : ℝ) / 2 ↔
      (2 : ℝ) ≤ Code.agree radiusWord radiusWord := by
  have h := Code.relHammingDist_le_one_sub_div_iff
    (ι := Fin 2) (A := Bool) (by decide) (c := radiusWord) (y := radiusWord) (x := 2)
  norm_num [Code.relHammingDist, hammingDist, Code.agree] at h ⊢

example : radiusWord ∈ Code.closeCodewordsRel radiusCode radiusWord (1 - (2 : ℝ) / 2) := by
  apply Code.mem_closeCodewordsRel_of_le_agree
  · simp [radiusCode]
  · simp [Code.agree]

example : 1 ≤ Code.Lambda radiusCode 0 := by
  have hset :
      {c : Fin 2 → Bool | c ∈ radiusCode ∧ 2 ≤ Code.agree c radiusWord} =
        {radiusWord} := by
    ext c
    by_cases hc : c = radiusWord
    · subst c
      simp [radiusCode, Code.agree]
    · simp [radiusCode, hc]
  have h := Code.encard_setOf_le_agree_le_Lambda radiusCode radiusWord 2
  rw [hset] at h
  simpa using h

private def radiusEncode (b : Bool) : Fin 2 → Bool :=
  if b then radiusWord else ![false, true]

example : 1 ≤ Code.Lambda radiusCode 0 := by
  have hinj : Function.Injective radiusEncode := by
    intro b c h
    cases b <;> cases c <;> simp [radiusEncode, radiusWord] at h ⊢
  have hmem : ∀ b ∈ ({true} : Set Bool), radiusEncode b ∈ radiusCode := by
    intro b hb
    simp only [Set.mem_singleton_iff] at hb
    subst b
    simp [radiusEncode, radiusCode, radiusWord]
  have h := Code.encard_setOf_le_agree_encode_le_Lambda
    (M := Bool) (C := radiusCode) (y := radiusWord) (a := 2)
    (encode := radiusEncode) (S := {true}) hinj.injOn hmem
  have hset :
      {b : Bool | b ∈ ({true} : Set Bool) ∧
        2 ≤ Code.agree (radiusEncode b) radiusWord} = {true} := by
    ext b
    cases b <;> simp [radiusEncode, radiusWord, Code.agree]
  rw [hset] at h
  simpa using h

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

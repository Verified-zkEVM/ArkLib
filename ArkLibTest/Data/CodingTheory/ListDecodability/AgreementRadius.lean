/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.Tactic.NormNum

/-!
# Agreement-radius clients

These clients bound the relative distance of a binary word with three agreements out of four by
`1 / 4`, check the length-zero case, recover a real agreement threshold from a distance bound,
check that the iff form needs a nonempty coordinate type, and show that the message form of the
`Lambda` bound needs injectivity of the encoding: the constant encoding of `Bool` into the code of
length one over `Unit` puts two messages into a list of size one.
-/

open Code

namespace AgreementRadiusTest

-- Three agreements out of four give relative distance at most `1 / 4`.
example : (δᵣ((fun _ : Fin 4 ↦ true), ![true, true, true, false]) : ℝ) ≤ 1 / 4 := by
  have h : 3 ≤ agree ![true, true, true, false] (fun _ : Fin 4 ↦ true) := by decide
  have := relHammingDist_le_one_sub_div_of_le_agree h
  norm_num at this
  exact this

-- Length zero: the radius is `1`.
example (c y : Fin 0 → Bool) (a : ℕ) (h : a ≤ agree c y) : (δᵣ(y, c) : ℝ) ≤ 1 := by
  simpa using relHammingDist_le_one_sub_div_of_le_agree h

-- A real threshold: relative distance at most `1 - (5 / 2) / 4 = 3 / 8` out of four coordinates
-- means at least `5 / 2` agreements.
example (c y : Fin 4 → Bool) (h : (δᵣ(y, c) : ℝ) ≤ 1 - (5 / 2 : ℝ) / 4) :
    (5 / 2 : ℝ) ≤ agree c y := by
  exact (relHammingDist_le_one_sub_div_iff (by simp)).mp (by simpa using h)

-- `0 < n` is needed in the iff: at length zero the distance bound `0 ≤ 1 - 1 / 0` holds, while
-- one agreement is impossible.
example : ¬ ∀ (c y : Fin 0 → Bool),
    ((δᵣ(y, c) : ℝ) ≤ 1 - (1 : ℝ) / Fintype.card (Fin 0) ↔ (1 : ℝ) ≤ agree c y) := by
  intro h
  have := (h Fin.elim0 Fin.elim0).mp (by simp [relHammingDist])
  simp [agree] at this
  norm_num at this

-- The agreement list at threshold `a` lies in the point list at radius `1 - a / n`.
example (C : Set (Fin 4 → Bool)) (y : Fin 4 → Bool) :
    {c | c ∈ C ∧ 3 ≤ agree c y}.encard ≤ Lambda C (1 / 4) := by
  have := encard_setOf_le_agree_le_Lambda C y 3
  norm_num at this
  exact this

-- Injectivity of the encoding is needed.
example : ¬ {m : Bool | m ∈ Set.univ ∧
      0 ≤ agree ((fun _ ↦ fun _ ↦ ()) m : Fin 1 → Unit) (fun _ ↦ ())}.encard ≤
    Lambda (Set.univ : Set (Fin 1 → Unit)) (1 - ((0 : ℕ) : ℝ) / Fintype.card (Fin 1)) := by
  intro h
  have hup : Lambda (Set.univ : Set (Fin 1 → Unit))
      (1 - ((0 : ℕ) : ℝ) / Fintype.card (Fin 1)) ≤ 1 :=
    Lambda_le_iff_forall_encard_le.mpr fun f ↦
      (Set.encard_le_encard (Set.subset_univ _)).trans (by simp)
  have hset : {m : Bool | m ∈ Set.univ ∧
      0 ≤ agree ((fun _ ↦ fun _ ↦ ()) m : Fin 1 → Unit) (fun _ ↦ ())} = Set.univ := by
    ext m
    simp
  rw [hset] at h
  have := h.trans hup
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool] at this
  exact absurd this (by decide)

end AgreementRadiusTest

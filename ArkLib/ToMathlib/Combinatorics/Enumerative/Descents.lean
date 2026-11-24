/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.WellFounded

/-!
# Injective tuples with few descents

A descent of a tuple `f : Fin r → α` is a position `j` with `f (j + 1) < f j`. An injective tuple
with fewer than `m` descents splits into at most `m` strictly increasing runs, so it is determined
by its `r`-element image together with the run of each image element. Hence at most
`(card α).choose r * m ^ r` injective tuples `Fin r ↪ α` have fewer than `m` descents.

## Main definitions

* `Tuple.descents f`: the positions `j` with `f (j + 1) < f j`.

## Main statements

* `Tuple.card_filter_card_descents_lt_le`: at most `(card α).choose r * m ^ r` embeddings
  `Fin r ↪ α` have fewer than `m` descents.

`card_filter_card_descents_lt_le` at `m = 2 ^ t` is the counting step of the certificate count
of [AGL24], where the `r` distinct indices of a certificate lie in at most `2 ^ t` increasing
runs.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

open Finset

namespace Tuple

variable {α : Type*} [LinearOrder α] {r : ℕ}

/-- The descents of a tuple `f : Fin r → α`: the positions `j` with `f (j + 1) < f j`. -/
def descents (f : Fin r → α) : Finset (Fin r) :=
  {j | ∃ h : (j : ℕ) + 1 < r, f ⟨j + 1, h⟩ < f j}

/-- A position `j` is a descent of `f` exactly when `j + 1 < r` and `f (j + 1) < f j`. -/
@[simp]
theorem mem_descents {f : Fin r → α} {j : Fin r} :
    j ∈ descents f ↔ ∃ h : (j : ℕ) + 1 < r, f ⟨j + 1, h⟩ < f j := by
  simp [descents]

/-- The run of position `j`: the number of descents before `j`. -/
private def runIndex (f : Fin r → α) (j : Fin r) : ℕ :=
  #{i ∈ descents f | i < j}

/-- An injective tuple increases lexicographically when each entry is tagged by its run. -/
private theorem strictMono_toLex_runIndex {f : Fin r → α} (hf : Function.Injective f) :
    StrictMono fun j ↦ toLex (runIndex f j, f j) := by
  cases r with
  | zero => exact fun i ↦ i.elim0
  | succ n =>
    refine Fin.strictMono_iff_lt_succ.2 fun i ↦ Prod.Lex.toLex_lt_toLex.2 ?_
    have hsub : {k ∈ descents f | k < i.castSucc} ⊆ {k ∈ descents f | k < i.succ} :=
      monotone_filter_right _ fun k _ h ↦ h.trans i.castSucc_lt_succ
    by_cases hd : i.castSucc ∈ descents f
    · refine .inl (card_lt_card (ssubset_iff_of_subset hsub |>.2 ⟨i.castSucc, ?_, ?_⟩))
      · exact mem_filter.2 ⟨hd, i.castSucc_lt_succ⟩
      · simp
    · refine .inr ⟨congrArg card (subset_antisymm hsub fun k hk ↦ ?_), ?_⟩
      · obtain ⟨hk, hki⟩ := mem_filter.1 hk
        refine mem_filter.2 ⟨hk, lt_of_le_of_ne (Fin.le_castSucc_iff.2 hki) ?_⟩
        rintro rfl
        exact hd hk
      · refine lt_of_le_of_ne (not_lt.1 fun h ↦ hd ?_) (hf.ne i.castSucc_lt_succ.ne)
        exact mem_descents.2 ⟨by simp, h⟩

/-- At most `(card α).choose r * m ^ r` embeddings `Fin r ↪ α` have fewer than `m` descents: such
an embedding is determined by its image and by the run of each image element, the run of the
entry at position `j` being the number of descents before `j`. -/
theorem card_filter_card_descents_lt_le [Fintype α] (r m : ℕ) :
    #{c : Fin r ↪ α | #(descents c) < m} ≤ (Fintype.card α).choose r * m ^ r := by
  classical
  let label (c : Fin r ↪ α) (x : α) : ℕ := ∑ j, if c j = x then runIndex c j else 0
  have hlabel (c : Fin r ↪ α) (j : Fin r) : label c (c j) = runIndex c j := by
    simp [label, c.injective.eq_iff]
  let t (S : Finset α) : Finset (α → ℕ) := Fintype.piFinset fun x ↦ if x ∈ S then range m else {0}
  calc #{c : Fin r ↪ α | #(descents c) < m}
      ≤ #((powersetCard r univ).biUnion fun S ↦ (t S).image (Prod.mk S)) := by
        refine card_le_card_of_injOn (fun c ↦ (univ.map c, label c)) (fun c hc ↦ ?_) ?_
        · refine mem_biUnion.2 ⟨univ.map c, by simp, mem_image.2 ⟨label c, ?_, rfl⟩⟩
          refine Fintype.mem_piFinset.2 fun x ↦ ?_
          split_ifs with hx
          · obtain ⟨j, -, rfl⟩ := mem_map.1 hx
            rw [hlabel, mem_range]
            exact (card_filter_le _ _).trans_lt (mem_filter.1 hc).2
          · refine mem_singleton.2 (sum_eq_zero fun j _ ↦ ite_eq_right_iff.2 fun h ↦ ?_)
            exact (hx (mem_map.2 ⟨j, mem_univ j, h⟩)).elim
        · intro c _ c' _ h
          obtain ⟨hS, hl⟩ := Prod.ext_iff.1 h
          dsimp only at hS hl
          have key := (StrictMono.range_inj_of_wellFoundedLT
            (strictMono_toLex_runIndex c.injective)
            (strictMono_toLex_runIndex c'.injective)).1 <| by
              have hr : Set.range c = Set.range c' := by
                simpa [Set.image_univ] using congrArg (fun S : Finset α ↦ (S : Set α)) hS
              simp only [← hlabel]
              rw [show (fun j ↦ toLex (label c' (c' j), c' j)) =
                  (fun x ↦ toLex (label c x, x)) ∘ c' by rw [hl]; rfl,
                Set.range_comp, ← hr, ← Set.range_comp]
              rfl
          exact DFunLike.ext _ _ fun j ↦ congrArg (fun p ↦ (ofLex p).2) (congrFun key j)
    _ ≤ #(powersetCard r univ) * m ^ r := card_biUnion_le_card_mul _ _ _ fun S hS ↦ by
        refine card_image_le.trans_eq ?_
        rw [Fintype.card_piFinset, prod_congr rfl fun x _ ↦ apply_ite card _ _ _]
        simp only [card_range, card_singleton]
        rw [prod_ite_mem, univ_inter, prod_const, (mem_powersetCard.1 hS).2]
    _ = (Fintype.card α).choose r * m ^ r := by rw [card_powersetCard, card_univ]

end Tuple

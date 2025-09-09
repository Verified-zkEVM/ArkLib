/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import ArkLib.Data.Fin.Basic

noncomputable section

variable {F : Type*}
         {ι : Type*} [Fintype ι]
         {ι' : Type*} [Fintype ι']
         {m n : ℕ}

namespace Matrix

def neqCols [DecidableEq F] (U V : Matrix ι ι' F) : Finset ι' :=
  {j | ∃ i : ι, V i j ≠ U i j}

section

variable [Semiring F] (U : Matrix ι ι' F)

def rowSpan : Submodule F (ι' → F) :=
  Submodule.span F {U i | i : ι}

def rowRank : ℕ :=
  Module.finrank F (rowSpan U)

def colSpan : Submodule F (ι → F) :=
  Submodule.span F {Matrix.transpose U i | i : ι'}

def colRank : ℕ :=
  Module.finrank F (colSpan U)

end

section

def subUpFull (U : Matrix (Fin m) (Fin n) F) (r_reindex : Fin n → Fin m) :
  Matrix (Fin n) (Fin n) F := Matrix.submatrix U r_reindex id

def subLeftFull (U : Matrix (Fin m) (Fin n) F) (c_reindex : Fin m → Fin n) :
  Matrix (Fin m) (Fin m) F := Matrix.submatrix U id c_reindex

variable [CommRing F]
         {U : Matrix (Fin m) (Fin n) F}

lemma rank_eq_min_row_col_rank  :
  U.rank = min (rowRank U) (colRank U) := by sorry

lemma rank_eq_iff_det_ne_zero {U : Matrix (Fin n) (Fin n) F} :
  U.rank = n ↔ Matrix.det U ≠ 0 := by sorry

lemma rank_eq_iff_subUpFull_eq (h : n ≤ m) :
  U.rank = n ↔ (subUpFull U (Fin.castLE h)).rank = n := sorry

lemma full_row_rank_via_rank_subLeftFull (h : m ≤ n) :
  U.rank = m ↔ (subLeftFull U (Fin.castLE h)).rank = m := by sorry

end

end Matrix

end

/-- Affine line between two vectors with coefficients in a semiring.
-/
def Affine.line {F : Type*} {ι : Type*} [Ring F] (u v : ι → F) : Submodule F (ι → F) :=
  vectorSpan _ {u, v}

namespace sInf

lemma sInf_UB_of_le_UB {S : Set ℕ} {i : ℕ} : (∀ s ∈ S, s ≤ i) → sInf S ≤ i := fun h ↦ by
  by_cases S_empty : S.Nonempty
  · classical
    rw [Nat.sInf_def S_empty, Nat.find_le_iff]
    choose s hs using S_empty
    aesop
  · aesop (add simp (show S = ∅ by aesop (add simp Set.Nonempty)))

lemma le_sInf_of_LB {S : Set ℕ} (hne : S.Nonempty) {i : ℕ}
    (hLB : ∀ s ∈ S, i ≤ s) : i ≤ sInf S := by
  rw [Nat.sInf_def hne]
  contrapose hLB
  simp at hLB ⊢
  rcases hLB with ⟨s, hsS, hsle⟩
  exact ⟨s, hsle, hsS⟩

end sInf

@[simp]
lemma Fintype.zero_lt_card {ι : Type*} [Fintype ι] [Nonempty ι] : 0 < Fintype.card ι := by
  have := Fintype.card_ne_zero (α := ι); omega

namespace Finset

@[simp]
theorem card_univ_filter_eq {α : Type*} [Fintype α] [DecidableEq α] {e : α} :
  #{x : α | x ≠ e} = #(Finset.univ (α := α)) - 1 := by
  rw [
    Finset.filter_congr (q := (· ∉ ({e} : Finset _))) (by simp),
    ←Finset.sdiff_eq_filter, Finset.card_univ_diff
  ]
  simp

@[simp]
theorem card_prod_self_eq {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α} :
  #(((s ×ˢ s : Finset _) ∩ ({x : α × α | x.1 = x.2} : Finset _)) : Finset _) = #s := by
  rw [Finset.card_eq_of_equiv]
  simp
  exact ⟨
    fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, by tauto⟩,
    (fun ⟨x, _⟩ ↦ by use ⟨x, x⟩),
    by simp [Function.LeftInverse],
    by simp [Function.RightInverse, Function.LeftInverse]
  ⟩

@[simp]
theorem card_filter_prod_self_eq {α : Type*} [Fintype α] [DecidableEq α] {s : Finset α} :
  #({x ∈ s ×ˢ s | x.1 = x.2}) = #s := by
  rw [Finset.card_eq_of_equiv]
  simp
  exact ⟨
    fun ⟨x, _⟩ ↦ ⟨x.1, by tauto⟩,
    fun ⟨x, hx⟩ ↦ ⟨(x, x), by tauto⟩,
    by simp [Function.LeftInverse],
    by simp [Function.LeftInverse, Function.RightInverse]
  ⟩

end Finset

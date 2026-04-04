/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import Mathlib.Analysis.Convex.Jensen
import Mathlib.RingTheory.Binomial

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.JohnsonBound.Choose2
/-! # Johnson Bound Expectations -/


namespace JohnsonBound

open Finset Fintype

variable {n : ℕ}
variable {F : Type*} [DecidableEq F]
         {B : Finset (Fin n → F)} {v : Fin n → F}

@[simp, grind]
def e (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  (1 : ℚ) / B.card * ∑ x ∈ B, Δ₀(v, x)

@[simp, grind]
def d (B : Finset (Fin n → F)) : ℚ :=
  (1 : ℚ) / (2 * choose_2 B.card) * ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2)

@[simp]
lemma lin_shift_card [Field F] [Fintype F] :
    B.card = ({ x - v | x ∈ B } : Finset _).card := by
  apply card_bij (i := fun x _ => x - v) <;> aesop

@[simp]
lemma lin_shift_hamming_distance [Field F] {x₁ x₂ v : Fin n → F} :
    Δ₀(x₁ - v, x₂ - v) = Δ₀(x₁, x₂) := by simp [hammingDist]

@[simp]
lemma lin_shift_e [Field F] [Fintype F] (h_B : B.card ≠ 0) :
    e B v = e ({ x - v | x ∈ B } : Finset _) 0 := by
  simp only [e, one_div, Nat.cast_sum, hammingDist_zero_left]
  rw [← lin_shift_card]
  field_simp
  apply sum_bij (i := fun x _ => x - v) <;>
    simp [hammingDist, hammingNorm, sub_eq_zero, eq_comm]

@[simp]
lemma lin_shift_d [Field F] [Fintype F] (h_B : 2 ≤ B.card) :
    d B = d ({ x - v | x ∈ B } : Finset _) := by
  simp only [d, one_div, mul_inv_rev, ne_eq, Nat.cast_sum]
  rw [← lin_shift_card]
  have h : choose_2 B.card ≠ 0 := by aesop (add simp [choose_2, sub_eq_zero])
  field_simp
  apply sum_bij (fun x _ => (x.1 - v, x.2 - v)) <;> try aesop

@[simp]
lemma e_ball_le_radius [Field F] [Fintype F] {B : Finset (Fin n → F)} (v : Fin n → F) (r : ℚ)
    (h_B : (B ∩ ({ x | Δ₀(x, v) ≤ r } : Finset _)).card > 0) :
    e (B ∩ ({ x | Δ₀(x, v) ≤ r } : Finset _)) v ≤ r := by
  unfold e
  have hamming_symm : ∀ x y : Fin n → F, Δ₀(x, y) = Δ₀(y, x) := by
    unfold hammingDist
    simp_rw [ne_comm]; simp
  simp_rw [hamming_symm v]
  have h1 : ∑ x ∈ B ∩ ({ x | ↑Δ₀(x, v) ≤ r } : Finset _), Δ₀(x, v)
      ≤ ∑ x ∈ B ∩ ({ x | ↑Δ₀(x, v) ≤ r } : Finset _), r := by
    have h : ∀ x ∈ B ∩ ({ x | ↑Δ₀(x, v) ≤ r } : Finset _), Δ₀(x, v) ≤ r := by
      grind only [= mem_inter, = mem_filter]
    exact_mod_cast sum_le_sum h
  have h2 : ∑ x ∈ B ∩ ({ x | ↑Δ₀(x, v) ≤ r } : Finset _), r
      = r * (B ∩ ({ x | ↑Δ₀(x, v) ≤ r } : Finset _)).card := by
    rw [sum_const, mul_comm]; simp
  have h3 : ∑ x ∈ B ∩ ({ x | ↑Δ₀(x, v) ≤ r } : Finset _), Δ₀(x, v)
      ≤ r * (B ∩ ({ x | ↑Δ₀(x, v) ≤ r } : Finset _)).card := by grind only
  field_simp
  have h_B' : (0 : ℚ) < (B ∩ ({ x | Δ₀(x, v) ≤ r } : Finset _)).card :=
    by exact_mod_cast h_B
  exact_mod_cast h3

lemma min_dist_le_d [Field F] {B : Finset (Fin n → F)} (h_B : B.card > 1) :
    sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d } ≤ d B := by
  unfold d
  let d_weak := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  have h_d : ∀ x ∈ { x ∈ B ×ˢ B | x.1 ≠ x.2 }, d_weak ≤ Δ₀(x.1, x.2) := by
    intro x hx
    simp only [ne_eq, mem_filter, mem_product] at hx
    unfold d_weak
    have : Δ₀(x.1, x.2) ∈ { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d } := by
      use x.1, hx.1.1, x.2, hx.1.2
      exact ⟨hx.2, rfl⟩
    apply Nat.sInf_le this
  have B2_card : 2 * choose_2 ↑B.card = { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card := by
    simp only [ne_eq]
    unfold choose_2
    ring_nf
    have BBcard : (B ×ˢ B).card = B.card ^ 2 := by rw [card_product, sq]
    have BBdiagcard : { x ∈ B ×ˢ B | x.1 = x.2 }.card = B.card := by simp
    have BBdisjoint : { x ∈ B ×ˢ B | x.1 = x.2 } ∩ { x ∈ B ×ˢ B | x.1 ≠ x.2 } = ∅ := by
      grind only [= mem_inter, ← notMem_empty, = mem_filter]
    have BBunion : B ×ˢ B = { x ∈ B ×ˢ B | x.1 = x.2 } ∪ { x ∈ B ×ˢ B | x.1 ≠ x.2 } := by
      grind only [= mem_union, = mem_filter]
    have BBcount : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card
        = (B ×ˢ B).card - { x ∈ B ×ˢ B | x.1 = x.2 }.card := by
      grind only [usr card_filter_le, usr card_union_add_card_inter, = Finset.card_empty]
    rw [BBcount, BBcard, BBdiagcard, Nat.cast_sub]
    · grind only
    · grind only [usr card_filter_le]
  have B2_card_pos : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card > 0 := by
    have ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp h_B
    have : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.Nonempty := by use ⟨u, v⟩; simp [hu, hv, huv]
    exact card_pos.mpr this
  have h_bound : ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, d_weak ≤
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2) :=
    sum_le_sum h_d
  have h_eq : d_weak =
      1 / (2 * choose_2 ↑B.card) * ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, d_weak := by
    rw [sum_const, B2_card]
    simp only [ne_eq, one_div, smul_eq_mul, Nat.cast_mul]
    rw [← mul_assoc]
    set c := ({ x ∈ B ×ˢ B | ¬x.1 = x.2 }.card : ℚ) with hc
    have c_nonzero : c > 0 := by unfold c; exact_mod_cast B2_card_pos
    field_simp [c_nonzero]
  rw [h_eq]
  have h_B2nonzero : 0 < (2 * choose_2 ↑B.card : ℚ) := by rw [B2_card]; exact_mod_cast B2_card_pos
  set c2 := (2 * choose_2 ↑B.card : ℚ) with hc2
  have c2_pos : c2 > 0 := by rw [B2_card]; exact_mod_cast B2_card_pos
  field_simp [c2_pos]
  simp at h_bound
  gcongr
  grind only

end JohnsonBound

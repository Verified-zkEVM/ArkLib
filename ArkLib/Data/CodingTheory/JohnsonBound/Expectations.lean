/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.RingTheory.Binomial

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.JohnsonBound.Choose2

namespace JohnsonBound

variable {n : ℕ}
variable {F : Type*} [DecidableEq F]
         {B : Finset (Fin n → F)} {v : Fin n → F}

def e (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  (1 : ℚ)/B.card * ∑ x ∈ B, Δ₀(v, x)

def d (B : Finset (Fin n → F)) : ℚ :=
  (1 : ℚ)/(2 * choose_2 B.card) * ∑ x ∈ (Finset.product B B) with x.1 ≠ x.2, Δ₀(x.1, x.2)

lemma lin_shift_card [Field F] [Fintype F]
  :
  B.card = ({ x - v | x ∈ B} : Finset _).card := by
  apply Finset.card_bij (i := fun x _ => x - v) <;> aesop

@[simp]
lemma lin_shift_hamming_distance [Field F] {x₁ x₂ v : Fin n → F}
  :
  Δ₀(x₁ - v, x₂ - v) = Δ₀(x₁, x₂) := by simp [hammingDist]

lemma lin_shift_e [Field F] [Fintype F]
  (h_B : B.card ≠ 0)
  :
  e B v = e ({ x - v | x ∈ B} : Finset _) 0 := by
  simp [e]
  rw [←lin_shift_card]
  field_simp
  apply Finset.sum_bij (i := fun x _ => x - v) <;>
    simp [hammingDist, hammingNorm, sub_eq_zero, eq_comm]

lemma lin_shift_d [Field F] [Fintype F]
  (h_B : 2 ≤ B.card)
  :
  d B = d ({x - v | x ∈ B} : Finset _) := by
  simp [d]
  rw [←lin_shift_card]
  have h : choose_2 B.card ≠ 0 := by aesop (add simp [choose_2, sub_eq_zero])
  field_simp
  apply Finset.sum_bij (fun x _ => (x.1 - v, x.2 -v)) <;> try aesop

lemma e_ball_le_radius [Field F] [Fintype F] {B : Finset (Fin n → F)} (v : Fin n → F) (r : ℚ)
  (h_B : (B ∩ ({ x | Δ₀(x, v) ≤ r} : Finset _)).card > 0)
  :
  e (B ∩ ({ x | Δ₀(x, v) ≤ r} : Finset _)) v ≤ r := by
  unfold e
  have hamming_symm : ∀ x y : Fin n → F, Δ₀(x, y) = Δ₀(y, x) := by
    unfold hammingDist
    simp_rw [ne_comm] ; simp
  simp_rw[hamming_symm v]
  have : ∑ x ∈ (B ∩ ({x | ↑Δ₀(x, v) ≤ r} : Finset _)), Δ₀(x, v)
     ≤ ∑ x ∈ (B ∩ ({x | ↑Δ₀(x, v) ≤ r} : Finset _)), r := by
    have h : ∀ x ∈ (B ∩ ({x | ↑Δ₀(x, v) ≤ r} : Finset _)), Δ₀(x, v) ≤ r := by simp
    exact_mod_cast Finset.sum_le_sum h
  have : ∑ x ∈ (B ∩ ({x | ↑Δ₀(x, v) ≤ r} : Finset _)), r
    = r * (B ∩ ({x | ↑Δ₀(x, v) ≤ r} : Finset _)).card := by
    rw [Finset.sum_const, mul_comm] ; simp
  have : ∑ x ∈ B ∩ ({x | ↑Δ₀(x, v) ≤ r} : Finset _), Δ₀(x, v)
    ≤ r * (B ∩ ({x | ↑Δ₀(x, v) ≤ r} : Finset _)).card := by grind
  field_simp
  have h_B' : (0 : ℚ) < (B ∩ ({ x | Δ₀(x, v) ≤ r} : Finset _)).card := by
    exact_mod_cast h_B
  exact_mod_cast this

lemma min_dist_le_d [Field F] {B : Finset (Fin n → F)}
  (h_B : B.card > 1)
  :
  sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d } ≤ d B := by
  unfold d
  let d_weak := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  have h_d :  ∀ x ∈ {x ∈ B.product B | x.1 ≠ x.2}, d_weak ≤ Δ₀(x.1, x.2) := by
    intro x hx
    simp at hx
    unfold d_weak
    have : Δ₀(x.1, x.2) ∈ { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d } := by
      use x.1, hx.1.1, x.2, hx.1.2
      exact ⟨hx.2, rfl⟩
    apply Nat.sInf_le this
  have B2_card : 2 * choose_2 ↑B.card = {x ∈ B.product B | x.1 ≠ x.2}.card := by
    simp
    unfold choose_2
    ring_nf
    have BBcard : (B ×ˢ B).card = B.card ^ 2 := by
        rw[Finset.card_product, sq]
    have BBdiagcard : {x ∈ B ×ˢ B | x.1=x.2}.card = B.card := by
      simp
    have BBdisjoint : {x ∈ B ×ˢ B | x.1=x.2} ∩ {x ∈ B ×ˢ B | x.1 ≠ x.2} = ∅ := by grind
    have BBunion : B ×ˢ B = {x ∈ B ×ˢ B | x.1 = x.2} ∪ {x ∈ B ×ˢ B | x.1 ≠ x.2} := by
      ext ⟨a, b⟩
      simp
      tauto
    have BBcount: {x ∈ B ×ˢ B | x.1 ≠ x.2}.card
      = (B ×ˢ B).card - {x ∈ B ×ˢ B | x.1=x.2}.card := by
      rw[BBunion, Finset.card_union, BBdiagcard, BBdisjoint]
      have doubleindex1 : {x ∈ {x ∈ B ×ˢ B | x.1 = x.2} ∪ {x ∈ B ×ˢ B | x.1 ≠ x.2} | x.1 = x.2}
        = {x ∈ B ×ˢ B | x.1 = x.2} := by grind
      have doubleindex2 : {x ∈ {x ∈ B ×ˢ B | x.1 = x.2} ∪ {x ∈ B ×ˢ B | x.1 ≠ x.2} | x.1 ≠ x.2}
        = {x ∈ B ×ˢ B | x.1 ≠ x.2} := by grind
      rw[doubleindex1, BBdiagcard]
      simp
      rw[doubleindex2]
    rw[BBcount, BBcard, BBdiagcard]
    rw[Nat.cast_sub] ; ring_nf ; rfl
    nlinarith [sq_nonneg (B.card - 1)]
  have B2_card_pos : {x ∈ B.product B | x.1 ≠ x.2}.card > 0 := by
    have : ∃ u ∈ B, ∃ v ∈ B, u ≠ v := by
      exact Finset.one_lt_card.mp h_B
    have ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h_B
    have : {x ∈ B.product B | x.1 ≠ x.2}.Nonempty := by
        use ⟨u, v⟩ ; simp [hu, hv, huv]
    apply Finset.card_pos.mpr ; exact this
  have h_bound : ∑ x ∈ B.product B with x.1 ≠ x.2, d_weak ≤
    ∑ x ∈ B.product B with x.1 ≠ x.2, Δ₀(x.1, x.2) := by
      exact Finset.sum_le_sum h_d
  have : d_weak =
    1 / (2 * choose_2 ↑B.card) * ∑ x ∈ B.product B with x.1 ≠ x.2, d_weak := by
    rw [Finset.sum_const, B2_card]; simp[Nat.cast_mul]; rw[←mul_assoc]
    set c := ({x ∈ B ×ˢ B | ¬x.1 = x.2}.card : ℚ) with hc
    have c_nonzero : c > 0 := by unfold c ; exact_mod_cast B2_card_pos
    field_simp [c_nonzero]
  rw[this]
  have h_B2nonzero : 0 < (2 * choose_2 ↑B.card : ℚ) := by rw[B2_card]; exact_mod_cast B2_card_pos
  set c2 := (2 * choose_2 ↑B.card : ℚ) with hc2
  have c2_pos : c2 > 0 := by rw[B2_card]; exact_mod_cast B2_card_pos
  field_simp [c2_pos]
  simp at h_bound
  gcongr
  stop
  exact_mod_cast h_bound

end JohnsonBound

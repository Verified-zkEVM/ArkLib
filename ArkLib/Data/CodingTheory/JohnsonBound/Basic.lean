/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Lemmas
/-! # Johnson Bound Basics -/


namespace JohnsonBound

/-!
This module is based on the Johnson Bound section from [listdecoding].
In what follows we reference theorems from [listdecoding] by default.

## References

* [Guruswami, V. and others, *Algorithmic results in list decoding*][listdecoding]
* [Guruswami, V., Rudra, A., and Sudan, M., *Essential coding theory*][codingtheory]
-/

open Fintype Finset Real

variable {n : ℕ}
         {F : Type} [Fintype F] [DecidableEq F]
         {B : Finset (Fin n → F)} {v : Fin n → F}

/-- The denominator of the bound from Theorem 3.1. -/
def JohnsonDenominator (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  let e := e B v
  let d := d B
  let q : ℚ := card F
  let frac := q / (q - 1)
  (1 - frac * e / n) ^ 2 - (1 - frac * d / n)

/-- Unfolds `JohnsonDenominator` into an explicit rational expression. -/
lemma johnson_denominator_def :
    JohnsonDenominator B v = ((1 - (card F) / (card F - 1) * (e B v / n)) ^ 2
      - (1 - (card F) / (card F - 1) * (d B / n))) := by
  simp [JohnsonDenominator]
  field_simp

/-- The strong Johnson condition: the denominator of Theorem 3.1 is positive. -/
def JohnsonConditionStrong (B : Finset (Fin n → F)) (v : Fin n → F) : Prop :=
  let e := e B v
  let d := d B
  let q : ℚ := card F
  let frac := q / (q - 1)
  (1 - frac * d / n) < (1 - frac * e / n) ^ 2

/-- The function used for the `q`-ary Johnson Bound. -/
noncomputable def J (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - √(1 - frac * δ))

/-- Rationalization of `a - √b` via conjugate multiplication. -/
lemma division_by_conjugate {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + √b ≠ 0) :
    a - √b = (a ^ 2 - b) / (a + √b) := by
  rw [eq_div_iff hnonzero]
  ring_nf
  simp_all

/-- The binary Johnson bound `1 - √(1-δ)` is at most the `q`-ary bound `J q δ`. -/
lemma sqrt_le_J {q δ : ℚ} (hq : q > 1) (hx0 : 0 ≤ δ) (hx1 : δ ≤ 1)
    (hqx : q / (q - 1) * δ ≤ 1) :
    1 - √(1 - δ) ≤ J q δ := by
  unfold J
  set frac := q / (q - 1) with hfrac
  have hfrac_ge : frac ≥ 1 := by
    rw [hfrac, ge_iff_le, one_le_div] <;> grind
  have hx' : 1 - δ ≥ 0 := by grind only
  have hfracx' : 1 - frac * δ ≥ 0 := by grind only
  suffices 1 - √(1 - δ) ≤ (1 / frac) * (1 - √(1 - frac * δ)) by grind only
  field_simp
  norm_cast
  by_cases hδ : δ = 0
  · simp [hδ]
  · have hδ_pos : (0 : ℚ) < δ := lt_of_le_of_ne hx0 (Ne.symm hδ)
    have hfracx'2 : 1 - δ * frac ≥ 0 := by linarith [mul_comm frac δ]
    rw [division_by_conjugate (b := ↑(1 - δ)) (by exact_mod_cast hx') (by positivity)]
    rw [division_by_conjugate (b := ↑(1 - δ * frac))
        (by exact_mod_cast hfracx'2) (by positivity)]
    simp only [one_pow]
    push_cast
    rw [show (1 : ℝ) - (1 - (δ : ℝ)) = δ from by ring,
        show (1 : ℝ) - (1 - (δ : ℝ) * (frac : ℝ)) = δ * frac from by ring,
        div_mul_eq_mul_div]
    have hsqrt_le : √(1 - ↑δ * ↑frac) ≤ √(1 - ↑δ) := by
      apply sqrt_le_sqrt
      nlinarith [show (1 : ℝ) ≤ ↑frac from by exact_mod_cast hfrac_ge,
                 show (0 : ℝ) ≤ ↑δ from by exact_mod_cast hx0]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- The `q`-ary Johnson bound condition (weak form via `J`). -/
def JohnsonConditionWeak (B : Finset (Fin n → F)) (e : ℕ) : Prop :=
  let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let q : ℚ := card F
  (e : ℚ) / n < J q (d / n)

/-- The weak Johnson condition implies the strong one on the ball intersection. -/
lemma johnson_condition_weak_implies_strong [Field F]
    {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ}
    (h_J_cond_weak : JohnsonConditionWeak B e)
    (h_B2_not_one : 1 < (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card)
    (h_F_nontriv : 2 ≤ card F) :
    JohnsonConditionStrong (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)) v := by
  have h_n_pos : 0 < n := by
    by_contra hn
    push Not at hn
    have : n = 0 := by omega
    subst this
    have B_singleton : B.card ≤ 1 :=
      card_le_one.2 (fun _ _ _ _ => funext (Fin.elim0 ·))
    have : (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card ≤ 1 :=
      le_trans (card_le_card inter_subset_left) B_singleton
    omega
  unfold JohnsonConditionStrong
  intro e_1 d q frac
  by_cases h_dsqrt_pos : (0 : ℝ) ≤ 1 - frac * d / ↑n
  · have h_B2_nonempty : (0 : ℚ) < ((B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card : ℚ) :=
      by norm_cast; omega
    have h_frac_pos : frac > 0 := by
      unfold frac
      have : 1 < card F := by
        simpa [Fintype.one_lt_card_iff] using (⟨(0 : F), (1 : F), by simp⟩ : ∃ a b : F, a ≠ b)
      field_simp
      unfold q
      simp only [Nat.cast_pos, Fintype.zero_lt_card, div_pos_iff_of_pos_left, sub_pos,
        Nat.one_lt_cast]
      exact h_F_nontriv
    have j_fun_bound : (↑e / ↑n : ℝ) < (1 / ↑frac * (1 - √(1 - ↑frac * ↑d / ↑n))) := by
      unfold JohnsonConditionWeak J at h_J_cond_weak
      simp_all only [Rat.cast_natCast, Rat.cast_div, Rat.cast_sub, Rat.cast_one, one_div, inv_div,
        ne_eq, sub_nonneg, Nat.cast_pos, Finset.card_pos, gt_iff_lt]
      let d_weak := sInf { d | ∃ u ∈ B, ∃ v ∈ B, ¬u = v ∧ Δ₀(u, v) = d }
      have d_subset : ↑d_weak ≤ (d : ℚ) := by
          unfold d
          unfold JohnsonBound.d
          unfold d_weak
          have min_dist := min_dist_le_d h_B2_not_one
          have subset_inf_ineq :
              sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d } ≤
              sInf { d |
              ∃ u ∈ (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)),
              ∃ v_1 ∈ (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)),
              u ≠ v_1 ∧ Δ₀(u, v_1) = d } := by
              have subset : { d |
                          ∃ u ∈ (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)),
                          ∃ v_1 ∈ (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)),
                          u ≠ v_1 ∧ Δ₀(u, v_1) = d }
                          ⊆ { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d } := by
                intro d ⟨u, hu_in, v_1, hv_in, hne, heq⟩
                exact
                  ⟨u, by
                    simp only [mem_inter, mem_filter, mem_univ, true_and] at hu_in; exact hu_in.1,
                  v_1, by
                    simp only [mem_inter, mem_filter, mem_univ, true_and] at hv_in; exact hv_in.1,
                  hne, heq⟩
              gcongr
              obtain ⟨u, hu, v_1, hv_1, hne⟩ := one_lt_card.mp h_B2_not_one
              use Δ₀(u, v_1)
              exact ⟨u, hu, v_1, hv_1, hne, rfl⟩
          calc ↑d_weak
              = ↑(sInf { d | ∃ u ∈ B, ∃ v ∈ B, ¬u = v ∧ Δ₀(u, v) = d }) := by rfl
            _ ≤ ↑(sInf { d |
              ∃ u ∈ (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)),
              ∃ v_1 ∈ (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)),
              u ≠ v_1 ∧ Δ₀(u, v_1) = d }) := by exact_mod_cast subset_inf_ineq
            _ ≤ JohnsonBound.d (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)) :=
              by exact_mod_cast min_dist
      have bound : (↑frac)⁻¹ * (1 - √(1 - ↑frac * ↑d_weak / ↑n))
          ≤ (↑frac)⁻¹ * (1 - √(1 - ↑frac * ↑d / ↑n)) := by
        have ineq1 : (↑d_weak / ↑n) ≤ (d / ↑n) := by
          rw [← mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr h_n_pos)]
          field_simp
          exact d_subset
        have ineq2 : frac * (d_weak / n) ≤ frac * (d / n) :=
          mod_cast (mul_le_mul_iff_of_pos_left h_frac_pos).mpr ineq1
        have ineq3' : (1 : ℝ) - frac * d / n ≤ (1 : ℝ) - frac * d_weak / n := by
          norm_cast; grind
        have ineq4 : √(1 - ↑frac * ↑d / ↑n) ≤ √(1 - ↑frac * ↑d_weak / ↑n) :=
          sqrt_le_sqrt ineq3'
        have ineq5 :
            (1 - √(1 - ↑frac * ↑d_weak / ↑n)) ≤ (1 - √(1 - ↑frac * ↑d / ↑n)) := by linarith
        simp_all
      have h_J_cond_weak' : ↑e / ↑n < 1 / (↑frac) * (1 - √(1 - frac * (d_weak / ↑n))) := by
        unfold frac
        unfold q
        unfold d_weak
        push_cast
        rw [one_div_div]
        exact h_J_cond_weak
      field_simp
      field_simp at h_J_cond_weak'
      field_simp at bound
      nlinarith [mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg n)]
    have err_n : (↑e_1 / ↑n : ℝ) ≤ (↑e / ↑n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast e_ball_le_radius v e
        (by simpa using show 0 < (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card by omega)
    have j_fun_bound_e1 : (↑e_1 / ↑n : ℝ) < (1 / ↑frac * (1 - √(1 - ↑frac * ↑d / ↑n))) :=
      lt_of_le_of_lt err_n j_fun_bound
    have rearrange_jboundw_e1 : √(1 - ↑frac * ↑d / ↑n) < 1 - frac * e_1 / ↑n := by
      have : frac * e_1 / ↑n < 1 - √(1 - frac * d / ↑n) := by
        calc ↑frac * ↑e_1 / ↑n
            = ↑frac * (↑e_1 / ↑n) := by ring
          _ < ↑frac * (1 / ↑frac * (1 - √(1 - ↑frac * ↑d / ↑n))) := by
            simp_all only [Rat.cast_div, Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, sub_nonneg,
              Nat.cast_pos, Finset.card_pos, gt_iff_lt, zero_lt_card, div_pos_iff_of_pos_left,
              sub_pos, Nat.one_lt_cast, one_div, inv_div, mul_lt_mul_iff_right₀, frac, q, d, e_1]
          _ = 1 - √(1 - ↑frac * ↑d / ↑n) := by
            grind only [= division_by_conjugate, = sqrt_one]
      grind only
    have h_esqrtpos : (0 : ℝ) ≤ 1 - frac * e_1 / ↑n := by
      have : (0 : ℝ) ≤ √(1 - ↑frac * ↑d / ↑n) := by
        simp_all only [Rat.cast_div, Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, sub_nonneg,
          Nat.cast_pos, Finset.card_pos, gt_iff_lt, zero_lt_card, div_pos_iff_of_pos_left,
          sub_pos, Nat.one_lt_cast, one_div, inv_div, sqrt_nonneg, frac, q, d, e_1]
      grind only
    suffices recast_main_goal : (1 - frac * d / ↑n : ℝ) < (1 - frac * e_1 / ↑n) ^ 2 by
      exact_mod_cast recast_main_goal
    suffices roots : √(1 - frac * d / ↑n) < 1 - frac * e_1 / ↑n by
      rw [← sqrt_lt h_dsqrt_pos h_esqrtpos]
      exact_mod_cast roots
    exact rearrange_jboundw_e1
  · have strict_neg : 1 - ↑frac * ↑d / ↑n < (0 : ℚ) := by
      have : ¬(0 : ℚ) ≤ 1 - frac * d / ↑n := by exact_mod_cast h_dsqrt_pos
      rw [Rat.not_le] at this
      exact this
    calc 1 - ↑frac * ↑d / ↑n < (0 : ℚ) := strict_neg
      _ ≤ (1 - ↑frac * ↑e_1 / ↑n) ^ 2 := by exact_mod_cast sq_nonneg (1 - frac * ↑e_1 / ↑n)

/-- The strong Johnson condition forces the block length to be positive. -/
lemma johnson_condition_strong_implies_n_pos
    (h_johnson : JohnsonConditionStrong B v) :
    0 < n := by
  cases n <;> try simp [JohnsonConditionStrong] at *

/-- The strong Johnson condition forces the alphabet to have at least two elements. -/
lemma johnson_condition_strong_implies_2_le_F_card
    (h_johnson : JohnsonConditionStrong B v) :
    2 ≤ card F := by
  revert h_johnson
  dsimp [JohnsonConditionStrong]
  rcases card F with _ | _ | _ <;> aesop

/-- The strong Johnson condition forces the code to have at least two codewords. -/
lemma johnson_condition_strong_implies_2_le_B_card
    (h_johnson : JohnsonConditionStrong B v) :
    2 ≤ B.card := by
  dsimp [JohnsonConditionStrong] at h_johnson
  rcases eq : B.card with _ | card | _ <;> [simp_all; skip; omega]
  obtain ⟨a, ha⟩ := card_eq_one.1 eq
  replace h_johnson : 1 < |1 - (card F) / ((card F) - 1) * Δ₀(v, a) / (n : ℚ)| := by
    simp_all [choose_2]
  generalize eq₁ : card F = q
  rcases q with _ | _ | q <;> [simp_all; simp_all; skip]
  have h : (card F : ℚ) / (card F - 1) = 1 + 1 / (card F - 1) := by
    have : (card F : ℚ) - 1 ≠ 0 := by simp [sub_eq_zero]; omega
    field_simp
    ring
  have h' := JohnsonBound.abs_one_sub_div_le_one (v := v) (a := a) (by omega)
  exact absurd (lt_of_lt_of_le (h ▸ h_johnson) h') (lt_irrefl _)

/-- `JohnsonConditionStrong` is equivalent to `JohnsonDenominator` being positive. -/
lemma johnson_condition_strong_iff_johnson_denom_pos {B : Finset (Fin n → F)} {v : Fin n → F} :
    JohnsonConditionStrong B v ↔ 0 < JohnsonDenominator B v := by
  simp [JohnsonDenominator, JohnsonConditionStrong]

/-- Theorem 3.1: the Johnson bound on list size. -/
theorem johnson_bound [Field F]
    (h_condition : JohnsonConditionStrong B v) :
    let d := d B
    let q : ℚ := card F
    let frac := q / (q - 1)
    B.card ≤ (frac * d / n) / JohnsonDenominator B v := by
  suffices B.card * JohnsonDenominator B v ≤
           (card F : ℚ) / (card F - 1) * d B / n by
    rw [johnson_condition_strong_iff_johnson_denom_pos] at h_condition
    exact (le_div_iff₀ h_condition).mpr (by linarith)
  rw [johnson_denominator_def]
  exact JohnsonBound.johnson_bound_lemma
    (johnson_condition_strong_implies_n_pos h_condition)
    (johnson_condition_strong_implies_2_le_B_card h_condition)
    (johnson_condition_strong_implies_2_le_F_card h_condition)

/-- Alphabet-free Johnson bound from [codingtheory]. -/
theorem johnson_bound_alphabet_free [Field F]
    {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ} (hB : 1 < B.card) :
    let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
    let q : ℚ := card F
    let _frac := q / (q - 1)
    e ≤ n - ((n * (n - d)) : ℝ).sqrt →
    (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card ≤ q * d * n := by
  intro d q frac h
  let B' := B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)
  -- Parameter bounds.
  have q_not_small : q ≥ (2 : ℚ) := by
    simpa [q] using show (2 : ℚ) ≤ (card F : ℚ) from by
      exact_mod_cast Nat.succ_le_of_lt (by
        simpa [Fintype.one_lt_card_iff] using (⟨(0 : F), (1 : F), by simp⟩ : ∃ a b : F, a ≠ b))
  have d_not_small : d ≥ 1 := by
    let S : Set ℕ := { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
    simpa [S] using sInf.le_sInf_of_LB (S := S) (i := 1)
      (by obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hB
          exact ⟨hammingDist u v, u, hu, v, hv, huv, rfl⟩)
      (fun s ⟨u, _, v, _, huv, hdist⟩ => hdist ▸ Nat.succ_le_of_lt (hammingDist_pos.mpr huv))
  have n_not_small : n ≥ 1 := by
    by_contra hn
    have : n = 0 := by omega
    subst this
    have : B.card ≤ 1 := card_le_one.2 (fun _ _ _ _ => funext (Fin.elim0 ·))
    omega
  have qdn_not_small : (q * d * n) ≥ 2 := by
    simpa [mul_assoc] using johnson_qdn_ge_two q_not_small d_not_small n_not_small
  by_cases h_size : B'.card < 2
  -- Trivial case: |B'| < 2.
  · exact le_trans (show (B'.card : ℚ) ≤ 1 from by exact_mod_cast Nat.le_of_lt_succ h_size)
      (le_trans (by norm_num : (1 : ℚ) ≤ 2) qdn_not_small)
  -- Main case: |B'| ≥ 2.
  · have hd_le_dB' : (d : ℚ) ≤ JohnsonBound.d B' := by
      let S : Set ℕ := { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
      let S' : Set ℕ := { d | ∃ u ∈ B', ∃ v ∈ B', u ≠ v ∧ hammingDist u v = d }
      have hsubset : S' ⊆ S := fun _ ⟨u, hu, w, hw, huw, hd⟩ =>
        ⟨u, (mem_inter.mp hu).1, w, (mem_inter.mp hw).1, huw, hd⟩
      have hS'nonempty : S'.Nonempty := by
        obtain ⟨u, hu, w, hw, huw⟩ := one_lt_card.mp (show 1 < B'.card by omega)
        exact ⟨hammingDist u w, u, hu, w, hw, huw, rfl⟩
      calc (d : ℚ)
          ≤ ↑(sInf S') := by exact_mod_cast Nat.sInf_le (hsubset (Nat.sInf_mem hS'nonempty))
        _ ≤ JohnsonBound.d B' := by exact_mod_cast min_dist_le_d (B := B') (by omega)
    -- Positivity facts used in both subcases.
    have hn_pos_nat : 0 < n := Nat.succ_le_iff.1 n_not_small
    have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos_nat
    have hq1_pos : (0 : ℚ) < q - 1 := by linarith
    by_cases h_d_close_n : q / (q - 1) * (d / n) > 1
    -- Subcase: frac·d/n > 1.
    · have h_strong : JohnsonConditionStrong B' v := by
        simpa [JohnsonConditionStrong, q, mul_div_assoc] using
          lt_of_lt_of_le (show (1 - (q / (q - 1)) * (JohnsonBound.d B' / n) : ℚ) < 0 from by
            linarith [lt_of_lt_of_le h_d_close_n (mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hd_le_dB' (by exact_mod_cast Nat.cast_nonneg n))
              (div_nonneg (by linarith) (by linarith)))]) (sq_nonneg _)
      have hden_ge : JohnsonDenominator B' v ≥ frac * JohnsonBound.d B' / n - 1 := by
        simpa [JohnsonDenominator, q, frac, mul_div_assoc] using
          johnson_den_ge_frac_d (B := B') (v := v)
      have hgap : frac * JohnsonBound.d B' / (n : ℚ) - 1 ≥ 1 / (n * (q - 1)) := by
        simpa [q, frac] using johnson_gap_frac_d_gt_one (B := B')
          (q_not_small := by simpa [q] using q_not_small)
          (n_not_small := n_not_small)
          (h_d_close_n := by simpa [q, frac] using h_d_close_n)
          (hd_le_dB := hd_le_dB')
      have hden_lb : (1 : ℚ) / (n * (q - 1)) ≤ JohnsonDenominator B' v := by linarith
      have hnum_nonneg : (0 : ℚ) ≤ frac * JohnsonBound.d B' / n :=
        div_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith))
          (le_trans (by exact_mod_cast Nat.zero_le d) hd_le_dB')) hn_pos.le
      calc (B'.card : ℚ)
          ≤ (frac * JohnsonBound.d B' / n) / JohnsonDenominator B' v := by
            simpa using johnson_bound h_strong
        _ ≤ (frac * JohnsonBound.d B' / n) / (1 / (n * (q - 1))) :=
            div_le_div_of_nonneg_left hnum_nonneg
              (one_div_pos.mpr (mul_pos hn_pos hq1_pos)) hden_lb
        _ = q * JohnsonBound.d B' := by
            field_simp [frac, hn_pos.ne', hq1_pos.ne']; simp [mul_comm]; grind only
        _ ≤ q * d * n := by
            have hd_le_n := johnson_d_le_n (B := B') (le_of_not_gt h_size)
            have hd_ge1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast d_not_small
            have hq_nn : (0 : ℚ) ≤ q := by linarith
            nlinarith [mul_le_mul_of_nonneg_left hd_le_n hq_nn,
              mul_le_mul_of_nonneg_left hd_ge1 (mul_nonneg hq_nn (le_of_lt hn_pos))]
    -- Subcase: frac·d/n ≤ 1 (main case, via weak → strong).
    · have d_le_n : d ≤ n := by
        obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hB
        exact le_trans (Nat.sInf_le ⟨u, hu, v, hv, huv, rfl⟩)
          (by simpa using hammingDist_le_card_fintype (x := u) (y := v))
      have hn_nonneg : (0 : ℚ) ≤ n := hn_pos.le
      have hq_pos : (0 : ℚ) < q := by linarith
      have hfrac_pos : (0 : ℚ) < frac := div_pos hq_pos hq1_pos
      have hfrac_gt1 : (1 : ℚ) < frac := by
        simpa [frac] using (one_lt_div hq1_pos).2 (by linarith : q - 1 < q)
      have hn2_pos : (0 : ℚ) < (n : ℚ) ^ 2 := pow_pos hn_pos _
      have h_johnson_strong : JohnsonConditionStrong B' v := by
        have h_muln : (e : ℚ) / n ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt := by
          by_cases hn : n = 0
          · simp [hn]
          · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
            have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.cast_nonneg n
            suffices (e : ℝ) / n ≤ 1 - ((1 - (d : ℝ) / n) : ℝ).sqrt by simpa using this
            calc (e : ℝ) / n
                ≤ (n - ((n * (n - d) : ℝ).sqrt)) / n :=
                  div_le_div_of_nonneg_right (by simpa using h) hn_nn
              _ = 1 - ((n * (n - d) : ℝ).sqrt) / n := by simp [sub_div, hn']
              _ = 1 - ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                  congr 1
                  calc ((n * (n - d) : ℝ).sqrt) / n
                      = ((n * (n - d) : ℝ).sqrt) / ((n : ℝ) ^ 2).sqrt := by simp [hn_nn]
                    _ = (((n * (n - d) : ℝ) / (n : ℝ) ^ 2).sqrt) := by
                          symm; exact sqrt_div' ((n : ℝ) * (n - d)) (sq_nonneg _)
                    _ = ((1 - (d : ℝ) / n) : ℝ).sqrt := by congr 1; field_simp [hn']
        have h_J_bound : 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt ≤ J q (d / n) := by
          simpa using sqrt_le_J (by linarith : q > 1)
            (div_nonneg (by exact_mod_cast Nat.cast_nonneg d) (by exact_mod_cast Nat.cast_nonneg n))
            (by rcases eq_or_ne n 0 with rfl | hn
                · simp
                · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).2
                    (by exact_mod_cast d_le_n))
            (le_of_not_gt h_d_close_n)
        exact johnson_condition_weak_implies_strong
          (lt_of_le_of_ne (by linarith) (johnson_e_div_ne_J hn_pos_nat
            (Nat.succ_le_iff.1 d_not_small) (by linarith) h_muln h_J_bound
            (le_of_not_gt h_d_close_n)))
          (show 1 < B'.card by omega) (by
            have : 1 < card F := by
              simpa [Fintype.one_lt_card_iff] using (⟨(0 : F), (1 : F), by simp⟩ : ∃ a b : F, a ≠ b)
            omega)
      -- Core inequality from the hypothesis.
      have h_div'_q : (1 - (d / n : ℚ)) ≤ (1 - (e / n : ℚ)) ^ 2 := by
        have : ((1 - (d / n : ℚ)) : ℝ) ≤ ((1 - (e / n : ℚ)) ^ 2 : ℝ) := by
          simpa using JohnsonBound.johnson_hyp_implies_div_ineq hn_pos_nat d_le_n h
        exact_mod_cast this
      calc (B'.card : ℚ)
          ≤ (frac * JohnsonBound.d B' / n) / JohnsonDenominator B' v := by
            simpa using johnson_bound h_johnson_strong
        _ ≤ q * (d : ℚ) * n := by
            set D0 : ℚ := d / n
            set E0 : ℚ := e / n
            set Den : ℚ := D0 - 2 * E0 + frac * E0 ^ 2
            have quad_nonneg : (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by grind only
            have frac_sub_one_eq : frac - 1 = (1 : ℚ) / (q - 1) := by grind only
            have one_div_q_le : (1 : ℚ) / q ≤ frac - 1 := by
              simpa [frac_sub_one_eq] using
                (one_div_le_one_div_of_le hq1_pos (by linarith : q - 1 ≤ q))
            -- Expand and cancel frac from JohnsonDenominator.
            have denom_expansion : JohnsonDenominator B' v =
                frac * (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2) := by
              simp [JohnsonDenominator, q, frac, mul_div_assoc]; grind only
            have term_simplification : (frac * JohnsonBound.d B' / (n : ℚ)) /
                JohnsonDenominator B' v =
                (JohnsonBound.d B' / n) /
                (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2) := by
                  grind only [= johnson_condition_strong_iff_johnson_denom_pos]
            -- Bound eB' by e.
            have e_ineq : JohnsonBound.e B' v ≤ e := by
              simpa [B'] using JohnsonBound.e_ball_le_radius (B := B) (v := v) (r := (e : ℚ))
                (by simpa [B'] using show 0 < B'.card by omega)
            -- Denominator positivity.
            have hden1_pos : (0 : ℚ) <
                JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2 := by
              have hdenJ : (0 : ℚ) < JohnsonDenominator B' v :=
                johnson_condition_strong_iff_johnson_denom_pos.1 h_johnson_strong
              have hdenJ' : (0 : ℚ) < frac * (JohnsonBound.d B' / n -
                  2 * JohnsonBound.e B' v / n +
                  frac * (JohnsonBound.e B' v / n) ^ 2) := by
                simpa [denom_expansion] using hdenJ
              rcases mul_pos_iff.mp hdenJ' with hpos | hneg
              · exact hpos.2
              · exact absurd hneg.1 (not_lt.mpr hfrac_pos.le)
            -- Monotone worst-case bound.
            have worst_case_bound :
                (JohnsonBound.d B' / n) /
                (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                  frac * (JohnsonBound.e B' v / n) ^ 2) ≤
                (d / n) / (d / n - 2 * e / n + frac * (e / n) ^ 2) :=
              johnson_worst_case_bound hn_pos (Nat.succ_le_iff.1 d_not_small) d_le_n h
                (le_of_not_gt h_d_close_n) hfrac_gt1 e_ineq hd_le_dB' quad_nonneg hden1_pos
            -- Final algebraic bound.
            have hden_lb : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ Den := by
              by_cases he0 : e = 0
              · subst he0; simpa [D0, E0, Den] using
                  johnson_den_lb_e_zero hn_pos_nat (by linarith) (by exact_mod_cast d_not_small)
              · exact johnson_den_lb_e_pos hn_pos he0 one_div_q_le
                  (by linarith) quad_nonneg
            rw [term_simplification]
            calc (JohnsonBound.d B' / n) /
                    (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                      frac * (JohnsonBound.e B' v / n) ^ 2)
                ≤ (d / n) / (d / n - 2 * e / n + frac * (e / n) ^ 2) := worst_case_bound
              _ = (d / n) / Den := by simp [Den, D0, E0, mul_div_assoc]
              _ ≤ (d / n) / ((1 : ℚ) / (q * (n : ℚ) ^ 2)) :=
                  div_le_div_of_nonneg_left
                    (div_nonneg (by exact_mod_cast Nat.zero_le d) hn_nonneg)
                    (one_div_pos.mpr (mul_pos hq_pos hn2_pos)) hden_lb
              _ = q * d * n := by field_simp [ne_of_gt hq_pos, ne_of_gt hn_pos]

end JohnsonBound

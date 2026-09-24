/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
module

public import ArkLib.Data.CodingTheory.JohnsonBound.Lemmas
/-! # Johnson Bound Basics -/

@[expose] public section


namespace JohnsonBound

/-!
This module is based on the Johnson Bound section from [listdecoding].
In what follows we reference theorems from [listdecoding] by default.

## References

* [Guruswami, V. and others, *Algorithmic results in list decoding*][listdecoding]
* [Guruswami, V., Rudra, A., and Sudan, M., *Essential coding theory*][codingtheory]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
Agreement*][ABF26]
-/

open Fintype Finset Real

variable {n : ℕ}
         {F : Type*} [Fintype F] [DecidableEq F]
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

/-- The asymptotic ("capacity") Johnson bound `1 - √(1 - δ)`, the `q → ∞` limit of the
`q`-ary `JohnsonBound.J`.

This is not the binary Johnson bound, which is `J 2 δ = (1 - √(1 - 2δ))/2`. -/
noncomputable def Jcap (δ : ℝ) : ℝ := 1 - √(1 - δ)

@[simp]
lemma Jcap_zero : Jcap 0 = 0 := by simp [Jcap]

@[simp]
lemma Jcap_one : Jcap 1 = 1 := by simp [Jcap]

/-- Rationalization of `a - √b` via conjugate multiplication. -/
lemma division_by_conjugate {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + √b ≠ 0) :
    a - √b = (a ^ 2 - b) / (a + √b) := by
  rw [eq_div_iff hnonzero]
  ring_nf
  simp_all

/-- The asymptotic Johnson bound is at most the `q`-ary one: `Jcap δ ≤ J q δ`. -/
lemma sqrt_le_J {q δ : ℚ} (hq : q > 1) (hx0 : 0 ≤ δ) (hx1 : δ ≤ 1)
    (hqx : q / (q - 1) * δ ≤ 1) :
    Jcap δ ≤ J q δ := by
  unfold Jcap J
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

private lemma weak_to_strong_aux {q e e1 D d : ℚ} (hf : 0 < q / (q - 1)) (he1 : e1 ≤ e)
    (hD : D ≤ d) (hd : 0 ≤ 1 - q / (q - 1) * d) (h : (e : ℝ) < J q D) :
    1 - q / (q - 1) * d < (1 - q / (q - 1) * e1) ^ 2 := by
  simp only [J] at h
  set f := q / (q - 1)
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hfe : (f : ℝ) * e < 1 - √(1 - f * D) := by
    have := mul_lt_mul_of_pos_left h hf'
    rwa [← mul_assoc, mul_one_div_cancel hf'.ne', one_mul] at this
  have hfe1 : (f : ℝ) * e1 ≤ f * e := mul_le_mul_of_nonneg_left (by exact_mod_cast he1) hf'.le
  have hfD : (f : ℝ) * D ≤ f * d := mul_le_mul_of_nonneg_left (by exact_mod_cast hD) hf'.le
  have hmono : √(1 - (f : ℝ) * d) ≤ √(1 - f * D) := sqrt_le_sqrt (by linarith)
  have hs : √(1 - (f : ℝ) * d) ^ 2 = 1 - f * d := sq_sqrt (by exact_mod_cast hd)
  have key : ((1 - f * d : ℚ) : ℝ) < ((1 - f * e1) ^ 2 : ℚ) := by
    push_cast
    rw [← hs]
    exact pow_lt_pow_left₀ (by linarith) (sqrt_nonneg _) two_ne_zero
  exact_mod_cast key

/-- The weak Johnson condition implies the strong one on the ball intersection. -/
lemma johnson_condition_weak_implies_strong
    {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ}
    (h_J_cond_weak : JohnsonConditionWeak B e)
    (h_B2_not_one : 1 < (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card)
    (h_F_nontriv : 2 ≤ card F) :
    JohnsonConditionStrong (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)) v := by
  unfold JohnsonConditionStrong
  intro e_1 d q frac
  simp only [mul_div_assoc]
  by_cases h_pos : (0 : ℚ) ≤ 1 - frac * (d / n)
  · have hq2 : (2 : ℚ) ≤ q := show (2 : ℚ) ≤ (card F : ℚ) by exact_mod_cast h_F_nontriv
    have hn : (0 : ℚ) ≤ n := n.cast_nonneg
    have he : e_1 ≤ e := by
      have := e_ball_le_radius (B := B) v (e : ℚ) (by simp only [Nat.cast_le]; omega)
      simp only [Nat.cast_le] at this
      exact this
    have hD : ((sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d } : ℕ) : ℚ) ≤ d := by
      refine le_trans ?_ (min_dist_le_d h_B2_not_one)
      obtain ⟨u, hu, w, hw, huw⟩ := one_lt_card.mp h_B2_not_one
      refine Nat.cast_le.mpr (csInf_le_csInf (OrderBot.bddBelow _) ⟨_, u, hu, w, hw, huw, rfl⟩ ?_)
      rintro _ ⟨u, hu, w, hw, huw, rfl⟩
      exact ⟨u, (mem_inter.mp hu).1, w, (mem_inter.mp hw).1, huw, rfl⟩
    exact weak_to_strong_aux (div_pos (by linarith) (by linarith))
      (div_le_div_of_nonneg_right he hn) (div_le_div_of_nonneg_right hD hn) h_pos
      (by rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]; exact h_J_cond_weak)
  · exact (not_le.mp h_pos).trans_le (sq_nonneg _)

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
theorem johnson_bound
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

/-- Cancellation used in the `frac · d / n > 1` case of `johnson_bound_alphabet_free`. -/
private lemma frac_mul_div_div_one_div {q D N : ℚ} (hN : N ≠ 0) (hq : q - 1 ≠ 0) :
    q / (q - 1) * D / N / (1 / (N * (q - 1))) = q * D := by
  field_simp

/-- Alphabet-free Johnson bound from [codingtheory]. -/
theorem johnson_bound_alphabet_free
    {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ} (hB : 1 < B.card) :
    let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
    let q : ℚ := card F
    let _frac := q / (q - 1)
    e ≤ n - ((n * (n - d)) : ℝ).sqrt →
    (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card ≤ q * d * n := by
  intro d q frac h
  let B' := B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)
  -- Parameter bounds.
  have hF2 : 2 ≤ card F := by
    obtain ⟨u, _, w, _, huw⟩ := one_lt_card.mp hB
    obtain ⟨i, hi⟩ := Function.ne_iff.mp huw
    exact Fintype.one_lt_card_iff.mpr ⟨u i, w i, hi⟩
  have q_not_small : q ≥ (2 : ℚ) := show (2 : ℚ) ≤ (card F : ℚ) by exact_mod_cast hF2
  have d_not_small : d ≥ 1 := by
    obtain ⟨u, hu, w, hw, huw⟩ := one_lt_card.mp hB
    exact le_csInf ⟨_, u, hu, w, hw, huw, rfl⟩
      fun _ ⟨_, _, _, _, huv, hdist⟩ => hdist ▸ Nat.succ_le_of_lt (hammingDist_pos.mpr huv)
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
    have hq_nn : (0 : ℚ) ≤ q := zero_le_two.trans q_not_small
    have hfrac_nn : (0 : ℚ) ≤ frac := div_nonneg hq_nn hq1_pos.le
    by_cases h_d_close_n : q / (q - 1) * (d / n) > 1
    -- Subcase: frac·d/n > 1.
    · have hdn : 1 < frac * JohnsonBound.d B' / n := by
        rw [mul_div_assoc]
        exact h_d_close_n.trans_le (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hd_le_dB' hn_pos.le) hfrac_nn)
      have h_strong : JohnsonConditionStrong B' v :=
        show 1 - frac * JohnsonBound.d B' / n < (1 - frac * JohnsonBound.e B' v / n) ^ 2 from
          (sub_neg.mpr hdn).trans_le (sq_nonneg _)
      have hgap : frac * JohnsonBound.d B' / (n : ℚ) - 1 ≥ 1 / (n * (q - 1)) :=
        johnson_gap_frac_d_gt_one q_not_small n_not_small h_d_close_n hd_le_dB'
      have hden_lb : (1 : ℚ) / (n * (q - 1)) ≤ JohnsonDenominator B' v := by
        change _ ≤ (1 - frac * JohnsonBound.e B' v / n) ^ 2 - (1 - frac * JohnsonBound.d B' / n)
        linarith [sq_nonneg (1 - frac * JohnsonBound.e B' v / n)]
      have hnum_nonneg : (0 : ℚ) ≤ frac * JohnsonBound.d B' / n :=
        div_nonneg (mul_nonneg hfrac_nn (d.cast_nonneg.trans hd_le_dB')) hn_pos.le
      calc (B'.card : ℚ)
          ≤ (frac * JohnsonBound.d B' / n) / JohnsonDenominator B' v := johnson_bound h_strong
        _ ≤ (frac * JohnsonBound.d B' / n) / (1 / (n * (q - 1))) :=
            div_le_div_of_nonneg_left hnum_nonneg
              (one_div_pos.mpr (mul_pos hn_pos hq1_pos)) hden_lb
        _ = q * JohnsonBound.d B' := frac_mul_div_div_one_div hn_pos.ne' hq1_pos.ne'
        _ ≤ q * n :=
            mul_le_mul_of_nonneg_left (johnson_d_le_n (B := B') (le_of_not_gt h_size)) hq_nn
        _ ≤ q * n * d := le_mul_of_one_le_right (mul_nonneg hq_nn hn_pos.le)
            (by exact_mod_cast d_not_small)
        _ = q * d * n := by ring
    -- Subcase: frac·d/n ≤ 1 (main case, via weak → strong).
    · have d_le_n : d ≤ n := by
        obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hB
        exact le_trans (Nat.sInf_le ⟨u, hu, v, hv, huv, rfl⟩)
          (by simpa using hammingDist_le_card_fintype (x := u) (y := v))
      have hn_nonneg : (0 : ℚ) ≤ n := hn_pos.le
      have hq_pos : (0 : ℚ) < q := by linarith
      have hfrac_pos : (0 : ℚ) < frac := div_pos hq_pos hq1_pos
      have hfrac_gt1 : (1 : ℚ) < frac := (one_lt_div hq1_pos).2 (by linarith)
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
          simpa [Jcap] using sqrt_le_J (one_lt_two.trans_le q_not_small)
            (div_nonneg (by exact_mod_cast Nat.cast_nonneg d) (by exact_mod_cast Nat.cast_nonneg n))
            (by rcases eq_or_ne n 0 with rfl | hn
                · simp
                · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).2
                    (by exact_mod_cast d_le_n))
            (le_of_not_gt h_d_close_n)
        exact johnson_condition_weak_implies_strong
          (lt_of_le_of_ne (h_muln.trans h_J_bound) (johnson_e_div_ne_J hn_pos_nat
            (Nat.succ_le_iff.1 d_not_small) (one_lt_two.trans_le q_not_small) h_muln h_J_bound
            (le_of_not_gt h_d_close_n)))
          (show 1 < B'.card by omega) hF2
      -- Core inequality from the hypothesis.
      have h_div'_q : (1 - (d / n : ℚ)) ≤ (1 - (e / n : ℚ)) ^ 2 := by
        have : ((1 - (d / n : ℚ)) : ℝ) ≤ ((1 - (e / n : ℚ)) ^ 2 : ℝ) := by
          simpa using JohnsonBound.johnson_hyp_implies_div_ineq hn_pos_nat d_le_n h
        exact_mod_cast this
      calc (B'.card : ℚ)
          ≤ (frac * JohnsonBound.d B' / n) / JohnsonDenominator B' v :=
            johnson_bound h_johnson_strong
        _ ≤ q * (d : ℚ) * n := by
            set D0 : ℚ := d / n
            set E0 : ℚ := e / n
            set Den : ℚ := D0 - 2 * E0 + frac * E0 ^ 2
            have quad_nonneg : (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by linarith
            have one_div_q_le : (1 : ℚ) / q ≤ frac - 1 := by
              rw [show frac - 1 = 1 / (q - 1) by
                simp only [frac]; rw [div_sub_one hq1_pos.ne', sub_sub_cancel]]
              exact one_div_le_one_div_of_le hq1_pos (by linarith)
            -- Expand and cancel frac from JohnsonDenominator.
            have denom_expansion : JohnsonDenominator B' v =
                frac * (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2) := by
              change (1 - frac * JohnsonBound.e B' v / n) ^ 2 -
                (1 - frac * JohnsonBound.d B' / n) = _
              ring
            have term_simplification : (frac * JohnsonBound.d B' / (n : ℚ)) /
                JohnsonDenominator B' v =
                (JohnsonBound.d B' / n) /
                (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2) := by
              rw [denom_expansion, mul_div_assoc, mul_div_mul_left _ _ hfrac_pos.ne']
            -- Bound eB' by e.
            have e_ineq : JohnsonBound.e B' v ≤ e := by
              have := JohnsonBound.e_ball_le_radius (B := B) v (e : ℚ)
                (by simp only [Nat.cast_le]; exact (show 0 < B'.card by omega))
              simp only [Nat.cast_le] at this
              exact this
            -- Denominator positivity.
            have hden1_pos : (0 : ℚ) <
                JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2 := by
              have hdenJ := johnson_condition_strong_iff_johnson_denom_pos.1 h_johnson_strong
              rw [denom_expansion] at hdenJ
              exact pos_of_mul_pos_right hdenJ hfrac_pos.le
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
              · have hE0 : E0 = 0 := by simp only [E0, he0, Nat.cast_zero, zero_div]
                calc (1 : ℚ) / (q * (n : ℚ) ^ 2)
                    ≤ D0 := johnson_den_lb_e_zero hn_pos_nat (one_le_two.trans q_not_small)
                      (by exact_mod_cast d_not_small)
                  _ = Den := by simp only [Den, hE0]; ring
              · exact johnson_den_lb_e_pos hn_pos he0 one_div_q_le
                  (sub_pos.mpr hfrac_gt1) quad_nonneg
            rw [term_simplification]
            calc (JohnsonBound.d B' / n) /
                    (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                      frac * (JohnsonBound.e B' v / n) ^ 2)
                ≤ (d / n) / (d / n - 2 * e / n + frac * (e / n) ^ 2) := worst_case_bound
              _ = (d / n) / Den := by rw [mul_div_assoc]
              _ ≤ (d / n) / ((1 : ℚ) / (q * (n : ℚ) ^ 2)) :=
                  div_le_div_of_nonneg_left
                    (div_nonneg (by exact_mod_cast Nat.zero_le d) hn_nonneg)
                    (one_div_pos.mpr (mul_pos hq_pos hn2_pos)) hden_lb
              _ = q * d * n := by field_simp [ne_of_gt hq_pos, ne_of_gt hn_pos]

end JohnsonBound

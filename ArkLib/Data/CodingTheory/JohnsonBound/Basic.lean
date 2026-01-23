/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Lemmas

namespace JohnsonBound

/-!
This module is based on the Johnson Bound section from [listdecoding].
In what follows we reference theorems from [listdecoding] by default.

## References

* [Guruswami, V. and others, *Algorithmic results in list decoding*][listdecoding]
* [Guruswami, V., Rudra, A., and Sudan, M., *Essential coding theory*][codingtheory]
-/

variable {n : ℕ}
         {F : Type} [Fintype F] [DecidableEq F]
         {B : Finset (Fin n → F)} {v : Fin n → F}

/-- The denominator of the bound from Theorem 3.1.
-/
def JohnsonDenominator (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  let e := e B v
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  (1- frac * e/n) ^ 2 - (1 - frac * d/n)

lemma johnson_denominator_def :
  JohnsonDenominator B v = ((1 - ((Fintype.card F) / (Fintype.card F - 1)) * (e B v / n)) ^ 2
      - (1 - ((Fintype.card F) / (Fintype.card F - 1)) * (d B/n))) := by
  simp [JohnsonDenominator]
  field_simp

/-- The bound from `Theorem 3.1` makes sense only if the denominator is positive.
This condition ensures that holds.
-/
def JohnsonConditionStrong (B : Finset (Fin n → F)) (v : Fin n → F) : Prop :=
  let e := e B v
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  (1 - frac * d/n) < (1- frac * e/n) ^ 2

/-- The function used for `q`-ary Johnson Bound.
-/
noncomputable def J (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - Real.sqrt (1 - frac * δ))

/-- A lemma for proving sqrt_le_J
-/
lemma division_by_conjugate {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + b.sqrt ≠ 0) :
  a - (b).sqrt = (a^2 - b)/(a + b.sqrt) := by
  rw[eq_div_iff hnonzero]
  ring_nf
  simp_all

lemma sqrt_le_J {q δ : ℚ} (hq : q > 1) (hx0 : 0 ≤ δ) (hx1 : δ ≤ 1) (hqx : q / (q - 1) * δ ≤ 1) :
  1 - ((1-δ) : ℝ).sqrt ≤ J q δ := by
  unfold J
  set frac := q / (q - 1) with hfrac
  have hfrac_ge : frac ≥ 1 := by rw [hfrac, ge_iff_le, one_le_div] <;> grind
  have hx' : 1 - δ ≥ 0 := by linarith
  have hfracx' : 1 - frac * δ ≥ 0 := by nlinarith
  suffices 1 - √(1 - δ) ≤ (1 / frac) * (1 - √(1 - frac * δ)) by simpa
  rw[
    division_by_conjugate (by exact_mod_cast hx') (by positivity),
    division_by_conjugate (by exact_mod_cast hfracx') (by positivity)]
  have : δ = 1 - (1 - δ) := by ring
  have : frac * δ = 1 - (1 - frac * δ) := by ring
  field_simp
  norm_cast
  gcongr
  have : 1 * δ  ≤ frac * δ  := by exact mul_le_mul_of_nonneg_right hfrac_ge hx0
  simp at this
  exact this

/-- The `q`-ary Johnson bound.
-/
def JohnsonConditionWeak (B : Finset (Fin n → F)) (e : ℕ) : Prop :=
  let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let q : ℚ := Fintype.card F
  (e : ℚ) / n < J q (d / n)

lemma johnson_condition_weak_implies_strong [Field F]
  {B : Finset (Fin n → F)}
  {v : Fin n → F}
  {e : ℕ}
  (h_J_cond_weak : JohnsonConditionWeak B e)
  (h_B2_not_one : 1 < (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)).card)
  (h_F_nontriv : 2 ≤ Fintype.card F)
  :
  JohnsonConditionStrong (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)) v := by
  --We show that n > 0, the theorem is ill-posed in this case but it follows from our assumptions.
  have h_n_pos : 0 < n := by
    by_contra hn
    push_neg at hn
    have : n = 0 := by omega
    subst this
    have B_singleton : B.card ≤ 1 := by
      have : ∀ u ∈ B, ∀ v ∈ B, u = v := by
        intros u hu v hv
        funext s
        exact Fin.elim0 s
      have : ¬∃ (u v : B), u ≠ v := by grind
      have neg_of_ineq := (Fintype.one_lt_card_iff.1).mt this
      simp at neg_of_ineq
      exact neg_of_ineq
    have B2_too_small : (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)).card ≤ 1 := by
      have B_supset : B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _) ⊆ B := by grind
      have eval_cards := Finset.card_le_card B_supset
      linarith
    omega
  unfold JohnsonConditionStrong
  intro e_1 d q frac
  -- The real 'proof' is not really by cases, the second case is uninteresting in practice.
  -- However, the theorem still holds when 1 - frac * d / ↑n < 0 and we prove both cases to avoid
  -- adding unnecessary assumptions.
  by_cases h_dsqrt_pos : (0 : ℝ)  ≤ 1 - frac * d / ↑n
  · have h_B2_nonempty : (0 : ℚ) < ((B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)).card : ℚ)
      := by norm_cast; omega
    have h_frac_pos : frac > 0 := by
      unfold frac
      have : 1 < Fintype.card F := by linarith
      field_simp
      unfold q
      exact_mod_cast this
    --The main proof is here, and in the proof of err_n, the rest is algebraic manipulations.
    have j_fun_bound : (↑e / ↑n : ℝ) < (1/↑frac * (1-√(1 - ↑frac * ↑d / ↑n)))  := by
      unfold JohnsonConditionWeak J at h_J_cond_weak
      simp_all
      let d_weak := sInf {d | ∃ u ∈ B, ∃ v ∈ B, ¬u=v ∧ Δ₀(u,v)=d}
      have d_subset : ↑d_weak ≤ (d : ℚ)  := by
          unfold d
          unfold JohnsonBound.d
          unfold d_weak
          have min_dist := min_dist_le_d h_B2_not_one
          have subset_inf_ineq : sInf {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d} ≤
              sInf {d |
              ∃ u ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              ∃ v_1 ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              u ≠ v_1 ∧ Δ₀(u, v_1) = d}:= by
              have subset : {d |
                          ∃ u ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
                          ∃ v_1 ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
                          u ≠ v_1 ∧ Δ₀(u, v_1) = d}
                          ⊆ {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d} := by
                intro d ⟨u, hu_in, v_1, hv_in, hne, heq⟩
                exact
                  ⟨u, by simp at hu_in; exact hu_in.1, v_1
                  , by simp at hv_in; exact hv_in.1, hne, heq⟩
              gcongr
              obtain ⟨u, hu, v_1, hv_1, hne⟩ := Finset.one_lt_card.mp h_B2_not_one
              use Δ₀(u, v_1)
              exact ⟨u, hu, v_1, hv_1, hne, rfl⟩
          calc ↑d_weak
              = ↑(sInf {d | ∃ u ∈ B, ∃ v ∈ B, ¬u = v ∧ Δ₀(u, v) = d}) := by rfl
            _ ≤ ↑(sInf {d |
              ∃ u ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              ∃ v_1 ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              u ≠ v_1 ∧ Δ₀(u, v_1) = d}):= by exact_mod_cast subset_inf_ineq
            _ ≤ JohnsonBound.d (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)) := by exact_mod_cast min_dist
      have bound: (↑frac)⁻¹ * (1 - √(1 - ↑frac * ↑d_weak / ↑n))
        ≤ (↑frac)⁻¹ * (1 - √(1 - ↑frac * ↑d / ↑n)) := by
        have ineq1 : (↑d_weak / ↑n) ≤ (d / ↑n) := by
          rw[←mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr h_n_pos)]
          field_simp
          exact d_subset
        have ineq2 : frac * (d_weak / n) ≤ frac * (d / n) := by
          exact_mod_cast (mul_le_mul_iff_of_pos_left h_frac_pos).mpr ineq1
        have ineq3 : 1 - frac * (d / n) ≤ 1 - frac * (d_weak / n ) := by linarith
        have ineq3' : (1 : ℝ) - frac * d / n ≤ (1 : ℝ) - frac * d_weak / n := by
          norm_cast; grind
        have ineq4 : √(1 - ↑frac * ↑d / ↑n) ≤ √(1 - ↑frac * ↑d_weak / ↑n) :=
          by exact Real.sqrt_le_sqrt ineq3'
        have ineq5 :  (1 - √(1 - ↑frac * ↑d_weak / ↑n)) ≤ (1 - √(1 - ↑frac * ↑d / ↑n)) := by
          linarith
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
      linarith
    have err_n : (↑e_1 / ↑n : ℝ) ≤ (↑e / ↑n : ℝ)   := by
      gcongr
      have err : e_1 ≤ e := by
          unfold e_1
          dsimp[JohnsonBound.e]
          have : ∀ x ∈ B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _), Δ₀(v, x) ≤ e := by
            unfold hammingDist
            simp
            (simp_rw [eq_comm] ; grind)
          have sum_bound :=
            Finset.sum_le_card_nsmul (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _))
              (fun x => Δ₀(v, x)) e this
          simp
          rw[inv_mul_le_iff₀ h_B2_nonempty]
          exact_mod_cast sum_bound
      exact_mod_cast err
    have j_fun_bound_e1 : (↑e_1 / ↑n : ℝ) < (1/↑frac * (1-√(1 - ↑frac * ↑d / ↑n))) :=
      by linarith [err_n, j_fun_bound]
    have rearrange_jboundw_e1 : √(1 - ↑frac * ↑d / ↑n) < 1 - frac * e_1 / ↑n := by
      have : frac * e_1 / ↑n < 1-√(1 - frac * d / ↑n) := by
        calc ↑frac * ↑e_1 / ↑n
            = ↑frac * (↑e_1 / ↑n) := by ring
          _ < ↑frac * (1/↑frac * (1-√(1 - ↑frac * ↑d / ↑n))) := by
              exact (mul_lt_mul_left (by exact_mod_cast h_frac_pos)).mpr j_fun_bound_e1
          _ = 1-√(1 - ↑frac * ↑d / ↑n) := by ring_nf ; field_simp
      linarith
    have h_esqrtpos :  (0 : ℝ)  ≤ 1- frac * e_1 / ↑n  := by
      have : (0 : ℝ) ≤ √(1 - ↑frac * ↑d / ↑n) := by aesop
      linarith[this, rearrange_jboundw_e1]
    suffices recast_main_goal : (1 - frac * d / ↑n : ℝ) < (1 - frac * e_1 / ↑n) ^ 2 by
     exact_mod_cast recast_main_goal
    suffices roots : √(1 - frac * d / ↑n) < 1- frac * e_1 / ↑n by
      rw[←Real.sqrt_lt h_dsqrt_pos h_esqrtpos]
      exact_mod_cast roots
    exact rearrange_jboundw_e1
  · have strict_neg : 1 - ↑frac * ↑d / ↑n < (0 : ℚ) := by
      have : ¬(0 : ℚ)  ≤ 1 - frac * d / ↑n := by exact_mod_cast h_dsqrt_pos
      rw[Rat.not_le] at this
      exact this
    have nonneg : (0 : ℝ) ≤(1 - ↑frac * ↑e_1 / ↑n) ^ 2  :=
      by exact_mod_cast sq_nonneg (1 - frac * ↑e_1 / ↑n)
    calc 1 - ↑frac * ↑d / ↑n < (0 : ℚ) := strict_neg
      _ ≤ (1 - ↑frac * ↑e_1 / ↑n) ^ 2 := by exact_mod_cast nonneg

private lemma johnson_condition_strong_implies_n_pos
  (h_johnson : JohnsonConditionStrong B v)
  :
  0 < n := by
  cases n <;> try simp [JohnsonConditionStrong] at *

private lemma johnson_condition_strong_implies_2_le_F_card
  (h_johnson : JohnsonConditionStrong B v)
  :
  2 ≤ Fintype.card F := by
  revert h_johnson
  dsimp [JohnsonConditionStrong]
  rcases Fintype.card F with _ | _ | _ <;> aesop

private lemma johnson_condition_strong_implies_2_le_B_card
  (h_johnson : JohnsonConditionStrong B v)
  :
  2 ≤ B.card := by
  dsimp [JohnsonConditionStrong] at h_johnson
  rcases eq : B.card with _ | card | _ <;> [simp_all [e, d]; skip; omega]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 eq
  replace h_johnson : 1 < |1 - (Fintype.card F) / ((Fintype.card F) - 1) * Δ₀(v, a) / (n : ℚ)| := by
    simp_all [e, d, choose_2]
  generalize eq₁ : Fintype.card F = q
  rcases q with _ | _ | q <;> [simp_all; simp_all; skip]
  have h : (Fintype.card F : ℚ) / (Fintype.card F - 1) = 1 + 1 / (Fintype.card F - 1) := by
    have : (Fintype.card F : ℚ) - 1 ≠ 0 := by simp [sub_eq_zero]; omega
    field_simp
  have h' := JohnsonBound.abs_one_sub_div_le_one (v := v) (a := a) (by omega)
  exact absurd (lt_of_lt_of_le (h ▸ h_johnson) h') (lt_irrefl _)

/-- `JohnsonConditionStrong` is equvalent to `JohnsonDenominator` being positive.
-/
lemma johnson_condition_strong_iff_johnson_denom_pos {B : Finset (Fin n → F)} {v : Fin n → F} :
  JohnsonConditionStrong B v ↔ 0 < JohnsonDenominator B v := by
  simp [JohnsonDenominator, JohnsonConditionStrong]

/-- Theorem 3.1.
-/
theorem johnson_bound [Field F]
  (h_condition : JohnsonConditionStrong B v)
  :
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  B.card ≤ (frac * d/n) / JohnsonDenominator B v
  := by
  suffices B.card * JohnsonDenominator B v ≤
           Fintype.card F / (Fintype.card F - 1) * d B / n by
    rw [johnson_condition_strong_iff_johnson_denom_pos] at h_condition
    rw [←mul_le_mul_right h_condition]
    convert this using 1
    field_simp; rw [mul_div_mul_right]; linarith
  rw [johnson_denominator_def]
  exact JohnsonBound.johnson_bound_lemma
    (johnson_condition_strong_implies_n_pos h_condition)
    (johnson_condition_strong_implies_2_le_B_card h_condition)
    (johnson_condition_strong_implies_2_le_F_card h_condition)

/-- Alphabet-free Johnson bound from [codingtheory].
-/
theorem johnson_bound_alphabet_free [Field F] [DecidableEq F]
  {B : Finset (Fin n → F)}
  {v : Fin n → F}
  {e : ℕ}
  (hB : 1 < B.card)
  :
  let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  e ≤ n - ((n * (n - d)) : ℝ).sqrt
  →
  (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card ≤ q * d * n := by
    -- the proof mostly organized as in the instructions in issue #235,
    -- one major difference is the frac*d/n > 1 subcase which is not covered in the issue.
    intro d q frac h
    let B' := B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)
    -- Helper bounds on parameters.
    have q_not_small : q ≥ (2 : ℚ) := by
      have hF : (2 : ℕ) ≤ Fintype.card F := by
        classical
        have : 1 < Fintype.card F := by
          simpa [Fintype.one_lt_card_iff] using (⟨(0:F), (1:F), by simp⟩ : ∃ a b : F, a ≠ b)
        omega
      simpa [q] using (show (2 : ℚ) ≤ (Fintype.card F : ℚ) from by exact_mod_cast hF)
    have d_not_small : d ≥ 1 := by
      let S : Set ℕ := {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d}
      have hS_nonempty : S.Nonempty := by
        rcases Finset.one_lt_card.mp hB with ⟨u, hu, v, hv, huv⟩
        refine ⟨hammingDist u v, ?_⟩
        exact ⟨u, hu, v, hv, huv, rfl⟩
      have hLB : ∀ s ∈ S, (1 : ℕ) ≤ s := by
        intro s hs
        rcases hs with ⟨u, hu, v, hv, huv, hdist⟩
        have hpos : 0 < hammingDist u v := hammingDist_pos.mpr huv
        have : 1 ≤ hammingDist u v := (Nat.succ_le_iff).2 hpos
        simpa [S] using (hdist ▸ this)
      simpa [S] using (sInf.le_sInf_of_LB (S := S) hS_nonempty (i := 1) hLB)
    have n_not_small : n ≥ 1 := by
      by_contra hn
      have : n = 0 := by omega
      subst this
      have hcard_le : B.card ≤ 1 := by
        have : ∀ u ∈ B, ∀ v ∈ B, u = v := by
          intro u hu v hv
          funext s
          exact Fin.elim0 s
        exact Finset.card_le_one.2 (by
          intro a ha b hb
          exact this a ha b hb)
      omega

    -- Lower bound on RHS for the small-cardinality case.
    have qdn_not_small : (q * d * n) ≥ 2 := by
      simpa [mul_assoc] using
        (johnson_qdn_ge_two (q := q) (d := d) (n := n) q_not_small d_not_small n_not_small)

    by_cases h_size : B'.card < 2
    -- Case: B'.card < 2 (trivial case)
    · have hcard_nat : B'.card ≤ 1 := by exact Nat.le_of_lt_succ h_size
      have hcard : (B'.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hcard_nat
      have rhs_ge_two : (2 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by simpa [mul_assoc] using qdn_not_small
      have rhs_ge_one : (1 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) :=
        le_trans (by norm_num : (1 : ℚ) ≤ 2) rhs_ge_two
      exact le_trans hcard rhs_ge_one

    -- Case: B'.card ≥ 2
    · have hd_le_dB' : (d : ℚ) ≤ JohnsonBound.d B' := by
        have hB'_gt : 1 < B'.card := by omega
        let S : Set ℕ :=
          {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d}
        let S' : Set ℕ :=
          {d | ∃ u ∈ B', ∃ v ∈ B', u ≠ v ∧ hammingDist u v = d}
        have hsubset : S' ⊆ S := by
          intro t ht
          rcases ht with ⟨u, hu, w, hw, huw, hdist⟩
          have hu' : u ∈ B := by
            have hu'' := hu
            simp [B'] at hu''
            exact hu''.1
          have hw' : w ∈ B := by
            have hw'' := hw
            simp [B'] at hw''
            exact hw''.1
          exact ⟨u, hu', w, hw', huw, hdist⟩
        have hS'nonempty : S'.Nonempty := by
          obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB'_gt
          refine ⟨hammingDist u w, ?_⟩
          exact ⟨u, hu, w, hw, huw, rfl⟩
        have h_inf : sInf S ≤ sInf S' := by
          have hmem : sInf S' ∈ S := hsubset (Nat.sInf_mem hS'nonempty)
          exact Nat.sInf_le hmem
        let dmin : ℕ := sInf S'
        have h_inf_nat : d ≤ dmin := by
          simpa [d, S, S', dmin] using h_inf
        have h_inf_q : (d : ℚ) ≤ (dmin : ℚ) := by
          exact_mod_cast h_inf_nat
        have h_min : (dmin : ℚ) ≤ JohnsonBound.d B' := by
          simpa [S', dmin] using (min_dist_le_d (B := B') (by simpa using hB'_gt))
        exact le_trans h_inf_q h_min
      by_cases h_d_close_n : q / (q - 1) * (d / n) > 1
      -- Subcase: frac*d/n > 1 (the case not very realistic but possible we will directly prove JohnsonConditionStrong here)
      · have hfrac_dB'_gt_one : q/(q-1) * (JohnsonBound.d B' / n) > 1 := by
          have hn_nonneg : (0 : ℚ) ≤ n := by
            exact_mod_cast (Nat.cast_nonneg n)
          have h_div_le : (d : ℚ) / n ≤ JohnsonBound.d B' / n := by
            exact div_le_div_of_nonneg_right hd_le_dB' hn_nonneg
          have hfrac_nonneg : (0 : ℚ) ≤ q / (q - 1) := by
            have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
            have hq1_nonneg : (0 : ℚ) ≤ q - 1 := by linarith [q_not_small]
            exact div_nonneg hq_nonneg hq1_nonneg
          have h_mul_le :
              q / (q - 1) * (d / n) ≤ q / (q - 1) * (JohnsonBound.d B' / n) := by
            exact mul_le_mul_of_nonneg_left h_div_le hfrac_nonneg
          exact lt_of_lt_of_le h_d_close_n h_mul_le
        have h_strong : JohnsonConditionStrong B' v := by
          have hneg :
              (1 - (q / (q - 1)) * (JohnsonBound.d B' / n) : ℚ) < 0 := by
            linarith [hfrac_dB'_gt_one]
          have hnonneg :
              (0 : ℚ) ≤ (1 - (q / (q - 1)) * (JohnsonBound.e B' v / n)) ^ 2 := by
            exact sq_nonneg (1 - (q / (q - 1)) * (JohnsonBound.e B' v / n))
          have hgoal :
              (1 - (q / (q - 1)) * (JohnsonBound.d B' / n) : ℚ) <
                (1 - (q / (q - 1)) * (JohnsonBound.e B' v / n)) ^ 2 := by
            exact lt_of_lt_of_le hneg hnonneg
          simpa [JohnsonConditionStrong, q, mul_div_assoc] using hgoal

        have johnson_result := johnson_bound h_strong
        have current_bound :
            (B'.card : ℚ) ≤
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v := by
          simpa using johnson_result

        have hden_ge :
            JohnsonDenominator B' v ≥
              frac * (JohnsonBound.d B') / (n : ℚ) - 1 := by
          simpa [JohnsonDenominator, q, frac, mul_div_assoc] using
            (johnson_den_ge_frac_d (B := B') (v := v))
        have hgap : frac * (JohnsonBound.d B') / (n:ℚ) - 1 ≥ 1 / ((n:ℚ) * (q-1)) := by
          simpa [q, frac] using
            (johnson_gap_frac_d_gt_one (B := B')
              (q_not_small := by simpa [q] using q_not_small)
              (n_not_small := n_not_small)
              (h_d_close_n := by simpa [q, frac] using h_d_close_n)
              (hd_le_dB := hd_le_dB'))
        have hfrac_bound :
            (frac * (JohnsonBound.d B') / (n:ℚ)) / JohnsonDenominator B' v ≤
            q * JohnsonBound.d B' := by
          have hden_lb : (1 : ℚ) / ((n : ℚ) * (q - 1)) ≤ JohnsonDenominator B' v := by
            linarith [hden_ge, hgap]
          have hn_pos_nat : 0 < n := (Nat.succ_le_iff).1 n_not_small
          have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos_nat
          have hq1_pos : (0 : ℚ) < q - 1 := by linarith [q_not_small]
          have hden_pos : (0 : ℚ) < (1 : ℚ) / ((n : ℚ) * (q - 1)) := by
            have hmul_pos : (0 : ℚ) < (n : ℚ) * (q - 1) := by
              exact mul_pos hn_pos hq1_pos
            exact one_div_pos.mpr hmul_pos
          have hnum_nonneg : (0 : ℚ) ≤ frac * (JohnsonBound.d B') / (n : ℚ) := by
            have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (Nat.zero_le d)
            have hd_nonneg : (0 : ℚ) ≤ JohnsonBound.d B' := by
              exact le_trans hd0 hd_le_dB'
            have hfrac_nonneg : (0 : ℚ) ≤ frac := by
              have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
              have hq1_nonneg : (0 : ℚ) ≤ q - 1 := by linarith [q_not_small]
              exact div_nonneg hq_nonneg hq1_nonneg
            have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
            have hmul_nonneg : (0 : ℚ) ≤ frac * JohnsonBound.d B' := by
              exact mul_nonneg hfrac_nonneg hd_nonneg
            exact div_nonneg hmul_nonneg hn_nonneg
          have hstep :
              (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v ≤
              (frac * (JohnsonBound.d B') / (n : ℚ)) /
                (1 / ((n : ℚ) * (q - 1))) := by
            exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_lb
          calc
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v
                ≤ (frac * (JohnsonBound.d B') / (n : ℚ)) /
                    (1 / ((n : ℚ) * (q - 1))) := hstep
            _ = q * JohnsonBound.d B' := by
                  have hn_ne : (n : ℚ) ≠ 0 := by exact ne_of_gt hn_pos
                  have hq1_ne : (q - 1 : ℚ) ≠ 0 := by exact ne_of_gt hq1_pos
                  field_simp [frac, hn_ne, hq1_ne]
                  simp [mul_comm]
        have le_q_times_d : (B'.card : ℚ) ≤ q * JohnsonBound.d B' := by
          linarith [current_bound, hfrac_bound]
        have le_q_times_n : (B'.card : ℚ) ≤ q * (n : ℚ) := by
          have hB'_ge2 : 2 ≤ B'.card := by
            exact le_of_not_gt h_size
          have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
          have hd_le_n : JohnsonBound.d B' ≤ (n : ℚ) := by
            simpa using (johnson_d_le_n (B := B') hB'_ge2)
          exact le_trans le_q_times_d (mul_le_mul_of_nonneg_left hd_le_n hq_nonneg)
        have final : (B'.card : ℚ) ≤ q * d * (n : ℚ) := by
          have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
          have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
          have hqn_nonneg : (0 : ℚ) ≤ q * (n : ℚ) := by
            exact mul_nonneg hq_nonneg hn_nonneg
          have hd_ge1 : (1 : ℚ) ≤ (d : ℚ) := by
            exact_mod_cast d_not_small
          have hstep : q * (n : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by
            have hmul :
                q * (n : ℚ) * (1 : ℚ) ≤ q * (n : ℚ) * (d : ℚ) := by
              exact mul_le_mul_of_nonneg_left hd_ge1 hqn_nonneg
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact le_trans le_q_times_n hstep
        exact_mod_cast final

      -- Subcase: frac*d/n ≤ 1 (main case, we will prove JohnsonConditionStrong through JohnsonConditionWeak)
      · have d_le_n : d ≤ n := by
          let S : Set ℕ :=
            {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d}
          obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB
          have hdist_le : hammingDist u v ≤ n := by
            simpa using (hammingDist_le_card_fintype (x := u) (y := v))
          have hdist_in : hammingDist u v ∈ S := by
            exact ⟨u, hu, v, hv, huv, rfl⟩
          have hdist_ge : d ≤ hammingDist u v := by
            simpa [d, S] using (Nat.sInf_le hdist_in)
          exact le_trans hdist_ge hdist_le
        -- Helper positivity facts for the main-case algebra.
        have hn_pos_nat : 0 < n := (Nat.succ_le_iff).1 n_not_small
        have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos_nat
        have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        have hq_pos : (0 : ℚ) < q := by linarith [q_not_small]
        have hq1_pos : (0 : ℚ) < q - 1 := by linarith [q_not_small]
        have hq_ne : (q : ℚ) ≠ 0 := by exact ne_of_gt hq_pos
        have hq1_ne : (q - 1 : ℚ) ≠ 0 := by exact ne_of_gt hq1_pos
        have hfrac_pos : (0 : ℚ) < frac := by
          exact div_pos hq_pos hq1_pos
        have hfrac_gt1 : (1 : ℚ) < frac := by
          have hq1_lt : (q - 1 : ℚ) < q := by linarith
          have h := (one_lt_div hq1_pos).2 hq1_lt
          simpa [frac] using h
        have hfrac_ne : (frac : ℚ) ≠ 0 := by
          simpa [frac] using (div_ne_zero hq_ne hq1_ne)
        have hn2_nonneg : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by
          exact sq_nonneg (n : ℚ)
        have hn2_pos : (0 : ℚ) < (n : ℚ) ^ 2 := by
          exact pow_pos hn_pos _
        have h_johnson_strong : JohnsonConditionStrong B' v := by
          have h_johnson_weak : JohnsonConditionWeak B e := by
            have h_muln : (e : ℚ) / n ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt := by
              by_cases hn : n = 0
              · subst hn
                simp
              · have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
                  exact_mod_cast (Nat.cast_nonneg n)
                have hn' : (n : ℝ) ≠ 0 := by
                  exact_mod_cast hn
                have h_div : (e : ℝ) / n ≤ (n - ((n * (n - d) : ℝ).sqrt)) / n := by
                  exact (div_le_div_of_nonneg_right (by simpa using h) hn_nonneg)
                have h_div' : (e : ℝ) / n ≤ 1 - ((n * (n - d) : ℝ).sqrt) / n := by
                  simpa [sub_div, hn'] using h_div
                have h_sqrt :
                    ((n * (n - d) : ℝ).sqrt) / n =
                    ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                  have hsq_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by
                    exact sq_nonneg (n : ℝ)
                  calc
                    ((n * (n - d) : ℝ).sqrt) / n
                        = ((n * (n - d) : ℝ).sqrt) / ((n : ℝ) ^ 2).sqrt := by
                            have h_sqrt_n : ((n : ℝ) ^ 2).sqrt = (n : ℝ) := by
                              simp [hn_nonneg]
                            simp [h_sqrt_n]
                    _ = (((n * (n - d) : ℝ) / (n : ℝ) ^ 2).sqrt) := by
                            symm
                            exact Real.sqrt_div' ((n : ℝ) * (n - d)) hsq_nonneg
                    _ = (((n - d) / n : ℝ).sqrt) := by
                            have hfrac : ((n : ℝ) * (n - d)) / (n : ℝ) ^ 2 = (n - d) / n := by
                              field_simp [hn']
                              ring
                            simp [hfrac]
                    _ = ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                            calc
                              ((n - d) / n : ℝ).sqrt
                                  = (((n : ℝ) - (d : ℝ)) / n).sqrt := by
                                    simp
                              _ = ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                                    simp [sub_div, hn']
                have h_final :
                    (e : ℝ) / n ≤ 1 - ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                  calc
                    (e : ℝ) / n ≤ 1 - ((n * (n - d) : ℝ).sqrt) / n := h_div'
                    _ = 1 - ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                        rw [h_sqrt]
                simpa using h_final
            have h_J_bound : 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt ≤ J q (d / n) := by
              have hq : q > 1 := by
                classical
                have hF : (2 : ℕ) ≤ Fintype.card F := by
                  have : 1 < Fintype.card F := by
                    simpa [Fintype.one_lt_card_iff] using
                      (⟨(0 : F), (1 : F), by simp⟩ : ∃ a b : F, a ≠ b)
                  omega
                have hq2 : (2 : ℚ) ≤ q := by
                  simpa [q] using
                    (show (2 : ℚ) ≤ (Fintype.card F : ℚ) from by exact_mod_cast hF)
                linarith
              have hx0 : (0 : ℚ) ≤ d / n := by
                exact div_nonneg (by exact_mod_cast (Nat.cast_nonneg d))
                  (by exact_mod_cast (Nat.cast_nonneg n))
              have hx1 : d / n ≤ (1 : ℚ) := by
                by_cases hn : n = 0
                · simp [hn]
                · have hnpos : (0 : ℚ) < n := by
                    exact_mod_cast (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
                  have hd : (d : ℚ) ≤ n := by exact_mod_cast d_le_n
                  exact (div_le_one hnpos).2 hd
              have hqx : q / (q - 1) * (d / n) ≤ (1 : ℚ) := by
                exact le_of_not_gt h_d_close_n
              simpa using (sqrt_le_J (q := q) (δ := d / n) hq hx0 hx1 hqx)
            have h_le : (e : ℚ) / n ≤  J q (d / n) := by
              linarith [h_muln ,h_J_bound]
            have h_ne : ((e : ℚ) / n : ℝ)  ≠  J q (d / n) := by
              have hd_pos : 0 < d := (Nat.succ_le_iff).1 d_not_small
              have hq : 1 < q := by linarith [q_not_small]
              exact johnson_e_div_ne_J (n := n) (d := d) (e := e) (q := q)
                hn_pos_nat hd_pos hq h_muln h_J_bound (le_of_not_gt h_d_close_n)
            exact lt_of_le_of_ne h_le h_ne
          have h_size' : 1 < B'.card := by
            omega
          have hF_nontriv : (2 : ℕ) ≤ Fintype.card F := by
            have : 1 < Fintype.card F := by
              simpa [Fintype.one_lt_card_iff] using (⟨(0:F), (1:F), by simp⟩ : ∃ a b : F, a ≠ b)
            omega
          exact johnson_condition_weak_implies_strong h_johnson_weak h_size' hF_nontriv

        have johnson_result := johnson_bound h_johnson_strong

        have current_bound :
            (B'.card : ℚ) ≤
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v := by
          simpa using johnson_result

        -- Core inequality from the hypothesis (reused below).
        have h_div' :
            1 - (d : ℝ) / n ≤ (1 - (e : ℝ) / n) ^ 2 := by
          exact JohnsonBound.johnson_hyp_implies_div_ineq
            (n := n) (d := d) (e := e) hn_pos_nat d_le_n h
        have h_div'_q : (1 - (d / n : ℚ)) ≤ (1 - (e / n : ℚ)) ^ 2 := by
          have h_div'_real :
              ((1 - (d / n : ℚ)) : ℝ) ≤ ((1 - (e / n : ℚ)) ^ 2 : ℝ) := by
            simpa using h_div'
          exact_mod_cast h_div'_real

        have last_bound :
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v ≤
            q * (d : ℚ) * (n : ℚ) := by
          set D0 : ℚ := d / n
          set E0 : ℚ := e / n
          set Den : ℚ := D0 - 2 * E0 + frac * E0 ^ 2
          have quad_nonneg : (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by
            have htmp_q :
                (0 : ℚ) ≤ (1 - (e / n : ℚ)) ^ 2 - (1 - (d / n : ℚ)) := by
              linarith [h_div'_q]
            have h_eq_q :
                (1 - (e / n : ℚ)) ^ 2 - (1 - (d / n : ℚ)) =
                  D0 - 2 * E0 + E0 ^ 2 := by
              ring
            simpa [h_eq_q] using htmp_q
          have frac_sub_one_eq : frac - 1 = (1 : ℚ) / (q - 1) := by
            field_simp [frac, hq1_ne]
          have one_div_q_le : (1 : ℚ) / q ≤ frac - 1 := by
            have hq1_le_q : (q - 1 : ℚ) ≤ q := by linarith
            have h1 : (1 : ℚ) / q ≤ (1 : ℚ) / (q - 1) := by
              exact (one_div_le_one_div_of_le hq1_pos hq1_le_q)
            simpa [frac_sub_one_eq] using h1
          -- 1. Expand JohnsonDenominator.
          have denom_expansion : JohnsonDenominator B' v =
              frac * (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
              frac * (JohnsonBound.e B' v / n)^2) := by
            simp [JohnsonDenominator, q, frac, mul_div_assoc]
            ring

          -- 2. Cancel frac.
          have term_simplification : (frac * (JohnsonBound.d B') / (n : ℚ)) /
              JohnsonDenominator B' v =
              (JohnsonBound.d B' / n) /
              (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
              frac * (JohnsonBound.e B' v / n)^2) := by
            set D : ℚ :=
              JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2
            calc
              (frac * JohnsonBound.d B' / (n : ℚ)) / JohnsonDenominator B' v
                  = (frac * (JohnsonBound.d B' / n)) / JohnsonDenominator B' v := by
                      simp [mul_div_assoc]
              _ = (frac * (JohnsonBound.d B' / n)) / (frac * D) := by
                      simp [denom_expansion, D]
              _ = (JohnsonBound.d B' / n) / D := by
                      simpa [D] using
                        (mul_div_mul_left (a := JohnsonBound.d B' / n) (b := D)
                          (c := frac) hfrac_ne)

          -- 3. Bound eB' by e.
          have e_ineq : JohnsonBound.e B' v ≤ e := by
            have hB'_pos : 0 < B'.card := by
              have hB'_ge2 : 2 ≤ B'.card := by
                exact le_of_not_gt h_size
              omega
            simpa [B'] using
              (JohnsonBound.e_ball_le_radius (B := B) (v := v) (r := (e : ℚ))
                (by simpa [B'] using hB'_pos))

          -- 4. Bound dB' by d.
          have d_ineq : (d : ℚ) ≤ JohnsonBound.d B' := by
            simp[hd_le_dB']

          -- 5. Compare worst-case values (monotone).
          have worst_case_bound : (JohnsonBound.d B' / n) /
              (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
              frac * (JohnsonBound.e B' v / n)^2) ≤
              (d / n) / (d / n - 2 * e / n + frac * (e / n)^2) := by
            have hden1_pos :
                (0 : ℚ) <
                  JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                  frac * (JohnsonBound.e B' v / n) ^ 2 := by
              have hdenJ :
                  (0 : ℚ) < JohnsonDenominator B' v := by
                exact (johnson_condition_strong_iff_johnson_denom_pos).1 h_johnson_strong
              have hdenJ' :
                  (0 : ℚ) <
                    frac * (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                    frac * (JohnsonBound.e B' v / n) ^ 2) := by
                simpa [denom_expansion] using hdenJ
              have hdenJ'' :
                  (0 : ℚ) <
                    JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                    frac * (JohnsonBound.e B' v / n) ^ 2 := by
                rcases (mul_pos_iff.mp hdenJ') with hpos | hneg
                · exact hpos.2
                · exfalso
                  linarith [hneg.1, hfrac_pos]
              simpa [mul_div_assoc] using hdenJ''
            have hd_pos : 0 < d := (Nat.succ_le_iff).1 d_not_small
            exact johnson_worst_case_bound (B := B') (v := v) (n := n) (d := d) (e := e)
              (frac := frac) hn_pos hd_pos d_le_n h (le_of_not_gt h_d_close_n) hfrac_gt1
              e_ineq d_ineq quad_nonneg hden1_pos

          -- 6. Final algebraic bound.
          have final_calc : (d / n) / (d / n - 2 * e / n + frac * (e / n)^2) ≤
              q * d * n := by
            have hfrac1_pos : (0 : ℚ) < frac - 1 := by linarith [hfrac_gt1]
            have hbase_nonneg : (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by
              exact quad_nonneg
            have hden_lb : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ Den := by
              by_cases he0 : e = 0
              · subst he0
                have hq_ge1 : (1 : ℚ) ≤ q := by linarith [q_not_small]
                have hd_ge1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast d_not_small
                have hden : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (d : ℚ) / n := by
                  exact johnson_den_lb_e_zero (n := n) (d := d) (q := q)
                    hn_pos_nat hq_ge1 hd_ge1
                simpa [D0, E0, Den] using hden
              · exact johnson_den_lb_e_pos (n := n) (d := d) (e := e) (q := q) (frac := frac)
                  hn_pos hn_nonneg hn2_nonneg hq_ne one_div_q_le hfrac1_pos hbase_nonneg he0
            have hnum_nonneg : (0 : ℚ) ≤ d / n := by
              have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (Nat.zero_le d)
              exact div_nonneg hd0 hn_nonneg
            have hden_pos : (0 : ℚ) < (1 : ℚ) / (q * (n : ℚ) ^ 2) := by
              have hpos : (0 : ℚ) < q * (n : ℚ) ^ 2 := by
                exact mul_pos hq_pos hn2_pos
              exact one_div_pos.mpr hpos
            have hstep :
                (d / n) / Den ≤ (d / n) / ((1 : ℚ) / (q * (n : ℚ) ^ 2)) := by
              exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_lb
            calc
              (d / n) / (d / n - 2 * e / n + frac * (e / n) ^ 2)
                  = (d / n) / Den := by simp [Den, D0, E0, mul_div_assoc]
              _ ≤ (d / n) / ((1 : ℚ) / (q * (n : ℚ) ^ 2)) := hstep
              _ = q * d * n := by
                    field_simp [hq_ne, hn_pos.ne']
                    ring

          -- Combine the steps.
          rw [term_simplification]
          apply le_trans worst_case_bound
          exact final_calc

        exact le_trans current_bound last_bound

end JohnsonBound

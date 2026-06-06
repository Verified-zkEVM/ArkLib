/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Aristotle
-/

import ArkLib.Data.Probability.Notation
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Rat.Star
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.SimpleRing.Principal

open NNReal ENNReal unitInterval
open scoped ProbabilityTheory ENNReal NNReal BigOperators


/-! ## Schwartz-Zippel derived bound

We state and prove a counting version of the Schwartz-Zippel lemma for multivariate polynomials with
finitely many variables over a (possibly inifinite) field `F`.

The lemma is derived from mathlib's version `MvPolynomial.schwartz_zippel_sup_sum`.
-/

/-- For a nonzero multivariate polynomial `f` of total degree at most `d`, evaluated over a
product of finite subsets of a field `F`, each of cardinality at least `m`, the number of roots is
at most `d / m` multiplied by the side of the product set. -/
theorem schwartz_zippel_counting
    {F : Type*} [Field F] [DecidableEq F]
    {s : ℕ}
    (f : MvPolynomial (Fin s) F) (hf : f ≠ 0)
    (S : Fin s → Finset F)
    (d m : ℕ) (hd : f.totalDegree ≤ d) (hm_pos : 0 < m)
    (hm : ∀ i, m ≤ (S i).card) :
    (Finset.filter (fun x => MvPolynomial.eval x f = 0) (Fintype.piFinset S)).card * m
    ≤ d * ∏ i, (S i).card := by
  have h_schwartz_zippel : (Finset.card (Finset.filter (fun x => (MvPolynomial.eval x) f = 0)
      (Fintype.piFinset S))) / (∏ i, (S i).card : ℝ≥0∞) ≤ d / (m : ℝ≥0∞) := by
    convert MvPolynomial.schwartz_zippel_sup_sum hf S |> le_trans <| ?_ using 1
    rotate_left
    · exact d / m
    · simp only [div_eq_mul_inv, mul_comm, Finset.sup_le_iff, MvPolynomial.mem_support_iff, ne_eq]
      intro b hb
      have h_deg : ∑ i, b i ≤ d := by
        refine le_trans ?_ hd
        exact Finset.le_sup (f := fun s => Finsupp.sum s fun x e => e)
          (MvPolynomial.mem_support_iff.mpr hb) |> le_trans (by simp +decide [Finsupp.sum_fintype])
      refine le_trans (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (Nat.cast_le.mpr (hm i)))
          (Nat.cast_nonneg _)) ?_
      rw [← Finset.mul_sum _ _ _, mul_comm]; gcongr; norm_cast
    · rw [← ENNReal.toReal_le_toReal] <;> norm_num
      · rw [div_le_div_iff₀] <;> norm_cast <;> norm_num [Finset.prod_pos, hm_pos]
        · rw [div_le_div_iff₀] <;> norm_cast; norm_num [Finset.prod_pos, hm_pos]
          exact fun i => Finset.card_pos.mp (lt_of_lt_of_le hm_pos (hm i))
        · exact fun i => Finset.card_pos.mp (lt_of_lt_of_le hm_pos (hm i))
      · simp only [div_eq_top, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff, Fintype.mem_piFinset, not_forall,
        Decidable.not_not, natCast_ne_top, false_and, or_false, not_and, forall_exists_index]
        exact fun x hx hx' => Finset.prod_ne_zero_iff.mpr fun i _ =>
          Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le hm_pos (hm i)))
      · exact ENNReal.div_ne_top (by aesop) (by aesop)
  rw [ENNReal.div_le_iff_le_mul] at h_schwartz_zippel
  · rw [ENNReal.div_mul] at h_schwartz_zippel
    · rw [ENNReal.le_div_iff_mul_le] at h_schwartz_zippel
      · rw [mul_div, ENNReal.div_le_iff_le_mul] at h_schwartz_zippel <;> norm_cast at *
        · exact Or.inl <| Finset.prod_ne_zero_iff.mpr fun i _ =>
            ne_of_gt <| lt_of_lt_of_le hm_pos <| hm i
        · exact Or.inl <| ENNReal.natCast_ne_top _
      · simp only [ne_eq, ENNReal.div_eq_zero_iff, Nat.cast_eq_zero, hm_pos.ne', false_or]
        exact Or.inl <| ENNReal.prod_ne_top fun i _ => ENNReal.natCast_ne_top _
      · exact Or.inr (ENNReal.natCast_ne_top _)
    · exact Or.inl (by positivity)
    · exact Or.inl ENNReal.coe_ne_top
  · exact Or.inr (ENNReal.div_ne_top (by aesop) (by aesop))
  · exact Or.inl <| ENNReal.prod_ne_top fun i _ => ENNReal.natCast_ne_top _

/-- The uniform probability of a decidable event equals the ratio of favorable outcomes
to total outcomes, expressed in `ℝ≥0∞`. -/
lemma uniform_prob_eq_card_div {α : Type} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    Pr_{let x ←$ᵖ α}[P x] = ↑((Finset.univ.filter (fun x => P x)).card) / ↑(Fintype.card α) := by
  erw [PMF.map_apply]
  simp [div_eq_mul_inv, Finset.sum_ite]

/-- The number of elements in `∀ i, ↥(S i)` satisfying `eval (↑·) f = 0` equals
the number of elements in `Fintype.piFinset (fun i => (S i).toFinset)` satisfying
`eval · f = 0`. -/
lemma card_filter_eval_subtype_eq_piFinset
    {F : Type} [Field F] [DecidableEq F]
    {s : ℕ} (S : Fin s → Set F) [∀ i, Fintype ↥(S i)]
    (f : MvPolynomial (Fin s) F) :
    (Finset.univ.filter (fun (x : ∀ i, ↥(S i)) =>
      MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0)).card =
    (Finset.filter (fun x => MvPolynomial.eval x f = 0)
      (Fintype.piFinset (fun i => (S i).toFinset))).card := by
  refine Finset.card_bij ?_ ?_ ?_ ?_;
  · use fun a ha => fun i => a i
  · grind
  · exact fun a₁ ha₁ a₂ ha₂ h => funext fun i => Subtype.ext <| congr_fun h i
  · simp only [Finset.mem_filter, Fintype.mem_piFinset, Set.mem_toFinset, Finset.mem_univ,
    true_and, exists_prop, and_imp]
    exact fun b hb hb' => ⟨fun i => ⟨b i, hb i⟩, hb', rfl⟩

/- If `k * m ≤ d * n` with `m > 0` and `n > 0`, then `k / n ≤ d / m` in `ℝ≥0∞`. -/
lemma ENNReal.div_le_div_of_mul_le {k n d m : ℕ}
    (hm_pos : 0 < m) (hn_pos : 0 < n) (h : k * m ≤ d * n) :
    (k : ℝ≥0∞) / n ≤ d / m := by
  rw [ENNReal.div_le_iff_le_mul] <;> norm_cast
  · rw [← ENNReal.toReal_le_toReal] <;> norm_num
    · rw [div_mul_eq_mul_div, le_div_iff₀] <;> norm_cast
    · exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by aesop) (by aesop)) (by aesop)
  · grind
  · exact Or.inl <| ENNReal.natCast_ne_top _

/- A PMF probability is always at most `1`. -/
lemma pmf_prob_le_one {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    Pr_{let x ←$ᵖ α}[P x] ≤ 1 := by
  erw [PMF.bind_apply, tsum_fintype]
  refine le_trans (Finset.sum_le_sum fun _ _ => mul_le_of_le_one_right ( by positivity ) ?_) ?_
  · exact PMF.coe_le_one _ True
  · norm_num

/-- Probability of a nonzero polynomial evaluating to zero over a uniform product distribution
is at most `d / m`, where `d` bounds the total degree and `m` bounds below the cardinality
of each factor. This bridges `schwartz_zippel_counting` with the probability formulation. -/
lemma prob_eval_zero_le_div
  {F : Type} [Field F]
  {s : ℕ}
  {S : Fin s → Set F} [∀ i, Fintype ↥(S i)] [∀ i, Nonempty ↥(S i)]
  (f : MvPolynomial (Fin s) F) (hf : f ≠ 0)
  (d m : ℕ) (hd : f.totalDegree ≤ d) (hm_pos : 0 < m)
  (hm : ∀ i, m ≤ (S i).toFinset.card) :
  Pr_{let x ←$ᵖ (∀ i, ↥(S i))}[MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0] ≤ (d : ℝ≥0∞) / m :=
  by
  classical
  convert ENNReal.div_le_div_of_mul_le hm_pos _ _ using 1
  · convert uniform_prob_eq_card_div _
    · infer_instance
  · exact Fintype.card_pos_iff.mpr ⟨fun _ => Classical.arbitrary _⟩
  · convert schwartz_zippel_counting f hf ( fun i => ( S i ).toFinset ) d m hd hm_pos hm using 1
    · convert congr_arg₂ (· * ·) (card_filter_eval_subtype_eq_piFinset S f) rfl
    · rw [Fintype.card_pi]
      aesop

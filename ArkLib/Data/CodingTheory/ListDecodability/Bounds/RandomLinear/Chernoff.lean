/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.ProductLaw
public import ArkLib.Data.Probability.FiniteChernoff

/-!
# The plurality decoder

The error probability of the plurality decoder, from the Chernoff tails
`Probability.prodLaw_count_ge_le` and `Probability.prodLaw_count_le_le`.

## Main statements

* `CodingTheory.RandomLinearInternal.prodLaw_plurality_err_le`: the plurality decoder recovers `α`
  from `(v_i + w_i α)_{i ∈ J}` with `v ∼ Ber_q(p)^J`, except with probability `q · exp(-|J| κ)`.

`kappa` is noncomputable (`Real.log`). `plurality` is a
proof device, not an executable decoder: it takes a maximiser with `Classical.choose`, and any
maximiser works.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

open Probability

/-- The decoder's error exponent. -/
noncomputable def kappa (q : ℕ) (p : ℝ) : ℝ :=
  min (chernoffExp (1 / (q : ℝ)) (p / ((q : ℝ) - 1))) (chernoffExp (1 / (q : ℝ)) (1 - p))

/-- Plurality decoder: the `c` maximising `#{i ∈ J | y i = c * w i}`. -/
noncomputable def plurality {I F : Type} [Field F] [Fintype F] [DecidableEq F]
    (J : Finset I) (w : I → F) (y : J → F) : F :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun c : F => (Finset.univ.filter (fun i : J => y i = c * w i)).card) Finset.univ_nonempty)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- `p < 1 - 1/q` is `p q < q - 1`. -/
theorem mul_lt_sub_one {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp1 : p < 1 - 1 / q) : p * q < q - 1 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have := mul_lt_mul_of_pos_right hp1 (by linarith : (0 : ℝ) < q)
  rw [sub_mul, one_div, inv_mul_cancel₀ (by linarith)] at this
  linarith

/-- `p < 1 - 1/q` gives `p / (q - 1) < 1/q`, the weight of a nonzero symbol under `Ber_q(p)`. -/
theorem div_sub_one_lt_one_div {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp1 : p < 1 - 1 / q) :
    p / ((q : ℝ) - 1) < 1 / q := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith [mul_lt_sub_one hq hp1]

/-- The decoder's error exponent is positive. -/
theorem kappa_pos {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 - 1 / q) :
    0 < kappa q p := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlt := div_sub_one_lt_one_div hq hp1
  have hlt2 : 1 / (q : ℝ) < 1 - p := by linarith
  exact lt_min (chernoffExp_pos (div_pos hp0 (by linarith)) (by positivity) hlt.ne')
    (chernoffExp_pos (by linarith [one_div_pos.2 (by linarith : (0 : ℝ) < q)]) (by positivity)
      hlt2.ne)

private theorem card_filter_univ_subtype {I : Type} (J : Finset I) (P : I → Prop)
    [DecidablePred P] :
    (Finset.univ.filter (fun i : J => P i)).card = (J.filter P).card := by
  refine Finset.card_bij (fun i _ => (i : I)) (by simp) (fun a _ b _ h => Subtype.ext h) ?_
  intro x hx
  simp only [Finset.mem_filter] at hx
  exact ⟨⟨x, hx.1⟩, by simp [hx.2], rfl⟩

private theorem card_filter_le_plurality {I F : Type} [Field F] [Fintype F] [DecidableEq F]
    (J : Finset I) (w : I → F) (y : J → F) (c : F) :
    (Finset.univ.filter (fun i : J => y i = c * w i)).card ≤
      (Finset.univ.filter (fun i : J => y i = plurality J w y * w i)).card :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun c : F => (Finset.univ.filter (fun i : J => y i = c * w i)).card)
    Finset.univ_nonempty)).2 c (Finset.mem_univ c)

/-- The plurality decoder recovers `ω a` from `(ω i + w i * ω a)_{i ∈ J}` except with
probability `≤ q · exp(-|J| κ)`. -/
theorem prodLaw_plurality_err_le {F : Type} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}
    (hF : Fintype.card F = q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 - 1 / q)
    (b : I → F → ℝ) (hb : ∀ i, IsProbWeight (b i)) (J : Finset I) (a : I)
    (hJ : ∀ i ∈ J, b i = ber q p) (w : I → F) (hw : ∀ i ∈ J, w i ≠ 0) :
    ∑ ω, prodLaw b ω *
        (if plurality J w (fun i : J => ω i + w i * ω a) ≠ ω a then 1 else 0) ≤
      q * Real.exp (-(J.card * kappa q p)) := by
  have hq2 : 2 ≤ q := by
    rw [← hF]; exact Fintype.one_lt_card
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlt := div_sub_one_lt_one_div hq2 hp1
  have hlt2 : 1 / (q : ℝ) < 1 - p := by linarith
  have hn : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
  have hZ := prodLaw_count_le_le b hb J (fun i => ({(0 : F) * w i} : Finset F)) (1 - p) (1 / q)
    (by
      intro i hi
      simp [hJ i hi, ber]) (by positivity) hlt2
  have hU : ∀ β : F, β ≠ 0 → ∑ ω, prodLaw b ω *
      (if 1 / (q : ℝ) * J.card ≤
        ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ)
        then 1 else 0) ≤ Real.exp (-(J.card * chernoffExp (1 / q) (p / ((q : ℝ) - 1)))) := by
    intro β hβ
    exact prodLaw_count_ge_le b hb J (fun i => ({β * w i} : Finset F)) (p / ((q : ℝ) - 1))
      (1 / q) (by
        intro i hi
        have : β * w i ≠ 0 := mul_ne_zero hβ (hw i hi)
        simp [hJ i hi, ber, this]) (div_pos hp0 hq1) hlt
  have hZ' : ∑ ω, prodLaw b ω *
      (if ((J.filter (fun i => ω i ∈ ({(0 : F) * w i} : Finset F))).card : ℝ) ≤
        1 / (q : ℝ) * J.card then 1 else 0) ≤ Real.exp (-(J.card * kappa q p)) := by
    refine hZ.trans (Real.exp_le_exp.2 (neg_le_neg ?_))
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hn
  have hU' : ∀ β : F, β ≠ 0 → ∑ ω, prodLaw b ω *
      (if 1 / (q : ℝ) * J.card ≤
          ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ)
        then 1 else 0) ≤ Real.exp (-(J.card * kappa q p)) := by
    intro β hβ
    refine (hU β hβ).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hn
  have hA : ∀ (ω : I → F) (c : F),
      (Finset.univ.filter (fun i : J => ω i + w i * ω a = c * w i)).card =
        (J.filter (fun i => ω i ∈ ({(c - ω a) * w i} : Finset F))).card := by
    intro ω c
    rw [card_filter_univ_subtype J (fun i => ω i + w i * ω a = c * w i)]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    simp only [Finset.mem_singleton]
    constructor <;> intro h <;> linear_combination h
  have hpt : ∀ ω : I → F,
      (if plurality J w (fun i : J => ω i + w i * ω a) ≠ ω a then (1 : ℝ) else 0) ≤
        (if ((J.filter (fun i => ω i ∈ ({(0 : F) * w i} : Finset F))).card : ℝ) ≤
          1 / (q : ℝ) * J.card then 1 else 0) +
        ∑ β ∈ Finset.univ.erase (0 : F), (if 1 / (q : ℝ) * J.card ≤
          ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ) then 1 else 0) := by
    intro ω
    have hnn : (0 : ℝ) ≤ ∑ β ∈ Finset.univ.erase (0 : F), (if 1 / (q : ℝ) * J.card ≤
          ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ) then 1 else 0) :=
      Finset.sum_nonneg fun β _ => by split_ifs <;> norm_num
    by_cases herr : plurality J w (fun i : J => ω i + w i * ω a) ≠ ω a
    · rw [ite_eq_left herr]
      set c0 := plurality J w (fun i : J => ω i + w i * ω a) with hc0
      have hmax := card_filter_le_plurality J w (fun i : J => ω i + w i * ω a) (ω a)
      rw [← hc0, hA ω (ω a), hA ω c0, sub_self] at hmax
      have hmax' : ((J.filter (fun i => ω i ∈ ({(0 : F) * w i} : Finset F))).card : ℝ) ≤
          ((J.filter (fun i => ω i ∈ ({(c0 - ω a) * w i} : Finset F))).card : ℝ) := by
        exact_mod_cast hmax
      by_cases hz : ((J.filter (fun i => ω i ∈ ({(0 : F) * w i} : Finset F))).card : ℝ) ≤
          1 / (q : ℝ) * J.card
      · rw [ite_eq_left hz]; linarith
      · have hu : 1 / (q : ℝ) * J.card ≤
            ((J.filter (fun i => ω i ∈ ({(c0 - ω a) * w i} : Finset F))).card : ℝ) := by
          linarith [not_le.1 hz]
        have hmem : c0 - ω a ∈ Finset.univ.erase (0 : F) := by
          simp [sub_eq_zero, herr]
        have := Finset.single_le_sum (f := fun β : F => (if 1 / (q : ℝ) * J.card ≤
          ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ) then (1 : ℝ)
            else 0))
          (fun β _ => by split_ifs <;> norm_num) hmem
        simp only [ite_eq_left hu] at this
        split_ifs
        linarith
    · rw [ite_eq_right herr]
      split_ifs <;> linarith
  calc ∑ ω, prodLaw b ω *
        (if plurality J w (fun i : J => ω i + w i * ω a) ≠ ω a then 1 else 0)
      ≤ ∑ ω, prodLaw b ω * ((if (((J.filter
          (fun i => ω i ∈ ({(0 : F) * w i} : Finset F))).card : ℕ) : ℝ) ≤
          1 / (q : ℝ) * J.card then 1 else 0) +
        ∑ β ∈ Finset.univ.erase (0 : F), (if 1 / (q : ℝ) * J.card ≤
          ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ) then 1 else 0)) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (hpt ω) (prodLaw_nonneg b hb ω)
    _ = ∑ ω, prodLaw b ω * (if ((J.filter (fun i => ω i ∈ ({(0 : F) * w i} : Finset F))).card :
          ℝ) ≤ 1 / (q : ℝ) * J.card then 1 else 0) +
        ∑ β ∈ Finset.univ.erase (0 : F), ∑ ω, prodLaw b ω * (if 1 / (q : ℝ) * J.card ≤
          ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ) then 1 else 0) := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ Real.exp (-(J.card * kappa q p)) +
        ∑ β ∈ Finset.univ.erase (0 : F), Real.exp (-(J.card * kappa q p)) :=
        add_le_add hZ' (Finset.sum_le_sum fun β hβ => hU' β (Finset.ne_of_mem_erase hβ))
    _ = q * Real.exp (-(J.card * kappa q p)) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hF,
          nsmul_eq_mul, Nat.cast_sub (by omega)]
        push_cast
        ring

end CodingTheory.RandomLinearInternal

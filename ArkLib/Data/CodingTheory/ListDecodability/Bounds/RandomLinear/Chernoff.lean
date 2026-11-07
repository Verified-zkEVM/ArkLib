/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.ProductLaw

/-!
# Chernoff bounds and the plurality decoder

Exponential-moment tail bounds for a count of coordinates under a product weight, and the error
probability of the plurality decoder.

## Main statements

* `CodingTheory.RandomLinearInternal.prodLaw_count_ge_le`: the upper Chernoff tail.
* `CodingTheory.RandomLinearInternal.prodLaw_count_le_le`: the lower Chernoff tail.
* `CodingTheory.RandomLinearInternal.law_plurality_err_le`: the plurality decoder recovers `α` from
  `(v_i + w_i α)_{i ∈ J}` with `v ∼ Ber_q(p)^J`, except with probability `q · exp(-|J| κ)`.

For `a ≠ 0`, `kl t a = a * InformationTheory.klFun (t / a)`. It is written out because the tail
bounds use this form directly. `kl` and `kappa` are noncomputable (`Real.log`). `plurality` is a
proof device, not an executable decoder: it takes a maximiser with `Classical.choose`, and any
maximiser works.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

/-- The Chernoff exponent `t log(t/a) - t + a`. -/
noncomputable def kl (t a : ℝ) : ℝ := t * Real.log (t / a) - t + a

/-- The decoder's error exponent. -/
noncomputable def kappa (q : ℕ) (p : ℝ) : ℝ :=
  min (kl (1 / (q : ℝ)) (p / ((q : ℝ) - 1))) (kl (1 / (q : ℝ)) (1 - p))

/-- Plurality decoder: the `c` maximising `#{i ∈ J | y i = c * w i}`. -/
noncomputable def plurality {I F : Type} [Field F] [Fintype F] [DecidableEq F]
    (J : Finset I) (w : I → F) (y : J → F) : F :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun c : F => (Finset.univ.filter (fun i : J => y i = c * w i)).card) Finset.univ_nonempty)

variable {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
private theorem sum_prod_mul_eq_prod_sum (b f : I → A → ℝ) :
    ∑ ω : I → A, ∏ i, (b i (ω i) * f i (ω i)) = ∏ i, ∑ x, b i x * f i x := by
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]

omit [DecidableEq I] [DecidableEq A] in
private theorem prodLaw_nonneg (b : I → A → ℝ) (hb : ∀ i, IsProb (b i))
    (ω : I → A) :
    0 ≤ prodLaw b ω :=
  Finset.prod_nonneg fun i _ => (hb i).1 _

private theorem sum_prodLaw_mul_exp_count_le (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) (T : Finset I)
    (E : I → Finset A) (a : ℝ) (hp : ∀ i ∈ T, ∑ x ∈ E i, b i x = a) (lam : ℝ) :
    ∑ ω, prodLaw b ω *
        Real.exp (lam * ((T.filter (fun i => ω i ∈ E i)).card : ℝ)) ≤
      Real.exp (T.card * (a * (Real.exp lam - 1))) := by
  set g : I → A → ℝ :=
      fun i x => Real.exp (lam * if i ∈ T ∧ x ∈ E i then 1 else 0) with hg
  have h1 : ∀ ω : I → A,
      prodLaw b ω * Real.exp (lam * ((T.filter (fun i => ω i ∈ E i)).card : ℝ)) =
        ∏ i, (b i (ω i) * g i (ω i)) := by
    intro ω
    have hc : ((T.filter fun i => ω i ∈ E i).card : ℝ) =
        ∑ i, if i ∈ T ∧ ω i ∈ E i then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
      congr 2
      ext i
      simp
    rw [Finset.prod_mul_distrib, prodLaw, hc, Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [sum_prod_mul_eq_prod_sum b g]
  have h2 : ∀ i, ∑ x, b i x * g i x ≤
      Real.exp (if i ∈ T then a * (Real.exp lam - 1) else 0) := by
    intro i
    by_cases hi : i ∈ T
    · have e1 : ∀ x, b i x * g i x =
          b i x + (Real.exp lam - 1) * (if x ∈ E i then b i x else 0) := by
        intro x
        by_cases hx : x ∈ E i
        · simp [hg, hi, hx]; ring
        · simp [hg, hi, hx]
      simp_rw [e1]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, (hb i).2, Finset.sum_ite_mem,
        Finset.univ_inter, hp i hi]
      simp only [hi, ite_true]
      linarith [Real.add_one_le_exp (a * (Real.exp lam - 1))]
    · have e1 : ∀ x, b i x * g i x = b i x := by
        intro x
        simp [hg, hi]
      simp_rw [e1]
      simp [hi, (hb i).2]
  calc ∏ i, ∑ x, b i x * g i x
      ≤ ∏ i, Real.exp (if i ∈ T then a * (Real.exp lam - 1) else 0) := by
        apply Finset.prod_le_prod₀
        · exact fun i _ =>
            Finset.sum_nonneg fun x _ => mul_nonneg ((hb i).1 x) (Real.exp_pos _).le
        · exact fun i _ => h2 i
    _ = _ := by
        rw [← Real.exp_sum, ← Finset.sum_filter]
        simp

private theorem sum_prodLaw_mul_le_exp (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) (T : Finset I)
    (E : I → Finset A) (a : ℝ) (hp : ∀ i ∈ T, ∑ x ∈ E i, b i x = a) (t lam : ℝ)
    (ind : (I → A) → ℝ)
    (hind : ∀ ω, ind ω ≤
      Real.exp (lam * (((T.filter (fun i => ω i ∈ E i)).card : ℝ) - t * T.card))) :
    ∑ ω, prodLaw b ω * ind ω ≤
      Real.exp (-(lam * t * T.card) + T.card * (a * (Real.exp lam - 1))) := by
  calc ∑ ω, prodLaw b ω * ind ω
      ≤ ∑ ω, Real.exp (-(lam * t * T.card)) *
          (prodLaw b ω * Real.exp (lam * ((T.filter (fun i => ω i ∈ E i)).card : ℝ))) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        calc prodLaw b ω * ind ω ≤ prodLaw b ω * Real.exp (lam * (((T.filter
              (fun i => ω i ∈ E i)).card : ℝ) - t * T.card)) :=
            mul_le_mul_of_nonneg_left (hind ω) (prodLaw_nonneg b hb ω)
          _ = _ := by
            rw [show lam * (((T.filter (fun i => ω i ∈ E i)).card : ℝ) - t * T.card) =
              -(lam * t * T.card) + lam * ((T.filter (fun i => ω i ∈ E i)).card : ℝ) by ring,
              Real.exp_add]
            ring
    _ = Real.exp (-(lam * t * T.card)) * ∑ ω, prodLaw b ω *
          Real.exp (lam * ((T.filter (fun i => ω i ∈ E i)).card : ℝ)) := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (-(lam * t * T.card)) * Real.exp (T.card * (a * (Real.exp lam - 1))) :=
        mul_le_mul_of_nonneg_left (sum_prodLaw_mul_exp_count_le b hb T E a hp lam)
          (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

/-- Upper Chernoff tail for a count under a product weight. -/
theorem prodLaw_count_ge_le (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) (T : Finset I)
    (E : I → Finset A) (a t : ℝ) (hp : ∀ i ∈ T, ∑ x ∈ E i, b i x = a) (hat : 0 < a)
    (hta : a < t) :
    ∑ ω, prodLaw b ω *
        (if t * T.card ≤ ((T.filter (fun i => ω i ∈ E i)).card : ℝ) then 1 else 0) ≤
      Real.exp (-(T.card * (t * Real.log (t / a) - t + a))) := by
  have ht : 0 < t := hat.trans hta
  have hl : 0 ≤ Real.log (t / a) :=
    (Real.log_pos ((one_lt_div hat).2 hta)).le
  refine (sum_prodLaw_mul_le_exp b hb T E a hp t (Real.log (t / a)) _ fun ω => ?_).trans_eq ?_
  · split_ifs with h
    · exact Real.one_le_exp (mul_nonneg hl (by linarith))
    · exact (Real.exp_pos _).le
  · congr 1
    rw [Real.exp_log (div_pos ht hat)]
    have : a * (t / a - 1) = t - a := by field_simp
    rw [this]
    ring

/-- Lower Chernoff tail for a count under a product weight. -/
theorem prodLaw_count_le_le (b : I → A → ℝ) (hb : ∀ i, IsProb (b i)) (T : Finset I)
    (E : I → Finset A) (a t : ℝ) (hp : ∀ i ∈ T, ∑ x ∈ E i, b i x = a) (ht : 0 < t)
    (hta : t < a) :
    ∑ ω, prodLaw b ω *
        (if ((T.filter (fun i => ω i ∈ E i)).card : ℝ) ≤ t * T.card then 1 else 0) ≤
      Real.exp (-(T.card * (t * Real.log (t / a) - t + a))) := by
  have hat : 0 < a := ht.trans hta
  have hl : Real.log (t / a) ≤ 0 :=
    (Real.log_neg (div_pos ht hat) ((div_lt_one hat).2 hta)).le
  refine (sum_prodLaw_mul_le_exp b hb T E a hp t (Real.log (t / a)) _ fun ω => ?_).trans_eq ?_
  · split_ifs with h
    · exact Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos hl (by linarith))
    · exact (Real.exp_pos _).le
  · congr 1
    rw [Real.exp_log (div_pos ht hat)]
    have : a * (t / a - 1) = t - a := by field_simp
    rw [this]
    ring

/-- The Chernoff exponent is positive off the diagonal. -/
theorem kl_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (h : t ≠ a) :
    0 < t * Real.log (t / a) - t + a := by
  have h1 : Real.log (a / t) < a / t - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos ha ht) (fun h' => h ((div_eq_one_iff_eq ht.ne').1 h').symm)
  have h2 : Real.log (t / a) = -Real.log (a / t) := by
    rw [← Real.log_inv, inv_div]
  have h3 : t * Real.log (a / t) < t * (a / t - 1) := mul_lt_mul_of_pos_left h1 ht
  have h4 : t * (a / t - 1) = a - t := by field_simp
  rw [h2]
  nlinarith

/-- The decoder's error exponent is positive. -/
theorem kappa_pos {q : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 - 1 / q) :
    0 < kappa q p := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlt : p / ((q : ℝ) - 1) < 1 / q := by
    rw [div_lt_div_iff₀ hq1 hq0]
    have : p < 1 - 1 / (q : ℝ) := hp1
    have h2 : p * q < q - 1 := by
      have := mul_lt_mul_of_pos_right this hq0
      rw [sub_mul, one_div, inv_mul_cancel₀ hq0.ne'] at this
      linarith
    linarith
  have hlt2 : 1 / (q : ℝ) < 1 - p := by linarith
  refine lt_min (kl_pos (div_pos hp0 hq1) (by positivity) hlt.ne')
    (kl_pos ?_ (by positivity) hlt2.ne)
  linarith [hlt2, one_div_pos.2 hq0]

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
theorem law_plurality_err_le {F : Type} [Field F] [Fintype F] [DecidableEq F] {q : ℕ}
    (hF : Fintype.card F = q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1 - 1 / q)
    (b : I → F → ℝ) (hb : ∀ i, IsProb (b i)) (J : Finset I) (a : I)
    (hJ : ∀ i ∈ J, b i = ber q p) (w : I → F) (hw : ∀ i ∈ J, w i ≠ 0) :
    ∑ ω, prodLaw b ω *
        (if plurality J w (fun i : J => ω i + w i * ω a) ≠ ω a then 1 else 0) ≤
      q * Real.exp (-(J.card * kappa q p)) := by
  have hq2 : 2 ≤ q := by
    rw [← hF]; exact Fintype.one_lt_card
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlt : p / ((q : ℝ) - 1) < 1 / q := by
    rw [div_lt_div_iff₀ hq1 hq0]
    have h2 : p * q < q - 1 := by
      have := mul_lt_mul_of_pos_right (show p < 1 - 1 / (q : ℝ) from hp1) hq0
      rw [sub_mul, one_div, inv_mul_cancel₀ hq0.ne'] at this
      linarith
    linarith
  have hlt2 : 1 / (q : ℝ) < 1 - p := by linarith
  have hn : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
  have hZ := prodLaw_count_le_le b hb J (fun i => ({(0 : F) * w i} : Finset F)) (1 - p) (1 / q)
    (by
      intro i hi
      simp [hJ i hi, ber]) (by positivity) hlt2
  have hU : ∀ β : F, β ≠ 0 → ∑ ω, prodLaw b ω *
      (if 1 / (q : ℝ) * J.card ≤
        ((J.filter (fun i => ω i ∈ ({β * w i} : Finset F))).card : ℝ)
        then 1 else 0) ≤ Real.exp (-(J.card * kl (1 / q) (p / ((q : ℝ) - 1)))) := by
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

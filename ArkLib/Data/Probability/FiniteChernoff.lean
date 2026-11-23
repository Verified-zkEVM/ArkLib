/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.Probability.FiniteEntropy
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Chernoff and Chebyshev bounds for counts

Exponential-moment tail bounds for the number of coordinates `i ∈ T` with `ω i ∈ E i`, when `ω` is
drawn from a product weight under which each such event has weight `a`.
For a real function `X` on a finite type, Chebyshev's inequality in counting form bounds the
number of zeros of `X`.

## Main statements

* `Probability.prodLaw_count_ge_le`: the upper tail `≤ exp(-|T| chernoffExp t a)` for `a < t`.
* `Probability.prodLaw_count_le_le`: the lower tail `≤ exp(-|T| chernoffExp t a)` for `t < a`.
* `Probability.chernoffExp_pos`: the exponent is positive for `t ≠ a`.
* `Probability.card_zero_mul_sq_le`: Chebyshev in counting form.
-/

@[expose] public section

namespace Probability

open InformationTheory

/-- The Chernoff exponent `a · klFun (t / a)`, which is `t log(t/a) - t + a` for `a ≠ 0`: the
Kullback-Leibler divergence of `Poisson(t)` from `Poisson(a)`, not of two Bernoulli laws. -/
noncomputable def chernoffExp (t a : ℝ) : ℝ := a * klFun (t / a)

theorem chernoffExp_eq {t a : ℝ} (ha : a ≠ 0) : chernoffExp t a = t * Real.log (t / a) - t + a := by
  rw [chernoffExp, klFun_apply]
  field_simp
  ring

/-- The Chernoff exponent is positive off the diagonal. -/
theorem chernoffExp_pos {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (h : t ≠ a) : 0 < chernoffExp t a :=
  mul_pos ha <| (klFun_nonneg (div_nonneg ht ha.le)).lt_of_ne' fun h0 =>
    h ((div_eq_one_iff_eq ha.ne').1 ((klFun_eq_zero_iff (div_nonneg ht ha.le)).1 h0))

/-- Chebyshev in counting form: `#{X = 0} · μ² ≤ Σ (X - μ)²`. -/
theorem card_zero_mul_sq_le {α : Type*} [Fintype α] (X : α → ℝ) (μ : ℝ) :
    ((Finset.univ.filter (fun a => X a = 0)).card : ℝ) * μ ^ 2 ≤ ∑ a, (X a - μ) ^ 2 := by
  calc _ = ∑ a ∈ Finset.univ.filter (fun a => X a = 0), (X a - μ) ^ 2 := by
        rw [Finset.sum_congr rfl (fun a ha => by
          rw [(Finset.mem_filter.1 ha).2, zero_sub, neg_sq])]
        simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

private theorem sum_prodLaw_mul_exp_count_le (b : I → A → ℝ) (hb : ∀ i, IsProbWeight (b i))
    (T : Finset I) (E : I → Finset A) (a : ℝ) (hp : ∀ i ∈ T, ∑ x ∈ E i, b i x = a) (lam : ℝ) :
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
  rw [← Fintype.prod_sum fun i x => b i x * g i x]
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

private theorem sum_prodLaw_mul_le_exp (b : I → A → ℝ) (hb : ∀ i, IsProbWeight (b i)) (T : Finset I)
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
theorem prodLaw_count_ge_le (b : I → A → ℝ) (hb : ∀ i, IsProbWeight (b i)) (T : Finset I)
    (E : I → Finset A) (a t : ℝ) (hp : ∀ i ∈ T, ∑ x ∈ E i, b i x = a) (hat : 0 < a)
    (hta : a < t) :
    ∑ ω, prodLaw b ω *
        (if t * T.card ≤ ((T.filter (fun i => ω i ∈ E i)).card : ℝ) then 1 else 0) ≤
      Real.exp (-(T.card * chernoffExp t a)) := by
  have ht : 0 < t := hat.trans hta
  rw [chernoffExp_eq hat.ne']
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
theorem prodLaw_count_le_le (b : I → A → ℝ) (hb : ∀ i, IsProbWeight (b i)) (T : Finset I)
    (E : I → Finset A) (a t : ℝ) (hp : ∀ i ∈ T, ∑ x ∈ E i, b i x = a) (ht : 0 < t)
    (hta : t < a) :
    ∑ ω, prodLaw b ω *
        (if ((T.filter (fun i => ω i ∈ E i)).card : ℝ) ≤ t * T.card then 1 else 0) ≤
      Real.exp (-(T.card * chernoffExp t a)) := by
  have hat : 0 < a := ht.trans hta
  rw [chernoffExp_eq hat.ne']
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

end Probability

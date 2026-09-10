/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Rectangle-difference polynomials in arbitrary dimension

This file packages the polynomial identity underlying mixed bidegree bounds in an
arbitrary number of jet variables.
-/

@[expose] public section

open Polynomial

namespace Polynomial

noncomputable section

/-- The rectangle difference after substituting bidegrees `(a*N,b*N)` in jet dimension `s`
and cutting by bidegree `(h,v)`. -/
def rectangleDifference (s : ℕ) (a b h v : ℚ) : ℚ[X] :=
  (C a * X + 1) * (preHilbertPoly ℚ s 0).comp (C b * X) -
    (C a * X - C h + 1) * (preHilbertPoly ℚ s 0).comp (C b * X - C v)

private theorem coeff_comp_X_sub_C_pred {p : ℚ[X]} (r : ℕ) (v : ℚ)
    (hp : p.natDegree ≤ r + 1) :
    (p.comp (X - C v)).coeff r = p.coeff r - (r + 1) * v * p.coeff (r + 1) := by
  rw [show X - C v = X + C (-v) by
    rw [sub_eq_add_neg, map_neg]]
  change (taylor (-v) p).coeff r = _
  rw [taylor_coeff]
  have hdeg : (hasseDeriv r p).natDegree < 2 := by
    have h := natDegree_hasseDeriv_le p r
    omega
  rw [eval_eq_sum_range' hdeg]
  norm_num [Finset.sum_range_succ, hasseDeriv_coeff]
  rw [Nat.add_comm 1 r, Nat.choose_succ_self_right]
  push_cast
  ring

private theorem coeff_linear_mul (q : ℚ[X]) (a c : ℚ) (n : ℕ) :
    ((C a * X + C c) * q).coeff (n + 1) =
      a * q.coeff n + c * q.coeff (n + 1) := by
  rw [show (C a * X + C c) * q = C a * (X * q) + C c * q by ring]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul]

private theorem natDegree_le_of_le_succ_of_coeff_succ_eq_zero {p : ℚ[X]} {n : ℕ}
    (hdeg : p.natDegree ≤ n + 1) (hcoeff : p.coeff (n + 1) = 0) : p.natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  by_cases hNs : N = n + 1
  · simpa only [hNs] using hcoeff
  · apply coeff_eq_zero_of_natDegree_lt
    omega

private theorem preHilbertPoly_comp_scale_coeff_self (s : ℕ) (b : ℚ) :
    ((preHilbertPoly ℚ s 0).comp (C b * X)).coeff s =
      (s.factorial : ℚ)⁻¹ * b ^ s := by
  rw [comp_C_mul_X_coeff, coeff_preHilbertPoly_self]

private theorem preHilbertPoly_comp_scale_sub_coeff_self (s : ℕ) (b v : ℚ) :
    ((preHilbertPoly ℚ s 0).comp (C b * X - C v)).coeff s =
      (s.factorial : ℚ)⁻¹ * b ^ s := by
  have hcomp : (preHilbertPoly ℚ s 0).comp (C b * X - C v) =
      ((preHilbertPoly ℚ s 0).comp (X - C v)).comp (C b * X) := by
    rw [comp_assoc]
    congr 1
    simp
  rw [hcomp, comp_C_mul_X_coeff]
  have hcoeff : ((preHilbertPoly ℚ s 0).comp (X - C v)).coeff s =
      (s.factorial : ℚ)⁻¹ := by
    rw [show X - C v = X + C (-v) by rw [sub_eq_add_neg, map_neg]]
    change (taylor (-v) (preHilbertPoly ℚ s 0)).coeff s = _
    calc
      _ = (taylor (-v) (preHilbertPoly ℚ s 0)).coeff
          (preHilbertPoly ℚ s 0).natDegree := by rw [natDegree_preHilbertPoly]
      _ = (preHilbertPoly ℚ s 0).leadingCoeff := coeff_taylor_natDegree _ _
      _ = _ := leadingCoeff_preHilbertPoly (F := ℚ) s 0
  rw [hcoeff]

private theorem preHilbertPoly_comp_scale_pred_sub (r : ℕ) (b v : ℚ) :
    ((preHilbertPoly ℚ (r + 1) 0).comp (C b * X)).coeff r -
      ((preHilbertPoly ℚ (r + 1) 0).comp (C b * X - C v)).coeff r =
        (r + 1) * v * ((r + 1).factorial : ℚ)⁻¹ * b ^ r := by
  rw [comp_C_mul_X_coeff]
  have hcomp : (preHilbertPoly ℚ (r + 1) 0).comp (C b * X - C v) =
      ((preHilbertPoly ℚ (r + 1) 0).comp (X - C v)).comp (C b * X) := by
    rw [comp_assoc]
    congr 1
    simp
  rw [hcomp, comp_C_mul_X_coeff]
  rw [coeff_comp_X_sub_C_pred r v (by rw [natDegree_preHilbertPoly])]
  rw [coeff_preHilbertPoly_self]
  ring

/-- The coefficient controlling the mixed degree in jet dimension `r + 1`. -/
@[simp]
theorem rectangleDifference_coeff_succ (r : ℕ) (a b h v : ℚ) :
    (rectangleDifference (r + 1) a b h v).coeff (r + 1) =
      (h * b ^ (r + 1) + (r + 1) * v * a * b ^ r) /
        ((r + 1).factorial : ℚ) := by
  rw [rectangleDifference, coeff_sub]
  rw [show C a * X + 1 = C a * X + C 1 by simp]
  rw [show C a * X - C h + 1 = C a * X + C (1 - h) by
    rw [map_sub, map_one]
    ring]
  rw [coeff_linear_mul, coeff_linear_mul]
  rw [preHilbertPoly_comp_scale_coeff_self,
    preHilbertPoly_comp_scale_sub_coeff_self]
  have hpred := preHilbertPoly_comp_scale_pred_sub r b v
  rw [div_eq_mul_inv, pow_succ]
  calc
    a * ((preHilbertPoly ℚ (r + 1) 0).comp (C b * X)).coeff r +
          1 * ((↑(r + 1).factorial)⁻¹ * (b ^ r * b)) -
        (a * ((preHilbertPoly ℚ (r + 1) 0).comp (C b * X - C v)).coeff r +
          (1 - h) * ((↑(r + 1).factorial)⁻¹ * (b ^ r * b))) =
      a * (((preHilbertPoly ℚ (r + 1) 0).comp (C b * X)).coeff r -
          ((preHilbertPoly ℚ (r + 1) 0).comp (C b * X - C v)).coeff r) +
        h * (↑(r + 1).factorial)⁻¹ * (b ^ r * b) := by ring
    _ = _ := by rw [hpred]; ring

/-- A rectangle difference in jet dimension `r + 1` has degree at most `r + 1`;
the apparent degree-`r + 2` terms cancel. -/
theorem rectangleDifference_natDegree_le_succ (r : ℕ) (a b h v : ℚ) :
    (rectangleDifference (r + 1) a b h v).natDegree ≤ r + 1 := by
  let q₀ := (preHilbertPoly ℚ (r + 1) 0).comp (C b * X)
  let qᵥ := (preHilbertPoly ℚ (r + 1) 0).comp (C b * X - C v)
  have hinner₀ : (C b * X : ℚ[X]).natDegree ≤ 1 := by
    exact natDegree_mul_le.trans (by simp)
  have hinnerv : (C b * X - C v : ℚ[X]).natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (max_le hinner₀ (by simp))
  have hq₀ : q₀.natDegree ≤ r + 1 := by
    dsimp only [q₀]
    calc
      _ ≤ (preHilbertPoly ℚ (r + 1) 0).natDegree * (C b * X : ℚ[X]).natDegree :=
        natDegree_comp_le
      _ ≤ (r + 1) * 1 := Nat.mul_le_mul (by rw [natDegree_preHilbertPoly]) hinner₀
      _ = r + 1 := Nat.mul_one _
  have hqᵥ : qᵥ.natDegree ≤ r + 1 := by
    dsimp only [qᵥ]
    calc
      _ ≤ (preHilbertPoly ℚ (r + 1) 0).natDegree *
          (C b * X - C v : ℚ[X]).natDegree := natDegree_comp_le
      _ ≤ (r + 1) * 1 := Nat.mul_le_mul (by rw [natDegree_preHilbertPoly]) hinnerv
      _ = r + 1 := Nat.mul_one _
  have hlinear₀ : (C a * X + 1 : ℚ[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans
      (max_le (natDegree_mul_le.trans (by simp)) (by simp))
  have hlinearv : (C a * X - C h + 1 : ℚ[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans
        (max_le (natDegree_mul_le.trans (by simp)) (by simp))) (by simp))
  dsimp only [q₀, qᵥ] at hq₀ hqᵥ
  apply natDegree_le_of_le_succ_of_coeff_succ_eq_zero
  · unfold rectangleDifference
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      have hadd := Nat.add_le_add hlinear₀ hq₀
      omega
    · apply natDegree_mul_le.trans
      have hadd := Nat.add_le_add hlinearv hqᵥ
      omega
  · rw [rectangleDifference, coeff_sub]
    rw [show C a * X + 1 = C a * X + C 1 by simp]
    rw [show C a * X - C h + 1 = C a * X + C (1 - h) by
      rw [map_sub, map_one]
      ring]
    change ((C a * X + C 1) * q₀).coeff (r + 1 + 1) -
      ((C a * X + C (1 - h)) * qᵥ).coeff (r + 1 + 1) = 0
    rw [coeff_linear_mul, coeff_linear_mul]
    dsimp only [q₀, qᵥ]
    rw [coeff_eq_zero_of_natDegree_lt (hq₀.trans_lt (Nat.lt_succ_self _)),
      coeff_eq_zero_of_natDegree_lt (hqᵥ.trans_lt (Nat.lt_succ_self _))]
    rw [show q₀.coeff (r + 1) = (↑(r + 1).factorial)⁻¹ * b ^ (r + 1) by
      exact preHilbertPoly_comp_scale_coeff_self (r + 1) b]
    rw [show qᵥ.coeff (r + 1) = (↑(r + 1).factorial)⁻¹ * b ^ (r + 1) by
      exact preHilbertPoly_comp_scale_sub_coeff_self (r + 1) b v]
    ring

/-- Evaluation recovers the difference between an `(aN,bN)` rectangle and its
`(h,v)` translate. -/
theorem eval_rectangleDifference_natCast (s a b h v N : ℕ)
    (hh : h ≤ a * N) (hv : v ≤ b * N) :
    (rectangleDifference s a b h v).eval (N : ℚ) =
      (((a * N + 1) * (b * N + s).choose s -
        (a * N - h + 1) * (b * N - v + s).choose s : ℕ) : ℚ) := by
  have ha : a * N - h + 1 ≤ a * N + 1 := Nat.add_le_add_right (Nat.sub_le _ _) 1
  have hb : (b * N - v + s).choose s ≤ (b * N + s).choose s :=
    Nat.choose_le_choose s (Nat.add_le_add_right (Nat.sub_le _ _) s)
  have hp := Nat.mul_le_mul ha hb
  rw [Nat.cast_sub hp]
  simp only [rectangleDifference, eval_sub, eval_mul, eval_add, eval_C, eval_X,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [eval_comp, eval_comp]
  simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one]
  have hacast : (a : ℚ) * N - h = ((a * N - h : ℕ) : ℚ) := by
    rw [Nat.cast_sub hh]
    norm_num
  have hbcast : (b : ℚ) * N - v = ((b * N - v : ℕ) : ℚ) := by
    rw [Nat.cast_sub hv]
    norm_num
  have bmulcast : (b : ℚ) * N = ((b * N : ℕ) : ℚ) := by norm_num
  rw [hacast, hbcast, bmulcast]
  rw [preHilbertPoly_eq_choose_sub_add ℚ s (k := 0) (n := b * N) (Nat.zero_le _)]
  rw [preHilbertPoly_eq_choose_sub_add ℚ s (k := 0) (n := b * N - v) (Nat.zero_le _)]
  simp only [Nat.sub_zero, Nat.add_comm]

end

end Polynomial

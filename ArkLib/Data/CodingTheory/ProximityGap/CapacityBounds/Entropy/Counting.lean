/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Linear
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Internal entropy counting for Reed--Solomon codes

This internal module contains the CS25 entropy gap, certificate, agreement-space, and exact-error
combinatorics used by `CapacityBounds.Entropy`. Its non-private declarations form a narrow
cross-module API under `CodingTheory.EntropyInternal`.

## Module boundary

- `rs_entropy_rate_d_le_kf_proof` supplies the final arithmetic fact consumed by the assembly
  module.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [CS25] Crites–Stewart, *On Reed–Solomon Proximity Gaps Conjectures*, ePrint 2025/2046.
  Corollary 1 = source of Theorem 4.17.
-/

namespace CodingTheory
namespace EntropyInternal

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def cs25CertificateCount
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (w : ι → F) : ℕ := by
  classical
  exact (Finset.univ.filter fun E : Finset ι =>
    E.card = f ∧ ∃ c : ι → F, c ∈ ReedSolomon.code domain k ∧
      ∀ i, i ∉ E → w i = c i).card

private noncomputable def cs25EntropyGapFn (q : ℕ) (x : ℝ) : ℝ :=
  Real.log q * Real.qaryEntropy q x - x * (Real.log q) ^ 2 - 4 * x * (1 - x)

private theorem cs25EntropyGapFn_continuous_proof (q : ℕ) :
    Continuous (cs25EntropyGapFn q) := by
  unfold cs25EntropyGapFn
  fun_prop

open Filter Topology in
private theorem cs25EntropyGapFn_deriv2_proof
    (q : ℕ) (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (deriv^[2] (cs25EntropyGapFn q)) x =
      8 - Real.log (q : ℝ) / (x * (1 - x)) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp,
    Function.comp_apply]
  have hfirst (y : ℝ) (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
      deriv (cs25EntropyGapFn q) y =
        Real.log (q : ℝ) * deriv (Real.qaryEntropy q) y -
          Real.log (q : ℝ) ^ 2 - 4 + 8 * y := by
    have hqary : DifferentiableAt ℝ (Real.qaryEntropy q) y :=
      Real.differentiableAt_qaryEntropy hy0 hy1
    have hmain := hqary.hasDerivAt.const_mul (Real.log (q : ℝ))
    have hlin := (hasDerivAt_id y).mul_const (Real.log (q : ℝ) ^ 2)
    have hquad :=
      ((hasDerivAt_id y).const_mul 4).mul
        ((hasDerivAt_const y 1).sub (hasDerivAt_id y))
    have hder := (hmain.sub hlin).sub hquad
    unfold cs25EntropyGapFn
    have hfun :
        (fun z : ℝ => Real.log (q : ℝ) * Real.qaryEntropy q z -
          z * Real.log (q : ℝ) ^ 2 - 4 * z * (1 - z)) =
        (((fun z : ℝ => Real.log (q : ℝ) * Real.qaryEntropy q z) -
          (fun z : ℝ => id z * Real.log (q : ℝ) ^ 2)) -
          ((fun z : ℝ => 4 * id z) * ((fun _ : ℝ => 1) - id))) := by
      funext z
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    rw [hfun, hder.deriv]
    simp only [Pi.sub_apply, id_eq]
    ring
  have hev : ∀ᶠ y in (nhds x),
      deriv (cs25EntropyGapFn q) y =
        Real.log (q : ℝ) * deriv (Real.qaryEntropy q) y -
          Real.log (q : ℝ) ^ 2 - 4 + 8 * y := by
    filter_upwards [eventually_ne_nhds hx0, eventually_ne_nhds hx1]
      with y hy0 hy1
    exact hfirst y hy0 hy1
  refine (Filter.EventuallyEq.deriv_eq hev).trans ?_
  have hq2 : deriv (deriv (Real.qaryEntropy q)) x =
      -1 / (x * (1 - x)) := by
    simpa only [Function.iterate_succ, Function.iterate_zero, Function.id_comp,
      Function.comp_apply] using (Real.deriv2_qaryEntropy (q := q) (p := x))
  have hq2ne : deriv (deriv (Real.qaryEntropy q)) x ≠ 0 := by
    rw [hq2]
    have hxprod : x * (1 - x) ≠ 0 :=
      mul_ne_zero hx0 (sub_ne_zero.mpr hx1.symm)
    exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hxprod
  have hdq : DifferentiableAt ℝ (deriv (Real.qaryEntropy q)) x :=
    differentiableAt_of_deriv_ne_zero hq2ne
  have hR :=
    (((hdq.hasDerivAt.const_mul (Real.log (q : ℝ))).sub
      (hasDerivAt_const x (Real.log (q : ℝ) ^ 2))).sub
        (hasDerivAt_const x 4)).add ((hasDerivAt_id x).const_mul 8)
  have hfunR :
      (fun y : ℝ => Real.log (q : ℝ) * deriv (Real.qaryEntropy q) y -
        Real.log (q : ℝ) ^ 2 - 4 + 8 * y) =
      ((((fun y : ℝ => Real.log (q : ℝ) * deriv (Real.qaryEntropy q) y) -
        (fun _ : ℝ => Real.log (q : ℝ) ^ 2)) - (fun _ : ℝ => 4)) +
        (fun y : ℝ => 8 * id y)) := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, id_eq]
  rw [hfunR, hR.deriv, hq2]
  ring

noncomputable def cs25OverlapSum (q n k f : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range (n - f - k),
    (Nat.choose f ℓ : ℝ) * (Nat.choose (n - f) ℓ : ℝ) / (q : ℝ) ^ ℓ

theorem cs25OverlapSum_le_exp_two_sqrt
    (q n k f : ℕ) (hq : 0 < q) :
    cs25OverlapSum q n k f ≤
      Real.exp (2 * Real.sqrt ((f : ℝ) * (n - f : ℕ) / q)) := by
  let x : ℝ := Real.sqrt ((f : ℝ) * (n - f : ℕ) / q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbase : 0 ≤ (f : ℝ) * (n - f : ℕ) / q := by positivity
  have hx : 0 ≤ x := by exact Real.sqrt_nonneg _
  have hterm : ∀ ℓ : ℕ,
      (Nat.choose f ℓ : ℝ) * Nat.choose (n - f) ℓ / (q : ℝ) ^ ℓ ≤
        (x ^ ℓ / (Nat.factorial ℓ : ℝ)) ^ 2 := by
    intro ℓ
    calc
      (Nat.choose f ℓ : ℝ) * Nat.choose (n - f) ℓ / (q : ℝ) ^ ℓ ≤
          (((f : ℝ) ^ ℓ / (Nat.factorial ℓ : ℝ)) *
            ((n - f : ℕ) ^ ℓ / (Nat.factorial ℓ : ℝ))) / (q : ℝ) ^ ℓ := by
        gcongr
        · exact Nat.choose_le_pow_div ℓ f
        · exact Nat.choose_le_pow_div ℓ (n - f)
      _ = (x ^ ℓ / (Nat.factorial ℓ : ℝ)) ^ 2 := by
        have hfac : (Nat.factorial ℓ : ℝ) ≠ 0 := by positivity
        have hqpow : (q : ℝ) ^ ℓ ≠ 0 := pow_ne_zero _ hqR.ne'
        dsimp [x]
        rw [div_pow]
        rw [← pow_mul, Nat.mul_comm ℓ 2, pow_mul, Real.sq_sqrt hbase]
        rw [div_pow, mul_pow]
        field_simp
  unfold cs25OverlapSum
  calc
    (∑ ℓ ∈ Finset.range (n - f - k),
        (Nat.choose f ℓ : ℝ) * Nat.choose (n - f) ℓ / (q : ℝ) ^ ℓ) ≤
      ∑ ℓ ∈ Finset.range (n - f - k),
        (x ^ ℓ / (Nat.factorial ℓ : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          exact hterm ℓ
    _ ≤ (∑ ℓ ∈ Finset.range (n - f - k),
        x ^ ℓ / (Nat.factorial ℓ : ℝ)) ^ 2 := by
          apply Finset.sum_sq_le_sq_sum_of_nonneg
          intro ℓ hℓ
          positivity
    _ ≤ (Real.exp x) ^ 2 := by
          have hsum := Real.sum_le_exp_of_nonneg hx (n - f - k)
          have hsum_nonneg : 0 ≤ ∑ ℓ ∈ Finset.range (n - f - k),
              x ^ ℓ / (Nat.factorial ℓ : ℝ) := by
            apply Finset.sum_nonneg
            intro ℓ hℓ
            positivity
          have hexp : 0 < Real.exp x := Real.exp_pos x
          nlinarith only [hsum, hsum_nonneg, hexp]
    _ = Real.exp (2 * Real.sqrt ((f : ℝ) * (n - f : ℕ) / q)) := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          dsimp [x]
          ring

private theorem cs25OverlapSum_nonneg (q n k f : ℕ) :
    0 ≤ cs25OverlapSum q n k f := by
  unfold cs25OverlapSum
  apply Finset.sum_nonneg
  intro ℓ hℓ
  positivity

noncomputable def cs25SecondMomentA (q n k f : ℕ) : ℝ :=
  (q : ℝ) ^ (n - f - k) * cs25OverlapSum q n k f

open scoped BigOperators in
def cs25SecondMomentANat (q n k f : ℕ) : ℕ :=
  ∑ ℓ ∈ Finset.range (n - f - k),
    Nat.choose f ℓ * Nat.choose (n - f) ℓ * q ^ (n - f - k - ℓ)

open scoped BigOperators in
private theorem cs25SecondMomentA_eq_weighted_sum_proof
    (q n k f : ℕ) (hq : 0 < q) :
    cs25SecondMomentA q n k f =
      ∑ ℓ ∈ Finset.range (n - f - k),
        (Nat.choose f ℓ : ℝ) * (Nat.choose (n - f) ℓ : ℝ) *
          (q : ℝ) ^ (n - f - k - ℓ) := by
  unfold cs25SecondMomentA cs25OverlapSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  have hle : ℓ ≤ n - f - k := Nat.le_of_lt (Finset.mem_range.mp hℓ)
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [div_eq_mul_inv, pow_sub₀ (q : ℝ) hqne hle]
  ring

open scoped BigOperators in
theorem cs25SecondMomentANat_cast_proof
    (q n k f : ℕ) (hq : 0 < q) :
    (cs25SecondMomentANat q n k f : ℝ) = cs25SecondMomentA q n k f := by
  rw [cs25SecondMomentA_eq_weighted_sum_proof q n k f hq]
  unfold cs25SecondMomentANat
  push_cast
  rfl

theorem cs25SecondMomentA_nonneg_proof (q n k f : ℕ) :
    0 ≤ cs25SecondMomentA q n k f := by
  unfold cs25SecondMomentA
  exact mul_nonneg (by positivity) (cs25OverlapSum_nonneg q n k f)

theorem cs25_entropy_shell_le_choose_proof
    (q n f : ℕ) (hq : 10 ≤ q) (hn : 0 < n)
    (hfpos : 0 < f) (hflt : f < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((f : ℝ) / n)) ≤
      (Nat.choose n f : ℝ) * ((q : ℝ) - 1) ^ f *
        (8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n)) ^ ((1 : ℝ) / 2) := by
  have hq2 : 2 ≤ q := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hxpos : (0 : ℝ) < (f : ℝ) / n := by positivity
  have hxlt : (f : ℝ) / n < 1 :=
    (div_lt_one hnR).2 (by exact_mod_cast hflt)
  have hd : (f : ℝ) = ((f : ℝ) / n) * n := by
    field_simp [hnR.ne']
  have hshell := qary_shell_entropy_lower q n f ((f : ℝ) / n)
    hq2 hn hxpos hxlt hd
  let D : ℝ :=
    (8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n)) ^ ((1 : ℝ) / 2)
  have hDpos : 0 < D := by
    dsimp [D]
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_pos.2
    positivity
  have hcast :
      (((Nat.choose n f * (q - 1) ^ f : ℕ) : ℝ)) =
        (Nat.choose n f : ℝ) * ((q : ℝ) - 1) ^ f := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  change (q : ℝ) ^ ((n : ℝ) * qEntropy q ((f : ℝ) / n)) ≤
    (Nat.choose n f : ℝ) * ((q : ℝ) - 1) ^ f * D
  calc
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((f : ℝ) / n)) =
        ((q : ℝ) ^ ((n : ℝ) * qEntropy q ((f : ℝ) / n)) / D) * D := by
      field_simp [hDpos.ne']
    _ ≤ (((Nat.choose n f * (q - 1) ^ f : ℕ) : ℝ)) * D :=
      mul_le_mul_of_nonneg_right hshell hDpos.le
    _ = (Nat.choose n f : ℝ) * ((q : ℝ) - 1) ^ f * D := by
      rw [hcast]

private theorem cs25_log_card_gt_two (q : ℕ) (hq : 10 ≤ q) :
    2 < Real.log q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 10) hq)
  rw [Real.lt_log_iff_exp_lt hqR]
  have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hesq : Real.exp 1 * Real.exp 1 < 10 := by nlinarith
  calc
    Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    _ < 10 := hesq
    _ ≤ q := by exact_mod_cast hq

private theorem cs25EntropyGapFn_endpoints_proof
    (q : ℕ) (hq : 10 ≤ q) :
    cs25EntropyGapFn q 0 = 0 ∧
      0 ≤ cs25EntropyGapFn q (1 - 1 / (q : ℝ)) := by
  have hq2 : 2 ≤ q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq2)
  have hloggt : 2 < Real.log (q : ℝ) := cs25_log_card_gt_two q hq
  constructor
  · simp [cs25EntropyGapFn]
  · have hQ := qEntropy_one_sub_inv hq2
    rw [qEntropy_eq_qaryEntropy_div_log] at hQ
    have hqary :
        Real.qaryEntropy q (1 - 1 / (q : ℝ)) = Real.log (q : ℝ) := by
      have hQ' :
          Real.qaryEntropy q (1 - 1 / (q : ℝ)) / Real.log (q : ℝ) = 1 := hQ
      exact (div_eq_one_iff_eq hlogpos.ne').mp hQ'
    have ha_le : 1 - 1 / (q : ℝ) ≤ 1 := by
      have hinv : 0 ≤ 1 / (q : ℝ) := by positivity
      linarith
    unfold cs25EntropyGapFn
    rw [hqary]
    calc
      Real.log (q : ℝ) * Real.log (q : ℝ) -
            (1 - 1 / (q : ℝ)) * Real.log (q : ℝ) ^ 2 -
            4 * (1 - 1 / (q : ℝ)) * (1 - (1 - 1 / (q : ℝ))) =
          (1 - (1 - 1 / (q : ℝ))) *
            (Real.log (q : ℝ) ^ 2 - 4 * (1 - 1 / (q : ℝ))) := by ring
      _ ≥ 0 := mul_nonneg (by positivity) (by nlinarith [sq_nonneg (Real.log (q : ℝ) - 2)])

private theorem cs25_entropy_gap_lt_half_proof
    (q : ℕ) (x : ℝ) (hq : 10 ≤ q) (hx : 0 ≤ x) :
    qEntropy q x - x < (1 : ℝ) / 2 := by
  have hloggt : 2 < Real.log (q : ℝ) := cs25_log_card_gt_two q hq
  have hlogpos : 0 < Real.log (q : ℝ) := lt_trans (by norm_num) hloggt
  have hq10R : (10 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqm1pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hcast : ((((q : ℤ) - 1 : ℤ) : ℝ)) = (q : ℝ) - 1 := by
    push_cast
    ring
  have hlogle : Real.log ((q : ℝ) - 1) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hqm1pos (by linarith)
  have hqary_le :
      Real.qaryEntropy q x ≤ x * Real.log (q : ℝ) + Real.log 2 := by
    rw [Real.qaryEntropy, hcast]
    have hxlog := mul_le_mul_of_nonneg_left hlogle hx
    linarith [Real.binEntropy_le_log_two (p := x)]
  rw [qEntropy_eq_qaryEntropy_div_log]
  have hmain :
      Real.qaryEntropy q x / Real.log (q : ℝ) - x ≤
        Real.log 2 / Real.log (q : ℝ) := by
    calc
      Real.qaryEntropy q x / Real.log (q : ℝ) - x ≤
          (x * Real.log (q : ℝ) + Real.log 2) / Real.log (q : ℝ) - x := by
            exact sub_le_sub_right ((div_le_div_iff_of_pos_right hlogpos).2 hqary_le) x
      _ = Real.log 2 / Real.log (q : ℝ) := by
        field_simp [hlogpos.ne']
        ring
  have hlog2lt : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hfrac : Real.log 2 / Real.log (q : ℝ) < (1 : ℝ) / 2 := by
    rw [div_lt_iff₀ hlogpos]
    nlinarith
  exact lt_of_le_of_lt hmain hfrac

theorem cs25_quadratic_entropy_gap_proof
    (q : ℕ) (x : ℝ) (hq : 10 ≤ q)
    (hx0 : 0 ≤ x) (hxpeak : x ≤ 1 - 1 / (q : ℝ)) :
    4 * x * (1 - x) ≤
      (Real.log (q : ℝ)) ^ 2 * (qEntropy q x - x) := by
  let a : ℝ := 1 - 1 / (q : ℝ)
  have hq2 : 2 ≤ q := by omega
  have hqR : (0 : ℝ) < q := by positivity
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq2)
  have hloggt : 2 < Real.log (q : ℝ) := cs25_log_card_gt_two q hq
  have ha0 : 0 ≤ a := by
    dsimp [a]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    exact sub_nonneg.mpr (div_le_one hqR |>.2 hq1)
  have halt : a < 1 := by
    dsimp [a]
    have hinv : 0 < 1 / (q : ℝ) := by positivity
    linarith
  have hconc : StrictConcaveOn ℝ (Set.Icc 0 a) (cs25EntropyGapFn q) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 a)
      (cs25EntropyGapFn_continuous_proof q).continuousOn
    intro y hy
    rw [interior_Icc] at hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    have hy1lt : y < 1 := lt_trans hy.2 halt
    have hy1 : y ≠ 1 := ne_of_lt hy1lt
    rw [cs25EntropyGapFn_deriv2_proof q y hy0 hy1]
    have hp : 0 < y * (1 - y) := mul_pos hy.1 (sub_pos.mpr hy1lt)
    have hquad : y * (1 - y) ≤ 1 / 4 := by
      nlinarith only [sq_nonneg (y - 1 / 2)]
    have hmul : 8 * (y * (1 - y)) < Real.log (q : ℝ) := by
      nlinarith only [hquad, hloggt]
    have hdiv : 8 < Real.log (q : ℝ) / (y * (1 - y)) :=
      (lt_div_iff₀ hp).2 hmul
    linarith
  obtain ⟨hG0, hGa⟩ := cs25EntropyGapFn_endpoints_proof q hq
  have hxmem : x ∈ Set.Icc (0 : ℝ) a := by
    exact ⟨hx0, by simpa only [a] using hxpeak⟩
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) a := ⟨le_rfl, ha0⟩
  have ha : a ∈ Set.Icc (0 : ℝ) a := ⟨ha0, le_rfl⟩
  have hmin := hconc.concaveOn.min_le_of_mem_Icc hzero ha hxmem
  have hGx : 0 ≤ cs25EntropyGapFn q x := by
    rw [hG0, min_eq_left hGa] at hmin
    exact hmin
  have hident :
      cs25EntropyGapFn q x =
        (Real.log (q : ℝ)) ^ 2 * (qEntropy q x - x) -
          4 * x * (1 - x) := by
    unfold cs25EntropyGapFn
    rw [qEntropy_eq_qaryEntropy_div_log]
    field_simp [hlogpos.ne']
  rw [hident] at hGx
  linarith

private theorem cs25_shell_factor_lt_q
    (q n f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q)
    (hfpos : 0 < f) (hflt : f < n) :
    (8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n)) ^ ((1 : ℝ) / 2) < q := by
  rw [← Real.sqrt_eq_rpow]
  have hn : 0 < n := lt_trans hfpos hflt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 10) hq)
  apply (Real.sqrt_lt' hqR).2
  let x : ℝ := (f : ℝ) / n
  have hquad : x * (1 - x) ≤ 1 / 4 := by
    nlinarith only [sq_nonneg (x - 1 / 2)]
  have hmul : (n : ℝ) * (x * (1 - x)) ≤ (n : ℝ) * (1 / 4) :=
    mul_le_mul_of_nonneg_left hquad hnR.le
  have hA : 8 * (n : ℝ) * x * (1 - x) ≤ 2 * n := by
    nlinarith only [hmul]
  have hnqR : (n : ℝ) ≤ q := by exact_mod_cast hnq
  have hq10R : (10 : ℝ) ≤ q := by exact_mod_cast hq
  dsimp [x] at hA ⊢
  nlinarith only [hA, hnqR, hq10R]

theorem cs25_shell_power_bound
    (q n f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q)
    (hfpos : 0 < f) (hflt : f < n) :
    ((q : ℝ) - 1) ^ (f + 1) *
        (8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n)) ^ ((1 : ℝ) / 2) <
      (q : ℝ) ^ (f + 2) := by
  have hD := cs25_shell_factor_lt_q q n f hq hnq hfpos hflt
  have hq1R : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hqR : (0 : ℝ) < q := lt_trans zero_lt_one hq1R
  have hqm1 : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr hq1R
  have hp : 0 < ((q : ℝ) - 1) ^ (f + 1) := pow_pos hqm1 _
  have hbase : (q : ℝ) - 1 < q := by linarith
  have hpow : ((q : ℝ) - 1) ^ (f + 1) < (q : ℝ) ^ (f + 1) :=
    pow_lt_pow_left₀ hbase hqm1.le (by omega)
  calc
    ((q : ℝ) - 1) ^ (f + 1) *
        (8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n)) ^ ((1 : ℝ) / 2) <
      ((q : ℝ) - 1) ^ (f + 1) * q := mul_lt_mul_of_pos_left hD hp
    _ < (q : ℝ) ^ (f + 1) * q := mul_lt_mul_of_pos_right hpow hqR
    _ = (q : ℝ) ^ (f + 2) := by
      simp only [pow_succ]

private theorem epsCa_le_one
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Set (ι → F)) (δ_fld δ_int : NNReal) :
    epsCa (F := F) (A := F) C δ_fld δ_int ≤ 1 := by
  classical
  unfold epsCa
  refine iSup_le fun u => ?_
  split_ifs
  · exact zero_le_one
  · exact PMF.coe_le_one _ _

open scoped ProbabilityTheory in
theorem epsCa_eq_one_of_all_folds_close_not_joint
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Set (ι → F)) (δ : NNReal) (u : Code.WordStack F (Fin 2) ι)
    (hjoint : ¬ Code.jointProximity C (u := u) δ)
    (hclose : ∀ γ : F, Code.relDistFromCode (u 0 + γ • u 1) C ≤ (δ : ENNReal)) :
    epsCa (F := F) (A := F) C δ δ = 1 := by
  classical
  refine le_antisymm (epsCa_le_one C δ δ) ?_
  have hprob :
      Pr_{let γ ← $ᵖ F}[Code.relDistFromCode (u 0 + γ • u 1) C ≤ (δ : ENNReal)] = 1 := by
    rw [Probability.prob_uniform_eq_card_filter_div_card]
    have hfilter :
        Finset.univ.filter (fun γ : F =>
          Code.relDistFromCode (u 0 + γ • u 1) C ≤ (δ : ENNReal)) = Finset.univ := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (hclose γ)
    rw [hfilter]
    apply ENNReal.div_self
    · simp
    · simp
  calc
    1 = Pr_{let γ ← $ᵖ F}[Code.relDistFromCode (u 0 + γ • u 1) C ≤ (δ : ENNReal)] := hprob.symm
    _ = (if Code.jointProximity C (u := u) δ then 0
        else Pr_{let γ ← $ᵖ F}[
          Code.relDistFromCode (u 0 + γ • u 1) C ≤ (δ : ENNReal)]) := (if_neg hjoint).symm
    _ ≤ epsCa (F := F) (A := F) C δ δ := by
      unfold epsCa
      exact le_iSup (fun w : Code.WordStack F (Fin 2) ι =>
        if Code.jointProximity C (u := w) δ then 0
        else Pr_{let γ ← $ᵖ F}[
          Code.relDistFromCode (w 0 + γ • w 1) C ≤ (δ : ENNReal)]) u

theorem exists_base_all_translates_close_of_bad_count
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Set (ι → F)) (v : ι → F) (f : ℕ)
    (hbad :
      (Finset.univ.filter fun w : ι → F => ¬ Code.distFromCode w C ≤ f).card <
        (Fintype.card F) ^ (Fintype.card ι - 1)) :
    ∃ u : ι → F, ∀ γ : F, Code.distFromCode (u + γ • v) C ≤ f := by
  classical
  let B : Finset (ι → F) :=
    Finset.univ.filter fun w : ι → F => ¬ Code.distFromCode w C ≤ f
  let U : Finset (ι → F) :=
    Finset.univ.biUnion fun γ : F => B.image fun w => w - γ • v
  by_contra h
  push Not at h
  have hcover : (Finset.univ : Finset (ι → F)) ⊆ U := by
    intro u hu
    obtain ⟨γ, hγ⟩ := h u
    have hwB : u + γ • v ∈ B := by
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_le_of_gt hγ
    have himage : u ∈ B.image (fun w => w - γ • v) := by
      refine Finset.mem_image.mpr ⟨u + γ • v, hwB, ?_⟩
      ext i
      simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    exact Finset.mem_biUnion.mpr ⟨γ, Finset.mem_univ γ, himage⟩
  have hUcard : U.card ≤ Fintype.card F * B.card := by
    calc
      U.card ≤ ∑ γ ∈ (Finset.univ : Finset F),
          (B.image fun w => w - γ • v).card := Finset.card_biUnion_le
      _ ≤ ∑ _γ ∈ (Finset.univ : Finset F), B.card := by
        apply Finset.sum_le_sum
        intro γ hγ
        exact Finset.card_image_le
      _ = Fintype.card F * B.card := by
        simp [Finset.card_univ]
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hq_pos : 0 < Fintype.card F := Fintype.card_pos
  have hBlt : B.card < (Fintype.card F) ^ (Fintype.card ι - 1) := by
    simpa only [B] using hbad
  have hstrict : Fintype.card F * B.card <
      Fintype.card F * (Fintype.card F) ^ (Fintype.card ι - 1) :=
    (Nat.mul_lt_mul_left hq_pos).2 hBlt
  have hpow : Fintype.card F * (Fintype.card F) ^ (Fintype.card ι - 1) =
      (Fintype.card F) ^ Fintype.card ι := by
    rw [Nat.mul_comm, ← pow_succ]
    congr
    omega
  have hambient : (Finset.univ : Finset (ι → F)).card =
      (Fintype.card F) ^ Fintype.card ι := by
    rw [Finset.card_univ, Fintype.card_fun]
  have hlt : (Finset.univ : Finset (ι → F)).card <
      (Fintype.card F) ^ Fintype.card ι := by
    calc
      (Finset.univ : Finset (ι → F)).card ≤ U.card := Finset.card_le_card hcover
      _ ≤ Fintype.card F * B.card := hUcard
      _ < Fintype.card F * (Fintype.card F) ^ (Fintype.card ι - 1) := hstrict
      _ = (Fintype.card F) ^ Fintype.card ι := hpow
  rw [← hambient] at hlt
  exact (lt_irrefl _ hlt)

theorem nat_card_lt_pow_pred_of_weighted_bound
    (q n N B : ℕ) (A : ℝ)
    (hq : 1 < q) (hn : 0 < n) (hN : 0 < N) (hA : 0 ≤ A)
    (hsmall : ((q : ℝ) - 1) * A < (N : ℝ))
    (hbound : (B : ℝ) * ((N : ℝ) + A) ≤ (q : ℝ) ^ n * A) :
    B < q ^ (n - 1) := by
  by_contra hnot
  have hB : q ^ (n - 1) ≤ B := Nat.le_of_not_gt hnot
  have hBreal : (q : ℝ) ^ (n - 1) ≤ (B : ℝ) := by exact_mod_cast hB
  have hNA : (0 : ℝ) ≤ (N : ℝ) + A := by positivity
  have hmul :
      (q : ℝ) ^ (n - 1) * ((N : ℝ) + A) ≤
        (B : ℝ) * ((N : ℝ) + A) :=
    mul_le_mul_of_nonneg_right hBreal hNA
  have hchain :
      (q : ℝ) ^ (n - 1) * ((N : ℝ) + A) ≤
        (q : ℝ) ^ n * A := le_trans hmul hbound
  have hnrep : n = (n - 1) + 1 := by omega
  have hpow : (q : ℝ) ^ n = (q : ℝ) ^ (n - 1) * (q : ℝ) := by
    calc
      (q : ℝ) ^ n = (q : ℝ) ^ ((n - 1) + 1) := by congr 1
      _ = (q : ℝ) ^ (n - 1) * (q : ℝ) := pow_succ _ _
  have hfactor :
      (q : ℝ) ^ (n - 1) * ((N : ℝ) + A) ≤
        (q : ℝ) ^ (n - 1) * ((q : ℝ) * A) := by
    calc
      (q : ℝ) ^ (n - 1) * ((N : ℝ) + A) ≤
          (q : ℝ) ^ n * A := hchain
      _ = (q : ℝ) ^ (n - 1) * ((q : ℝ) * A) := by rw [hpow]; ring
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hpPos : (0 : ℝ) < (q : ℝ) ^ (n - 1) := pow_pos hqR _
  have hcancel : (N : ℝ) + A ≤ (q : ℝ) * A :=
    le_of_mul_le_mul_of_pos_left hfactor hpPos
  have hcontr : (N : ℝ) ≤ ((q : ℝ) - 1) * A := by linarith
  exact (not_le_of_gt hsmall) hcontr

theorem not_jointProximity_of_second_row_far
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [DecidableEq F]
    (C : Set (ι → F)) (u : Code.WordStack F (Fin 2) ι) (δ : NNReal)
    (hfar : ¬ Code.relDistFromCode (u 1) C ≤ (δ : ENNReal)) :
    ¬ Code.jointProximity C (u := u) δ := by
  intro hjoint
  rw [← Code.jointAgreement_iff_jointProximity] at hjoint
  obtain ⟨S, hS_card, v, hv⟩ := hjoint
  apply hfar
  rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨v 1, (hv 1).1, ?_⟩
  rw [Code.relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (Code.relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  constructor
  · intro hj
    exact ((Finset.mem_filter.mp ((hv 1).2 hj)).2).symm
  · intro hne hj
    exact hne ((Finset.mem_filter.mp ((hv 1).2 hj)).2).symm

noncomputable def rsAgreementSpace
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι) : Submodule F (ι → F) :=
  ReedSolomon.code domain k ⊔ Pi.spanSubset F (E : Set ι)

noncomputable def rsAgreementPairCount
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E E' : Finset ι) : ℕ := by
  classical
  exact (Finset.univ.filter fun w : ι → F =>
    w ∈ rsAgreementSpace domain k E ∧
    w ∈ rsAgreementSpace domain k E').card

private theorem rsAgreementSpace_mem_iff
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι) (w : ι → F) :
    w ∈ rsAgreementSpace domain k E ↔
      ∃ c : ι → F, c ∈ ReedSolomon.code domain k ∧
        ∀ i, i ∉ E → w i = c i := by
  unfold rsAgreementSpace
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨c, hc, v, hv, hcv⟩
    refine ⟨c, hc, ?_⟩
    intro i hi
    have hv0 : v i = 0 := (Pi.mem_spanSubset_iff.mp hv) i (by simpa using hi)
    simpa [Pi.add_apply, hv0] using (congrFun hcv i).symm
  · rintro ⟨c, hc, hagree⟩
    refine ⟨c, hc, w - c, ?_, ?_⟩
    · rw [Pi.mem_spanSubset_iff]
      intro i hi
      have hwi : w i = c i := hagree i (by simpa using hi)
      simp [Pi.sub_apply, hwi]
    · ext i
      simp [Pi.add_apply, Pi.sub_apply]

private theorem rsAgreementSpace_eq_top_of_large
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι)
    (hlarge : Fintype.card ι ≤ k + E.card) :
    rsAgreementSpace domain k E = ⊤ := by
  apply top_unique
  intro w hw
  rw [rsAgreementSpace_mem_iff]
  let T : Finset ι := Finset.univ \ E
  let p : Polynomial F := Lagrange.interpolate T domain w
  let c : ι → F := ReedSolomon.evalOnPoints domain p
  have hTcard : T.card = Fintype.card ι - E.card := by
    dsimp [T]
    rw [Finset.card_sdiff]
    simp
  have hTk : T.card ≤ k := by
    rw [hTcard]
    omega
  have hinj : Set.InjOn (domain : ι → F) (T : Set ι) := domain.injective.injOn
  have hpdeg : p.degree < (k : WithBot ℕ) := by
    exact lt_of_lt_of_le (Lagrange.degree_interpolate_lt w hinj) (by exact_mod_cast hTk)
  refine ⟨c, ReedSolomon.evalOnPoints_mem_code_of_degree_lt hpdeg, ?_⟩
  intro i hiE
  have hiT : i ∈ T := by
    simp [T, hiE]
  change w i = p.eval (domain i)
  simpa only [p] using (Lagrange.eval_interpolate_at_node w hinj hiT).symm

def rsBoundaryWord {ι F : Type} [Monoid F] (domain : ι ↪ F) (k : ℕ) : ι → F :=
  fun i => domain i ^ k

theorem rsBoundaryWord_far
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hslack : k + f + 2 ≤ Fintype.card ι) :
    Code.distFromCode (rsBoundaryWord domain k)
      (ReedSolomon.code domain k : Set (ι → F)) > f := by
  classical
  have hk_lt_n : k < Fintype.card ι := by omega
  have hv_mem_succ : rsBoundaryWord domain k ∈ ReedSolomon.code domain (k + 1) := by
    apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (Polynomial.X ^ k)
    · simp
    · intro i
      simp [rsBoundaryWord]
  have hv_not_mem : rsBoundaryWord domain k ∉ ReedSolomon.code domain k := by
    intro hv
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv
    obtain ⟨p, hp, hpv⟩ := hv
    have heq : p = Polynomial.X ^ k := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
        (v := domain) (s := Finset.univ)
      · intro x _ y _ hxy
        exact domain.injective hxy
      · exact lt_trans hp (by exact_mod_cast hk_lt_n)
      · simpa using (show (Polynomial.X ^ k : Polynomial F).degree <
          (Fintype.card ι : WithBot ℕ) by simp [hk_lt_n])
      · intro i hi
        have hi_eq := congrFun hpv i
        simpa [ReedSolomon.evalOnPoints, rsBoundaryWord] using hi_eq.symm
    have hcoeff := congrArg (fun r : Polynomial F => r.coeff k) heq
    have hpcoeff : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_degree_lt hp
    simp [hpcoeff] at hcoeff
  apply lt_of_not_ge
  intro hclose
  rw [Code.closeToCode_iff_closeToCodeword_of_minDist] at hclose
  obtain ⟨c, hc, hdist⟩ := hclose
  have hc_succ : c ∈ ReedSolomon.code domain (k + 1) :=
    ReedSolomon.code_mono (Nat.le_succ k) domain hc
  have hne : rsBoundaryWord domain k ≠ c := by
    intro hvc
    apply hv_not_mem
    simpa [hvc] using hc
  have hagree := ReedSolomon.agree_lt_of_mem_code hv_mem_succ hc_succ hne
  have hsum := Code.agree_add_hammingDist
    (u := rsBoundaryWord domain k) (v := c)
  have hfar : f < hammingDist (rsBoundaryWord domain k) c := by omega
  exact (not_le_of_gt hfar) (by exact_mod_cast hdist)

private theorem rsCode_disjoint_supported_of_small
    {ι F : Type} [Fintype ι] [Nonempty ι]
    [Field F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι)
    (hsmall : k + E.card ≤ Fintype.card ι) :
    Disjoint (ReedSolomon.code domain k) (Pi.spanSubset F (E : Set ι)) := by
  classical
  rw [Submodule.disjoint_def]
  intro c hc hsupport
  by_contra hne
  have hagree : Code.agree c 0 < k :=
    ReedSolomon.agree_lt_of_mem_code hc (Submodule.zero_mem _) hne
  have hsupp := Pi.mem_spanSubset_iff.mp hsupport
  have hsub : Finset.univ \ E ⊆ ({i | c i = (0 : ι → F) i} : Finset ι) := by
    intro i hi
    have hiE : i ∉ E := (Finset.mem_sdiff.mp hi).2
    have hc0 : c i = 0 := hsupp i (by simpa using hiE)
    simpa using hc0
  have hcard : (Finset.univ \ E).card ≤ Code.agree c 0 := by
    simpa [Code.agree] using Finset.card_le_card hsub
  have hcomp : (Finset.univ \ E).card = Fintype.card ι - E.card := by
    rw [Finset.card_sdiff]
    simp
  rw [hcomp] at hcard
  omega

private theorem rsAgreementSpace_finrank_small
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι)
    (hsmall : k + E.card ≤ Fintype.card ι) :
    Module.finrank F (rsAgreementSpace domain k E) = k + E.card := by
  have hk : k ≤ Fintype.card ι := by omega
  have hRS : Module.finrank F (ReedSolomon.code domain k) = k := by
    exact ReedSolomon.dim_eq_deg_of_le (α := domain) hk
  have hV : Module.finrank F (Pi.spanSubset F (E : Set ι)) = E.card := by
    rw [Pi.dim_spanSubset (R := F) (s := (E : Set ι)), Set.ncard_coe_finset]
  have hdis := rsCode_disjoint_supported_of_small domain k E hsmall
  have hinf : ReedSolomon.code domain k ⊓ Pi.spanSubset F (E : Set ι) = ⊥ :=
    disjoint_iff.mp hdis
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (ReedSolomon.code domain k) (Pi.spanSubset F (E : Set ι))
  rw [hinf, finrank_bot, hRS, hV] at hdim
  unfold rsAgreementSpace
  omega

private theorem rsAgreementSpace_filter_card_small_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι)
    (hsmall : k + E.card ≤ Fintype.card ι) :
    (@Finset.filter (ι → F) (fun w => w ∈ rsAgreementSpace domain k E)
      (Classical.decPred _) Finset.univ).card =
        Fintype.card F ^ (k + E.card) := by
  classical
  rw [← Fintype.card_subtype]
  let e :
      {w : ι → F // w ∈ rsAgreementSpace domain k E} ≃
        ↥(rsAgreementSpace domain k E) :=
    { toFun := fun w => ⟨w.1, w.2⟩
      invFun := fun w => ⟨w.1, w.2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  calc
    Fintype.card {w : ι → F // w ∈ rsAgreementSpace domain k E} =
        Fintype.card ↥(rsAgreementSpace domain k E) := Fintype.card_congr e
    _ = Fintype.card F ^ Module.finrank F (rsAgreementSpace domain k E) :=
      Module.card_eq_pow_finrank
    _ = Fintype.card F ^ (k + E.card) := by
      rw [rsAgreementSpace_finrank_small domain k E hsmall]

theorem rsAgreementSpace_finrank
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι) :
    Module.finrank F (rsAgreementSpace domain k E) =
      min (Fintype.card ι) (k + E.card) := by
  by_cases hsmall : k + E.card ≤ Fintype.card ι
  · rw [rsAgreementSpace_finrank_small domain k E hsmall, min_eq_right hsmall]
  · have hlarge : Fintype.card ι ≤ k + E.card := by omega
    rw [rsAgreementSpace_eq_top_of_large domain k E hlarge, finrank_top,
      Module.finrank_pi, min_eq_left hlarge]

private theorem rsAgreementSpace_ncard_small_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι)
    (hsmall : k + E.card ≤ Fintype.card ι) :
    (rsAgreementSpace domain k E : Set (ι → F)).ncard =
      Fintype.card F ^ (k + E.card) := by
  rw [submodule_ncard_eq_pow_finrank,
    rsAgreementSpace_finrank_small domain k E hsmall]

def rsExactErrorSets {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ℕ) : Finset (Finset ι) :=
  Finset.univ.powersetCard f

private noncomputable def rsAgreementCertificates
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (w : ι → F) : Finset (Finset ι) := by
  classical
  exact (rsExactErrorSets f).filter fun E =>
    w ∈ rsAgreementSpace domain k E

private theorem cs25CertificateCount_eq_filter_proof
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (w : ι → F) :
    cs25CertificateCount domain k f w =
      (rsAgreementCertificates domain k f w).card := by
  classical
  unfold cs25CertificateCount rsAgreementCertificates rsExactErrorSets
  apply congrArg Finset.card
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard, Finset.subset_univ]
  rw [rsAgreementSpace_mem_iff]

private theorem cs25CertificateCount_pos_iff_close_proof
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (w : ι → F)
    (hf : f ≤ Fintype.card ι) :
    0 < cs25CertificateCount domain k f w ↔
      Code.distFromCode w (ReedSolomon.code domain k : Set (ι → F)) ≤ f := by
  classical
  rw [cs25CertificateCount_eq_filter_proof, Finset.card_pos]
  constructor
  · rintro ⟨E, hE⟩
    have hE' : E.card = f ∧ w ∈ rsAgreementSpace domain k E := by
      simpa [rsAgreementCertificates, rsExactErrorSets] using hE
    rw [Code.closeToCode_iff_closeToCodeword_of_minDist]
    rw [rsAgreementSpace_mem_iff] at hE'
    obtain ⟨c, hc, hagree⟩ := hE'.2
    refine ⟨c, hc, ?_⟩
    rw [Code.hammingDist_eq_disagreementCols_card]
    calc
      (Code.disagreementCols w c).card ≤ E.card := by
        apply Finset.card_le_card
        intro i hi
        by_contra hiE
        exact (Code.mem_disagreementCols.mp hi) (hagree i hiE)
      _ = f := hE'.1
  · intro hclose
    rw [Code.closeToCode_iff_closeToCodeword_of_minDist] at hclose
    obtain ⟨c, hc, hdist⟩ := hclose
    let D : Finset ι := Code.disagreementCols w c
    have hDcard : D.card ≤ f := by
      rw [← Code.hammingDist_eq_disagreementCols_card]
      exact hdist
    obtain ⟨E, hDE, hEcard⟩ := Finset.exists_superset_card_eq hDcard hf
    refine ⟨E, ?_⟩
    simp only [rsAgreementCertificates, Finset.mem_filter]
    constructor
    · simp [rsExactErrorSets, hEcard]
    · rw [rsAgreementSpace_mem_iff]
      refine ⟨c, hc, ?_⟩
      intro i hiE
      by_contra hne
      apply hiE
      exact hDE (Code.mem_disagreementCols.mpr hne)

open scoped BigOperators in
theorem cs25CertificateCount_sq_sum_eq_pair_sum_nat_proof
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) :
    ∑ w : ι → F, (cs25CertificateCount domain k f w) ^ 2 =
      ∑ E ∈ rsExactErrorSets (ι := ι) f,
        ∑ E' ∈ rsExactErrorSets (ι := ι) f,
          rsAgreementPairCount domain k E E' := by
  classical
  let S : Finset (Finset ι) := rsExactErrorSets (ι := ι) f
  let P : Finset (Finset ι × Finset ι) := S ×ˢ S
  let r : (Finset ι × Finset ι) → (ι → F) → Prop :=
    fun p w => w ∈ rsAgreementSpace domain k p.1 ∧
      w ∈ rsAgreementSpace domain k p.2
  have hdc :
      (∑ p ∈ P,
        ((Finset.univ : Finset (ι → F)).bipartiteAbove r p).card) =
      ∑ w ∈ (Finset.univ : Finset (ι → F)),
        (P.bipartiteBelow r w).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := r) (s := P) (t := (Finset.univ : Finset (ι → F)))
  have hleft :
      (∑ p ∈ P,
        ((Finset.univ : Finset (ι → F)).bipartiteAbove r p).card) =
      ∑ p ∈ P, rsAgreementPairCount domain k p.1 p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.bipartiteAbove]
    unfold rsAgreementPairCount
    rfl
  have hright :
      (∑ w ∈ (Finset.univ : Finset (ι → F)),
        (P.bipartiteBelow r w).card) =
      ∑ w : ι → F, (cs25CertificateCount domain k f w) ^ 2 := by
    apply Finset.sum_congr rfl
    intro w hw
    have heq :
        P.bipartiteBelow r w =
          rsAgreementCertificates domain k f w ×ˢ
            rsAgreementCertificates domain k f w := by
      ext p
      simp [P, S, r, rsAgreementCertificates]
      tauto
    rw [heq, Finset.card_product, ← cs25CertificateCount_eq_filter_proof,
      pow_two]
  calc
    (∑ w : ι → F, (cs25CertificateCount domain k f w) ^ 2) =
        ∑ w ∈ (Finset.univ : Finset (ι → F)), (P.bipartiteBelow r w).card :=
      hright.symm
    _ = ∑ p ∈ P,
        ((Finset.univ : Finset (ι → F)).bipartiteAbove r p).card := hdc.symm
    _ = ∑ p ∈ P, rsAgreementPairCount domain k p.1 p.2 := hleft
    _ = ∑ E ∈ rsExactErrorSets (ι := ι) f,
        ∑ E' ∈ rsExactErrorSets (ι := ι) f,
          rsAgreementPairCount domain k E E' := by
      dsimp [P, S]
      exact Finset.sum_product _ _ _

theorem rsExactErrorSets_card_proof
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ℕ) :
    (rsExactErrorSets (ι := ι) f).card = Nat.choose (Fintype.card ι) f := by
  unfold rsExactErrorSets
  rw [Finset.card_powersetCard, Finset.card_univ]

open scoped BigOperators in
theorem cs25CertificateCount_sum_nat_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hsmall : k + f ≤ Fintype.card ι) :
    ∑ w : ι → F, cs25CertificateCount domain k f w =
      Nat.choose (Fintype.card ι) f * Fintype.card F ^ (k + f) := by
  classical
  let r : Finset ι → (ι → F) → Prop :=
    fun E w => w ∈ rsAgreementSpace domain k E
  have hdc :
      (∑ E ∈ rsExactErrorSets (ι := ι) f,
        ((Finset.univ : Finset (ι → F)).bipartiteAbove r E).card) =
      ∑ w ∈ (Finset.univ : Finset (ι → F)),
        ((rsExactErrorSets (ι := ι) f).bipartiteBelow r w).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := r) (s := rsExactErrorSets (ι := ι) f)
      (t := (Finset.univ : Finset (ι → F)))
  have hleft :
      (∑ E ∈ rsExactErrorSets (ι := ι) f,
        ((Finset.univ : Finset (ι → F)).bipartiteAbove r E).card) =
      (rsExactErrorSets (ι := ι) f).card * Fintype.card F ^ (k + f) := by
    calc
      (∑ E ∈ rsExactErrorSets (ι := ι) f,
          ((Finset.univ : Finset (ι → F)).bipartiteAbove r E).card) =
          ∑ E ∈ rsExactErrorSets (ι := ι) f,
            Fintype.card F ^ (k + f) := by
        apply Finset.sum_congr rfl
        intro E hE
        have hEcard : E.card = f := by
          simpa [rsExactErrorSets] using hE
        have hsmallE : k + E.card ≤ Fintype.card ι := by omega
        rw [Finset.bipartiteAbove]
        simpa only [r, hEcard] using
          rsAgreementSpace_filter_card_small_proof domain k E hsmallE
      _ = (rsExactErrorSets (ι := ι) f).card *
          Fintype.card F ^ (k + f) := by simp
  have hright :
      (∑ w ∈ (Finset.univ : Finset (ι → F)),
        ((rsExactErrorSets (ι := ι) f).bipartiteBelow r w).card) =
      ∑ w : ι → F, cs25CertificateCount domain k f w := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.bipartiteBelow]
    simpa only [r, rsAgreementCertificates] using
      (cs25CertificateCount_eq_filter_proof domain k f w).symm
  calc
    (∑ w : ι → F, cs25CertificateCount domain k f w) =
        ∑ w ∈ (Finset.univ : Finset (ι → F)),
          ((rsExactErrorSets (ι := ι) f).bipartiteBelow r w).card := hright.symm
    _ = ∑ E ∈ rsExactErrorSets (ι := ι) f,
        ((Finset.univ : Finset (ι → F)).bipartiteAbove r E).card := hdc.symm
    _ = (rsExactErrorSets (ι := ι) f).card *
        Fintype.card F ^ (k + f) := hleft
    _ = Nat.choose (Fintype.card ι) f * Fintype.card F ^ (k + f) := by
      rw [rsExactErrorSets_card_proof]

noncomputable def rsFarWords
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) : Finset (ι → F) := by
  classical
  exact Finset.univ.filter fun w =>
    ¬ Code.distFromCode w (ReedSolomon.code domain k : Set (ι → F)) ≤ f

private theorem rsSupportedSpace_sup
    {ι F : Type} [Finite ι] [DecidableEq ι]
    [Field F] (E E' : Finset ι) :
    Pi.spanSubset F (E : Set ι) ⊔ Pi.spanSubset F (E' : Set ι) =
      Pi.spanSubset F (((E ∪ E' : Finset ι) : Set ι)) := by
  let := Fintype.ofFinite ι
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [Pi.mem_spanSubset_iff]
    intro i hi
    have hiE : i ∉ (E : Set ι) := by
      intro h
      exact hi (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inl h)
    have hiE' : i ∉ (E' : Set ι) := by
      intro h
      exact hi (by simp only [Finset.coe_union, Set.mem_union]; exact Or.inr h)
    have hy0 : y i = 0 := (Pi.mem_spanSubset_iff.mp hy) i hiE
    have hz0 : z i = 0 := (Pi.mem_spanSubset_iff.mp hz) i hiE'
    simp [Pi.add_apply, hy0, hz0]
  · intro hv
    have hv' := Pi.mem_spanSubset_iff.mp hv
    let y : ι → F := fun i => if i ∈ E then v i else 0
    let z : ι → F := v - y
    refine ⟨y, ?_, z, ?_, ?_⟩
    · rw [Pi.mem_spanSubset_iff]
      intro i hi
      have hi' : i ∉ E := by simpa using hi
      simp [y, hi']
    · rw [Pi.mem_spanSubset_iff]
      intro i hiE'
      have hiE'' : i ∉ E' := by simpa using hiE'
      by_cases hiE : i ∈ E
      · simp [z, y, hiE]
      · have hv0 : v i = 0 := hv' i (by
          simp only [Finset.coe_union, Set.mem_union]
          exact not_or_intro hiE hiE'')
        simp [z, y, hiE, hv0]
    · ext i
      simp [z, y]

theorem rsAgreementSpace_sup
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E E' : Finset ι) :
    rsAgreementSpace domain k E ⊔ rsAgreementSpace domain k E' =
      rsAgreementSpace domain k (E ∪ E') := by
  unfold rsAgreementSpace
  rw [← rsSupportedSpace_sup E E']
  calc
    (ReedSolomon.code domain k ⊔ Pi.spanSubset F (E : Set ι)) ⊔
        (ReedSolomon.code domain k ⊔ Pi.spanSubset F (E' : Set ι)) =
      ReedSolomon.code domain k ⊔
        (ReedSolomon.code domain k ⊔
          (Pi.spanSubset F (E : Set ι) ⊔ Pi.spanSubset F (E' : Set ι))) := by
            ac_rfl
    _ = ReedSolomon.code domain k ⊔
        (Pi.spanSubset F (E : Set ι) ⊔ Pi.spanSubset F (E' : Set ι)) := by
          rw [← sup_assoc, sup_idem]

theorem rs_close_words_eq_certificate_support_proof
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (hf : f ≤ Fintype.card ι) :
    (Finset.univ.filter (fun w : ι → F =>
      0 < cs25CertificateCount domain k f w)) =
      Finset.univ \ rsFarWords domain k f := by
  classical
  ext w
  simp [rsFarWords, cs25CertificateCount_pos_iff_close_proof domain k f w hf]

theorem rs_entropy_rate_d_le_kf_proof
    (q n k f : ℕ) (hq : 10 ≤ q) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n) :
    n - f - k ≤ k + f := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let s : ℝ :=
    ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
  have hs : 0 ≤ s := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hgap := cs25_entropy_gap_lt_half_proof q ((f : ℝ) / n) hq (by positivity)
  have hgap_scaled := mul_lt_mul_of_pos_right hgap hnR
  have hm := mul_le_mul_of_nonneg_right hlo hnR.le
  have hkn :
      (1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) + s) * n ≤ k := by
    calc
      _ ≤ ((k : ℝ) / n) * n := by simpa only [s] using hm
      _ = k := by field_simp [hnR.ne']
  have hkn' :
      (n : ℝ) - (n : ℝ) * qEntropy q ((f : ℝ) / n) + 2 + (n : ℝ) * s ≤ k := by
    calc
      _ = (1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) + s) * n := by
        field_simp [hnR.ne']
      _ ≤ k := hkn
  have hreal : (n : ℝ) < 2 * ((k : ℝ) + f) := by
    field_simp [hnR.ne'] at hgap_scaled
    nlinarith only [hgap_scaled, hkn', hs]
  have hnat : n < 2 * (k + f) := by exact_mod_cast hreal
  omega

end ReedSolomon

end EntropyInternal
end CodingTheory

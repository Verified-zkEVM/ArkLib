/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Linear
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import ArkLib.Data.CodingTheory.ProximityGap.Errors

set_option linter.style.longFile 2200

/-!
# Entropy-regime CA breakdown for Reed--Solomon codes

This file proves the complete correlated-agreement breakdown for a Reed--Solomon code whose
rate lies inside an entropy-defined band: `ε_ca(C, δ) = 1` at the integer grid radius `δ = f/n`.
The argument is a CS25-style second-moment/entropy counting bound on the number of certificates
of a codeword, combined with a "boundary word" construction to exhibit a bad joint-proximity
witness.

## Main result

- `rs_epsCa_eq_one_of_entropy_rate` — ABF26 Theorem 4.17 [CS25 Cor 1]: complete CA breakdown
  for RS codes when the rate sits inside an entropy-defined band, stated at the source's
  integer error radius.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [CS25] Crites–Stewart, *On Reed–Solomon Proximity Gaps Conjectures*, ePrint 2025/2046.
  Corollary 1 = source of Theorem 4.17.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private noncomputable def cs25CertificateCount
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

private noncomputable def cs25OverlapSum (q n k f : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range (n - f - k),
    (Nat.choose f ℓ : ℝ) * (Nat.choose (n - f) ℓ : ℝ) / (q : ℝ) ^ ℓ

private theorem cs25OverlapSum_le_exp_two_sqrt
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

private noncomputable def cs25SecondMomentA (q n k f : ℕ) : ℝ :=
  (q : ℝ) ^ (n - f - k) * cs25OverlapSum q n k f

open scoped BigOperators in
private def cs25SecondMomentANat (q n k f : ℕ) : ℕ :=
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
private theorem cs25SecondMomentANat_cast_proof
    (q n k f : ℕ) (hq : 0 < q) :
    (cs25SecondMomentANat q n k f : ℝ) = cs25SecondMomentA q n k f := by
  rw [cs25SecondMomentA_eq_weighted_sum_proof q n k f hq]
  unfold cs25SecondMomentANat
  push_cast
  rfl

private theorem cs25SecondMomentA_nonneg_proof (q n k f : ℕ) :
    0 ≤ cs25SecondMomentA q n k f := by
  unfold cs25SecondMomentA
  exact mul_nonneg (by positivity) (cs25OverlapSum_nonneg q n k f)

private theorem cs25_entropy_shell_le_choose_proof
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

private theorem cs25_quadratic_entropy_gap_proof
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

private theorem cs25_shell_power_bound
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
private theorem epsCa_eq_one_of_all_folds_close_not_joint
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

private theorem exists_base_all_translates_close_of_bad_count
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

private theorem nat_card_lt_pow_pred_of_weighted_bound
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

private theorem not_jointProximity_of_second_row_far
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

private noncomputable def rsAgreementSpace
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (E : Finset ι) : Submodule F (ι → F) :=
  ReedSolomon.code domain k ⊔ Pi.spanSubset F (E : Set ι)

private noncomputable def rsAgreementPairCount
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

private def rsBoundaryWord {ι F : Type} [Monoid F] (domain : ι ↪ F) (k : ℕ) : ι → F :=
  fun i => domain i ^ k

private theorem rsBoundaryWord_far
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

private theorem rsAgreementSpace_finrank
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

private def rsExactErrorSets {ι : Type} [Fintype ι] [DecidableEq ι]
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
private theorem cs25CertificateCount_sq_sum_eq_pair_sum_nat_proof
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

private theorem rsExactErrorSets_card_proof
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ℕ) :
    (rsExactErrorSets (ι := ι) f).card = Nat.choose (Fintype.card ι) f := by
  unfold rsExactErrorSets
  rw [Finset.card_powersetCard, Finset.card_univ]

open scoped BigOperators in
private theorem cs25CertificateCount_sum_nat_proof
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

private noncomputable def rsFarWords
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

private theorem rsAgreementSpace_sup
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

private theorem rs_close_words_eq_certificate_support_proof
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (hf : f ≤ Fintype.card ι) :
    (Finset.univ.filter (fun w : ι → F =>
      0 < cs25CertificateCount domain k f w)) =
      Finset.univ \ rsFarWords domain k f := by
  classical
  ext w
  simp [rsFarWords, cs25CertificateCount_pos_iff_close_proof domain k f w hf]

private theorem rs_entropy_rate_d_le_kf_proof
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

private theorem rs_entropy_rate_nat_margin {ι : Type} [Fintype ι] [Nonempty ι]
    (k f : ℕ)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤
      1 - (f : ℝ) / Fintype.card ι - 2 / (Fintype.card ι : ℝ)) :
    k + f + 2 ≤ Fintype.card ι := by
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn_pos
  have h := mul_le_mul_of_nonneg_right hδ_hi hnR.le
  field_simp at h
  have hR : (k : ℝ) + f + 2 ≤ Fintype.card ι := by nlinarith
  exact_mod_cast hR

private theorem rs_entropy_rate_parameter_facts
    (q n k f : ℕ) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi :
      (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    k + f + 2 ≤ n ∧ 0 < f ∧ f < n ∧
      0 < qEntropy q ((f : ℝ) / n) - (f : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hslackR : (k : ℝ) + f + 2 ≤ n := by
    have h := mul_le_mul_of_nonneg_right hhi hnR.le
    field_simp at h
    nlinarith only [h]
  have hslack : k + f + 2 ≤ n := by exact_mod_cast hslackR
  have hfpos : 0 < f := by
    by_contra hf
    have hf0 : f = 0 := Nat.eq_zero_of_not_pos hf
    subst f
    simp only [Nat.cast_zero, zero_div, qEntropy_zero, sub_zero, one_div] at hlo hhi
    have htwo : (0 : ℝ) < 2 / n := div_pos (by norm_num) hnR
    linarith only [hlo, hhi, htwo]
  have hflt : f < n := by omega
  let s : ℝ :=
    ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hcomp :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) + s ≤
        1 - (f : ℝ) / n - 2 / (n : ℝ) := by
    exact le_trans hlo hhi
  have hgap : 4 / (n : ℝ) + s ≤
      qEntropy q ((f : ℝ) / n) - (f : ℝ) / n := by
    rw [show 4 / (n : ℝ) = 2 / (n : ℝ) + 2 / (n : ℝ) by ring]
    linarith only [hcomp]
  have hfour : (0 : ℝ) < 4 / n := div_pos (by norm_num) hnR
  have hdiff : 0 < qEntropy q ((f : ℝ) / n) - (f : ℝ) / n :=
    lt_of_lt_of_le (by linarith only [hfour, hs_nonneg] : 0 < 4 / (n : ℝ) + s) hgap
  exact ⟨hslack, hfpos, hflt, hdiff⟩

private theorem rs_entropy_rate_exponent_slack
    (q n k f : ℕ) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi :
      (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    let h : ℝ := qEntropy q ((f : ℝ) / n) - (f : ℝ) / n
    let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
    (((n - f - k : ℕ) : ℝ) + 2 + (n : ℝ) * s) ≤ (n : ℝ) * h := by
  dsimp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hslack, hfpos, hflt, hgap⟩ :=
    rs_entropy_rate_parameter_facts q n k f hn hlo hhi
  have hm := mul_le_mul_of_nonneg_right hlo hnR.le
  have hkn :
      (1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) * n ≤ k := by
    calc
      _ ≤ ((k : ℝ) / n) * n := hm
      _ = k := by field_simp
  have hkn' :
      (n : ℝ) - (n : ℝ) * qEntropy q ((f : ℝ) / n) + 2 +
          (n : ℝ) *
            ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2) ≤ k := by
    calc
      _ = (1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) * n := by
            field_simp
      _ ≤ k := hkn
  have hdcast : (((n - f - k : ℕ) : ℝ)) = (n : ℝ) - f - k := by
    rw [Nat.cast_sub (by omega : k ≤ n - f), Nat.cast_sub (by omega : f ≤ n)]
  have hrhs :
      (n : ℝ) * (qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) =
        (n : ℝ) * qEntropy q ((f : ℝ) / n) - f := by
    field_simp
  rw [hdcast, hrhs]
  linarith only [hkn']

private theorem rs_entropy_rate_full_parameter_facts_proof
    (q n k f : ℕ) (hq : 10 ≤ q) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi : (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    k + f + 2 ≤ n ∧ 0 < f ∧ f < n ∧ 2 ≤ n - f - k ∧
      n - f - k ≤ k + f := by
  obtain ⟨hmargin, hfpos, hflt, _⟩ :=
    rs_entropy_rate_parameter_facts q n k f hn hlo hhi
  have hdle := rs_entropy_rate_d_le_kf_proof q n k f hq hn hlo
  exact ⟨hmargin, hfpos, hflt, by omega, hdle⟩

private theorem rs_exact_error_exchange_fiber_card_le_proof
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Finset ι) (f ℓ : ℕ) (hE : E.card = f) :
    ((rsExactErrorSets (ι := ι) f).filter
      (fun E' => (E \ E').card = ℓ)).card ≤
      Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ := by
  classical
  let S : Finset (Finset ι) :=
    (rsExactErrorSets (ι := ι) f).filter (fun E' => (E \ E').card = ℓ)
  let T : Finset (Finset ι × Finset ι) :=
    E.powersetCard ℓ ×ˢ (Finset.univ \ E).powersetCard ℓ
  let φ : Finset ι → Finset ι × Finset ι :=
    fun E' => (E \ E', E' \ E)
  have hmap : Set.MapsTo φ (S : Set (Finset ι)) (T : Set (Finset ι × Finset ι)) := by
    intro E' hE'S
    have hm := Finset.mem_filter.mp hE'S
    have hE'card : E'.card = f := by
      simpa [rsExactErrorSets] using hm.1
    have hrightcard : (E' \ E).card = ℓ := by
      have hdiff := Finset.card_sdiff_comm (hE.trans hE'card.symm)
      omega
    have hleftsubset : E \ E' ⊆ E := Finset.sdiff_subset
    have hrightsubset : E' \ E ⊆ Finset.univ \ E := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
    change (E \ E', E' \ E) ∈ E.powersetCard ℓ ×ˢ (Finset.univ \ E).powersetCard ℓ
    rw [Finset.mem_product]
    constructor
    · rw [Finset.mem_powersetCard]
      exact ⟨hleftsubset, hm.2⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨hrightsubset, hrightcard⟩
  have hinj : (S : Set (Finset ι)).InjOn φ := by
    intro A hAS B hBS hab
    have hfst : E \ A = E \ B := congrArg Prod.fst hab
    have hsnd : A \ E = B \ E := congrArg Prod.snd hab
    have hrecover (X : Finset ι) :
        X = (E \ (E \ X)) ∪ (X \ E) := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    rw [hrecover A, hrecover B, hfst, hsnd]
  have hcard := Finset.card_le_card_of_injOn φ hmap hinj
  change S.card ≤ T.card at hcard
  simpa [S, T, Finset.card_product, Finset.card_powersetCard,
    Finset.card_sdiff, hE, Finset.card_univ] using hcard

private theorem rs_exact_error_union_card_proof
    {ι : Type} [DecidableEq ι] (E E' : Finset ι) (f : ℕ)
    (_hE : E.card = f) (hE' : E'.card = f) :
    (E ∪ E').card = f + (E \ E').card := by
  calc
    (E ∪ E').card = (E \ E').card + E'.card :=
      (Finset.card_sdiff_add_card E E').symm
    _ = f + (E \ E').card := by omega

private theorem rsAgreementPair_finrank_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E E' : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι)
    (hE : E.card = f) (hE' : E'.card = f) :
    Module.finrank F
      ↥(rsAgreementSpace domain k E ⊓ rsAgreementSpace domain k E') =
      k + f - min (E \ E').card (Fintype.card ι - f - k) := by
  have hfinE : Module.finrank F (rsAgreementSpace domain k E) = k + f := by
    rw [rsAgreementSpace_finrank domain k E, hE, min_eq_right hsmall]
  have hfinE' : Module.finrank F (rsAgreementSpace domain k E') = k + f := by
    rw [rsAgreementSpace_finrank domain k E', hE', min_eq_right hsmall]
  have hunion : (E ∪ E').card = f + (E \ E').card :=
    rs_exact_error_union_card_proof E E' f hE hE'
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (rsAgreementSpace domain k E) (rsAgreementSpace domain k E')
  rw [rsAgreementSpace_sup domain k E E', rsAgreementSpace_finrank,
    hunion, hfinE, hfinE'] at hdim
  by_cases hℓ : (E \ E').card ≤ Fintype.card ι - f - k
  · rw [min_eq_left hℓ]
    have hsumle : k + (f + (E \ E').card) ≤ Fintype.card ι := by omega
    rw [min_eq_right hsumle] at hdim
    omega
  · have hdle : Fintype.card ι - f - k ≤ (E \ E').card := by omega
    rw [min_eq_right hdle]
    have hnle : Fintype.card ι ≤ k + (f + (E \ E').card) := by omega
    rw [min_eq_left hnle] at hdim
    omega

private theorem rsAgreementPairCount_eq_pow_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E E' : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι)
    (hE : E.card = f) (hE' : E'.card = f) :
    rsAgreementPairCount domain k E E' =
      Fintype.card F ^
        (k + f - min (E \ E').card (Fintype.card ι - f - k)) := by
  classical
  unfold rsAgreementPairCount
  rw [← Fintype.card_subtype]
  let e :
      {w : ι → F // w ∈ rsAgreementSpace domain k E ∧
        w ∈ rsAgreementSpace domain k E'} ≃
      ↥(rsAgreementSpace domain k E ⊓ rsAgreementSpace domain k E') :=
    { toFun := fun w => ⟨w.1, Submodule.mem_inf.mpr w.2⟩
      invFun := fun w => ⟨w.1, Submodule.mem_inf.mp w.2⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl }
  calc
    Fintype.card {w : ι → F // w ∈ rsAgreementSpace domain k E ∧
        w ∈ rsAgreementSpace domain k E'} =
      Fintype.card ↥(rsAgreementSpace domain k E ⊓
        rsAgreementSpace domain k E') := Fintype.card_congr e
    _ = Fintype.card F ^
        Module.finrank F
          ↥(rsAgreementSpace domain k E ⊓ rsAgreementSpace domain k E') :=
      Module.card_eq_pow_finrank
    _ = _ := by
      rw [rsAgreementPair_finrank_proof domain k f E E' hsmall hE hE']

open scoped BigOperators in
private theorem rsAgreementPairCount_high_overlap_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f) :
    ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => Fintype.card ι - f - k ≤ (E \ E').card),
      rsAgreementPairCount domain k E E' ≤
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          Nat.choose (Fintype.card ι) f := by
  classical
  let d : ℕ := Fintype.card ι - f - k
  let S : Finset (Finset ι) :=
    (rsExactErrorSets (ι := ι) f).filter (fun E' => d ≤ (E \ E').card)
  let Q : ℕ := Fintype.card F ^ (k + f - d)
  have hterm : ∀ E' ∈ S, rsAgreementPairCount domain k E E' ≤ Q := by
    intro E' hE'S
    have hm := Finset.mem_filter.mp hE'S
    have hE'card : E'.card = f := by
      simpa [S, rsExactErrorSets] using hm.1
    have hp := rsAgreementPairCount_eq_pow_proof domain k f E E'
      hsmall hE hE'card
    have hmin : min (E \ E').card d = d := min_eq_right hm.2
    rw [hp, hmin]
  have hsum := Finset.sum_le_card_nsmul S
    (fun E' => rsAgreementPairCount domain k E E') Q hterm
  have hcard : S.card ≤ Nat.choose (Fintype.card ι) f := by
    calc
      S.card ≤ (rsExactErrorSets (ι := ι) f).card := by
        simpa only [S] using Finset.card_filter_le
          (rsExactErrorSets (ι := ι) f) (fun E' => d ≤ (E \ E').card)
      _ = Nat.choose (Fintype.card ι) f := rsExactErrorSets_card_proof f
  have hmul := Nat.mul_le_mul_right Q hcard
  change (∑ E' ∈ S, rsAgreementPairCount domain k E E') ≤
    Q * Nat.choose (Fintype.card ι) f
  exact le_trans (by simpa [Nat.nsmul_eq_mul] using hsum) (by
    simpa [Nat.mul_comm] using hmul)

open scoped BigOperators in
private theorem rsAgreementPairCount_low_overlap_fiber_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f ℓ : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f)
    (hℓ : ℓ < Fintype.card ι - f - k) :
    ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => (E \ E').card = ℓ),
      rsAgreementPairCount domain k E E' ≤
        Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ *
          Fintype.card F ^ (k + f - ℓ) := by
  classical
  let S : Finset (Finset ι) :=
    (rsExactErrorSets (ι := ι) f).filter (fun E' => (E \ E').card = ℓ)
  let Q : ℕ := Fintype.card F ^ (k + f - ℓ)
  have hterm : ∀ E' ∈ S, rsAgreementPairCount domain k E E' ≤ Q := by
    intro E' hE'S
    have hm := Finset.mem_filter.mp hE'S
    have hE'card : E'.card = f := by
      simpa [S, rsExactErrorSets] using hm.1
    have hp := rsAgreementPairCount_eq_pow_proof domain k f E E'
      hsmall hE hE'card
    have hmin : min (E \ E').card (Fintype.card ι - f - k) = ℓ := by
      rw [hm.2, min_eq_left (Nat.le_of_lt hℓ)]
    rw [hp, hmin]
  have hsum := Finset.sum_le_card_nsmul S
    (fun E' => rsAgreementPairCount domain k E E') Q hterm
  have hcard : S.card ≤ Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ := by
    simpa [S] using rs_exact_error_exchange_fiber_card_le_proof E f ℓ hE
  have hmul := Nat.mul_le_mul_right Q hcard
  change (∑ E' ∈ S, rsAgreementPairCount domain k E E') ≤
    Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ * Q
  exact le_trans (by simpa [Nat.nsmul_eq_mul] using hsum) (by
    simpa [Nat.mul_assoc] using hmul)

open scoped BigOperators in
private theorem rsAgreementPairCount_low_overlap_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => (E \ E').card < Fintype.card ι - f - k),
      rsAgreementPairCount domain k E E' ≤
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f := by
  classical
  let d : ℕ := Fintype.card ι - f - k
  have hregroup :
      (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
          (fun E' => (E \ E').card < d),
        rsAgreementPairCount domain k E E') =
        ∑ ℓ ∈ Finset.range d,
          ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => (E \ E').card = ℓ),
            rsAgreementPairCount domain k E E' := by
    have h := Finset.sum_fiberwise_eq_sum_filter
      (rsExactErrorSets (ι := ι) f) (Finset.range d)
      (fun E' : Finset ι => (E \ E').card)
      (fun E' => rsAgreementPairCount domain k E E')
    symm
    simpa only [Finset.mem_range] using h
  calc
    (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
        (fun E' => (E \ E').card < Fintype.card ι - f - k),
      rsAgreementPairCount domain k E E') =
        ∑ ℓ ∈ Finset.range d,
          ∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => (E \ E').card = ℓ),
            rsAgreementPairCount domain k E E' := by simpa only [d] using hregroup
    _ ≤ ∑ ℓ ∈ Finset.range d,
        Nat.choose f ℓ * Nat.choose (Fintype.card ι - f) ℓ *
          Fintype.card F ^ (k + f - ℓ) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      exact rsAgreementPairCount_low_overlap_fiber_le_proof
        domain k f ℓ E hsmall hE (by simpa only [d] using Finset.mem_range.mp hℓ)
    _ = Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
        cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f := by
      unfold cs25SecondMomentANat
      rw [Finset.mul_sum]
      apply Finset.sum_congr
      · rfl
      · intro ℓ hℓ
        have hℓlt : ℓ < Fintype.card ι - f - k := Finset.mem_range.mp hℓ
        have hexp : k + f - ℓ =
            (k + f - (Fintype.card ι - f - k)) +
              (Fintype.card ι - f - k - ℓ) := by omega
        rw [hexp, pow_add]
        ac_rfl

open scoped BigOperators in
private theorem rsAgreementPairCount_fixed_error_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ) (E : Finset ι)
    (hsmall : k + f ≤ Fintype.card ι) (hE : E.card = f)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ∑ E' ∈ rsExactErrorSets (ι := ι) f,
      rsAgreementPairCount domain k E E' ≤
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
            Nat.choose (Fintype.card ι) f) := by
  classical
  let d : ℕ := Fintype.card ι - f - k
  let Q : ℕ := Fintype.card F ^ (k + f - d)
  let A : ℕ := cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f
  let N : ℕ := Nat.choose (Fintype.card ι) f
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (rsExactErrorSets (ι := ι) f) (fun E' : Finset ι => (E \ E').card < d)
    (fun E' => rsAgreementPairCount domain k E E')
  have hlo :
      (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
          (fun E' => (E \ E').card < d),
        rsAgreementPairCount domain k E E') ≤ Q * A := by
    simpa only [d, Q, A] using
      rsAgreementPairCount_low_overlap_sum_le_proof domain k f E hsmall hE hdle
  have hhi :
      (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
          (fun E' => d ≤ (E \ E').card),
        rsAgreementPairCount domain k E E') ≤ Q * N := by
    simpa only [d, Q, N] using
      rsAgreementPairCount_high_overlap_sum_le_proof domain k f E hsmall hE
  change (∑ E' ∈ rsExactErrorSets (ι := ι) f,
      rsAgreementPairCount domain k E E') ≤ Q * (A + N)
  calc
    (∑ E' ∈ rsExactErrorSets (ι := ι) f,
        rsAgreementPairCount domain k E E') =
        (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => (E \ E').card < d),
          rsAgreementPairCount domain k E E') +
        (∑ E' ∈ (rsExactErrorSets (ι := ι) f).filter
            (fun E' => d ≤ (E \ E').card),
          rsAgreementPairCount domain k E E') := by
      simpa only [not_lt] using hsplit.symm
    _ ≤ Q * A + Q * N := Nat.add_le_add hlo hhi
    _ = Q * (A + N) := by rw [Nat.mul_add]

open scoped BigOperators in
private theorem cs25CertificateCount_sq_sum_le_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hsmall : k + f ≤ Fintype.card ι)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ∑ w : ι → F, (cs25CertificateCount domain k f w) ^ 2 ≤
      Nat.choose (Fintype.card ι) f *
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
            Nat.choose (Fintype.card ι) f) := by
  classical
  rw [cs25CertificateCount_sq_sum_eq_pair_sum_nat_proof domain k f]
  let Q : ℕ :=
    Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
      (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
        Nat.choose (Fintype.card ι) f)
  have hterm : ∀ E ∈ rsExactErrorSets (ι := ι) f,
      (∑ E' ∈ rsExactErrorSets (ι := ι) f,
        rsAgreementPairCount domain k E E') ≤ Q := by
    intro E hE
    have hEcard : E.card = f := by
      simpa [rsExactErrorSets] using hE
    simpa only [Q] using
      rsAgreementPairCount_fixed_error_sum_le_proof
        domain k f E hsmall hEcard hdle
  have hsum := Finset.sum_le_card_nsmul (rsExactErrorSets (ι := ι) f)
    (fun E => ∑ E' ∈ rsExactErrorSets (ι := ι) f,
      rsAgreementPairCount domain k E E') Q hterm
  calc
    (∑ E ∈ rsExactErrorSets (ι := ι) f,
        ∑ E' ∈ rsExactErrorSets (ι := ι) f,
          rsAgreementPairCount domain k E E') ≤
        (rsExactErrorSets (ι := ι) f).card • Q := hsum
    _ = Nat.choose (Fintype.card ι) f *
        Fintype.card F ^ (k + f - (Fintype.card ι - f - k)) *
          (cs25SecondMomentANat (Fintype.card F) (Fintype.card ι) k f +
            Nat.choose (Fintype.card ι) f) := by
      rw [rsExactErrorSets_card_proof]
      simp only [Q, Nat.nsmul_eq_mul, Nat.mul_assoc]

open scoped BigOperators in
private theorem cs25CertificateSupport_lower_bound_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hqpos : 0 < Fintype.card F)
    (hsmall : k + f ≤ Fintype.card ι)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    (Nat.choose (Fintype.card ι) f : ℝ) *
        (Fintype.card F : ℝ) ^ Fintype.card ι ≤
      ((Finset.univ.filter (fun w : ι → F =>
          0 < cs25CertificateCount domain k f w)).card : ℝ) *
        ((Nat.choose (Fintype.card ι) f : ℝ) +
          cs25SecondMomentA (Fintype.card F) (Fintype.card ι) k f) := by
  classical
  let n : ℕ := Fintype.card ι
  let q : ℕ := Fintype.card F
  let d : ℕ := n - f - k
  let K : ℕ := k + f
  let N : ℕ := Nat.choose n f
  let AN : ℕ := cs25SecondMomentANat q n k f
  let A : ℝ := cs25SecondMomentA q n k f
  let X : (ι → F) → ℕ := fun w => cs25CertificateCount domain k f w
  let S : Finset (ι → F) := Finset.univ.filter (fun w => 0 < X w)
  have hf_le_n : f ≤ n := by dsimp [n]; omega
  have hNposNat : 0 < N := by
    dsimp [N]
    exact Nat.choose_pos hf_le_n
  have hqposR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hsumNat : ∑ w : ι → F, X w = N * q ^ K := by
    simpa only [X, N, q, n, K] using
      cs25CertificateCount_sum_nat_proof domain k f hsmall
  have hsumReal : ∑ w : ι → F, (X w : ℝ) = (N : ℝ) * (q : ℝ) ^ K := by
    exact_mod_cast hsumNat
  have hsumSupport :
      ∑ w ∈ S, (X w : ℝ) = (N : ℝ) * (q : ℝ) ^ K := by
    calc
      (∑ w ∈ S, (X w : ℝ)) = ∑ w : ι → F, (X w : ℝ) := by
        dsimp [S]
        apply Finset.sum_filter_of_ne
        intro w hw hne
        have hxne : X w ≠ 0 := by
          intro hx
          apply hne
          simp [hx]
        exact Nat.pos_of_ne_zero hxne
      _ = (N : ℝ) * (q : ℝ) ^ K := hsumReal
  have hsqNat :
      ∑ w : ι → F, (X w) ^ 2 ≤
        N * q ^ (K - d) * (AN + N) := by
    simpa only [X, N, q, n, K, d, AN] using
      cs25CertificateCount_sq_sum_le_proof domain k f hsmall hdle
  have hsqReal :
      ∑ w : ι → F, (X w : ℝ) ^ 2 ≤
        (N : ℝ) * (q : ℝ) ^ (K - d) * ((AN : ℝ) + (N : ℝ)) := by
    exact_mod_cast hsqNat
  have hANcast : (AN : ℝ) = A := by
    simpa only [AN, A, q, n] using cs25SecondMomentANat_cast_proof q n k f hqpos
  have hsqSupport :
      ∑ w ∈ S, (X w : ℝ) ^ 2 ≤
        (N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ)) := by
    calc
      (∑ w ∈ S, (X w : ℝ) ^ 2) = ∑ w : ι → F, (X w : ℝ) ^ 2 := by
        dsimp [S]
        apply Finset.sum_filter_of_ne
        intro w hw hne
        have hxne : X w ≠ 0 := by
          intro hx
          apply hne
          simp [hx]
        exact Nat.pos_of_ne_zero hxne
      _ ≤ (N : ℝ) * (q : ℝ) ^ (K - d) * ((AN : ℝ) + (N : ℝ)) := hsqReal
      _ = (N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ)) := by rw [hANcast]
  have hcs :
      (∑ w ∈ S, (X w : ℝ)) ^ 2 ≤
        (S.card : ℝ) * ∑ w ∈ S, (X w : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmoment :
      ((N : ℝ) * (q : ℝ) ^ K) ^ 2 ≤
        (S.card : ℝ) *
          ((N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ))) := by
    rw [hsumSupport] at hcs
    exact le_trans hcs (mul_le_mul_of_nonneg_left hsqSupport (by positivity))
  have hKn : K + d = n := by
    dsimp [K, d, n]
    omega
  have hdK : d ≤ K := by simpa only [d, K, n] using hdle
  have hexp : (K - d) + n = K + K := by omega
  have hpowers :
      (q : ℝ) ^ (K - d) * (q : ℝ) ^ n =
        (q : ℝ) ^ K * (q : ℝ) ^ K := by
    rw [← pow_add, ← pow_add, hexp]
  have hleft :
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) =
        ((N : ℝ) * (q : ℝ) ^ K) ^ 2 := by
    rw [pow_two]
    calc
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) =
          (N : ℝ) * (N : ℝ) *
            ((q : ℝ) ^ (K - d) * (q : ℝ) ^ n) := by ring
      _ = (N : ℝ) * (N : ℝ) *
            ((q : ℝ) ^ K * (q : ℝ) ^ K) := by rw [hpowers]
      _ = ((N : ℝ) * (q : ℝ) ^ K) *
            ((N : ℝ) * (q : ℝ) ^ K) := by ring
  have hright :
      (S.card : ℝ) *
          ((N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ))) =
        ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((S.card : ℝ) * ((N : ℝ) + A)) := by ring
  have hfactor :
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) ≤
        ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((S.card : ℝ) * ((N : ℝ) + A)) := by
    calc
      ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((N : ℝ) * (q : ℝ) ^ n) =
          ((N : ℝ) * (q : ℝ) ^ K) ^ 2 := hleft
      _ ≤ (S.card : ℝ) *
          ((N : ℝ) * (q : ℝ) ^ (K - d) * (A + (N : ℝ))) := hmoment
      _ = ((N : ℝ) * (q : ℝ) ^ (K - d)) *
          ((S.card : ℝ) * ((N : ℝ) + A)) := hright
  have hfactorPos : (0 : ℝ) < (N : ℝ) * (q : ℝ) ^ (K - d) := by
    exact mul_pos (by exact_mod_cast hNposNat) (pow_pos hqposR _)
  change (N : ℝ) * (q : ℝ) ^ n ≤ (S.card : ℝ) * ((N : ℝ) + A)
  exact le_of_mul_le_mul_of_pos_left hfactor hfactorPos

open scoped BigOperators in
private theorem rsFarWords_weighted_card_bound_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hqpos : 0 < Fintype.card F)
    (hsmall : k + f ≤ Fintype.card ι)
    (hdle : Fintype.card ι - f - k ≤ k + f) :
    ((rsFarWords domain k f).card : ℝ) *
        ((Nat.choose (Fintype.card ι) f : ℝ) +
          cs25SecondMomentA (Fintype.card F) (Fintype.card ι) k f) ≤
      (Fintype.card F : ℝ) ^ Fintype.card ι *
        cs25SecondMomentA (Fintype.card F) (Fintype.card ι) k f := by
  classical
  let n : ℕ := Fintype.card ι
  let q : ℕ := Fintype.card F
  let N : ℕ := Nat.choose n f
  let A : ℝ := cs25SecondMomentA q n k f
  let S : Finset (ι → F) := Finset.univ.filter
    (fun w => 0 < cs25CertificateCount domain k f w)
  let B : Finset (ι → F) := rsFarWords domain k f
  have hf_le : f ≤ Fintype.card ι := by omega
  have hsupport :
      (N : ℝ) * (q : ℝ) ^ n ≤ (S.card : ℝ) * ((N : ℝ) + A) := by
    simpa only [N, q, n, A, S] using
      cs25CertificateSupport_lower_bound_proof domain k f hqpos hsmall hdle
  have hclose : S = Finset.univ \ B := by
    simpa only [S, B] using
      rs_close_words_eq_certificate_support_proof domain k f hf_le
  have hcardNat : S.card + B.card = q ^ n := by
    have hcard0 :
        (Finset.univ \ B).card + B.card =
          (Finset.univ : Finset (ι → F)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    rw [← hclose, Finset.card_univ, Fintype.card_fun] at hcard0
    simpa only [q, n] using hcard0
  have hcardReal : (S.card : ℝ) + (B.card : ℝ) = (q : ℝ) ^ n := by
    exact_mod_cast hcardNat
  have hcardN := congrArg (fun x : ℝ => x * (N : ℝ)) hcardReal
  have hBN : (B.card : ℝ) * (N : ℝ) ≤ (S.card : ℝ) * A := by
    nlinarith [hsupport, hcardN]
  change (B.card : ℝ) * ((N : ℝ) + A) ≤ (q : ℝ) ^ n * A
  calc
    (B.card : ℝ) * ((N : ℝ) + A) =
        (B.card : ℝ) * (N : ℝ) + (B.card : ℝ) * A := by ring
    _ ≤ (S.card : ℝ) * A + (B.card : ℝ) * A :=
      add_le_add hBN le_rfl
    _ = ((S.card : ℝ) + (B.card : ℝ)) * A := by ring
    _ = (q : ℝ) ^ n * A := by rw [hcardReal]

private theorem rs_fraction_le_entropy_peak
    (q n f : ℕ) (hq : 2 ≤ q) (hnq : n ≤ q) (hf : f < n) :
    (f : ℝ) / n ≤ 1 - 1 / (q : ℝ) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq)
  have hdiv : (n : ℝ) / q ≤ 1 := (div_le_one hqR).2 (by exact_mod_cast hnq)
  rw [div_le_iff₀ hnR]
  have hfRle : (f : ℝ) + 1 ≤ n := by
    exact_mod_cast (show f + 1 ≤ n by omega)
  calc
    (f : ℝ) ≤ (n : ℝ) - 1 := by linarith
    _ ≤ (n : ℝ) - (n : ℝ) / q := by linarith
    _ = (1 - 1 / (q : ℝ)) * n := by ring

private theorem cs25_overlap_exp_le_entropy_power_proof
    (q n f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q)
    (hfpos : 0 < f) (hflt : f < n) :
    Real.exp (2 * Real.sqrt ((f : ℝ) * (n - f : ℕ) / q)) ≤
      (q : ℝ) ^ ((n : ℝ) *
        ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) := by
  have hn : 0 < n := lt_trans hfpos hflt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by positivity
  have hq2 : 2 ≤ q := by omega
  let x : ℝ := (f : ℝ) / n
  let h : ℝ := qEntropy q x - x
  let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
  let y : ℝ := (f : ℝ) * (n - f : ℕ) / q
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxlt : x < 1 := by
    dsimp [x]
    exact (div_lt_one hnR).2 (by exact_mod_cast hflt)
  have hxpeak : x ≤ 1 - 1 / (q : ℝ) := by
    dsimp [x]
    exact rs_fraction_le_entropy_peak q n f hq2 hnq hflt
  have hgap : 4 * x * (1 - x) ≤ (Real.log (q : ℝ)) ^ 2 * h := by
    dsimp [h]
    exact cs25_quadratic_entropy_gap_proof q x hq hxpos.le hxpeak
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq2)
  have hh : 0 ≤ h := by
    have hleft : 0 < 4 * x * (1 - x) := by positivity
    nlinarith only [hgap, hleft, sq_nonneg (Real.log (q : ℝ))]
  have hy_nonneg : 0 ≤ y := by dsimp [y]; positivity
  have hnum_nonneg : 0 ≤ (f : ℝ) * (n - f : ℕ) := by positivity
  have hy_le : y ≤ (n : ℝ) * x * (1 - x) := by
    have hdiv : (f : ℝ) * (n - f : ℕ) / (q : ℝ) ≤
        (f : ℝ) * (n - f : ℕ) / (n : ℝ) :=
      div_le_div_of_nonneg_left hnum_nonneg hnR (by exact_mod_cast hnq)
    have hid : (f : ℝ) * (n - f : ℕ) / (n : ℝ) =
        (n : ℝ) * x * (1 - x) := by
      dsimp [x]
      rw [Nat.cast_sub (Nat.le_of_lt hflt)]
      field_simp [hnR.ne']
    rw [hid] at hdiv
    exact hdiv
  have hsq_bound : 4 * y ≤
      (Real.log (q : ℝ)) ^ 2 * (n : ℝ) * h := by
    have hm := mul_le_mul_of_nonneg_left hgap hnR.le
    nlinarith only [hm, hy_le]
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = h / (n : ℝ) := by
    dsimp [s]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact div_nonneg hh hnR.le
  have hl_nonneg : 0 ≤ 2 * Real.sqrt y := by positivity
  have hr_nonneg : 0 ≤ Real.log (q : ℝ) * ((n : ℝ) * s) := by positivity
  have hl_sq : (2 * Real.sqrt y) ^ 2 = 4 * y := by
    rw [mul_pow, Real.sq_sqrt hy_nonneg]
    norm_num
  have hr_sq : (Real.log (q : ℝ) * ((n : ℝ) * s)) ^ 2 =
      (Real.log (q : ℝ)) ^ 2 * (n : ℝ) * h := by
    rw [mul_pow, mul_pow, hs_sq]
    field_simp [hnR.ne']
  change Real.exp (2 * Real.sqrt y) ≤ (q : ℝ) ^ ((n : ℝ) * s)
  rw [Real.rpow_def_of_pos hqR]
  apply Real.exp_le_exp.mpr
  apply (sq_le_sq₀ hl_nonneg hr_nonneg).mp
  rw [hl_sq, hr_sq]
  exact hsq_bound

private theorem cs25SecondMomentA_le_entropy_power_proof
    (q n k f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q)
    (hfpos : 0 < f) (hflt : f < n) :
    let h : ℝ := qEntropy q ((f : ℝ) / n) - (f : ℝ) / n
    let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
    cs25SecondMomentA q n k f ≤
      (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) := by
  dsimp
  have hqNat : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqNat
  have hover := cs25OverlapSum_le_exp_two_sqrt q n k f hqNat
  have hexp := cs25_overlap_exp_le_entropy_power_proof q n f hq hnq hfpos hflt
  have hcomp :
      cs25OverlapSum q n k f ≤
        (q : ℝ) ^ ((n : ℝ) *
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) :=
    le_trans hover hexp
  unfold cs25SecondMomentA
  calc
    (q : ℝ) ^ (n - f - k) * cs25OverlapSum q n k f ≤
        (q : ℝ) ^ (n - f - k) *
          (q : ℝ) ^ ((n : ℝ) *
            ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) *
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)) := by
      rw [Real.rpow_add hqR, Real.rpow_natCast]

private theorem cs25_second_momentA_small_of_entropy_rate_proof
    (q n k f : ℕ) (hq : 10 ≤ q) (hnq : n ≤ q) (hn : 0 < n)
    (hlo :
      1 - qEntropy q ((f : ℝ) / n) + 2 / (n : ℝ) +
          ((qEntropy q ((f : ℝ) / n) - (f : ℝ) / n) / (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (k : ℝ) / n)
    (hhi : (k : ℝ) / n ≤ 1 - (f : ℝ) / n - 2 / (n : ℝ)) :
    ((q : ℝ) - 1) * cs25SecondMomentA q n k f <
      (Nat.choose n f : ℝ) := by
  obtain ⟨_, hfpos, hflt, _⟩ :=
    rs_entropy_rate_parameter_facts q n k f hn hlo hhi
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by positivity
  have hqgt1R : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq1R : (1 : ℝ) ≤ q := hqgt1R.le
  have hqm1pos : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr hqgt1R
  let H : ℝ := qEntropy q ((f : ℝ) / n)
  let h : ℝ := H - (f : ℝ) / n
  let s : ℝ := (h / (n : ℝ)) ^ ((1 : ℝ) / 2)
  let D : ℝ :=
    (8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n)) ^ ((1 : ℝ) / 2)
  let B : ℝ := ((q : ℝ) - 1) ^ f * D
  have hxpos : (0 : ℝ) < (f : ℝ) / n := by positivity
  have hxlt : (f : ℝ) / n < 1 :=
    (div_lt_one hnR).2 (by exact_mod_cast hflt)
  have hbasepos :
      0 < 8 * (n : ℝ) * ((f : ℝ) / n) * (1 - (f : ℝ) / n) := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hnR) hxpos) (sub_pos.mpr hxlt)
  have hDpos : 0 < D := by
    dsimp [D]
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_pos.2 hbasepos
  have hBpos : 0 < B := by
    dsimp [B]
    exact mul_pos (pow_pos hqm1pos _) hDpos
  have hA0 := cs25SecondMomentA_le_entropy_power_proof q n k f hq hnq hfpos hflt
  have hA :
      cs25SecondMomentA q n k f ≤
        (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) := by
    simpa only [H, h, s] using hA0
  have hpower0 := cs25_shell_power_bound q n f hq hnq hfpos hflt
  have hpower : ((q : ℝ) - 1) ^ (f + 1) * D < (q : ℝ) ^ (f + 2) := by
    simpa only [D] using hpower0
  have hexp0 := rs_entropy_rate_exponent_slack q n k f hn hlo hhi
  have hexp :
      (((n - f - k : ℕ) : ℝ) + 2 + (n : ℝ) * s) ≤ (n : ℝ) * h := by
    simpa only [H, h, s] using hexp0
  have hid : (n : ℝ) * h + f = (n : ℝ) * H := by
    dsimp [h, H]
    field_simp [hnR.ne']
    ring
  have hexp' :
      (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s + ((f + 2 : ℕ) : ℝ)) ≤
        (n : ℝ) * H := by
    norm_num at hexp ⊢
    nlinarith only [hexp, hid]
  have hshell0 := cs25_entropy_shell_le_choose_proof q n f hq hn hfpos hflt
  have hshell :
      (q : ℝ) ^ ((n : ℝ) * H) ≤ (Nat.choose n f : ℝ) * B := by
    simpa only [H, B, D, mul_assoc] using hshell0
  have hprod :
      (((q : ℝ) - 1) * cs25SecondMomentA q n k f) * B <
        (Nat.choose n f : ℝ) * B := by
    calc
      (((q : ℝ) - 1) * cs25SecondMomentA q n k f) * B =
          cs25SecondMomentA q n k f * (((q : ℝ) - 1) ^ (f + 1) * D) := by
        dsimp [B]
        rw [pow_succ]
        ring
      _ ≤ (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) *
          (((q : ℝ) - 1) ^ (f + 1) * D) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
      _ < (q : ℝ) ^ (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s) *
          (q : ℝ) ^ (f + 2) :=
        mul_lt_mul_of_pos_left hpower
          (Real.rpow_pos_of_pos hqR _)
      _ = (q : ℝ) ^
          (((n - f - k : ℕ) : ℝ) + (n : ℝ) * s + ((f + 2 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hqR]
      _ ≤ (q : ℝ) ^ ((n : ℝ) * H) :=
        Real.rpow_le_rpow_of_exponent_le hq1R hexp'
      _ ≤ (Nat.choose n f : ℝ) * B := hshell
  exact lt_of_mul_lt_mul_right hprod hBpos.le

open scoped BigOperators in
private theorem rsFarWords_card_lt_of_entropy_rate_proof
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (hq : 10 ≤ Fintype.card F)
    (hnq : Fintype.card ι ≤ Fintype.card F)
    (hf : f ≤ Fintype.card ι)
    (hlo :
      1 - qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι) +
          2 / (Fintype.card ι : ℝ) +
          ((qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι) -
              (f : ℝ) / Fintype.card ι) /
            (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2) ≤
        (k : ℝ) / Fintype.card ι)
    (hhi :
      (k : ℝ) / Fintype.card ι ≤
        1 - (f : ℝ) / Fintype.card ι -
          2 / (Fintype.card ι : ℝ)) :
    (rsFarWords domain k f).card <
      Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  let n : ℕ := Fintype.card ι
  let q : ℕ := Fintype.card F
  let N : ℕ := Nat.choose n f
  let A : ℝ := cs25SecondMomentA q n k f
  let B : Finset (ι → F) := rsFarWords domain k f
  have hn : 0 < n := by simpa only [n] using (Fintype.card_pos : 0 < Fintype.card ι)
  have hqpos : 0 < q := by simpa only [q] using (Fintype.card_pos : 0 < Fintype.card F)
  have hq1 : 1 < q := by simpa only [q] using (show 1 < Fintype.card F by omega)
  obtain ⟨hmargin, hfpos, hflt, hd2, hdle⟩ :=
    rs_entropy_rate_full_parameter_facts_proof q n k f
      (by simpa only [q] using hq) hn
      (by simpa only [q, n] using hlo) (by simpa only [n] using hhi)
  have hkf : k + f ≤ n := by omega
  have hweighted :
      (B.card : ℝ) * ((N : ℝ) + A) ≤ (q : ℝ) ^ n * A := by
    simpa only [B, N, A, q, n] using
      rsFarWords_weighted_card_bound_proof domain k f
        (by simpa only [q] using hqpos) (by simpa only [n] using hkf)
        (by simpa only [q, n] using hdle)
  have hA : 0 ≤ A := by
    simpa only [A] using cs25SecondMomentA_nonneg_proof q n k f
  have hN : 0 < N := by
    dsimp [N]
    exact Nat.choose_pos (by simpa only [n] using hf)
  have hAsm : ((q : ℝ) - 1) * A < (N : ℝ) := by
    simpa only [q, n, N, A] using
      cs25_second_momentA_small_of_entropy_rate_proof q n k f
        (by simpa only [q] using hq) (by simpa only [q, n] using hnq) hn
        (by simpa only [q, n] using hlo) (by simpa only [n] using hhi)
  have hfinal := nat_card_lt_pow_pred_of_weighted_bound
    q n N B.card A hq1 hn hN hA hAsm hweighted
  simpa only [q, n, B] using hfinal

open scoped ProbabilityTheory in
open scoped BigOperators in
private theorem rs_epsCa_eq_one_of_entropy_rate_impl
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k f : ℕ)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hn_le_q : Fintype.card ι ≤ Fintype.card F)
    (_hf_le : f ≤ Fintype.card ι)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
            + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
                  - (f : ℝ) / Fintype.card ι)
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi :
        (k : ℝ) / Fintype.card ι ≤
          1 - (f : ℝ) / Fintype.card ι - 2 / (Fintype.card ι : ℝ)) :
    let δ : NNReal := (f : NNReal) / Fintype.card ι
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ = 1 := by
  classical
  dsimp
  let C : Set (ι → F) := ReedSolomon.code domain k
  let v : ι → F := rsBoundaryWord domain k
  let δ : NNReal := (f : NNReal) / Fintype.card ι
  change epsCa (F := F) (A := F) C δ δ = 1
  have hbad :
      (Finset.univ.filter (fun w : ι → F =>
        ¬ Code.distFromCode w C ≤ f)).card <
        Fintype.card F ^ (Fintype.card ι - 1) := by
    dsimp [C]
    simpa [rsFarWords] using
      rsFarWords_card_lt_of_entropy_rate_proof domain k f
        _hq_ge _hn_le_q _hf_le _hδ_lo _hδ_hi
  obtain ⟨u0, hu0⟩ :=
    exists_base_all_translates_close_of_bad_count C v f hbad
  let u : Code.WordStack F (Fin 2) ι :=
    fun j => if j = 0 then u0 else v
  have hclose : ∀ γ : F,
      Code.relDistFromCode (u 0 + γ • u 1) C ≤ (δ : ENNReal) := by
    intro γ
    have habs := hu0 γ
    have hrel :=
      (Code.distFromCode_le_iff_relDistFromCode_le (u0 + γ • v) f).mp habs
    simpa [u, δ] using hrel
  have hmargin : k + f + 2 ≤ Fintype.card ι :=
    rs_entropy_rate_nat_margin k f _hδ_hi
  have hvfar : Code.distFromCode v C > f := by
    simpa [v, C] using rsBoundaryWord_far domain k f hmargin
  have hrelfar :
      ¬ Code.relDistFromCode (u 1) C ≤ (δ : ENNReal) := by
    intro hrel
    have hrel' : Code.relDistFromCode v C ≤ (δ : ENNReal) := by
      simpa [u] using hrel
    have habs : Code.distFromCode v C ≤ f :=
      (Code.distFromCode_le_iff_relDistFromCode_le v f).mpr (by
        simpa [δ] using hrel')
    exact (not_le_of_gt hvfar) habs
  have hjoint : ¬ Code.jointProximity C (u := u) δ :=
    not_jointProximity_of_second_row_far C u δ hrelfar
  exact epsCa_eq_one_of_all_folds_close_not_joint C δ u hjoint hclose

omit [DecidableEq ι] in
/-- Complete CA breakdown for a Reed--Solomon code whose rate lies in the entropy band

  `1 - H_q(f/n) + 2/n + √((H_q(f/n) - f/n)/n) ≤ ρ ≤ 1 - f/n - 2/n`

The radius is the integer grid point `f/n`; the entropy hypothesis is not extended to arbitrary
real radii. -/
theorem rs_epsCa_eq_one_of_entropy_rate
    (domain : ι ↪ F) (k f : ℕ)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hn_le_q : Fintype.card ι ≤ Fintype.card F)
    (_hf_le : f ≤ Fintype.card ι)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
            + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) ((f : ℝ) / Fintype.card ι)
                  - (f : ℝ) / Fintype.card ι)
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi :
        (k : ℝ) / Fintype.card ι ≤
          1 - (f : ℝ) / Fintype.card ι - 2 / (Fintype.card ι : ℝ)) :
    let δ : ℝ≥0 := (f : ℝ≥0) / Fintype.card ι
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ = 1 := by
  classical
  exact rs_epsCa_eq_one_of_entropy_rate_impl domain k f
    _hq_ge _hn_le_q _hf_le _hδ_lo _hδ_hi

end ReedSolomon

end CodingTheory

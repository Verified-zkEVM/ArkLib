/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Asymptotic Reed--Solomon list-size lower bound

For every rate `ρ ∈ (0,1)` and exponent `c`, this module constructs arbitrarily large smooth
Reed--Solomon codes whose list size is at least `n^c` within `O(1/log n)` of minimum distance.

## Main declaration

- `exists_rs_asymptotic_Lambda_lower_bound` gives the family statement over `Code.Lambda`,
  with an explicit uniform constant for the `O(1/log₂ n)` loss. It is proved from
  `choose_le_Lambda_rs_vanilla_of_smooth`; existence of arbitrarily large smooth domains is
  carried by the `supply` hypothesis.

## Proof structure

The construction uses `h = 2^b`, `d = 2^a`, and `n = 2^{a+b}`, so `log₂ n = a+b` exactly.
Its main components are:

- `choose_ge_div_pow`, the classical lower bound `(s/t)^t ≤ C(s,t)`;
- `core_ineq`, the entropy-scale comparison between `n^{c+1}` and `(h/khat)^khat`;
- `exists_asymptotic_params`, which chooses `a`, `b`, `k`, and `khat` and proves the rate,
  radius-loss, and binomial bounds.

## Formulation

- The radius loss has only the source-supported upper bound `slack ≤ Kc/log₂ n`; no lower
  `Θ(1/log n)` bound is claimed.

- The rate is represented by the satisfiable rounding band `ρ < k/n ≤ ρ+1/n`.

- The `supply` hypothesis isolates finite-field existence; all remaining steps are proved in-tree.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- [KKH26] Krachun, Kazanin, Haböck. *Failure of proximity gaps close to capacity*. ePrint 2026/782.
-/

set_option linter.unusedVariables false

open Polynomial Finset Code ProximityGap Real Filter Topology
open scoped NNReal BigOperators

namespace CodingTheory.AdditiveSetListDecoding

/-! ## Counting helpers (not in mathlib) -/

/-- The classical binomial lower bound `(s/t)^t ≤ C(s,t)` for `1 ≤ t ≤ s`, proved by
comparing the factors in `C(s,t) = ∏_{i<t} (s-i)/(t-i)`. -/
theorem choose_ge_div_pow (s t : ℕ) (ht : 1 ≤ t) (hts : t ≤ s) :
    ((s : ℝ) / t) ^ t ≤ (s.choose t : ℝ) := by
  have hnat : ∏ i ∈ range t, (t - i) = t.factorial := by
    rw [Nat.factorial_eq_prod_range_add_one, ← Finset.prod_range_reflect (fun i => i + 1) t]
    apply Finset.prod_congr rfl; intro i hi; rw [mem_range] at hi; omega
  have hfact : (t.factorial : ℝ) = ∏ i ∈ range t, ((t - i : ℕ) : ℝ) := by
    rw [← hnat]; push_cast; rfl
  have hdesc : (s.descFactorial t : ℝ) = ∏ i ∈ range t, ((s - i : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range]; push_cast; rfl
  have hchoose : (s.choose t : ℝ) = (s.descFactorial t : ℝ) / (t.factorial : ℝ) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose s t
    have hfac : (t.factorial : ℝ) ≠ 0 := by exact_mod_cast t.factorial_ne_zero
    rw [eq_div_iff hfac, mul_comm]; exact_mod_cast h.symm
  have hprod : (s.choose t : ℝ) = ∏ i ∈ range t, (((s - i : ℕ) : ℝ) / ((t - i : ℕ) : ℝ)) := by
    rw [hchoose, hdesc, hfact, ← Finset.prod_div_distrib]
  rw [hprod, show ((s : ℝ) / t) ^ t = ∏ _i ∈ range t, ((s : ℝ) / t) from by
    rw [Finset.prod_const, card_range]]
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i hi
    rw [mem_range] at hi
    have his : i < s := lt_of_lt_of_le hi hts
    rw [Nat.cast_sub hi.le, Nat.cast_sub his.le]
    have hti : (i : ℝ) < t := by exact_mod_cast hi
    have hts' : (t : ℝ) ≤ s := by exact_mod_cast hts
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    rw [div_le_div_iff₀ ht0 (by linarith)]
    nlinarith [Nat.cast_nonneg (α := ℝ) i, hts']

/-- Analytic core: `(2^K)^{cp} ≤ (2^b / khat)^{khat}` when `khat ≈ ρ·2^b` and
`cp·K·log 2 ≤ ρ·log(1/ρ)·2^b - 2`. -/
theorem core_ineq (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (cp : ℕ) (hcp : 1 ≤ cp)
    (b K khat : ℕ) (hkhat1 : 1 ≤ khat)
    (hkhat_lo : ρ * 2 ^ b < (khat : ℝ)) (hkhat_hi : (khat : ℝ) ≤ ρ * 2 ^ b + 2)
    (hkhat_lt : (khat : ℝ) < 2 ^ b) (hbig : (2 : ℝ) ≤ (1 - ρ) * 2 ^ b)
    (hK : (cp : ℝ) * K * Real.log 2 ≤ ρ * Real.log (1 / ρ) * 2 ^ b - 2) :
    (((2 : ℝ) ^ K) ^ cp) ≤ ((2 ^ b : ℝ) / khat) ^ khat := by
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  have hkhatR : (0 : ℝ) < khat := by exact_mod_cast hkhat1
  have hbase : (1 : ℝ) < (2 ^ b : ℝ) / khat := by rw [lt_div_iff₀ hkhatR]; linarith
  have hrhs_pos : (0 : ℝ) < ((2 ^ b : ℝ) / khat) ^ khat := by positivity
  have hlhs_pos : (0 : ℝ) < (((2 : ℝ) ^ K) ^ cp) := by positivity
  rw [← Real.log_le_log_iff hlhs_pos hrhs_pos]
  rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_div (by positivity) (ne_of_gt hkhatR)]
  rw [show Real.log ((2 : ℝ) ^ b) = (b : ℝ) * Real.log 2 from Real.log_pow 2 b]
  have key : ρ * Real.log (1 / ρ) * 2 ^ b - 2
      ≤ (khat : ℝ) * ((b : ℝ) * Real.log 2 - Real.log khat) := by
    have hlogpos : (0 : ℝ) ≤ Real.log ((2 ^ b : ℝ) / (ρ * 2 ^ b + 2)) := by
      apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
    have hstep1 : ρ * 2 ^ b * Real.log ((2 ^ b : ℝ) / (ρ * 2 ^ b + 2))
        ≤ (khat : ℝ) * ((b : ℝ) * Real.log 2 - Real.log khat) := by
      have heq : (b : ℝ) * Real.log 2 - Real.log khat = Real.log ((2 ^ b : ℝ) / khat) := by
        rw [Real.log_div (by positivity) (ne_of_gt hkhatR), Real.log_pow]
      rw [heq]
      apply mul_le_mul (le_of_lt hkhat_lo)
      · apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_left (by positivity) hkhatR; linarith
      · exact hlogpos
      · exact le_of_lt hkhatR
    have hlog1 : ρ * 2 ^ b * Real.log ((2 ^ b : ℝ) / (ρ * 2 ^ b + 2))
        ≥ ρ * Real.log (1 / ρ) * 2 ^ b - 2 := by
      have hx : (0 : ℝ) < 1 + 2 / (ρ * 2 ^ b) := by positivity
      have hlogle : Real.log (1 + 2 / (ρ * 2 ^ b)) ≤ 2 / (ρ * 2 ^ b) := by
        have := Real.log_le_sub_one_of_pos hx; linarith
      have hsplit : Real.log ((2 ^ b : ℝ) / (ρ * 2 ^ b + 2))
          = Real.log (1 / ρ) - Real.log (1 + 2 / (ρ * 2 ^ b)) := by
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_div (by norm_num) (ne_of_gt hρ0)]
        rw [Real.log_one,
          show (1 : ℝ) + 2 / (ρ * 2 ^ b) = (ρ * 2 ^ b + 2) / (ρ * 2 ^ b) from by field_simp]
        rw [Real.log_div (by positivity) (by positivity),
          Real.log_mul (ne_of_gt hρ0) (by positivity), Real.log_pow]
        ring
      rw [hsplit]
      have hρ2b : (0 : ℝ) < ρ * 2 ^ b := by positivity
      rw [show ρ * 2 ^ b * (Real.log (1 / ρ) - Real.log (1 + 2 / (ρ * 2 ^ b)))
           = ρ * Real.log (1 / ρ) * 2 ^ b - ρ * 2 ^ b * Real.log (1 + 2 / (ρ * 2 ^ b)) from by
        ring]
      have hbound : ρ * 2 ^ b * Real.log (1 + 2 / (ρ * 2 ^ b)) ≤ 2 :=
        calc ρ * 2 ^ b * Real.log (1 + 2 / (ρ * 2 ^ b)) ≤ ρ * 2 ^ b * (2 / (ρ * 2 ^ b)) :=
              mul_le_mul_of_nonneg_left hlogle (le_of_lt hρ2b)
          _ = 2 := by field_simp
      linarith
    linarith
  linarith

/-! ## Parameter selection -/

set_option maxHeartbeats 1600000 in
-- Long `Filter.Eventually`/`nlinarith`/`Real.log` chain over many hypotheses; raised limit.
/-- For every rate `ρ ∈ (0,1)` and `c ∈ ℕ`, there is a constant `Kc > 0` and a threshold
`b₀` such that
for every `b ≥ b₀` the parameters `a`, `k = ⌈ρ·2^{a+b}⌉`, `khat = ⌈k/2^a⌉` satisfy the
hypotheses of `choose_le_Lambda_rs_vanilla_of_smooth` at `d = 2^a`, `h = 2^b`,
`n = 2^{a+b}`, together with the rate
band, the `O(1/log n)` slack bound, and the list target `n^c ≤ C(2^b, khat)`. -/
theorem exists_asymptotic_params (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : ℕ) :
    ∃ (Kc : ℝ), 0 < Kc ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      ∃ a k khat : ℕ,
        1 ≤ a + b ∧ 1 ≤ khat ∧ khat < 2 ^ b ∧
        (khat - 1) * 2 ^ a < k ∧ k ≤ khat * 2 ^ a ∧
        ρ * 2 ^ (a + b) < (k : ℝ) ∧ (k : ℝ) ≤ ρ * 2 ^ (a + b) + 1 ∧
        ((↑(khat * 2 ^ a - k + 1) : ℝ) / 2 ^ (a + b) ≤ Kc / ((a + b : ℕ) : ℝ)) ∧
        ((2 : ℝ) ^ (a + b)) ^ c ≤ (Nat.choose (2 ^ b) khat : ℝ) := by
  obtain ⟨cp, hcpdef⟩ : ∃ cp : ℕ, cp = c + 1 := ⟨_, rfl⟩
  have hcp1 : 1 ≤ cp := by omega
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcpR : (0 : ℝ) < (cp : ℝ) := by exact_mod_cast hcp1
  obtain ⟨A₀, hA0def⟩ : ∃ A₀ : ℝ, A₀ = ρ * Real.log (1 / ρ) := ⟨_, rfl⟩
  have hA0 : 0 < A₀ := by
    rw [hA0def]; apply mul_pos hρ0; apply Real.log_pos; rw [lt_div_iff₀ hρ0]; linarith
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ, Kc = A₀ / (2 * (cp : ℝ) * Real.log 2) := ⟨_, rfl⟩
  have hKc : 0 < Kc := by rw [hKcdef]; exact div_pos hA0 (by positivity)
  refine ⟨Kc, hKc, ?_⟩
  -- eventually facts.
  have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / (2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have ev1 : ∀ᶠ b : ℕ in atTop, (b : ℝ) ≤ Kc * 2 ^ b := by
    have := hlim.eventually (Iio_mem_nhds hKc)
    filter_upwards [this] with b hb
    simp only [pow_one] at hb
    have h2 : (0 : ℝ) < 2 ^ b := by positivity
    rw [div_lt_iff₀ h2] at hb; nlinarith [hb]
  have hpowlim : Filter.Tendsto (fun b : ℕ => (2 : ℝ) ^ b) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have ev2 : ∀ᶠ b : ℕ in atTop, (2 : ℝ) ≤ (1 - ρ) * 2 ^ b :=
    (hpowlim.const_mul_atTop (by linarith)).eventually_ge_atTop 2
  have ev3 : ∀ᶠ b : ℕ in atTop, (4 : ℝ) ≤ A₀ * 2 ^ b :=
    (hpowlim.const_mul_atTop hA0).eventually_ge_atTop 4
  have ev4 : ∀ᶠ b : ℕ in atTop, 1 ≤ b := eventually_atTop.mpr ⟨1, fun b hb => hb⟩
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨b₀, fun b hbge => ?_⟩
  obtain ⟨P1, P2, P3, P4⟩ := hb₀ b hbge
  -- opaque definitions (avoid `set`-let whnf blowups).
  obtain ⟨Kf, hKfdef⟩ : ∃ Kf : ℕ, Kf = ⌊Kc * (2 : ℝ) ^ b⌋₊ := ⟨_, rfl⟩
  have hbKf : b ≤ Kf := by rw [hKfdef]; exact Nat.le_floor P1
  obtain ⟨a, hadef⟩ : ∃ a : ℕ, a = Kf - b := ⟨_, rfl⟩
  have hab : a + b = Kf := by rw [hadef]; exact Nat.sub_add_cancel hbKf
  have h2bpos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌊ρ * (2 : ℝ) ^ (a + b)⌋₊ + 1 := ⟨_, rfl⟩
  obtain ⟨d, hddef⟩ : ∃ d : ℕ, d = 2 ^ a := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hddef]; positivity
  obtain ⟨khat, hkhatdef⟩ : ∃ khat : ℕ, khat = (k + d - 1) / d := ⟨_, rfl⟩
  -- ceil-division facts.
  have hk1 : 1 ≤ k := by rw [hkdef]; omega
  have hcomm : khat * d = d * khat := Nat.mul_comm khat d
  have heucl : d * khat + (k + d - 1) % d = k + d - 1 := by
    rw [hkhatdef]; exact Nat.div_add_mod (k + d - 1) d
  have hmod : (k + d - 1) % d < d := Nat.mod_lt _ hd0
  have hq1 : 1 ≤ khat := by rw [hkhatdef]; apply (Nat.one_le_div_iff hd0).mpr; omega
  have hsub : (khat - 1) * d = khat * d - d := by rw [Nat.sub_mul, Nat.one_mul]
  have N1 : k ≤ khat * d := by omega
  have N2 : (khat - 1) * d < k := by omega
  -- real bookkeeping.
  have hnpow : (2 : ℝ) ^ (a + b) = (2 : ℝ) ^ a * 2 ^ b := by rw [pow_add]
  have hdR : (d : ℝ) = (2 : ℝ) ^ a := by rw [hddef]; push_cast; rfl
  have h2apos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hρnn : (0 : ℝ) ≤ ρ * (2 : ℝ) ^ (a + b) := by positivity
  have hrate_lo : ρ * (2 : ℝ) ^ (a + b) < (k : ℝ) := by
    rw [hkdef]; push_cast; have := Nat.lt_floor_add_one (ρ * (2 : ℝ) ^ (a + b)); linarith
  have hrate_hi : (k : ℝ) ≤ ρ * (2 : ℝ) ^ (a + b) + 1 := by
    rw [hkdef]; push_cast; have := Nat.floor_le hρnn; linarith
  have hN1R : (k : ℝ) ≤ (khat : ℝ) * d := by exact_mod_cast N1
  have hN2R : ((khat : ℝ) - 1) * d < (k : ℝ) := by
    have : (((khat - 1) * d : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast N2
    rwa [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_one] at this
  have hRlo : ρ * 2 ^ b < (khat : ℝ) := by
    have h1 : ρ * (2 : ℝ) ^ a * 2 ^ b < (khat : ℝ) * d := by
      rw [hnpow] at hrate_lo; nlinarith [hrate_lo, hN1R]
    rw [hdR] at h1; nlinarith [h1, h2apos]
  have hRhi : (khat : ℝ) < ρ * 2 ^ b + 2 := by
    have h1 : ((khat : ℝ) - 1) * d < ρ * (2 : ℝ) ^ a * 2 ^ b + 1 := by
      rw [hnpow] at hrate_hi; nlinarith [hN2R, hrate_hi]
    rw [hdR] at h1
    have h2a1 : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
    nlinarith [h1, h2apos, h2a1]
  have hF2 : (khat : ℝ) < 2 ^ b := by nlinarith [hRhi, P2]
  have hF2n : khat < 2 ^ b := by exact_mod_cast hF2
  have N1' : k ≤ khat * 2 ^ a := by rw [← hddef]; exact N1
  have N2' : (khat - 1) * 2 ^ a < k := by rw [← hddef]; exact N2
  -- list bound + slack (discharge the `cor:kikh-vanilla` hypotheses' definitions first).
  have hbig : (2 : ℝ) ≤ (1 - ρ) * 2 ^ b := P2
  have hKf_le : (Kf : ℝ) ≤ Kc * 2 ^ b := by rw [hKfdef]; exact Nat.floor_le (by positivity)
  have hnum : khat * d - k + 1 ≤ d := by omega
  have hnumn : khat * 2 ^ a - k + 1 ≤ 2 ^ a := by rw [← hddef]; exact hnum
  have hle1ab : 1 ≤ a + b := by omega
  have hK : (cp : ℝ) * ((a + b : ℕ) : ℝ) * Real.log 2 ≤ ρ * Real.log (1 / ρ) * 2 ^ b - 2 := by
    have hKfeq : ((a + b : ℕ) : ℝ) = (Kf : ℝ) := by exact_mod_cast hab
    rw [hKfeq]
    have h1 : (cp : ℝ) * Kf * Real.log 2 ≤ (cp : ℝ) * (Kc * 2 ^ b) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hL2)
      apply mul_le_mul_of_nonneg_left hKf_le (le_of_lt hcpR)
    have hne : (2 * (cp : ℝ) * Real.log 2) ≠ 0 := by positivity
    have e1 : Kc * (2 * (cp : ℝ) * Real.log 2) = A₀ := by
      rw [hKcdef]; exact div_mul_cancel₀ A₀ hne
    have h2 : (cp : ℝ) * (Kc * 2 ^ b) * Real.log 2 = A₀ * 2 ^ b / 2 := by
      have hh : A₀ * 2 ^ b / 2 = (Kc * (2 * (cp : ℝ) * Real.log 2)) * 2 ^ b / 2 := by rw [e1]
      rw [hh]; ring
    rw [h2] at h1
    have hP3 : (4 : ℝ) ≤ A₀ * 2 ^ b := P3
    have hAe : A₀ = ρ * Real.log (1 / ρ) := hA0def
    rw [hAe] at h1 hP3; linarith [h1, hP3]
  have hcore := core_ineq ρ hρ0 hρ1 cp hcp1 b (a + b) khat hq1 hRlo (le_of_lt hRhi) hF2 hbig hK
  have hchoose : (((2 : ℝ) ^ b) / khat) ^ khat ≤ (Nat.choose (2 ^ b) khat : ℝ) := by
    have h := choose_ge_div_pow (2 ^ b) khat hq1 hF2n.le
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have hlist_cp : ((2 : ℝ) ^ (a + b)) ^ cp ≤ (Nat.choose (2 ^ b) khat : ℝ) :=
    le_trans hcore hchoose
  have h2Kf1 : (1 : ℝ) ≤ (2 : ℝ) ^ (a + b) := one_le_pow₀ (by norm_num)
  have hcle : c ≤ cp := by omega
  have hlist : ((2 : ℝ) ^ (a + b)) ^ c ≤ (Nat.choose (2 ^ b) khat : ℝ) :=
    calc ((2 : ℝ) ^ (a + b)) ^ c ≤ ((2 : ℝ) ^ (a + b)) ^ cp := pow_le_pow_right₀ h2Kf1 hcle
      _ ≤ _ := hlist_cp
  have hslack : ((↑(khat * 2 ^ a - k + 1) : ℝ) / 2 ^ (a + b)) ≤ Kc / ((a + b : ℕ) : ℝ) := by
    have hnumR : ((khat * 2 ^ a - k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := by
      calc ((khat * 2 ^ a - k + 1 : ℕ) : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hnumn
        _ = (2 : ℝ) ^ a := by push_cast; rfl
    have hnpos : (0 : ℝ) < (2 : ℝ) ^ (a + b) := by positivity
    have hstep : (↑(khat * 2 ^ a - k + 1) : ℝ) / 2 ^ (a + b) ≤ (2 : ℝ) ^ a / 2 ^ (a + b) := by
      gcongr
    have hexp : (2 : ℝ) ^ a / 2 ^ (a + b) = 1 / 2 ^ b := by
      rw [hnpow, div_mul_eq_div_div, div_self (ne_of_gt h2apos)]
    have hKfpos : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast hle1ab
    have hfinal : (1 : ℝ) / 2 ^ b ≤ Kc / ((a + b : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ h2bpos hKfpos, one_mul]
      have hcastab : ((a + b : ℕ) : ℝ) = (Kf : ℝ) := by exact_mod_cast hab
      rw [hcastab]; nlinarith [hKf_le]
    calc (↑(khat * 2 ^ a - k + 1) : ℝ) / 2 ^ (a + b) ≤ (2 : ℝ) ^ a / 2 ^ (a + b) := hstep
      _ = 1 / 2 ^ b := hexp
      _ ≤ Kc / ((a + b : ℕ) : ℝ) := hfinal
  exact ⟨a, k, khat, hle1ab, hq1, hF2n, N2', N1', hrate_lo, hrate_hi, hslack, hlist⟩

/-! ## Main theorem -/

set_option maxHeartbeats 1600000 in
-- Large existential goal with many instance-carrying witnesses; raised limit.
/-- For every rate `ρ ∈ (0,1)` and `c ∈ ℕ`, given arbitrarily large smooth Reed--Solomon
evaluation domains, there is a constant `Kc > 0` such
that for every `N` there is a smooth RS code `C = RS[F, L, k]` with block length `n = |L| ≥ N`,
rate within `1/n` of `ρ`, and a radius loss `slack ≤ Kc / log₂ n` for which

  `n^c ≤ |Λ(C, δ_min(C) − slack)|`.

This is derived from `choose_le_Lambda_rs_vanilla_of_smooth`. -/
theorem exists_rs_asymptotic_Lambda_lower_bound
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : ℕ)
    (supply : ∀ K : ℕ, ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
        (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
        (domain : ιC ↪ FC) (_ : ReedSolomon.Smooth domain), Fintype.card ιC = 2 ^ K) :
    ∃ Kc : ℝ, 0 < Kc ∧
    ∀ N : ℕ,
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (_ : ReedSolomon.Smooth domain) (k : ℕ) (slack : ℝ),
      N ≤ Fintype.card ιC ∧
      ρ < (k : ℝ) / Fintype.card ιC ∧
      (k : ℝ) / Fintype.card ιC ≤ ρ + 1 / Fintype.card ιC ∧
      0 ≤ slack ∧
      slack ≤ Kc / Real.logb 2 (Fintype.card ιC) ∧
      ((Fintype.card ιC ^ c : ℕ) : ℕ∞) ≤
        Lambda (↑(ReedSolomon.code domain k) : Set (ιC → FC))
          (((δᵣ (↑(ReedSolomon.code domain k) : Set (ιC → FC)) : ℚ≥0) : ℝ) - slack) := by
  obtain ⟨Kc, hKc, b₀, hparams⟩ := exists_asymptotic_params ρ hρ0 hρ1 c
  refine ⟨Kc, hKc, fun N => ?_⟩
  -- pick `b` large enough for both the asymptotics and `n ≥ N`.
  set b := max b₀ N with hb
  obtain ⟨a, k, khat, hle1ab, hq1, hkh, hk1, hk2, hrlo, hrhi, hslack, hlist⟩ :=
    hparams b (le_max_left _ _)
  obtain ⟨ιC, fι, neι, decι, FC, fieldF, finF, decF, domain, smoothD, hcard⟩ := supply (a + b)
  have hcard_real : (Fintype.card ιC : ℝ) = (2 : ℝ) ^ (a + b) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcard; simpa using h
  have hcardpos : (0 : ℝ) < (Fintype.card ιC : ℝ) := by rw [hcard_real]; positivity
  -- `cor:kikh-vanilla` at `d = 2^a`, `h = 2^b`.
  have hn : Fintype.card ιC = 2 ^ a * 2 ^ b := hcard.trans (pow_add 2 a b)
  have hcor := choose_le_Lambda_rs_vanilla_of_smooth domain hn hq1 hkh hk1 hk2
  refine ⟨ιC, inferInstance, inferInstance, inferInstance, FC, inferInstance, inferInstance,
    inferInstance, domain, inferInstance, k,
    ((khat * 2 ^ a - k + 1 : ℕ) : ℝ) / (Fintype.card ιC : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `N ≤ n = 2^{a+b}`.
    have hbN : N ≤ b := le_max_right _ _
    have hlt : a + b < 2 ^ (a + b) := Nat.lt_two_pow_self
    omega
  · -- rate lower: `ρ < k / n`.
    rw [hcard_real, lt_div_iff₀ (by positivity)]; linarith [hrlo]
  · -- rate upper: `k / n ≤ ρ + 1/n`.
    rw [hcard_real, div_le_iff₀ (by positivity), add_mul, one_div,
      inv_mul_cancel₀ (by positivity)]
    linarith [hrhi]
  · -- `0 ≤ slack`.
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · -- `slack ≤ Kc / log₂ n`.
    have hlogb : Real.logb 2 (Fintype.card ιC : ℝ) = ((a + b : ℕ) : ℝ) := by
      rw [hcard_real, Real.logb_pow, Real.logb_self_eq_one] <;> norm_num
    rw [hlogb, hcard_real]; exact hslack
  · -- list bound: `n^c ≤ Λ(C, δ_min − slack)`.
    have hlistN : Fintype.card ιC ^ c ≤ (2 ^ b).choose khat := by
      have h := hlist; rw [← hcard_real] at h; exact_mod_cast h
    have hstep : ((Fintype.card ιC ^ c : ℕ) : ℕ∞) ≤ ((2 ^ b).choose khat : ℕ∞) := by
      exact_mod_cast hlistN
    exact le_trans hstep hcor

end CodingTheory.AdditiveSetListDecoding

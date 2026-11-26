/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA.CS25
public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26Asymptotic

/-!
# CA lower bounds near capacity over prime fields

This module proves the [KKH26, Proposition 3] lower bound on `epsCa` close to capacity for every
large `K` and every prime `p ≡ 1 (mod 2^K)` with `p ≥ n^{c+2}`, `n = 2^K`. The list bound
`choose_le_Lambda_rs_vanilla_of_smooth` is turned into a CA bound by `le_rs_epsCa_of_le_Lambda`,
the contrapositive of [CS25, Theorem 2].

The source's family statement, with `|F| = Θ(n^β)`, also needs infinitely many primes
`p ≡ 1 (mod 2^K)` in `[n^β, 2n^β]`. That is a prime number theorem in arithmetic progressions to
the moduli `2^K`. ArkLib does not prove it, since no proof system in ArkLib needs it:
`exists_rs_epsCa_large_near_capacity_of_primes` takes it as the hypothesis
`NearCapacityPrimeSupply c`.

## Main definitions

- `NearCapacityPrimeSupply c` — for one `β > max(c+2, 12/5)` and infinitely many `K`, there is a
  prime `p ≡ 1 (mod 2^K)` in `[n^β, 2n^β]`, `n = 2^K`.
- `NearCapacityCaLowerBound c ρ` — the family statement: arbitrarily long smooth Reed--Solomon
  codes over prime fields of size `Θ(n^β)`, with rate within `O(1/log₂ n)` of `ρ`, whose CA error
  at distance `1 - ρ - Θ(1/log₂ n)` is at least `n^c / |F|`.

## Main results

- `rs_epsCa_large_of_smooth` — [KKH26, Proposition 3] via [CS25, Theorem 2]: over any finite
  field with a smooth domain of size `n = 2^a · 2^b`, `ε_ca(RS[F, domain, k], 1 - k̂/2^b) ≥ T / |F|`
  with `k = (k̂-1)·2^a` whenever `C(2^b, k̂) ≥ 2T + 1` and `|F| ≥ n + 2kT`.
- `exists_rs_epsCa_large_near_capacity_of_prime` — the per-prime statement, also
  [KKH26, Proposition 3] via [CS25, Theorem 2].
- `exists_rs_epsCa_large_near_capacity_of_primes` — `NearCapacityCaLowerBound c ρ` from
  `NearCapacityPrimeSupply c`.

## References

* [Krachun, D., Kazanin, S., and Haböck, U., *Failure of Proximity Gaps Close to Capacity*][KKH26]
* [Crites, E. and Stewart, A., *On Reed--Solomon Proximity Gaps Conjectures*][CS25]
-/
@[expose] public section

namespace CodingTheory

open scoped NNReal
open Code CoreDefinitions ProximityGap AdditiveSetListDecoding

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]

omit [DecidableEq ι] in
/-- For a smooth domain of size `2^a · 2^b` with `1 ≤ a` and `2 ≤ k̂ ≤ 2^b`, the code
`RS[F, domain, k]`, `k = (k̂-1)·2^a`, has `ε_ca(1 - k̂/2^b) ≥ T / |F|` whenever
`C(2^b, k̂) ≥ 2T + 1` and `|F| ≥ n + 2kT`. -/
theorem rs_epsCa_large_of_smooth (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    {a b khat : ℕ} (hn : Fintype.card ι = 2 ^ a * 2 ^ b) (ha : 1 ≤ a) (hk2 : 2 ≤ khat)
    (hkh : khat ≤ 2 ^ b) (T : ℝ) (hL : 2 * T + 1 ≤ ((2 ^ b).choose khat : ℝ))
    (hq : (Fintype.card ι : ℝ) + 2 * ((khat - 1) * 2 ^ a : ℕ) * T ≤ Fintype.card F) :
    ENNReal.ofReal (T / Fintype.card F) ≤
      epsCa (F := F) (A := F) (ReedSolomon.code domain ((khat - 1) * 2 ^ a) : Set (ι → F))
        ((((2 ^ b - khat) * 2 ^ a : ℕ) : ℝ≥0) / Fintype.card ι)
        ((((2 ^ b - khat) * 2 ^ a : ℕ) : ℝ≥0) / Fintype.card ι) := by
  have hd : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hh : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hkd : (khat - 1) * 2 ^ a + 2 ^ a = khat * 2 ^ a := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hhd : (2 ^ b - 1) * 2 ^ a + 2 ^ a = 2 ^ a * 2 ^ b := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hh, Nat.mul_comm]
  have hfk : (2 ^ b - khat) * 2 ^ a + (khat - 1) * 2 ^ a = (2 ^ b - 1) * 2 ^ a := by
    rw [← Nat.add_mul]; congr 1; omega
  refine le_rs_epsCa_of_le_Lambda domain _ _ T (Nat.mul_pos (by omega) (by omega)) (by omega)
    hq hL ?_
  have hlist := choose_le_Lambda_rs_vanilla_of_smooth (F := F) domain
    (khat := khat) (k := (khat - 1) * 2 ^ a + 1) hn (by omega) (by omega)
  rw [minRelDist_sub_eq domain hn (by omega) hkh (by omega)] at hlist
  convert hlist using 2
  rw [hn]
  push_cast [Nat.cast_sub hkh]
  field_simp

end ReedSolomon

section PrimeField

private theorem exists_near_capacity_params (c : ℝ≥0) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ K₀ : ℕ, 2 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      ∃ a b khat : ℕ, a + b = K ∧ 1 ≤ a ∧ 2 ≤ khat ∧ khat ≤ 2 ^ b ∧
        ρ * 2 ^ b < (khat : ℝ) - 1 ∧ (khat : ℝ) - 1 ≤ ρ * 2 ^ b + 1 ∧
        κ / K ≤ 1 / 2 ^ b ∧ 1 / 2 ^ b ≤ 2 * κ / K ∧
        2 * ((2 : ℝ) ^ K) ^ (c : ℝ) + 1 ≤ ((2 ^ b).choose khat : ℝ) := by
  obtain ⟨cp, hcp⟩ : ∃ cp : ℕ, cp = ⌈(c : ℝ)⌉₊ + 1 := ⟨_, rfl⟩
  have hL2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA : 0 < ρ * Real.log (1 / ρ) :=
    mul_pos hρ0 (Real.log_pos ((one_lt_div hρ0).mpr (by linarith)))
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = ρ * Real.log (1 / ρ) / (4 * cp * Real.log 2) := ⟨_, rfl⟩
  have hcp1 : (1 : ℝ) ≤ cp := by exact_mod_cast (show 1 ≤ cp by omega)
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hAκ : ρ * Real.log (1 / ρ) = 4 * cp * Real.log 2 * κ := by
    rw [hκdef]; field_simp
  have ev1 : ∀ᶠ K : ℕ in Filter.atTop, (K : ℝ) / 2 ^ K < κ / 2 := by
    filter_upwards [(tendsto_pow_const_div_const_pow_of_one_lt 1 one_lt_two).eventually
      (Iio_mem_nhds (half_pos hκ))] with K hK
    simpa only [pow_one, Set.mem_Iio] using hK
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp (ev1.and
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (max (8 * κ) (2 / Real.log 2))))
  refine ⟨κ, hκ, max K₁ 2, le_max_right _ _, fun K hK => ?_⟩
  obtain ⟨hKlt, hKge⟩ := hK₁ K (le_of_max_le_left hK)
  have hK2 : 2 ≤ K := le_of_max_le_right hK
  have hK8 : 8 * κ ≤ K := (le_max_left _ _).trans hKge
  have hKlog : 2 ≤ (K : ℝ) * Real.log 2 := (div_le_iff₀ hL2).mp ((le_max_right _ _).trans hKge)
  have hx0 : ⌊(K : ℝ) / κ⌋₊ ≠ 0 :=
    (Nat.floor_pos.mpr ((one_le_div hκ).mpr (by linarith))).ne'
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = Nat.log 2 ⌊(K : ℝ) / κ⌋₊ := ⟨_, rfl⟩
  have hh : (0 : ℝ) < 2 ^ b := by positivity
  have hb_le : (2 : ℝ) ^ b * κ ≤ K := by
    refine (le_div_iff₀ hκ).mp (le_trans ?_ (Nat.floor_le (by positivity)))
    exact_mod_cast hb ▸ Nat.pow_log_le_self 2 hx0
  have hb_gt : (K : ℝ) < 2 * 2 ^ b * κ := by
    have h1 : ⌊(K : ℝ) / κ⌋₊ + 1 ≤ 2 ^ (b + 1) :=
      Nat.lt_iff_add_one_le.mp (hb ▸ Nat.lt_pow_succ_log_self one_lt_two _)
    have h2 : ((⌊(K : ℝ) / κ⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (b + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    rw [pow_succ] at h2
    rw [← div_lt_iff₀ hκ]
    linarith [Nat.lt_floor_add_one ((K : ℝ) / κ)]
  have h4 : (4 : ℝ) < 2 ^ b := lt_of_mul_lt_mul_left (by linarith : κ * 4 < κ * 2 ^ b) hκ.le
  have hbK : b < K := by
    have h1 := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ K)).mp hKlt
    have h2 : κ * 2 ^ b < κ * 2 ^ K := by linarith [mul_pos hκ (by positivity : (0 : ℝ) < 2 ^ K)]
    exact (pow_lt_pow_iff_right₀ one_lt_two).mp (lt_of_mul_lt_mul_left h2 hκ.le)
  have hρh := mul_lt_mul_of_pos_right hρ1 hh
  have hfl_lo := Nat.lt_floor_add_one (ρ * 2 ^ b)
  have hfl_hi := Nat.floor_le (by positivity : 0 ≤ ρ * 2 ^ b)
  have hkhat : (((⌊ρ * 2 ^ b⌋₊ + 2 : ℕ)) : ℝ) = ⌊ρ * 2 ^ b⌋₊ + 2 := by push_cast; ring
  have hlt : ((⌊ρ * 2 ^ b⌋₊ + 2 : ℕ) : ℝ) < 2 ^ b := by rw [hkhat]; linarith
  have hltN : ⌊ρ * 2 ^ b⌋₊ + 2 < 2 ^ b := by exact_mod_cast hlt
  refine ⟨K - b, b, ⌊ρ * 2 ^ b⌋₊ + 2, by omega, by omega, by omega, hltN.le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hkhat]; linarith
  · rw [hkhat]; linarith
  · rw [div_le_div_iff₀ (by positivity) hh]; linarith
  · rw [div_le_div_iff₀ hh (by positivity)]; linarith
  have hcore := core_ineq ρ hρ0 cp b K _ (by rw [hkhat]; linarith) (by rw [hkhat]; linarith) hlt
    (by linarith) (by
      rw [hAκ]
      linarith [le_mul_of_one_le_left (by positivity : 0 ≤ (K : ℝ) * Real.log 2) hcp1,
        mul_lt_mul_of_pos_left hb_gt (by positivity : (0 : ℝ) < 2 * cp * Real.log 2)])
  rw [hkhat] at hcore
  have hchoose := choose_ge_div_pow (2 ^ b) _ hltN.le
  push_cast at hchoose
  have hN : (4 : ℝ) ≤ 2 ^ K := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ K := pow_le_pow_right₀ one_le_two hK2
  have hy := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ) ^ K) (by linarith)
    (Nat.le_ceil (c : ℝ))
  rw [Real.rpow_natCast] at hy
  have hy1 : (1 : ℝ) ≤ ((2 : ℝ) ^ K) ^ ⌈(c : ℝ)⌉₊ := one_le_pow₀ (by linarith)
  have hcp' : ((2 : ℝ) ^ K) ^ cp = ((2 : ℝ) ^ K) ^ ⌈(c : ℝ)⌉₊ * 2 ^ K := by rw [hcp, pow_succ]
  linarith [mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ ((2 : ℝ) ^ K) ^ ⌈(c : ℝ)⌉₊)]

private theorem exists_smooth_domain_zmod (p : ℕ) [Fact p.Prime] (K : ℕ) (hK : 2 ^ K ∣ p - 1) :
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (domain : ιC ↪ ZMod p) (_ : ReedSolomon.Smooth domain), Fintype.card ιC = 2 ^ K := by
  classical
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := (ZMod p)ˣ) 2
    (by rwa [Nat.card_eq_fintype_card, ZMod.card_units])
  let _ : Fintype H := Fintype.ofFinite H
  refine ⟨H, inferInstance, ⟨1⟩, inferInstance,
    ⟨fun x => ((x : (ZMod p)ˣ) : ZMod p), fun x y h => Subtype.ext (Units.ext h)⟩,
    ⟨H, 1, ?_, K, ?_⟩, ?_⟩
  · ext z
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Set.mem_image, SetLike.mem_coe, Units.val_one, one_mul, Subtype.exists]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩, fun ⟨a, ha, h⟩ => ⟨a, ha, h⟩⟩
  all_goals rw [← Nat.card_eq_fintype_card]; exact hH

private theorem near_capacity_slack (ρ : ℝ≥0) (κ : ℝ) {K a b khat : ℕ} (hab : a + b = K)
    (hK : 0 < K) (hkh : khat ≤ 2 ^ b) (hlo : (ρ : ℝ) * 2 ^ b < (khat : ℝ) - 1)
    (hhi : (khat : ℝ) - 1 ≤ ρ * 2 ^ b + 1) (hκlo : κ / K ≤ 1 / 2 ^ b)
    (hκhi : 1 / 2 ^ b ≤ 2 * κ / K) (slack : ℝ≥0) (hs : (slack : ℝ) = khat / 2 ^ b - ρ) :
    |(((khat - 1) * 2 ^ a : ℕ) : ℝ) / (2 ^ K : ℕ) - ρ| ≤ 2 * κ / Real.logb 2 (2 ^ K : ℕ) ∧
      κ / Real.logb 2 (2 ^ K : ℕ) ≤ slack ∧ (slack : ℝ) ≤ 4 * κ / Real.logb 2 (2 ^ K : ℕ) ∧
      1 - ρ - slack = (((2 ^ b - khat) * 2 ^ a : ℕ) : ℝ≥0) / (2 ^ K : ℕ) := by
  have hh : (0 : ℝ) < 2 ^ b := by positivity
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog : Real.logb 2 ((2 ^ K : ℕ) : ℝ) = K := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have hk1 : 1 ≤ khat := by
    have : (1 : ℝ) < khat := by linarith [mul_nonneg (NNReal.coe_nonneg ρ) hh.le]
    exact_mod_cast this.le
  have hrate : (((khat - 1) * 2 ^ a : ℕ) : ℝ) / (2 ^ K : ℕ) = ((khat : ℝ) - 1) / 2 ^ b := by
    rw [← hab]; push_cast [Nat.cast_sub hk1]; rw [pow_add]; field_simp
  have hr_lo : (ρ : ℝ) < ((khat : ℝ) - 1) / 2 ^ b := by rw [lt_div_iff₀ hh]; linarith
  have hr_hi : ((khat : ℝ) - 1) / 2 ^ b ≤ ρ + 1 / 2 ^ b := by
    rw [div_le_iff₀ hh, add_mul, one_div_mul_cancel hh.ne']; linarith
  have hsplit : (khat : ℝ) / 2 ^ b = ((khat : ℝ) - 1) / 2 ^ b + 1 / 2 ^ b := by
    rw [← add_div, sub_add_cancel]
  have hkh' : (khat : ℝ) ≤ 2 ^ b := by exact_mod_cast hkh
  have hρ1 : ρ ≤ 1 := by
    have : (ρ : ℝ) ≤ 1 := by linarith [(div_le_one hh).mpr hkh', NNReal.coe_nonneg slack]
    exact_mod_cast this
  have hs1 : slack ≤ 1 - ρ := by
    rw [← NNReal.coe_le_coe, NNReal.coe_sub hρ1]; push_cast; linarith [(div_le_one hh).mpr hkh']
  rw [hlog, hrate]
  have h4κ : 4 * κ / K = 2 * (2 * κ / K) := by ring
  refine ⟨abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩, by linarith, by linarith, ?_⟩
  apply NNReal.coe_injective
  rw [NNReal.coe_sub hs1, NNReal.coe_sub hρ1, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_natCast]
  push_cast [Nat.cast_sub hkh]
  rw [hs, ← hab, pow_add]
  field_simp
  ring

private theorem near_capacity_field_le (c : ℝ≥0) {n k q : ℕ} (hn : 3 ≤ n) (hk : k ≤ n)
    (hq : (n : ℝ) ^ ((c : ℝ) + 2) ≤ q) :
    (n : ℝ) + 2 * k * (n : ℝ) ^ (c : ℝ) ≤ q := by
  have hn0 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (c : ℝ) := Real.one_le_rpow (by linarith) c.2
  rw [Real.rpow_add (by linarith), Real.rpow_two] at hq
  linarith [mul_le_mul_of_nonneg_right hk' (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ (c : ℝ)),
    mul_le_mul_of_nonneg_left hone (by linarith : (0 : ℝ) ≤ n),
    mul_le_mul_of_nonneg_left hn0 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (c : ℝ) * n)]

/-- For every `c` and `ρ ∈ (0, 1/2)` there are
uniform constants such that for every large `K` and every prime `p ≡ 1 (mod 2^K)` with
`p ≥ n^{c+2}`, `n = 2^K`, some smooth Reed--Solomon code over `ZMod p` of length `n` and rate
within `O(1/log₂ n)` of `ρ` has

  `ε_ca(C, 1 - ρ - Θ(1/log₂ n)) ≥ n^c / p`. -/
theorem exists_rs_epsCa_large_near_capacity_of_prime
    (c : ℝ≥0) (ρ : ℝ≥0) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1 / 2) :
    ∃ Kρ K₁ K₂ : ℝ, 0 < Kρ ∧ 0 < K₁ ∧ K₁ ≤ K₂ ∧ ∃ K₀ : ℕ,
    ∀ K : ℕ, K₀ ≤ K → ∀ (p : ℕ) [Fact p.Prime], 2 ^ K ∣ p - 1 →
      ((2 : ℝ) ^ K) ^ ((c : ℝ) + 2) ≤ p →
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (domain : ιC ↪ ZMod p) (_ : ReedSolomon.Smooth domain) (k : ℕ) (slack : ℝ≥0),
      Fintype.card ιC = 2 ^ K ∧
      |(k : ℝ) / Fintype.card ιC - (ρ : ℝ)| ≤ Kρ / Real.logb 2 (Fintype.card ιC) ∧
      K₁ / Real.logb 2 (Fintype.card ιC) ≤ (slack : ℝ) ∧
      (slack : ℝ) ≤ K₂ / Real.logb 2 (Fintype.card ιC) ∧
      let _ : SampleableType (ZMod p) := SampleableType.ofFintype (ZMod p)
      epsCa (F := ZMod p) (A := ZMod p) ((ReedSolomon.code domain k : Set (ιC → ZMod p)))
          (1 - ρ - slack) (1 - ρ - slack) ≥
        ((Fintype.card ιC : ENNReal) ^ (c : ℝ)) / (p : ENNReal) := by
  have hρ0 : (0 : ℝ) < ρ := by exact_mod_cast hρ_pos
  have hρ1 : (ρ : ℝ) < 1 / 2 := by exact_mod_cast hρ_lt
  obtain ⟨κ, hκ, K₀, hK₀, hparams⟩ := exists_near_capacity_params c ρ hρ0 hρ1
  refine ⟨2 * κ, κ, 4 * κ, by positivity, hκ, by linarith, K₀, ?_⟩
  intro K hK p _ hdvd hp
  obtain ⟨a, b, khat, hab, ha, hk2, hkh, hlo, hhi, hκlo, hκhi, hL⟩ := hparams K hK
  obtain ⟨ιC, _, _, _, domain, _, hcard⟩ := exists_smooth_domain_zmod p K hdvd
  set slack : ℝ≥0 := ((khat : ℝ) / 2 ^ b - ρ).toNNReal with hslack
  have hs : (slack : ℝ) = khat / 2 ^ b - ρ := by
    rw [hslack, Real.coe_toNNReal _ (by
      have : (0 : ℝ) < 2 ^ b := by positivity
      rw [sub_nonneg, le_div_iff₀ this]; linarith)]
  obtain ⟨hrate, hs_lo, hs_hi, hrad⟩ :=
    near_capacity_slack ρ κ hab (by omega) hkh hlo hhi hκlo hκhi slack hs
  refine ⟨ιC, inferInstance, inferInstance, inferInstance, domain, inferInstance,
    (khat - 1) * 2 ^ a, slack, hcard, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact hrate
  · rw [hcard]; exact hs_lo
  · rw [hcard]; exact hs_hi
  · intro _
    have hn : Fintype.card ιC = 2 ^ a * 2 ^ b := by rw [hcard, ← hab, pow_add]
    have hn3 : 3 ≤ 2 ^ K := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkn : (khat - 1) * 2 ^ a ≤ 2 ^ K := by
      rw [← hab, pow_add, Nat.mul_comm (2 ^ a)]
      exact Nat.mul_le_mul_right _ (by omega)
    have hq := near_capacity_field_le c (q := p) hn3 hkn (by exact_mod_cast hp)
    have hcore := rs_epsCa_large_of_smooth (F := ZMod p) domain hn ha hk2 hkh
      (((2 : ℝ) ^ K) ^ (c : ℝ)) (by exact_mod_cast hL)
      (by rw [ZMod.card, hcard]; exact_mod_cast hq)
    rw [ZMod.card, hcard] at hcore
    rw [hcard, hrad, ge_iff_le]
    refine le_of_eq_of_le ?_ hcore
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast (Fact.out : p.Prime).pos),
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    simp

/-- The supply of primes behind the near-capacity family: for some `β > max(c + 2, 12/5)` and
infinitely many `K`, there is a prime `p ≡ 1 (mod 2^K)` with `n^β ≤ p ≤ 2n^β`, `n = 2^K`.

This holds by a prime number theorem in arithmetic progressions to prime-power moduli; ArkLib
does not prove it. -/
def NearCapacityPrimeSupply (c : ℝ≥0) : Prop :=
  ∃ β : ℝ, max ((c : ℝ) + 2) (12 / 5) < β ∧ ∀ K₀ : ℕ, ∃ K ≥ K₀, ∃ p : ℕ,
    p.Prime ∧ 2 ^ K ∣ p - 1 ∧ ((2 : ℝ) ^ K) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * ((2 : ℝ) ^ K) ^ β

/-- The near-capacity CA lower bound as a family statement. There are arbitrarily large smooth
Reed--Solomon codes over prime fields whose rate is within `O(1/log₂ n)` of `ρ` and for which

  `ε_ca(C, 1 - ρ - Θ(1/log₂ n)) ≥ n^c / |F|`.

The uniform constants record the `O(1/log₂ n)` rate control, `Θ(1/log₂ n)` capacity slack, and
two-sided `|F| = Θ(n^β)` field growth. Quantifying over every lower length bound makes this a
family statement rather than a single-instance asymptotic claim. -/
def NearCapacityCaLowerBound (c ρ : ℝ≥0) : Prop :=
  ∃ Kρ K₁ K₂ : ℝ, 0 < Kρ ∧ 0 < K₁ ∧ K₁ ≤ K₂ ∧
  ∃ β Kq_lo Kq_hi : ℝ,
  max ((c : ℝ) + 2) (12 / 5) < β ∧ 0 < Kq_lo ∧ Kq_lo ≤ Kq_hi ∧
  ∀ n₀ : ℕ,
  ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
    (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
    (domain : ιC ↪ FC) (_ : ReedSolomon.Smooth domain) (k : ℕ) (slack : ℝ≥0),
    -- arbitrarily large block length:
    n₀ ≤ Fintype.card ιC ∧
    -- `F` is a prime field:
    (∃ p : ℕ, p.Prime ∧ CharP FC p ∧ Fintype.card FC = p) ∧
    -- `|F| = Θ(n^β)` uniformly in the family:
    Kq_lo * (Fintype.card ιC : ℝ) ^ β ≤ Fintype.card FC ∧
    (Fintype.card FC : ℝ) ≤ Kq_hi * (Fintype.card ιC : ℝ) ^ β ∧
    -- the rate, controlled only up to `O(1/log n)`:
    |(k : ℝ) / Fintype.card ιC - (ρ : ℝ)|
      ≤ Kρ / Real.logb 2 (Fintype.card ιC) ∧
    -- slack pinned to `Θ(1/log₂ n)`:
    K₁ / Real.logb 2 (Fintype.card ιC) ≤ (slack : ℝ) ∧
    (slack : ℝ) ≤ K₂ / Real.logb 2 (Fintype.card ιC) ∧
    let _ : SampleableType FC := SampleableType.ofFintype FC
    epsCa (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
        (1 - ρ - slack) (1 - ρ - slack) ≥
      ((Fintype.card ιC : ENNReal) ^ (c : ℝ)) / (Fintype.card FC : ENNReal)

/-- The near-capacity family statement `NearCapacityCaLowerBound c ρ` for `ρ ∈ (0, 1/2)`, given
the prime supply `NearCapacityPrimeSupply c`. -/
theorem exists_rs_epsCa_large_near_capacity_of_primes
    (c : ℝ≥0) (ρ : ℝ≥0) (hρ_pos : 0 < ρ) (hρ_lt : ρ < (1 / 2 : ℝ≥0))
    (primes : NearCapacityPrimeSupply c) :
    NearCapacityCaLowerBound c ρ := by
  obtain ⟨β, hβ, hprimes⟩ := primes
  obtain ⟨Kρ, K₁, K₂, hKρ, hK₁, hK₁₂, K₀, hfam⟩ :=
    exists_rs_epsCa_large_near_capacity_of_prime c ρ hρ_pos hρ_lt
  refine ⟨Kρ, K₁, K₂, hKρ, hK₁, hK₁₂, β, 1, 2, hβ, one_pos, one_le_two, fun n₀ => ?_⟩
  obtain ⟨K, hK, p, hp, hdvd, hlo, hhi⟩ := hprimes (max K₀ n₀)
  have : Fact p.Prime := ⟨hp⟩
  have hc2 : (c : ℝ) + 2 ≤ β := (le_max_left _ _).trans hβ.le
  have hpc : ((2 : ℝ) ^ K) ^ ((c : ℝ) + 2) ≤ p :=
    (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hc2).trans hlo
  obtain ⟨ιC, _, _, _, domain, _, k, slack, hcard, hrate, hs_lo, hs_hi, hca⟩ :=
    hfam K (le_of_max_le_left hK) p hdvd hpc
  have hcardR : (Fintype.card ιC : ℝ) = (2 : ℝ) ^ K := by rw [hcard]; push_cast; rfl
  refine ⟨ιC, inferInstance, inferInstance, inferInstance, ZMod p, inferInstance, inferInstance,
    inferInstance, domain, inferInstance, k, slack, ?_, ⟨p, hp, ZMod.charP p, ZMod.card p⟩,
    ?_, ?_, hrate, hs_lo, hs_hi, ?_⟩
  · rw [hcard]
    exact (le_of_max_le_right hK).trans Nat.lt_two_pow_self.le
  · rw [hcardR, ZMod.card, one_mul]; exact hlo
  · rw [hcardR, ZMod.card]; exact hhi
  · rw [ZMod.card]; exact hca

end PrimeField

end CodingTheory

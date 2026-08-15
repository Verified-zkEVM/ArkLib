/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import CompPoly.Fields.KoalaBear.Ext6
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Folded Reed--Solomon reference implementations for the toy problem

This module supplies two concrete KoalaBear sextic folded-RS encoders.  It proves
admissibility of their multiplicative-coset domains, injectivity, exact encoder
range, minimum relative distance, and small exact numerical reference facts.
Application-specific parameter policy is intentionally outside this module.
-/

namespace ToyProblem

namespace Impl.FRS

open scoped NNReal ENNReal
open Polynomial ReedSolomon.Folded Code

set_option maxRecDepth 8000 in
/-- **A high-order field element.** There exists `γ : KoalaBear.Ext6`
with `γ ≠ 0` and multiplicative order at least `2^21`. KoalaBear's prime
`q = 2^31 - 2^24 + 1` has `2^24 | q - 1`, so the multiplicative group of
`KoalaBear.Ext6 = 𝔽_{q^6}` (cyclic of order `q^6 - 1`, divisible by `q - 1`) contains an
element of order exactly `2^21`. The proof is pure finite-group theory plus `ℕ`
arithmetic: a generator of `KoalaBear.Ext6ˣ` has order `q^6 - 1`, and the power
`g ^ ((q^6 - 1) / 2^21)` has order `2^21` (`orderOf_pow'` + `Nat.div_div_self`); its unit
coercion is the witness. No computation in the noncomputable field is needed.

**This single fact is the structural keystone behind both genuine multiplicative-coset FRS
rows.** From it, domain injectivity, `(L, s)`-admissibility (`koalaFRSDomain_admissible` /
`koalaFRS12Domain_admissible`), encoder injectivity (`koalaFRSEnc_injective` /
`koalaFRS12Enc_injective`), and the folded minimum distance (`koalaFRS_minRelDist` /
`koalaFRS12_minRelDist`) all derive from this theorem. Both `s = 32` and `s = 2^12` use the
*same* `γ` (each needs only order `≥ s · |L| = 2^21`). -/
theorem koalaFRSγ_exists : ∃ γ : KoalaBear.Ext6, γ ≠ 0 ∧ 2 ^ 21 ≤ orderOf γ := by
  -- Abstract group theory: the multiplicative group `KoalaBear.Ext6ˣ` of the finite field
  -- `𝔽_{q^6}` is cyclic of order `q^6 - 1`. Since `q - 1 = 2^24 · 127` and
  -- `(q - 1) ∣ (q^6 - 1)`, we have `2^21 ∣ q^6 - 1`, so a generator's appropriate power
  -- has order exactly `2^21`; its unit coercion is the desired nonzero element.
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := KoalaBear.Ext6ˣ)
  set n : ℕ := orderOf g with hn_def
  have hcardK : Fintype.card KoalaBear.Ext6 = KoalaBear.fieldSize ^ 6 := by
    exact KoalaBear.card_ext6
  -- A generator's order is the cardinality of the unit group, `q^6 - 1`.
  have hg_ord : n = KoalaBear.fieldSize ^ 6 - 1 := by
    have h1 : orderOf g = Nat.card KoalaBear.Ext6ˣ :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    rw [hn_def, h1, Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  -- `2^21 ∣ q - 1` (concretely `q - 1 = 2^21 · 1016`) and `(q - 1) ∣ (q^6 - 1)`.
  have hdvd_q : (2 ^ 21 : ℕ) ∣ KoalaBear.fieldSize - 1 := by
    norm_num [KoalaBear.fieldSize]
  have hdvd_pow : (KoalaBear.fieldSize - 1) ∣ (KoalaBear.fieldSize ^ 6 - 1) := by
    simpa using Nat.sub_one_dvd_pow_sub_one KoalaBear.fieldSize 6
  have hdvd : (2 ^ 21 : ℕ) ∣ n := by rw [hg_ord]; exact hdvd_q.trans hdvd_pow
  have hn_pos : n ≠ 0 := by rw [hg_ord]; norm_num [KoalaBear.fieldSize]
  -- `u := g ^ (n / 2^21)` has order `n / gcd(n, n/2^21) = n / (n/2^21) = 2^21`.
  refine ⟨(g ^ (n / 2 ^ 21) : KoalaBear.Ext6ˣ), Units.ne_zero _, ?_⟩
  rw [orderOf_units]
  have hm_ne : n / 2 ^ 21 ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn_pos) hdvd) (by norm_num)
    omega
  rw [orderOf_pow' g hm_ne, ← hn_def, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
    Nat.div_div_self hdvd hn_pos]

/-- The shared high-order generator `γ` of `koalaFRSγ_exists`. -/
noncomputable def koalaFRSγ : KoalaBear.Ext6 := koalaFRSγ_exists.choose

lemma koalaFRSγ_ne_zero : koalaFRSγ ≠ 0 := koalaFRSγ_exists.choose_spec.1

lemma koalaFRSγ_order : 2 ^ 21 ≤ orderOf koalaFRSγ := koalaFRSγ_exists.choose_spec.2

/-- Powers of `γ` below `2^21 ≤ orderOf γ` are pinned by their exponent: this is the
`pow`-injectivity on `Set.Iio (orderOf γ)` that turns every distinctness side condition of
the coset construction into a `ℕ`-arithmetic fact (dischargeable by `omega`). -/
lemma koalaFRSγ_pow_left_inj {a b : ℕ} (ha : a < 2 ^ 21) (hb : b < 2 ^ 21)
    (h : koalaFRSγ ^ a = koalaFRSγ ^ b) : a = b :=
  pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (lt_of_lt_of_le ha koalaFRSγ_order))
    (Set.mem_Iio.mpr (lt_of_lt_of_le hb koalaFRSγ_order)) h

/-- The folding multiplier `ω := γ` for the `s = 32` folded RS code — the shared
high-order generator (`koalaFRSγ`). With the multiplicative-coset domain
`koalaFRSDomain j = γ^(32·j)`, the folded points are `γ^(32·j) · γ^i = γ^(32·j + i)`
over `32·j + i < 2^21 ≤ orderOf γ`, so `(L, 32)`-admissibility holds genuinely
(`koalaFRSDomain_admissible`) rather than being a documentary placeholder. -/
noncomputable def koalaFoldω : KoalaBear.Ext6 := koalaFRSγ

/-- The `2^16`-point folded-RS evaluation domain as a genuine **multiplicative coset**
(here the cyclic subgroup `⟨γ^32⟩`): `j ↦ γ^(32·j) ⊆ KoalaBear.Ext6`, the [ABF26] §6.3
"common case" smooth-coset domain. Injectivity is `pow`-injectivity of `γ` below its
order: `32·j < 32·2^16 = 2^21 ≤ orderOf γ` (`koalaFRSγ_pow_left_inj`), replacing the
earlier additive `{1,…,2^16}` placeholder. The coset is zero-free (`γ ≠ 0`, so every
power is a unit), so the admissibility intra-orbit clause `α · ω^i ≠ α` is not
vacuously false at `0`; here it holds outright via the order bound. -/
noncomputable def koalaFRSDomain : Fin (2 ^ 16) ↪ KoalaBear.Ext6 where
  toFun j := koalaFRSγ ^ (32 * j.val)
  inj' i j hij := by
    have hi : 32 * (i : ℕ) < 2 ^ 21 := by have := i.isLt; omega
    have hj : 32 * (j : ℕ) < 2 ^ 21 := by have := j.isLt; omega
    exact Fin.val_injective (by have := koalaFRSγ_pow_left_inj hi hj hij; omega)

open Classical in
/-- **`(L, 32)`-admissibility of the coset domain.** The `32 · 2^16 = 2^21` folded points
`γ^(32·a) · γ^i = γ^(32·a + i)` are pairwise distinct because all exponents lie below
`2^21 ≤ orderOf γ`: both `Admissible` conjuncts reduce, via `koalaFRSγ_pow_left_inj`, to
`ℕ`-arithmetic facts about `32·a + i` (`omega`) and the order bound
`koalaFRSγ_order`. -/
lemma koalaFRSDomain_admissible :
    ReedSolomon.Folded.Admissible (Finset.univ.map koalaFRSDomain) 32 koalaFoldω := by
  refine ⟨?_, ?_⟩
  · intro α hα β hβ hαβ i hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα hβ
    obtain ⟨a, rfl⟩ := hα
    obtain ⟨b, rfl⟩ := hβ
    simp only [koalaFRSDomain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hαβ hcontra
    have ha := a.isLt; have hb := b.isLt
    have hab : (a : ℕ) ≠ (b : ℕ) := fun h => hαβ (by rw [h])
    have := koalaFRSγ_pow_left_inj (a := 32 * a.val + i) (b := 32 * b.val) (by omega) (by omega)
      hcontra
    omega
  · intro α hα i hipos hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα
    obtain ⟨a, rfl⟩ := hα
    simp only [koalaFRSDomain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hcontra
    have ha := a.isLt
    have := koalaFRSγ_pow_left_inj (a := 32 * a.val + i) (b := 32 * a.val) (by omega) (by omega)
      hcontra
    omega

/-- The genuine §6.3.2 folded encoder: the degree-`< 2^20` folded Reed–Solomon
evaluation map on the `2^16` points of `koalaFRSDomain` with folding `s = 32`
(`k = 2^20`, `|L| = 2^16`, `s = 2^5`, rate `ρ = 1/2`), as an `F`-linear map
`(Fin 2^20 → F) →ₗ (Fin 2^16 → Fin 32 → F)`. Built as
`frsEvalOnPoints ∘ (degreeLTEquiv).symm`, mirroring `koalaEnc` with
`ReedSolomon.Folded.frsEvalOnPoints` in place of `evalOnPoints` (the scalar
`s = 1` case). The codeword alphabet is `A = Fin 32 → KoalaBear.Ext6`. -/
noncomputable def koalaFRSEnc :
    (Fin (2 ^ 20) → KoalaBear.Ext6) →ₗ[KoalaBear.Ext6] (Fin (2 ^ 16) → Fin 32 → KoalaBear.Ext6) :=
  (frsEvalOnPoints koalaFRSDomain 32 koalaFoldω).domRestrict
      (Polynomial.degreeLT KoalaBear.Ext6 (2 ^ 20))
    ∘ₗ (Polynomial.degreeLTEquiv KoalaBear.Ext6 (2 ^ 20)).symm.toLinearMap

open Classical in
/-- **Injectivity of the folded encoder** ([ABF26] Definition 6.1's "code as the
injective map"). Mathematically this would follow from `(L, s)`-admissibility of
`koalaFoldω` (`ReedSolomon.Folded.Admissible`, the GR08 condition that the `s·|L|`
folded evaluation points `{α · ω^i}` are pairwise distinct) together with
`k ≤ s·|L|` (here `2^20 ≤ 32·2^16 = 2^21`): a degree-`< k` polynomial vanishing
on `s·|L| ≥ k` distinct points is zero, so the unfolded evaluation — hence
`frsEvalOnPoints` on `degreeLT k` — would be injective. `koalaFRSDomain` is
zero-free precisely so `Admissible koalaFoldω` is not *provably false* (its
intra-orbit clause fails at `0`; see `koalaFRSDomain`).

This is a direct derivation through the in-tree bridge
`ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective` (the `Admissible ω → injective`
bridge that also backs the FRS dimension formula `dim_frsCode`): the encoder is
`(injective domRestrict) ∘ (injective degreeLTEquiv.symm)`. The `domRestrict` injectivity
consumes `koalaFRSDomain_admissible`, `koalaFRSγ_ne_zero`, and `k = 2^20 ≤ 32 · 2^16 =
2^21 = s · |ι|`. The order witness `koalaFRSγ_exists` is proved using abstract cyclicity. -/
theorem koalaFRSEnc_injective : Function.Injective koalaFRSEnc := by
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  simp only [koalaFRSEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
  refine (ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective (k := 2 ^ 20) (s := 32)
    koalaFRSDomain koalaFoldω koalaFRSDomain_admissible koalaFRSγ_ne_zero ?_).comp
    (LinearEquiv.injective _)
  rw [Fintype.card_fin]; norm_num

open Classical in
set_option maxRecDepth 8000 in
/-- **The folded encoder's image is exactly the folded RS code** `FRS[koalaFRSDomain, 2^20,
32, koalaFoldω]`. The FRS counterpart of `koalaEnc_range`: `koalaFRSEnc = frsEvalOnPoints ∘
(degreeLTEquiv).symm`, and as the latter ranges over all degree-`< 2^20` polynomials its
image is `(degreeLT 2^20).map (frsEvalOnPoints …) = frsCode …`. This identifies
`Set.range ⇑koalaFRSEnc` with `frsCode`, unlocking the folded MDS distance below. -/
theorem koalaFRSEnc_range :
    Set.range ⇑koalaFRSEnc =
      (↑(ReedSolomon.Folded.frsCode koalaFRSDomain (2 ^ 20) 32 koalaFoldω) :
        Set (Fin (2 ^ 16) → Fin 32 → KoalaBear.Ext6)) := by
  ext y
  rw [SetLike.mem_coe, ReedSolomon.Folded.frsCode, Submodule.mem_map]
  simp only [Set.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨↑((Polynomial.degreeLTEquiv KoalaBear.Ext6 (2 ^ 20)).symm m), Submodule.coe_mem _, ?_⟩
    simp only [koalaFRSEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearMap.domRestrict_apply]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Polynomial.degreeLTEquiv KoalaBear.Ext6 (2 ^ 20) ⟨p, hp⟩, ?_⟩
    simp only [koalaFRSEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.domRestrict_apply]

open Classical in
/-- **Folded-RS minimum relative distance**, derived through the in-tree folded-distance
bridge `ReedSolomon.Folded.minDist_frsCode`.
`minRelHammingDistCode (Set.range ⇑koalaFRSEnc) = 32769/65536`, the folded-Singleton (MDS-type)
distance for `FRS[F, L, 2^20, 32, ω]`: a nonzero degree-`< 2^20` polynomial has `< 2^20`
roots, so it vanishes on `≤ ⌊(2^20-1)/32⌋ = 32767` *whole* folded symbols, hence the folded
Hamming distance is `D = |L| − 32767 = 65536 − 32767 = 32769` and `δ_min = D/|L| =
32769/65536`. Via `koalaFRSEnc_range` (the code *is* `frsCode`), `minDist_frsCode`, and the
absolute-to-relative bridge `minDist_div_card_eq_minRelHammingDistCode`. -/
theorem koalaFRS_minRelDist :
    minRelHammingDistCode (Set.range ⇑koalaFRSEnc) = (32769 / 65536 : ℚ≥0) := by
  haveI : Nonempty (Fin (2 ^ 16)) := inferInstance
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  have hcode : Set.range ⇑koalaFRSEnc =
      (↑(ReedSolomon.Folded.frsCode koalaFRSDomain (2 ^ 20) 32 koalaFoldω) :
        Set (Fin (2 ^ 16) → Fin 32 → KoalaBear.Ext6)) := koalaFRSEnc_range
  have hmin : Code.minDist (Set.range ⇑koalaFRSEnc) = 32769 := by
    have h := ReedSolomon.Folded.minDist_frsCode (k := 2 ^ 20) (s := 32) (by norm_num)
      koalaFRSDomain koalaFoldω koalaFRSDomain_admissible koalaFRSγ_ne_zero
      (by rw [Fintype.card_fin]; norm_num)
    simp only [Fintype.card_fin] at h
    norm_num at h
    rw [hcode]; exact h
  have hbridge := minDist_div_card_eq_minRelHammingDistCode (Set.range ⇑koalaFRSEnc)
  have hcardι : Fintype.card (Fin (2 ^ 16)) = 65536 := by
    rw [Fintype.card_fin]; norm_num
  rw [hmin, hcardι] at hbridge
  have hQ : ((minRelHammingDistCode (Set.range ⇑koalaFRSEnc) : ℚ≥0) : ℚ) =
      ((32769 / 65536 : ℚ≥0) : ℚ) := by
    rw [← hbridge]; push_cast; norm_num
  exact_mod_cast hQ

/-- **Exact numerical lower-bound reference:** `2^(-128.01) ≤
(32767/65536)^128`. The crux of the folded MDS sweep-floor. Split off `2^(-128)`:
since `32767/65536 = (32767/32768)·(1/2)`, this reduces to `2^(-0.01) ≤
(32767/32768)^128`. Bernoulli (`one_add_mul_le_pow`) gives `(32767/32768)^128 =
(1 - 1/32768)^128 ≥ 1 - 128/32768 = 255/256`, and `2^(-0.01) ≤ 255/256` is the
**proven integer inequality** `256^100 ≤ 2·255^100` (`log₁₀`: `100·2.4082 =
240.82 ≤ 0.301 + 240.65`). No float `#eval`. (True value `(32767/65536)^128 ≈
2^(-128.006)`, comfortably above the `2^(-128.01)` ceiling.) -/
theorem koalaFRS_spotcheck_lb :
    (2 : ℝ≥0) ^ (-(128.01 : ℝ)) ≤ ((32767 : ℝ≥0) / 65536) ^ (128 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [show (-128.01 : ℝ) = (-0.01 : ℝ) + (-(128 : ℝ)) by norm_num]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (32767:ℝ)/65536 = (32767/32768) * (1/2) by ring]
  rw [mul_pow]
  rw [show ((1:ℝ)/2)^128 = 2^(-(128:ℝ)) by
    rw [Real.rpow_neg (by norm_num), show (128:ℝ) = ((128:ℕ):ℝ) by norm_num,
        Real.rpow_natCast]; norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hbern : (255 : ℝ) / 256 ≤ (32767/32768 : ℝ)^128 := by
    have := one_add_mul_le_pow (a := (-1/32768:ℝ)) (by norm_num) 128
    linarith
  have h2neg : (2:ℝ)^(-0.01:ℝ) ≤ 255/256 := by
    apply le_of_pow_le_pow_left₀ (n := 100) (by norm_num) (by positivity)
    rw [← Real.rpow_natCast ((2:ℝ)^(-0.01:ℝ)) 100]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  linarith [hbern, h2neg]

/-! ## Large-folding reference at `s = 2^12 = 4096`

This second concrete parameter point keeps the message dimension `k = 2^20`
and unfolded length `s · |L| = 2^21`, so `s = 2^12` gives `|L| = 2^9 = 512`.
The folded MDS distance is
`δ_min = (|L| − ⌊(k−1)/s⌋)/|L| = (512 − 255)/512 = 257/512` (a degree-`< 2^20`
polynomial has `< 2^20` roots, so `< (2^20−1)/2^12 = 256`, i.e. `≤ 255`, *whole*
folded symbols can vanish — the same count that gives the `s = 32` value
`32769/65536`). -/

/-- The `2^9 = 512`-point folded-RS evaluation domain for the `s = 2^12` row, the genuine
multiplicative coset `j ↦ γ^(2^12·j) ⊆ KoalaBear.Ext6` (the cyclic subgroup `⟨γ^(2^12)⟩`),
exactly as `koalaFRSDomain` but at folding `2^12`. Injectivity is `pow`-injectivity below
`orderOf γ`: `2^12·j < 2^12·2^9 = 2^21 ≤ orderOf γ` (`koalaFRSγ_pow_left_inj`). -/
noncomputable def koalaFRS12Domain : Fin (2 ^ 9) ↪ KoalaBear.Ext6 where
  toFun j := koalaFRSγ ^ (2 ^ 12 * j.val)
  inj' i j hij := by
    have hi : 2 ^ 12 * (i : ℕ) < 2 ^ 21 := by have := i.isLt; omega
    have hj : 2 ^ 12 * (j : ℕ) < 2 ^ 21 := by have := j.isLt; omega
    exact Fin.val_injective (by have := koalaFRSγ_pow_left_inj hi hj hij; omega)

open Classical in
/-- **`(L, 2^12)`-admissibility of the `s = 2^12` coset domain.** The `2^12 · 2^9 = 2^21`
folded points `γ^(2^12·a) · γ^i = γ^(2^12·a + i)` are pairwise distinct, all exponents
below `2^21 ≤ orderOf γ`; both `Admissible` conjuncts reduce to `ℕ`-arithmetic via
`koalaFRSγ_pow_left_inj`. Same (now-proven) order bound as `koalaFRSDomain_admissible`. -/
lemma koalaFRS12Domain_admissible :
    ReedSolomon.Folded.Admissible (Finset.univ.map koalaFRS12Domain) (2 ^ 12) koalaFoldω := by
  refine ⟨?_, ?_⟩
  · intro α hα β hβ hαβ i hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα hβ
    obtain ⟨a, rfl⟩ := hα
    obtain ⟨b, rfl⟩ := hβ
    simp only [koalaFRS12Domain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hαβ hcontra
    have ha := a.isLt; have hb := b.isLt
    have hab : (a : ℕ) ≠ (b : ℕ) := fun h => hαβ (by rw [h])
    have := koalaFRSγ_pow_left_inj (a := 2 ^ 12 * a.val + i) (b := 2 ^ 12 * b.val)
      (by omega) (by omega) hcontra
    omega
  · intro α hα i hipos hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα
    obtain ⟨a, rfl⟩ := hα
    simp only [koalaFRS12Domain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hcontra
    have ha := a.isLt
    have := koalaFRSγ_pow_left_inj (a := 2 ^ 12 * a.val + i) (b := 2 ^ 12 * a.val)
      (by omega) (by omega) hcontra
    omega

/-- The `s = 2^12 = 4096` folded encoder: degree-`< 2^20` folded RS evaluation on
the `2^9` points of `koalaFRS12Domain` with folding `s = 4096` (`k = 2^20`,
`|L| = 2^9`, rate `ρ = 1/2`), as `(Fin 2^20 → F) →ₗ (Fin 2^9 → Fin 4096 → F)`.
Same `frsEvalOnPoints ∘ (degreeLTEquiv).symm` shape as `koalaFRSEnc`, with the
folding parameter `2^12` and the smaller `2^9`-point domain. -/
noncomputable def koalaFRS12Enc :
    (Fin (2 ^ 20) → KoalaBear.Ext6) →ₗ[KoalaBear.Ext6]
      (Fin (2 ^ 9) → Fin (2 ^ 12) → KoalaBear.Ext6) :=
  (frsEvalOnPoints koalaFRS12Domain (2 ^ 12) koalaFoldω).domRestrict
      (Polynomial.degreeLT KoalaBear.Ext6 (2 ^ 20))
    ∘ₗ (Polynomial.degreeLTEquiv KoalaBear.Ext6 (2 ^ 20)).symm.toLinearMap

open Classical in
/-- **Injectivity of the `s = 2^12` folded encoder** — the large-folding counterpart of
`koalaFRSEnc_injective`, derived through the in-tree bridge
`ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective`, consuming
`koalaFRS12Domain_admissible`, `koalaFRSγ_ne_zero`, and `k = 2^20 ≤ s·|L| = 2^12·2^9 =
2^21`. It uses the same shared order witness `koalaFRSγ_exists` as the `s = 32` row. -/
theorem koalaFRS12Enc_injective : Function.Injective koalaFRS12Enc := by
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  simp only [koalaFRS12Enc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
  refine (ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective (k := 2 ^ 20) (s := 2 ^ 12)
    koalaFRS12Domain koalaFoldω koalaFRS12Domain_admissible koalaFRSγ_ne_zero ?_).comp
    (LinearEquiv.injective _)
  rw [Fintype.card_fin]; norm_num

open Classical in
set_option maxRecDepth 8000 in
/-- **The `s = 2^12` folded encoder's image is exactly `frsCode`** — the large-folding
counterpart of `koalaFRSEnc_range`. -/
theorem koalaFRS12Enc_range :
    Set.range ⇑koalaFRS12Enc =
      (↑(ReedSolomon.Folded.frsCode koalaFRS12Domain (2 ^ 20) (2 ^ 12) koalaFoldω) :
        Set (Fin (2 ^ 9) → Fin (2 ^ 12) → KoalaBear.Ext6)) := by
  ext y
  rw [SetLike.mem_coe, ReedSolomon.Folded.frsCode, Submodule.mem_map]
  simp only [Set.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨↑((Polynomial.degreeLTEquiv KoalaBear.Ext6 (2 ^ 20)).symm m), Submodule.coe_mem _, ?_⟩
    simp only [koalaFRS12Enc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearMap.domRestrict_apply]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Polynomial.degreeLTEquiv KoalaBear.Ext6 (2 ^ 20) ⟨p, hp⟩, ?_⟩
    simp only [koalaFRS12Enc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.domRestrict_apply]

open Classical in
set_option maxRecDepth 8000 in
/-- **Folded-RS minimum relative distance at `s = 2^12`**, derived through
`ReedSolomon.Folded.minDist_frsCode` exactly as `koalaFRS_minRelDist`.
`minRelHammingDistCode (Set.range ⇑koalaFRS12Enc) = 257/512`, the folded-Singleton distance for
`FRS[F, L, 2^20, 4096, ω]`: a nonzero degree-`< 2^20` polynomial vanishes on
`≤ ⌊(2^20−1)/4096⌋ = 255` whole folded symbols, so `D = |L| − 255 = 512 − 255 = 257` and
`δ_min = 257/512`. -/
theorem koalaFRS12_minRelDist :
    minRelHammingDistCode (Set.range ⇑koalaFRS12Enc) = (257 / 512 : ℚ≥0) := by
  haveI : Nonempty (Fin (2 ^ 9)) := inferInstance
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  have hcode : Set.range ⇑koalaFRS12Enc =
      (↑(ReedSolomon.Folded.frsCode koalaFRS12Domain (2 ^ 20) (2 ^ 12) koalaFoldω) :
        Set (Fin (2 ^ 9) → Fin (2 ^ 12) → KoalaBear.Ext6)) := koalaFRS12Enc_range
  have hmin : Code.minDist (Set.range ⇑koalaFRS12Enc) = 257 := by
    have h := ReedSolomon.Folded.minDist_frsCode (k := 2 ^ 20) (s := 2 ^ 12) (by norm_num)
      koalaFRS12Domain koalaFoldω koalaFRS12Domain_admissible koalaFRSγ_ne_zero
      (by rw [Fintype.card_fin]; norm_num)
    simp only [Fintype.card_fin] at h
    norm_num at h
    rw [hcode]; exact h
  have hbridge := minDist_div_card_eq_minRelHammingDistCode (Set.range ⇑koalaFRS12Enc)
  have hcardι : Fintype.card (Fin (2 ^ 9)) = 512 := by
    rw [Fintype.card_fin]; norm_num
  rw [hmin, hcardι] at hbridge
  have hQ : ((minRelHammingDistCode (Set.range ⇑koalaFRS12Enc) : ℚ≥0) : ℚ) =
      ((257 / 512 : ℚ≥0) : ℚ) := by
    rw [← hbridge]; push_cast; norm_num
  exact_mod_cast hQ

/-- **Exact numerical lower-bound reference:** `2^(-128.75) ≤
(255/512)^128`, the folded MDS sweep-floor for `s = 2^12`. Split `255/512 =
(255/256)·(1/2)`, reduce `(1/2)^128 = 2^(-128)` to `2^(-0.75) ≤ (255/256)^128`.
Unlike the `s = 32` leaf (step `1/256` is far coarser than `1/32768`), Bernoulli
is too weak here, so we **sandwich through `3/5`**: `2^(-0.75) ≤ 3/5` (the small
integer fact `(3/5)^4 = 81/625 ≥ 1/8 = 2^(-3)`) and `3/5 ≤ (255/256)^128` (the
integer fact `3·256^128 ≤ 5·255^128`). True value `(255/512)^128 ≈ 2^(-128.723)`,
comfortably above the `2^(-128.75)` ceiling. No float `#eval`. -/
theorem koalaFRS12_spotcheck_lb :
    (2 : ℝ≥0) ^ (-(128.75 : ℝ)) ≤ ((255 : ℝ≥0) / 512) ^ (128 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [show (-128.75 : ℝ) = (-0.75 : ℝ) + (-(128 : ℝ)) by norm_num]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (255:ℝ)/512 = (255/256) * (1/2) by ring]
  rw [mul_pow]
  rw [show ((1:ℝ)/2)^128 = 2^(-(128:ℝ)) by
    rw [Real.rpow_neg (by norm_num), show (128:ℝ) = ((128:ℕ):ℝ) by norm_num,
        Real.rpow_natCast]; norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  -- ⊢ 2^(-0.75) ≤ (255/256)^128, via the rational sandwich 2^(-0.75) ≤ 3/5 ≤ (255/256)^128
  have hsand : (3 : ℝ) / 5 ≤ (255 / 256 : ℝ) ^ 128 := by
    rw [div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
    exact_mod_cast (by norm_num : (3:ℕ) * 256 ^ 128 ≤ 255 ^ 128 * 5)
  have h2neg : (2:ℝ) ^ (-0.75:ℝ) ≤ 3 / 5 := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
    rw [← Real.rpow_natCast ((2:ℝ)^(-0.75:ℝ)) 4]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  linarith [hsand, h2neg]

end Impl.FRS

end ToyProblem

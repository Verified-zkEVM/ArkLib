/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.LargeAlphabet.Pigeonhole

/-!
# Large-alphabet barrier: sparse large-union families, and the robust minimum-distance barrier

The sparse **large-union existence** theory — a family of
equal-sized coordinate sets, any `W` of which cover almost everything — with all of its floor/ceil
bookkeeping, then the two assembly theorems: `barrier_package_existence` produces the parameter
package, and `robust_minimum_distance_barrier` is the barrier itself, which
`Bounds/LargeAlphabet.lean` combines with the separated-subcode extraction to bound the alphabet.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview and the
references, and `Bounds/LargeAlphabet.lean` for the two theorems this development serves.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code

namespace LargeAlphabetBarrier

theorem sparse_ceil_rpow_budget
    (x : ℝ) (k : ℕ) (hx : x ≤ ((k / 2 : ℕ) : ℝ)) :
    Nat.ceil ((2 : ℝ) ^ x) ≤ 2 ^ (k / 2) := by
  apply (Nat.ceil_le).2
  calc
    (2 : ℝ) ^ x ≤ (2 : ℝ) ^ ((k / 2 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
    _ = (2 : ℝ) ^ (k / 2 : ℕ) := Real.rpow_natCast _ _
    _ = ((2 ^ (k / 2) : ℕ) : ℝ) := by norm_num

/-- The binomial ratio estimate behind the sparse count:
`C(b−1, a) / C(m, a) ≤ ((b−1)/(m+1−a))^a`. -/
theorem sparse_choose_ratio_bound :
    ∀ (m a b : ℕ), a ≤ b - 1 → b - 1 ≤ m →
      ((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ≤
        ((((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) ^ a) := by
  intro m a b hab hbm
  have ham : a ≤ m := hab.trans hbm
  have hchooseNat : 0 < Nat.choose m a := Nat.choose_pos ham
  have hchoose : (0 : ℝ) < Nat.choose m a := by
    exact_mod_cast hchooseNat
  have hbaseNat : 0 < m + 1 - a := by omega
  have hbase : (0 : ℝ) < (m + 1 - a : ℕ) := by
    exact_mod_cast hbaseNat
  have hfac : (0 : ℝ) < Nat.factorial a := by positivity
  have hfacne : (Nat.factorial a : ℝ) ≠ 0 := ne_of_gt hfac
  have hnum : (Nat.choose (b - 1) a : ℝ) ≤
      ((b - 1 : ℕ) : ℝ) ^ a / Nat.factorial a := by
    exact Nat.choose_le_pow_div a (b - 1)
  have hden : (((m + 1 - a : ℕ) : ℝ) ^ a) / Nat.factorial a ≤
      (Nat.choose m a : ℝ) := by
    exact Nat.pow_le_choose a m
  have hdenLower :
      0 < (((m + 1 - a : ℕ) : ℝ) ^ a) / Nat.factorial a := by
    exact div_pos (pow_pos hbase a) hfac
  calc
    (Nat.choose (b - 1) a : ℝ) / Nat.choose m a ≤
        (((b - 1 : ℕ) : ℝ) ^ a / Nat.factorial a) /
          ((((m + 1 - a : ℕ) : ℝ) ^ a) / Nat.factorial a) := by
      exact div_le_div₀ (by positivity) hnum hdenLower hden
    _ = (((b - 1 : ℕ) : ℝ) ^ a) /
        (((m + 1 - a : ℕ) : ℝ) ^ a) := by
      exact div_div_div_cancel_right₀ hfacne _ _
    _ = ((((b - 1 : ℕ) : ℝ) /
        ((m + 1 - a : ℕ) : ℝ)) ^ a) := by
      exact (div_pow _ _ a).symm

theorem sparse_clear_denominator
    (C₁ C₂ X U W T : ℕ) (hU : 0 < U) (hWT : W ≤ T)
    (hcoeff :
      (C₁ : ℝ) * C₂ * (((X : ℝ) / U) ^ W) < 1) :
    C₁ * C₂ * X ^ W * U ^ (T - W) < U ^ T := by
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  have hUne : (U : ℝ) ≠ 0 := ne_of_gt hUR
  have hpowSplit : (U : ℝ) ^ T =
      (U : ℝ) ^ W * (U : ℝ) ^ (T - W) := by
    rw [← pow_add, Nat.add_sub_of_le hWT]
  have hmul := mul_lt_mul_of_pos_right hcoeff (pow_pos hUR T)
  have hleft :
      ((C₁ : ℝ) * C₂ * (((X : ℝ) / U) ^ W)) * (U : ℝ) ^ T =
        (C₁ : ℝ) * C₂ * (X : ℝ) ^ W * (U : ℝ) ^ (T - W) := by
    rw [hpowSplit, div_pow]
    field_simp [pow_ne_zero W hUne]
  have hreal :
      (C₁ : ℝ) * C₂ * (X : ℝ) ^ W * (U : ℝ) ^ (T - W) <
        (U : ℝ) ^ T := by
    calc
      (C₁ : ℝ) * C₂ * (X : ℝ) ^ W * (U : ℝ) ^ (T - W) =
          ((C₁ : ℝ) * C₂ * (((X : ℝ) / U) ^ W)) *
            (U : ℝ) ^ T := hleft.symm
      _ < 1 * (U : ℝ) ^ T := hmul
      _ = (U : ℝ) ^ T := one_mul _
  exact_mod_cast hreal

theorem sparse_constants
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hsum : α + β < 1) :
    ∃ s W : ℕ, 0 < W ∧
      0 < β / (1 - α) ∧ β / (1 - α) < 1 ∧
      (β / (1 - α)) ^ s < (1 : ℝ) / 8 ∧
      (s : ℝ) < α * W := by
  have hβ : 0 < β := hα.trans hαβ
  have hden : 0 < 1 - α := by linarith
  have hθpos : 0 < β / (1 - α) := div_pos hβ hden
  have hθlt : β / (1 - α) < 1 := by
    rw [div_lt_one hden]
    linarith
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one
    (x := (1 : ℝ) / 8) (y := β / (1 - α)) (by norm_num) hθlt
  obtain ⟨W, hWgt⟩ := exists_nat_gt ((s : ℝ) / α)
  have hWreal : (0 : ℝ) < W := by
    exact (div_nonneg (Nat.cast_nonneg s) hα.le).trans_lt hWgt
  have hW : 0 < W := by exact_mod_cast hWreal
  have hsW : (s : ℝ) < α * W := by
    have h := (div_lt_iff₀ hα).mp hWgt
    simpa only [mul_comm] using h
  exact ⟨s, W, hW, hθpos, hθlt, hs, hsW⟩

theorem sparse_floor_exponent_budget
    (α : ℝ) (hα : 0 < α) (s W : ℕ)
    (hgap : (s : ℝ) < α * W) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      s * m ≤ Nat.floor (α * m) * W := by
  have hprod : (0 : ℝ) < α * W :=
    (Nat.cast_nonneg s).trans_lt hgap
  have hWreal : (0 : ℝ) < W := by
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · exact (not_lt_of_ge hα.le h.1).elim
  let δ : ℝ := α * W - s
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact sub_pos.mpr hgap
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt ((W : ℝ) / δ)
  refine ⟨m₀, ?_⟩
  intro m hm
  have hmreal : (W : ℝ) / δ < m :=
    hm₀.trans_le (by exact_mod_cast hm)
  have hWδ : (W : ℝ) < δ * m := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hmreal
  have hfloor : α * m < (Nat.floor (α * m) : ℝ) + 1 :=
    Nat.lt_floor_add_one (α * m)
  have hmul := mul_lt_mul_of_pos_right hfloor hWreal
  have hreal : ((s * m : ℕ) : ℝ) <
      ((Nat.floor (α * m) * W : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul]
    dsimp only [δ] at hWδ
    nlinarith
  exact_mod_cast hreal.le

/-- The numerics imply sparse existence — the probabilistic-method step, done by counting. -/
theorem sparse_large_union_existence_of_numerics :
    SparseLargeUnionNumerics → SparseLargeUnionExistence := by
  intro hNumerics α β hα hαβ hsum
  obtain ⟨W, hW, γ, hγ, m₀, hnum⟩ :=
    hNumerics α β hα hαβ hsum
  refine ⟨W, hW, γ, hγ, m₀, ?_⟩
  intro m hm
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  let T := 2 ^ (m / W)
  have hpack := hnum m hm
  change a < b ∧ b ≤ m ∧ W ≤ T ∧
      Nat.choose T W * Nat.choose m (b - 1) *
          Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) <
        Nat.choose m a ^ T ∧
      W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤ T at hpack
  rcases hpack with ⟨hab, hbm, hWT, hbadCoeff, hgrowth⟩
  have hb : 0 < b := by omega
  have hbadBound := bad_indexed_families_card_bound
    m a T W b hW hWT hb hbm hab
  have htypeCard :
      Fintype.card (Fin T → {S : Finset (Fin m) // S.card = a}) =
        Nat.choose m a ^ T := by
    rw [Fintype.card_fun, exact_subset_type_card, Fintype.card_fin]
  have hbadlt :
      (badIndexedFamilies m a T W b).card <
        (Finset.univ : Finset
          (Fin T → {S : Finset (Fin m) // S.card = a})).card := by
    rw [Finset.card_univ, htypeCard]
    exact hbadBound.trans_lt hbadCoeff
  obtain ⟨A, hAuniv, hAgood⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hbadlt
  obtain ⟨family, hfamily⟩ :=
    good_indexed_family_to_large_union_family
      m a T W b hW hab A hAgood
  refine ⟨family, ?_⟩
  have hmul :
      W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤
        W * family.sets.card := hgrowth.trans hfamily
  have hceil : Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤
      family.sets.card := le_of_mul_le_mul_left hmul hW
  exact (Nat.ceil_le).mp hceil

theorem sparse_power_budget (m W k : ℕ) :
    Nat.choose (2 ^ (m / W)) W ≤ 2 ^ m ∧
      Nat.choose m k ≤ 2 ^ m := by
  constructor
  · calc
      Nat.choose (2 ^ (m / W)) W ≤ (2 ^ (m / W)) ^ W :=
        Nat.choose_le_pow (2 ^ (m / W)) W
      _ = 2 ^ ((m / W) * W) := by rw [pow_mul]
      _ ≤ 2 ^ m :=
        pow_le_pow_right' (by omega) (Nat.div_mul_le_self m W)
  · exact Nat.choose_le_two_pow m k

theorem sparse_bad_coefficient_lt_one
    (m a b W : ℕ) (hm : 0 < m)
    (hWT : W ≤ 2 ^ (m / W)) (hbm : b - 1 ≤ m)
    (hratio :
      (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) <
        ((1 : ℝ) / 8) ^ m) :
    (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
        (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) < 1 := by
  obtain ⟨hchooseT, hchooseM⟩ := sparse_power_budget m W (b - 1)
  have hchooseTR : (Nat.choose (2 ^ (m / W)) W : ℝ) ≤
      (2 : ℝ) ^ m := by
    exact_mod_cast hchooseT
  have hchooseMR : (Nat.choose m (b - 1) : ℝ) ≤
      (2 : ℝ) ^ m := by
    exact_mod_cast hchooseM
  have hchooseTPos : (0 : ℝ) < Nat.choose (2 ^ (m / W)) W := by
    exact_mod_cast Nat.choose_pos hWT
  have hchooseMPos : (0 : ℝ) < Nat.choose m (b - 1) := by
    exact_mod_cast Nat.choose_pos hbm
  have hstrict :
      (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
          (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) <
        (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
          ((1 : ℝ) / 8) ^ m := by
    exact mul_lt_mul_of_pos_left hratio (mul_pos hchooseTPos hchooseMPos)
  have hcoeff :
      (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) ≤
        (2 : ℝ) ^ m * (2 : ℝ) ^ m :=
    mul_le_mul hchooseTR hchooseMR (by positivity) (by positivity)
  have hupper :
      (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
          ((1 : ℝ) / 8) ^ m ≤
        (2 : ℝ) ^ m * (2 : ℝ) ^ m * ((1 : ℝ) / 8) ^ m :=
    mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hnormalize :
      (2 : ℝ) ^ m * (2 : ℝ) ^ m * ((1 : ℝ) / 8) ^ m =
        ((1 : ℝ) / 2) ^ m := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have hhalf : ((1 : ℝ) / 2) ^ m < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hm)
  exact hstrict.trans_le hupper |>.trans_eq hnormalize |>.trans hhalf

theorem sparse_quotient_window
    (W m : ℕ) (hW : 0 < W) (hm : 2 * W * W ≤ m) :
    (2 * W ≤ m / W) ∧
      (m < (m / W + 1) * W) ∧
      (W ≤ m / W - (m / W) / 2) := by
  have hlow : 2 * W ≤ m / W := by
    apply (Nat.le_div_iff_mul_le hW).2
    simpa only [Nat.mul_assoc] using hm
  have hupp : m < (m / W + 1) * W := by
    apply ((Nat.galoisConnection_mul_div hW).lt_iff_lt).2
    exact Nat.lt_succ_self (m / W)
  refine ⟨hlow, hupp, ?_⟩
  omega

theorem sparse_growth_budget (W : ℕ) (hW : 0 < W) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤ 2 ^ (m / W) := by
  refine ⟨1 / (8 * (W : ℝ)), by positivity, 2 * W * W, ?_⟩
  intro m hm
  let k := m / W
  obtain ⟨h2W, hmUpper, hWrem⟩ :=
    sparse_quotient_window W m hW hm
  have hkTwo : 2 ≤ k := by
    dsimp only [k]
    omega
  have hnat : k + 1 ≤ 8 * (k / 2) := by omega
  have hmNat : m ≤ (k / 2) * (8 * W) := by
    calc
      m ≤ (k + 1) * W := hmUpper.le
      _ ≤ (8 * (k / 2)) * W := Nat.mul_le_mul_right W hnat
      _ = (k / 2) * (8 * W) := by ring
  have hden : (0 : ℝ) < 8 * W := by positivity
  have hexp :
      (1 / (8 * (W : ℝ))) * m ≤ ((k / 2 : ℕ) : ℝ) := by
    rw [show (1 / (8 * (W : ℝ))) * (m : ℝ) =
      (m : ℝ) / (8 * W) by ring]
    rw [div_le_iff₀ hden]
    exact_mod_cast hmNat
  have hceil :
      Nat.ceil ((2 : ℝ) ^
        ((1 / (8 * (W : ℝ))) * m)) ≤ 2 ^ (k / 2) :=
    sparse_ceil_rpow_budget _ k hexp
  have hWpow : W ≤ 2 ^ (k - k / 2) := by
    calc
      W = Nat.choose W 1 := (Nat.choose_one_right W).symm
      _ ≤ 2 ^ W := Nat.choose_le_two_pow W 1
      _ ≤ 2 ^ (k - k / 2) :=
        pow_le_pow_right' (by omega) hWrem
  calc
    W * Nat.ceil ((2 : ℝ) ^
        ((1 / (8 * (W : ℝ))) * m)) ≤
        2 ^ (k - k / 2) * 2 ^ (k / 2) :=
      Nat.mul_le_mul hWpow hceil
    _ = 2 ^ ((k - k / 2) + k / 2) := (pow_add _ _ _).symm
    _ = 2 ^ k := by rw [Nat.sub_add_cancel (Nat.div_le_self k 2)]
    _ = 2 ^ (m / W) := by rfl

theorem sparse_ratio_base_bound
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (m : ℕ) (hm : 0 < m) :
    let a := Nat.floor (α * m)
    let b := Nat.ceil (β * m)
    (((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) <
      β / (1 - α) := by
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hβ : 0 < β := hα.trans hαβ
  have hα1 : α < 1 := hαβ.trans hβ1
  have hdenBase : 0 < 1 - α := by linarith
  have hβm : 0 < β * m := mul_pos hβ hmR
  have hbPos : 0 < b := by
    dsimp only [b]
    exact (Nat.ceil_pos).2 hβm
  have hnum : ((b - 1 : ℕ) : ℝ) < β * m := by
    have hceil := Nat.ceil_lt_add_one hβm.le
    have hbOne : 1 ≤ b := by omega
    rw [Nat.cast_sub hbOne]
    norm_num only [Nat.cast_one]
    linarith
  have hαmNonneg : 0 ≤ α * m := mul_nonneg hα.le hmR.le
  have haReal : (a : ℝ) ≤ α * m := by
    dsimp only [a]
    exact Nat.floor_le hαmNonneg
  have haLt : a < m := by
    dsimp only [a]
    apply (Nat.floor_lt hαmNonneg).2
    have h := mul_lt_mul_of_pos_right hα1 hmR
    simpa only [one_mul] using h
  have haLe : a ≤ m + 1 := by omega
  have hdenLower : (1 - α) * m < ((m + 1 - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub haLe]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hdenPos : (0 : ℝ) < (m + 1 - a : ℕ) :=
    (mul_pos hdenBase hmR).trans hdenLower
  apply (div_lt_div_iff₀ hdenPos hdenBase).2
  calc
    ((b - 1 : ℕ) : ℝ) * (1 - α) <
        (β * m) * (1 - α) :=
      mul_lt_mul_of_pos_right hnum hdenBase
    _ = β * ((1 - α) * m) := by ring
    _ < β * ((m + 1 - a : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hdenLower hβ

theorem sparse_ratio_decay
    (m a b s W : ℕ) (θ : ℝ)
    (hm : 0 < m) (ha : 0 < a) (hW : 0 < W)
    (hab : a ≤ b - 1) (hbm : b - 1 ≤ m)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hbase : (((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) < θ)
    (hexp : s * m ≤ a * W) (hθpow : θ ^ s < (1 : ℝ) / 8) :
    (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) <
      ((1 : ℝ) / 8) ^ m := by
  let q : ℝ := (Nat.choose (b - 1) a : ℝ) / Nat.choose m a
  let r : ℝ := ((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)
  have hchoose : q ≤ r ^ a := by
    simpa only [q, r] using sparse_choose_ratio_bound m a b hab hbm
  have hqNonneg : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hrNonneg : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hfirst : q ^ W ≤ (r ^ a) ^ W :=
    pow_le_pow_left₀ hqNonneg hchoose W
  have hpowBase : (r ^ a) ^ W = r ^ (a * W) := by
    exact (pow_mul r a W).symm
  have hstrict : r ^ (a * W) < θ ^ (a * W) := by
    exact pow_lt_pow_left₀ hbase hrNonneg
      (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt hW))
  have hθexp : θ ^ (a * W) ≤ θ ^ (s * m) :=
    (pow_le_pow_iff_right_of_lt_one₀ hθ0 hθ1).2 hexp
  have hθsplit : θ ^ (s * m) = (θ ^ s) ^ m := pow_mul θ s m
  have hlast : (θ ^ s) ^ m < ((1 : ℝ) / 8) ^ m := by
    exact pow_lt_pow_left₀ hθpow (pow_nonneg hθ0.le s)
      (Nat.ne_of_gt hm)
  calc
    q ^ W ≤ (r ^ a) ^ W := hfirst
    _ = r ^ (a * W) := hpowBase
    _ < θ ^ (a * W) := hstrict
    _ ≤ θ ^ (s * m) := hθexp
    _ = (θ ^ s) ^ m := hθsplit
    _ < ((1 : ℝ) / 8) ^ m := hlast

theorem sparse_rounded_setup
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (s W : ℕ) (hW : 0 < W) (hgap : (s : ℝ) < α * W) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      let a := Nat.floor (α * m)
      let b := Nat.ceil (β * m)
      let T := 2 ^ (m / W)
      0 < m ∧ 0 < a ∧ a < b ∧ b ≤ m ∧ a ≤ b - 1 ∧
        b - 1 ≤ m ∧ W ≤ T ∧ s * m ≤ a * W := by
  obtain ⟨mExp, hExp⟩ :=
    sparse_floor_exponent_budget α hα s W hgap
  obtain ⟨mFloor, hFloor⟩ := exists_nat_gt ((1 : ℝ) / α)
  let m₀ := max (max 1 (W * W)) (max mFloor mExp)
  refine ⟨m₀, ?_⟩
  intro m hm
  have hmpos : 0 < m := by
    dsimp only [m₀] at hm
    omega
  have hWW : W * W ≤ m := by
    dsimp only [m₀] at hm
    omega
  have hmFloor : mFloor ≤ m := by
    dsimp only [m₀] at hm
    omega
  have hmExp : mExp ≤ m := by
    dsimp only [m₀] at hm
    omega
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  let T := 2 ^ (m / W)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hαm : (1 : ℝ) < α * m := by
    have hfrac : (1 : ℝ) / α < m :=
      hFloor.trans_le (by exact_mod_cast hmFloor)
    have h := (div_lt_iff₀ hα).mp hfrac
    simpa only [mul_comm] using h
  have haPos : 0 < a := by
    dsimp only [a]
    exact (Nat.floor_pos).2 hαm.le
  have hβ : 0 < β := hα.trans hαβ
  have hab : a < b := by
    dsimp only [a, b]
    exact Nat.floor_lt_ceil_of_lt_of_pos
      (mul_lt_mul_of_pos_right hαβ hmR) (mul_pos hβ hmR)
  have hbm : b ≤ m := by
    dsimp only [b]
    apply (Nat.ceil_le).2
    have h := mul_le_mul_of_nonneg_right hβ1.le hmR.le
    simpa only [one_mul] using h
  have habSub : a ≤ b - 1 := by omega
  have hbSub : b - 1 ≤ m := by omega
  have hdiv : W ≤ m / W := by
    exact (Nat.le_div_iff_mul_le hW).2
      (by simpa only [Nat.mul_comm] using hWW)
  have hWT : W ≤ T := by
    dsimp only [T]
    calc
      W = Nat.choose W 1 := (Nat.choose_one_right W).symm
      _ ≤ 2 ^ W := Nat.choose_le_two_pow W 1
      _ ≤ 2 ^ (m / W) := pow_le_pow_right' (by omega) hdiv
  have hsm : s * m ≤ a * W := by
    simpa only [a] using hExp m hmExp
  exact ⟨hmpos, haPos, hab, hbm, habSub, hbSub, hWT, hsm⟩

theorem sparse_counting_inequality
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hsum : α + β < 1) :
    ∃ W : ℕ, 0 < W ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      let a := Nat.floor (α * m)
      let b := Nat.ceil (β * m)
      let T := 2 ^ (m / W)
      a < b ∧ b ≤ m ∧ W ≤ T ∧
        Nat.choose T W * Nat.choose m (b - 1) *
            Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) <
          Nat.choose m a ^ T := by
  obtain ⟨s, W, hW, hθ0, hθ1, hθpow, hgap⟩ :=
    sparse_constants α β hα hαβ hsum
  have hβ1 : β < 1 := by linarith
  obtain ⟨m₀, hsetup⟩ :=
    sparse_rounded_setup α β hα hαβ hβ1 s W hW hgap
  refine ⟨W, hW, m₀, ?_⟩
  intro m hm
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  let T := 2 ^ (m / W)
  have hpack := hsetup m hm
  change 0 < m ∧ 0 < a ∧ a < b ∧ b ≤ m ∧ a ≤ b - 1 ∧
      b - 1 ≤ m ∧ W ≤ T ∧ s * m ≤ a * W at hpack
  rcases hpack with
    ⟨hmpos, haPos, hab, hbm, habSub, hbSub, hWT, hsm⟩
  have hbase :
      (((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) <
        β / (1 - α) := by
    simpa only [a, b] using
      sparse_ratio_base_bound α β hα hαβ hβ1 m hmpos
  have hratio := sparse_ratio_decay m a b s W (β / (1 - α))
    hmpos haPos hW habSub hbSub hθ0 hθ1 hbase hsm hθpow
  have hbad := sparse_bad_coefficient_lt_one
    m a b W hmpos (by simpa only [T] using hWT) hbSub hratio
  have haM : a ≤ m := hab.le.trans hbm
  have hchoose : 0 < Nat.choose m a := Nat.choose_pos haM
  have hcoeff := sparse_clear_denominator
    (Nat.choose T W) (Nat.choose m (b - 1))
    (Nat.choose (b - 1) a) (Nat.choose m a) W T
    hchoose hWT (by simpa only [T] using hbad)
  exact ⟨hab, hbm, hWT, hcoeff⟩

theorem sparse_large_union_numerics : SparseLargeUnionNumerics := by
  unfold SparseLargeUnionNumerics
  intro α β hα hαβ hsum
  obtain ⟨W, hW, mCount, hCount⟩ :=
    sparse_counting_inequality α β hα hαβ hsum
  obtain ⟨γ, hγ, mGrowth, hGrowth⟩ :=
    sparse_growth_budget W hW
  refine ⟨W, hW, γ, hγ, max mCount mGrowth, ?_⟩
  intro m hm
  have hmCount : mCount ≤ m := by omega
  have hmGrowth : mGrowth ≤ m := by omega
  have hc := hCount m hmCount
  have hg := hGrowth m hmGrowth
  dsimp only at hc ⊢
  rcases hc with ⟨hab, hbm, hWT, hcoeff⟩
  exact ⟨hab, hbm, hWT, hcoeff, hg⟩

theorem sparse_large_union_existence : SparseLargeUnionExistence :=
  sparse_large_union_existence_of_numerics sparse_large_union_numerics

theorem large_union_existence : LargeUnionExistence := by
  unfold LargeUnionExistence
  intro α β hα hαβ hβ1
  let α₀ : ℝ := min (α / 2) ((1 - β) / 4)
  let β₀ : ℝ := (1 + β) / 2
  have hα₀ : 0 < α₀ := by
    dsimp only [α₀]
    exact lt_min (by positivity) (by positivity)
  have hβ₀ : 0 < β₀ := by
    dsimp only [β₀]
    linarith
  have hβ₀1 : β₀ < 1 := by
    dsimp only [β₀]
    linarith
  have hα₀β₀ : α₀ < β₀ := by
    have hle : α₀ ≤ α / 2 := by
      dsimp only [α₀]
      exact min_le_left _ _
    dsimp only [β₀]
    linarith
  have hsum : α₀ + β₀ < 1 := by
    have hle : α₀ ≤ (1 - β) / 4 := by
      dsimp only [α₀]
      exact min_le_right _ _
    dsimp only [β₀]
    linarith
  obtain ⟨W, hW, γ₀, hγ₀, mSparse, hSparse⟩ :=
    sparse_large_union_existence α₀ β₀ hα₀ hα₀β₀ hsum
  obtain ⟨mAbsorb, hAbsorb⟩ :=
    fixed_factor_rpow_absorb W hW γ₀ hγ₀
  refine ⟨W, hW, γ₀ / 2, by positivity,
    max 1 (max mSparse mAbsorb), ?_⟩
  intro m hm
  have hmPos : 0 < m := by omega
  have hmSparse : mSparse ≤ m := by omega
  have hmAbsorb : mAbsorb ≤ m := by omega
  obtain ⟨source, hsource⟩ := hSparse m hmSparse
  let a₀ := Nat.floor (α₀ * m)
  let b₀ := Nat.ceil (β₀ * m)
  let a₁ := Nat.floor (α * m)
  let b₁ := Nat.ceil (β * m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
  have ha : a₀ ≤ a₁ := by
    dsimp only [a₀, a₁]
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right
      ((min_le_left (α / 2) ((1 - β) / 4)).trans
        (by linarith : α / 2 ≤ α)) hmR.le
  have hab : a₁ < b₀ := by
    dsimp only [a₁, b₀]
    apply Nat.floor_lt_ceil_of_lt_of_pos
    · apply mul_lt_mul_of_pos_right _ hmR
      have hαβ₀ : α < β₀ := by
        dsimp only [β₀]
        linarith
      exact hαβ₀
    · exact mul_pos hβ₀ hmR
  have hb : b₁ ≤ b₀ := by
    dsimp only [b₁, b₀]
    apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_right _ hmR.le
    dsimp only [β₀]
    linarith
  have ha₁m : a₁ ≤ m := by
    have hα1 : α < 1 := hαβ.trans hβ1
    have hfloor : (a₁ : ℝ) ≤ α * m := by
      dsimp only [a₁]
      exact Nat.floor_le (mul_nonneg hα.le hmR.le)
    have hmul : α * m ≤ m := by
      have h := mul_le_mul_of_nonneg_right hα1.le hmR.le
      simpa only [one_mul] using h
    exact_mod_cast hfloor.trans hmul
  obtain ⟨target, hresize⟩ :=
    large_union_family_resize W a₀ b₀ a₁ b₁ hW ha hab hb
      (ι := Fin m) (by simpa only [Fintype.card_fin] using ha₁m) source
  refine ⟨target, ?_⟩
  have hresizeR : (source.sets.card : ℝ) ≤
      (W : ℝ) * target.sets.card := by
    exact_mod_cast hresize
  have hmul : (W : ℝ) * (2 : ℝ) ^ ((γ₀ / 2) * m) ≤
      (W : ℝ) * target.sets.card :=
    (hAbsorb m hmAbsorb).trans (hsource.trans hresizeR)
  exact le_of_mul_le_mul_left hmul (by exact_mod_cast hW)

/-- The unused coordinates of a block structure are in bijection with `Fin` of their number, which
is how a family built on `Fin m` is transported onto them. -/
theorem unused_coordinates_equiv_fin :
    ∀ (ℓ dZero dOne : ℕ),
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (blocks : CoordinateBlocks ι ℓ dZero dOne),
        let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
        Nonempty (Fin (Fintype.card ι - used.card) ≃ {i : ι // i ∉ used}) := by
  classical
  intro ℓ dZero dOne ι _ _ blocks
  dsimp
  let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
  let ecomp : {i : ι // i ∈ usedᶜ} ≃ {i : ι // i ∉ used} :=
    { toFun := fun x => ⟨x.1, by simpa only [Finset.mem_compl] using x.2⟩
      invFun := fun x => ⟨x.1, by simpa only [Finset.mem_compl] using x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact ⟨(Finset.equivFinOfCardEq (Finset.card_compl used)).symm.trans ecomp⟩

/-- A large-union family on `Fin m` transports to one on the *unused* coordinates of a block
structure, keeping its size and staying disjoint from every block. -/
theorem large_union_family_transport :
    ∀ (ℓ dZero dOne W aFamily aUnion : ℕ),
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (blocks : CoordinateBlocks ι ℓ dZero dOne),
        let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
        ∀ (m : ℕ), m = Fintype.card ι - used.card →
          ∀ source : LargeUnionFamily (Fin m) W aFamily aUnion,
            ∃ target : LargeUnionFamily ι W aFamily aUnion,
              target.sets.card = source.sets.card ∧
              ∀ S ∈ target.sets, Disjoint S blocks.zero ∧
                ∀ j, Disjoint S (blocks.other j) := by
  classical
  intro ℓ dZero dOne W aFamily aUnion ι _ _ blocks
  dsimp
  intro m hm source
  subst m
  have heq := unused_coordinates_equiv_fin ℓ dZero dOne blocks
  dsimp at heq
  obtain ⟨e⟩ := heq
  let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
  let incl : {i : ι // i ∉ used} ↪ ι := Function.Embedding.subtype _
  let emb : Fin (Fintype.card ι - used.card) ↪ ι := e.toEmbedding.trans incl
  let mapSet : Finset (Fin (Fintype.card ι - used.card)) ↪ Finset ι :=
    (Finset.mapEmbedding emb).toEmbedding
  let target : LargeUnionFamily ι W aFamily aUnion :=
    { sets := source.sets.map mapSet
      card_each := by
        intro A hA
        rcases Finset.mem_map.mp hA with ⟨B, hB, rfl⟩
        change (B.map emb).card = aFamily
        rw [Finset.card_map]
        exact source.card_each B hB
      large_union := by
        intro T hT hTcard
        let U := source.sets.filter fun B => mapSet B ∈ T
        have hUsub : U ⊆ source.sets := Finset.filter_subset _ _
        have hmap : U.map mapSet = T := by
          ext A
          constructor
          · intro hA
            rcases Finset.mem_map.mp hA with ⟨B, hBU, hBA⟩
            have hBT := (Finset.mem_filter.mp hBU).2
            simpa only [hBA] using hBT
          · intro hA
            have hAtarget := hT hA
            rcases Finset.mem_map.mp hAtarget with ⟨B, hB, hBA⟩
            apply Finset.mem_map.mpr
            refine ⟨B, ?_, hBA⟩
            exact Finset.mem_filter.mpr ⟨hB, by simpa only [hBA] using hA⟩
        have hUcard : U.card = W := by
          rw [← hTcard, ← hmap, Finset.card_map]
        have hlarge := source.large_union U hUsub hUcard
        refine hlarge.trans ?_
        calc
          (U.biUnion id).card = ((U.biUnion id).map emb).card :=
            (Finset.card_map _).symm
          _ ≤ (T.biUnion id).card := by
            apply Finset.card_le_card
            intro x hx
            rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
            simp only [Finset.mem_biUnion] at hy ⊢
            obtain ⟨B, hBU, hyB⟩ := hy
            refine ⟨mapSet B, (Finset.mem_filter.mp hBU).2, ?_⟩
            change emb y ∈ B.map emb
            exact (Finset.mem_map' emb).2 hyB }
  refine ⟨target, ?_, ?_⟩
  · simp only [target, Finset.card_map]
  · intro A hA
    change A ∈ source.sets.map mapSet at hA
    rcases Finset.mem_map.mp hA with ⟨B, hB, rfl⟩
    constructor
    · rw [Finset.disjoint_left]
      intro x hx hzero
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hunused : emb y ∉ used := (e y).property
      exact hunused (Finset.mem_union_left _ hzero)
    · intro j
      rw [Finset.disjoint_left]
      intro x hx hother
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hunused : emb y ∉ used := (e y).property
      apply hunused
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hother⟩

theorem barrier_package_existence : BarrierPackageExistence := by
  unfold BarrierPackageExistence
  intro ℓ hℓ R hRpos hRlt B hB
  rcases barrier_constant_bounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  obtain ⟨W, hW, γ₀, hγ₀, mSource, hSource⟩ :=
    large_union_existence
      (barrierAlphaDensity R) (barrierBetaDensity ℓ R)
      hAlpha hAlphaBeta hBetaOne
  obtain ⟨mAbsorb, hAbsorb⟩ :=
    fixed_factor_rpow_absorb W hW γ₀ hγ₀
  let γ : ℝ := γ₀ / (2 * (ℓ + 1))
  let n₀ : ℕ := max (roundedBarrierDensityThreshold ℓ R B)
    (max ((ℓ + 1) * mSource) ((ℓ + 1) * mAbsorb))
  refine ⟨barrierEtaCut ℓ R B, hEta, γ, ?_,
    barrierK ℓ B, hK, W, hW, n₀, ?_⟩
  · dsimp only [γ]
    positivity
  · intro η hη hηcut ι _ _ _ hn hlen
    let n := Fintype.card ι
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    let m := d.unused
    change n₀ ≤ n at hn
    change 1 / η ≤ (n : ℝ) at hlen
    have hnDensity : roundedBarrierDensityThreshold ℓ R B ≤ n := by
      dsimp only [n₀] at hn
      omega
    have hnSource : (ℓ + 1) * mSource ≤ n := by
      dsimp only [n₀] at hn
      omega
    have hnAbsorb : (ℓ + 1) * mAbsorb ≤ n := by
      dsimp only [n₀] at hn
      omega
    rcases rounded_barrier_density_threshold_bounds
        ℓ hℓ R hRpos hRlt B hB n hnDensity with
      ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
    have hbasic := rounded_barrier_basic_bounds
      ℓ hℓ R hRpos hRlt B hB η hη hηcut n hBasicThreshold hlen
    change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
        d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
        d.boosted ≤ n ∧ d.radius ≤ n at hbasic
    rcases hbasic with
      ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
    have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
    rcases rounded_barrier_quotient_bounds
        ℓ hℓ R hRpos hRlt B n η hη hηhalf
        (by simpa only [d] using hdZero)
        (by simpa only [d] using hRadiusLe) with
      ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
    change n ≤ (ℓ + 1) * m at hnM
    have hmSource : mSource ≤ m := by
      apply le_of_mul_le_mul_left (hnSource.trans hnM)
      omega
    have hmAbsorb : mAbsorb ≤ m := by
      apply le_of_mul_le_mul_left (hnAbsorb.trans hnM)
      omega
    obtain ⟨source, hsource⟩ := hSource m hmSource
    have hwindow := rounded_barrier_density_window
      ℓ hℓ R hRpos hRlt B hB η hη hηcut n hnDensity hlen
    change Nat.floor (barrierAlphaDensity R * m) ≤ d.aFamily ∧
      d.aFamily < Nat.ceil (barrierBetaDensity ℓ R * m) ∧
      d.aUnion ≤ Nat.ceil (barrierBetaDensity ℓ R * m) ∧
      d.aFamily ≤ m at hwindow
    rcases hwindow with ⟨hLower, hUpperFamily, hUpperUnion, haUnused⟩
    obtain ⟨resized, hresize⟩ := large_union_family_resize
      W (Nat.floor (barrierAlphaDensity R * m))
      (Nat.ceil (barrierBetaDensity ℓ R * m))
      d.aFamily d.aUnion hW hLower hUpperFamily hUpperUnion
      (ι := Fin m) (by simpa only [Fintype.card_fin] using haUnused)
      source
    obtain ⟨params, hpW, hpWEq, hpa, hpu, hpz, hpo⟩ :=
      barrier_parameters_exist
        ℓ hℓ R hRpos hRlt B hB η hη hηcut n W hW
        hBasicThreshold hlen
    change params.aFamily = d.aFamily at hpa
    change params.aUnion = d.aUnion at hpu
    change params.dZero = d.dZero at hpz
    change params.dOne = d.dOne at hpo
    have hRateParam :
        params.aFamily + (B + 1) ≤ Nat.floor (R * n) := by
      rw [hpa]
      dsimp only [d, roundedBarrierData]
      omega
    have hZeroParam :
        params.dZero ≤ Nat.ceil (barrierK ℓ B * η * n) := by
      rw [hpz]
      rfl
    obtain ⟨blocks, hblocksTrue⟩ := coordinate_blocks_exists
      ℓ params.dZero params.dOne (ι := ι)
      (params.center_block_bound.trans (by
        simpa only [d] using hRadiusLe))
    let used : Finset ι :=
      blocks.zero ∪ Finset.univ.biUnion blocks.other
    have hUsedCard := coordinate_blocks_used_card
      ℓ params.dZero params.dOne blocks
    change used.card = params.dZero + ℓ * params.dOne at hUsedCard
    have hUsedEq : used.card = d.used := by
      calc
        used.card = params.dZero + ℓ * params.dOne := hUsedCard
        _ = d.dZero + ℓ * d.dOne := by rw [hpz, hpo]
        _ = d.used := by rfl
    have hmUsed : m = Fintype.card ι - used.card := by
      calc
        m = n - d.used := by rfl
        _ = Fintype.card ι - used.card := by rw [hUsedEq]
    obtain ⟨target, hTargetCard, hTargetDisjoint⟩ :=
      large_union_family_transport
        ℓ params.dZero params.dOne W d.aFamily d.aUnion
        blocks m hmUsed resized
    let family : LargeUnionFamily ι params.W
        params.aFamily params.aUnion :=
      { sets := target.sets
        card_each := by
          intro A hA
          rw [hpa]
          exact target.card_each A hA
        large_union := by
          intro T hT hTcard
          rw [hpu]
          apply target.large_union T hT
          simpa only [hpWEq] using hTcard }
    have hFamilyDisjoint : ∀ S ∈ family.sets,
        Disjoint S blocks.zero ∧
          ∀ j, Disjoint S (blocks.other j) := by
      intro S hS
      exact hTargetDisjoint S hS
    have hresizeR : (source.sets.card : ℝ) ≤
        (W : ℝ) * resized.sets.card := by
      exact_mod_cast hresize
    have hmul : (W : ℝ) * (2 : ℝ) ^ ((γ₀ / 2) * m) ≤
        (W : ℝ) * resized.sets.card :=
      (hAbsorb m hmAbsorb).trans (hsource.trans hresizeR)
    have hWReal : (0 : ℝ) < W := by exact_mod_cast hW
    have hresizedLower : (2 : ℝ) ^ ((γ₀ / 2) * m) ≤
        resized.sets.card := le_of_mul_le_mul_left hmul hWReal
    have hnMR : (n : ℝ) ≤ ((ℓ + 1) * m : ℕ) := by
      exact_mod_cast hnM
    have hγnonneg : 0 ≤ γ := by
      dsimp only [γ]
      positivity
    have hγexp : γ * (n : ℝ) ≤ (γ₀ / 2) * m := by
      calc
        γ * (n : ℝ) ≤ γ * (((ℓ + 1) * m : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hnMR hγnonneg
        _ = (γ₀ / 2) * m := by
          dsimp only [γ]
          norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp
    have hPowWeak : (2 : ℝ) ^ (γ * n) ≤
        (2 : ℝ) ^ ((γ₀ / 2) * m) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hγexp
    have hTargetCardR : (target.sets.card : ℝ) =
        (resized.sets.card : ℝ) := by exact_mod_cast hTargetCard
    have hFamilyLower : (2 : ℝ) ^ (γ * n) ≤ family.sets.card := by
      change (2 : ℝ) ^ (γ * n) ≤ target.sets.card
      calc
        (2 : ℝ) ^ (γ * n) ≤ (2 : ℝ) ^ ((γ₀ / 2) * m) := hPowWeak
        _ ≤ resized.sets.card := hresizedLower
        _ = target.sets.card := hTargetCardR.symm
    refine ⟨params, hpW, hpWEq.le, hRateParam, hZeroParam,
      blocks, family, hFamilyDisjoint, hFamilyLower⟩

open _root_.Code in
theorem robust_minimum_distance_barrier :
    RobustMinimumDistanceBarrierStatement := by
  unfold RobustMinimumDistanceBarrierStatement
  intro ℓ hℓ R hRpos hRlt B hB
  obtain ⟨ηCut, hηCut, γ, hγ, K, hK, Wmax, hWmax,
      nPackage, hPackage⟩ :=
    barrier_package_existence ℓ hℓ R hRpos hRlt B hB
  let ηUse : ℝ := min ηCut ((1 - R) / 2)
  have hηUse : 0 < ηUse := by
    dsimp only [ηUse]
    exact lt_min hηCut (by linarith)
  let Kfac : ℕ := 2 * Wmax * ℓ
  have hKfac : 0 < Kfac := by
    dsimp only [Kfac]
    positivity
  obtain ⟨nAbsorb, hAbsorb⟩ :=
    fixed_factor_rpow_absorb Kfac hKfac (γ / 2) (by positivity)
  let α : ℝ := min (ηUse / 2) (γ / (16 * (K + 1)))
  let n₀ : ℕ := max nPackage nAbsorb
  have hα : 0 < α := by
    dsimp only [α]
    exact lt_min (by positivity) (by positivity)
  refine ⟨α, hα, n₀, ?_⟩
  intro η hη ι A _ _ _ _ _ C hA hn hlen hsize hsep hLambda
  let n := Fintype.card ι
  let q := Fintype.card A
  change n₀ ≤ n at hn
  change 1 / η ≤ (n : ℝ) at hlen
  change (q : ℝ) ^ (R * n) ≤ (B : ℝ) * C.ncard at hsize
  change separated C
    (Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * n)) at hsep
  change Lambda C (relRadius ℓ R η) ≤ (ℓ : ℕ∞) at hLambda
  by_cases hηlarge : ηUse ≤ η
  · apply alphabet_card_ge_rpow_of_alpha_le_eta α η hη
    · have hαcut : α ≤ ηUse / 2 := min_le_left _ _
      linarith
    · simpa only [q] using hA
  · have hηsmall : η < ηUse := lt_of_not_ge hηlarge
    have hηPackage : η < ηCut :=
      hηsmall.trans_le (min_le_left _ _)
    have hηHalf : η < (1 - R) / 2 :=
      hηsmall.trans_le (min_le_right _ _)
    have hnPackage : nPackage ≤ n := by
      dsimp only [n₀] at hn
      omega
    have hnAbsorb : nAbsorb ≤ n := by
      dsimp only [n₀] at hn
      omega
    obtain ⟨params, hpW, hpWmax, hrate, hdZero,
        blocks, family, hdisjoint, hlower⟩ :=
      hPackage η hη hηPackage (ι := ι) hnPackage hlen
    have hnNat : 0 < n := by
      dsimp only [n]
      exact Fintype.card_pos
    have hone : 1 ≤ η * n := eta_times_length_one η n hη hlen
    have hmany : 2 * q ^ params.aFamily ≤ C.ncard :=
      rate_loss_to_cardinality q B params.aFamily n C.ncard R
        (by simpa only [q] using hA) hB hRpos.le hrate hsize
    have hp : 0 < relRadius ℓ R η := by
      apply relRadius_pos ℓ (by omega) R η
      linarith
    have hratio :
        (Nat.floor (relRadius ℓ R η * n) : ℝ) / n ≤
          relRadius ℓ R η :=
      floor_radius_ratio_le (relRadius ℓ R η) n hp.le hnNat
    have hLambdaRounded :
        Lambda C ((Nat.floor (relRadius ℓ R η * n) : ℝ) / n) ≤
          (ℓ : ℕ∞) :=
      (Code.Lambda_mono hratio).trans hLambda
    have hpigeon := deterministic_pigeonhole_bound
      ℓ n (Nat.floor (relRadius ℓ R η * n))
      (Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * n))
      hℓ hnNat C (by simpa only [q] using hA) rfl
      (Set.toFinite C) params hpW blocks family hdisjoint hsep
      hmany hLambdaRounded
    by_contra hnot
    have hqSmall : (q : ℝ) < (2 : ℝ) ^ (α / η) :=
      lt_of_not_ge hnot
    have hαK : α * (K + 1) ≤ γ / 4 := by
      have hαSecond : α ≤ γ / (16 * (K + 1)) :=
        min_le_right _ _
      have hKOne : 0 < K + 1 := by positivity
      calc
        α * (K + 1) ≤ (γ / (16 * (K + 1))) * (K + 1) :=
          mul_le_mul_of_nonneg_right hαSecond hKOne.le
        _ = γ / 16 := by
          field_simp [ne_of_gt hKOne]
        _ ≤ γ / 4 := by nlinarith
    have hqPower := small_alphabet_power_bound
      q params.dZero n α η K γ hα.le hη hK.le hqSmall
      hdZero hone hαK
    have hCoeffNat : 2 * params.W * ℓ ≤ Kfac := by
      dsimp only [Kfac]
      exact Nat.mul_le_mul_right ℓ
        (Nat.mul_le_mul_left 2 hpWmax)
    have hCoeff : ((2 * params.W * ℓ : ℕ) : ℝ) ≤ (Kfac : ℝ) := by
      exact_mod_cast hCoeffNat
    have hpigeonR : (family.sets.card : ℝ) ≤
        ((2 * params.W * ℓ : ℕ) : ℝ) *
          ((q ^ params.dZero : ℕ) : ℝ) := by
      exact_mod_cast hpigeon
    have hupper : (family.sets.card : ℝ) ≤
        (Kfac : ℝ) * (2 : ℝ) ^ ((γ / 4) * n) := by
      calc
        (family.sets.card : ℝ) ≤
            ((2 * params.W * ℓ : ℕ) : ℝ) *
              ((q ^ params.dZero : ℕ) : ℝ) := hpigeonR
        _ ≤ (Kfac : ℝ) * (2 : ℝ) ^ ((γ / 4) * n) :=
          mul_le_mul hCoeff hqPower (by positivity) (by positivity)
    have habsorbRaw := hAbsorb n hnAbsorb
    have habsorb : (Kfac : ℝ) *
        (2 : ℝ) ^ ((γ / 4) * n) ≤
          (2 : ℝ) ^ ((γ / 2) * n) := by
      convert habsorbRaw using 1
      ring
    exact barrier_exponent_contradiction
      Kfac family.sets.card n γ hγ hnNat hlower hupper habsorb

end LargeAlphabetBarrier

end CodingTheory

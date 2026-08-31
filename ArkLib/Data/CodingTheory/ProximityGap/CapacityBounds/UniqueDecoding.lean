/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.GoodCoeffs
import Mathlib.Algebra.Order.Floor.Div

/-!
# Reed--Solomon CA in the unique-decoding range

This file proves the BCHKS25 correlated-agreement bound between one third of the minimum
distance and the finite-length half-distance boundary.

## Main result

- `rs_epsCa_le_in_unique_decoding_range` is [BCHKS25, Theorem 1.3].

## References

- [BCHKS25] Theorem 1.3.
-/

-- Elaborate the legacy proximity API through its public Matrix aliases under Lean 4.33.
set_option backward.isDefEq.respectTransparency false

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private structure BchksParameterFacts (n k e gap ax bx dz : ℕ) (δ : NNReal) : Prop where
  n_pos : 0 < n
  k_pos : 0 < k
  delta_pos : 0 < δ
  e_eq_floor : e = Nat.floor (δ * n)
  k_two_e_margin : k + 2 * e + 2 ≤ n
  gap_pos : 0 < gap
  dz_pos : 0 < dz
  ceil_cover : e + 1 ≤ gap * dz
  ax_add_pred_k : ax + (k - 1) = bx
  ax_le_bx : ax ≤ bx
  bx_sub_ax : bx - ax = k - 1
  bx_lt_remaining : bx < n - e
  bx_lt_n : bx < n
  error_add_ax : e + ax = n - k
  dimension_strict : n * (dz + 1) < dz * (ax + 1) + (dz + 1) * (bx + 1)
  ratio_denom_pos : 0 < 1 - (k : ℝ) / n - 2 * (δ : ℝ)
  bx_ratio_lt : (bx : ℝ) / n < 1 - (δ : ℝ)
  dz_ratio_le : (dz : ℝ) ≤
    (1 - (k : ℝ) / n - (δ : ℝ)) / (1 - (k : ℝ) / n - 2 * (δ : ℝ))
  first_threshold_pos : 0 <
    (1 - (k : ℝ) / n - (δ : ℝ)) /
      ((δ : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ)))
  dz_div_delta_le : (dz : ℝ) / (δ : ℝ) ≤
    (1 - (k : ℝ) / n - (δ : ℝ)) /
      ((δ : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ)))

open scoped BigOperators in
private noncomputable def bchks_constraint {ι K : Type} [Field K]
    (domain : ι → K) (u : Fin 2 → ι → K) (ax bx dz : ℕ)
    (ab : Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K)
    (i : ι) (s : Fin (dz + 1)) : K :=
  (∑ j : Fin (bx + 1), ab.2 s j * domain i ^ (j : ℕ))
    - (if hs : (s : ℕ) < dz then
        u 0 i * ∑ j : Fin (ax + 1), ab.1 ⟨s, hs⟩ j * domain i ^ (j : ℕ)
      else 0)
    - (if hs : 0 < (s : ℕ) then
        u 1 i * ∑ j : Fin (ax + 1),
          ab.1 ⟨(s : ℕ) - 1, by omega⟩ j * domain i ^ (j : ℕ)
      else 0)

open scoped BigOperators in
private noncomputable def bchks_constraint_map {ι K : Type} [Fintype ι] [Field K]
    (domain : ι → K) (u : Fin 2 → ι → K) (ax bx dz : ℕ) :
    (Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K) →ₗ[K]
      Matrix ι (Fin (dz + 1)) K where
  toFun := fun ab i s => bchks_constraint domain u ax bx dz ab i s
  map_add' := by
    intro x y
    ext i s
    change (bchks_constraint domain u ax bx dz (x + y) i s =
      bchks_constraint domain u ax bx dz x i s + bchks_constraint domain u ax bx dz y i s)
    simp only [bchks_constraint, Prod.fst_add, Prod.snd_add, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib]
    split_ifs <;> ring
  map_smul' := by
    intro c x
    ext i s
    change bchks_constraint domain u ax bx dz (c • x) i s =
      c * bchks_constraint domain u ax bx dz x i s
    unfold bchks_constraint
    simp only [Prod.smul_fst, Prod.smul_snd, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp_rw [mul_assoc, ← Finset.mul_sum] <;> ring

private theorem bchks_constraint_map_eq_zero_of_mem_ker {ι K : Type} [Fintype ι] [Field K]
    (domain : ι → K) (u : Fin 2 → ι → K) (ax bx dz : ℕ)
    (ab : Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K)
    (hab : ab ∈ LinearMap.ker (bchks_constraint_map domain u ax bx dz))
    (i : ι) (s : Fin (dz + 1)) :
    bchks_constraint domain u ax bx dz ab i s = 0 := by
  have hmap : bchks_constraint_map domain u ax bx dz ab = 0 := LinearMap.mem_ker.mp hab
  exact congrFun (congrFun hmap i) s

private theorem bchks_constraint_map_exists_nonzero_ker {ι K : Type} [Fintype ι]
    [Field K] (domain : ι → K) (u : Fin 2 → ι → K) (ax bx dz : ℕ)
    (hdim : Fintype.card ι * (dz + 1) <
      dz * (ax + 1) + (dz + 1) * (bx + 1)) :
    ∃ ab : Matrix (Fin dz) (Fin (ax + 1)) K ×
        Matrix (Fin (dz + 1)) (Fin (bx + 1)) K,
      ab ≠ 0 ∧ ab ∈ LinearMap.ker (bchks_constraint_map domain u ax bx dz) := by
  have hfin :
      Module.finrank K (Matrix ι (Fin (dz + 1)) K) <
        Module.finrank K
          (Matrix (Fin dz) (Fin (ax + 1)) K ×
            Matrix (Fin (dz + 1)) (Fin (bx + 1)) K) := by
    simpa [Module.finrank_prod, Module.finrank_matrix, Module.finrank_self] using hdim
  have hker : LinearMap.ker (bchks_constraint_map domain u ax bx dz) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfin
  rcases (Submodule.ne_bot_iff (LinearMap.ker
    (bchks_constraint_map domain u ax bx dz))).mp hker with ⟨ab, hab, hne⟩
  exact ⟨ab, hne, hab⟩

private def bchks_dz (n k e : ℕ) : ℕ := CeilDiv.ceilDiv (e + 1) (n - k - 2 * e + 1)

private noncomputable def bchks_good_polynomial {ι K : Type} [Fintype ι] [Nonempty ι]
    [Field K] [Fintype K] [DecidableEq K] {k : ℕ} [NeZero k]
    (domain : ι ↪ K) (u : Fin 2 → ι → K) (δ : NNReal) (z : K) : Polynomial K :=
  if hz : z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ then
    Classical.choose
      (ProximityGap.RS_exists_Pz_of_mem_goodCoeffs
        (deg := k) (domain := domain) (δ := δ) u (z := z) hz)
  else 0

private theorem bchks_good_polynomial_spec {ι K : Type} [Fintype ι] [Nonempty ι]
    [Field K] [Fintype K] [DecidableEq K] {k : ℕ} [NeZero k]
    (domain : ι ↪ K) (u : Fin 2 → ι → K) (δ : NNReal) (z : K)
    (hz : z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ) :
    (bchks_good_polynomial (k := k) domain u δ z).natDegree < k ∧
      hammingDist (u 0 + z • u 1)
          ((bchks_good_polynomial (k := k) domain u δ z).eval ∘ domain) ≤
        Nat.floor (δ * Fintype.card ι) := by
  simpa only [bchks_good_polynomial, dif_pos hz] using
    Classical.choose_spec
      (ProximityGap.RS_exists_Pz_of_mem_goodCoeffs
        (deg := k) (domain := domain) (δ := δ) u (z := z) hz)

private theorem bchks_good_polynomial_mem_code {ι K : Type} [Fintype ι] [Nonempty ι]
    [Field K] [Fintype K] [DecidableEq K] {k : ℕ} [NeZero k]
    (domain : ι ↪ K) (u : Fin 2 → ι → K) (δ : NNReal) (z : K)
    (hz : z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ) :
    (bchks_good_polynomial (k := k) domain u δ z).eval ∘ domain ∈
      ReedSolomon.code domain k := by
  let Pz := bchks_good_polynomial (k := k) domain u δ z
  have hdeg : Pz.natDegree < k := (bchks_good_polynomial_spec domain u δ z hz).1
  exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval Pz hdeg (by intro i; rfl)

private noncomputable def bchks_horizontal_quotient {ι K : Type} [Nonempty ι] [Field K]
    (domain : ι ↪ K) (u : Fin 2 → ι → K) (x : K) : Polynomial K :=
  Polynomial.C (u 0 (Function.invFun domain x)) +
    Polynomial.X * Polynomial.C (u 1 (Function.invFun domain x))

private theorem bchks_horizontal_quotient_domain {ι K : Type} [Nonempty ι] [Field K]
    (domain : ι ↪ K) (u : Fin 2 → ι → K) (i : ι) :
    bchks_horizontal_quotient domain u (domain i) =
      Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i) := by
  unfold bchks_horizontal_quotient
  rw [Function.leftInverse_invFun domain.injective i]

private theorem bchks_horizontal_quotient_nat_degree_le_one {ι K : Type} [Nonempty ι] [Field K]
    (domain : ι ↪ K) (u : Fin 2 → ι → K) (x : K) :
    (bchks_horizontal_quotient domain u x).natDegree ≤ 1 := by
  have hconst :
      (Polynomial.C (u 0 (Function.invFun domain x)) : Polynomial K).natDegree ≤ 1 := by
    simp
  have hlin' :
      (Polynomial.X * Polynomial.C (u 1 (Function.invFun domain x)) : Polynomial K).natDegree ≤
        (Polynomial.X : Polynomial K).natDegree := by
    simpa using
      (Polynomial.natDegree_mul_C_le (f := (Polynomial.X : Polynomial K))
        (a := u 1 (Function.invFun domain x)))
  have hlin :
      (Polynomial.X * Polynomial.C
        (u 1 (Function.invFun domain x)) : Polynomial K).natDegree ≤ 1 := by
    simpa using hlin'
  simpa only [bchks_horizontal_quotient] using
    (le_trans (Polynomial.natDegree_add_le _ _) (max_le hconst hlin))

private noncomputable def bchks_pair_disagreements {ι K : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq K] (u p : Fin 2 → ι → K) : Finset ι :=
  Code.disagreementCols (u 0) (p 0) ∪ Code.disagreementCols (u 1) (p 1)

open scoped NNReal in
omit [DecidableEq ι] [Fintype F] in
private theorem bchks_parameter_facts_of_target_hypotheses
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hk : 0 < k)
    (h_ud : (δ : ℝ) ≤
      (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
      / Fintype.card ι / 3 ≤ δ) :
    BchksParameterFacts
      (Fintype.card ι)
      k
      (Nat.floor (δ * Fintype.card ι))
      (Fintype.card ι - k - 2 * Nat.floor (δ * Fintype.card ι) + 1)
      (Fintype.card ι - k - Nat.floor (δ * Fintype.card ι))
      (Fintype.card ι - Nat.floor (δ * Fintype.card ι) - 1)
      (bchks_dz (Fintype.card ι) k (Nat.floor (δ * Fintype.card ι)))
      δ := by
  classical
  let : NeZero k := ⟨hk.ne'⟩
  set n : ℕ := Fintype.card ι
  set e : ℕ := Nat.floor (δ * n)
  set gap : ℕ := n - k - 2 * e + 1
  set ax : ℕ := n - k - e
  set bx : ℕ := n - e - 1
  set dz : ℕ := bchks_dz n k e
  change BchksParameterFacts n k e gap ax bx dz δ
  have hn_pos : 0 < n := by simp [n]
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
  have heNN : (e : ℝ≥0) ≤ δ * n := by
    simpa [e] using
      (Nat.floor_le (show (0 : ℝ≥0) ≤ δ * n by positivity))
  have heR : (e : ℝ) ≤ (δ : ℝ) * n := by exact_mod_cast heNN
  have hud : (δ : ℝ) ≤ (1 - (k : ℝ) / n) / 2 - 1 / n := by
    simpa [n] using h_ud
  have hud' : 2 * (δ : ℝ) ≤ 1 - (k : ℝ) / n - 2 / n := by
    calc
      2 * (δ : ℝ) ≤ 2 * ((1 - (k : ℝ) / n) / 2 - 1 / n) := by gcongr
      _ = 1 - (k : ℝ) / n - 2 / n := by ring
  have hscaled := mul_le_mul_of_nonneg_right hud' (le_of_lt hnR_pos)
  have hscaled' : 2 * (δ : ℝ) * n + k + 2 ≤ n := by
    field_simp [hnR_ne] at hscaled ⊢
    nlinarith [hscaled]
  have hmargin : k + 2 * e + 2 ≤ n := by
    exact_mod_cast
      (by nlinarith [heR, hscaled'] : (k : ℝ) + 2 * (e : ℝ) + 2 ≤ n)
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    omega
  have hgapR_pos : (0 : ℝ) < gap := by exact_mod_cast hgap_pos
  have haxadd : ax + (k - 1) = bx := by
    dsimp [ax, bx]
    omega
  have haxle : ax ≤ bx := by
    dsimp [ax, bx]
    omega
  have hbxsub : bx - ax = k - 1 := by
    dsimp [ax, bx]
    omega
  have hbxrem : bx < n - e := by
    dsimp [bx]
    omega
  have hbxn : bx < n := lt_of_lt_of_le hbxrem (Nat.sub_le n e)
  have herr : e + ax = n - k := by
    dsimp [ax]
    omega
  have hk_n : k ≤ n := by omega
  have hk_card : k ≤ Fintype.card ι := by simpa [n] using hk_n
  have hmin : Code.minDist (ReedSolomon.code domain k : Set (ι → F)) = n - k + 1 := by
    simpa [n] using (ReedSolomon.minDist_of_le (α := domain) (n := k) hk_card)
  have hminNat : 0 < n - k + 1 := by omega
  have hminR : (0 : ℝ) < (n - k + 1 : ℕ) := by exact_mod_cast hminNat
  have hdminpos : (0 : ℝ) < (n - k + 1 : ℕ) / (n : ℝ) / 3 := by positivity
  have hdmin : ((n - k + 1 : ℕ) : ℝ) / n / 3 ≤ (δ : ℝ) := by
    simpa [n, hmin] using h_dmin
  have hdeltaR : (0 : ℝ) < δ := lt_of_lt_of_le hdminpos hdmin
  have hdelta : 0 < δ := by exact_mod_cast hdeltaR
  have hcover : e + 1 ≤ gap * dz := by
    have hc : e + 1 ≤ gap * CeilDiv.ceilDiv (e + 1) gap :=
      (ceilDiv_le_iff_le_mul hgap_pos).mp le_rfl
    simpa [dz, bchks_dz] using hc
  have hdz_pos : 0 < dz := by
    by_contra hnot
    have hz : dz = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, mul_zero] at hcover
    omega
  have hdim : n * (dz + 1) < dz * (ax + 1) + (dz + 1) * (bx + 1) := by
    have herrlt : e < gap * dz := by omega
    have hsum : (ax + 1) + (bx + 1) = n + gap := by
      dsimp [ax, bx, gap]
      omega
    have hbxone : bx + 1 = n - e := by
      dsimp [bx]
      omega
    have hcore : n < gap * dz + (n - e) := by omega
    calc
      n * (dz + 1) = n * dz + n := by ring
      _ < n * dz + (gap * dz + (n - e)) := Nat.add_lt_add_left hcore _
      _ = dz * (ax + 1) + (dz + 1) * (bx + 1) := by
        rw [show dz * (ax + 1) + (dz + 1) * (bx + 1) =
          dz * ((ax + 1) + (bx + 1)) + (bx + 1) by ring]
        rw [hsum, hbxone]
        ring
  have hden : 0 < 1 - (k : ℝ) / n - 2 * (δ : ℝ) := by
    have htwo : (0 : ℝ) < 2 / n := div_pos (by norm_num) hnR_pos
    nlinarith [hud']
  have hgapSum : gap + k + 2 * e = n + 1 := by
    dsimp [gap]
    omega
  have hgapSumR : (gap : ℝ) + k + 2 * e = n + 1 := by exact_mod_cast hgapSum
  have hcastgap :
      (n : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ)) ≤ (gap : ℝ) := by
    have hleft :
        (n : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ)) =
          n - k - 2 * (δ : ℝ) * n := by
      field_simp [hnR_ne]
    rw [hleft]
    nlinarith [heR, hgapSumR]
  have hfrac :
      (e : ℝ) / gap ≤ (δ : ℝ) / (1 - (k : ℝ) / n - 2 * (δ : ℝ)) := by
    rw [div_le_div_iff₀ hgapR_pos hden]
    have h1 := mul_le_mul_of_nonneg_right heR (le_of_lt hden)
    have h2 := mul_le_mul_of_nonneg_left hcastgap δ.coe_nonneg
    nlinarith
  have hdz_eq : dz = e / gap + 1 := by
    change CeilDiv.ceilDiv (e + 1) gap = e / gap + 1
    rw [Nat.ceilDiv_eq_add_pred_div]
    have hnum : e + 1 + gap - 1 = e + gap := by omega
    rw [hnum, Nat.add_div_of_dvd_left (dvd_refl gap)]
    rw [Nat.div_self hgap_pos]
  have hdz_cast : (dz : ℝ) ≤ 1 + (e : ℝ) / gap := by
    rw [hdz_eq]
    push_cast
    have hdiv : (((e / gap : ℕ) : ℝ)) ≤ (e : ℝ) / (gap : ℝ) := Nat.cast_div_le
    nlinarith
  have hident :
      1 + (δ : ℝ) / (1 - (k : ℝ) / n - 2 * (δ : ℝ)) =
        (1 - (k : ℝ) / n - (δ : ℝ)) /
          (1 - (k : ℝ) / n - 2 * (δ : ℝ)) := by
    calc
      1 + (δ : ℝ) / (1 - (k : ℝ) / n - 2 * (δ : ℝ)) =
          (1 - (k : ℝ) / n - 2 * (δ : ℝ)) /
              (1 - (k : ℝ) / n - 2 * (δ : ℝ)) +
            (δ : ℝ) / (1 - (k : ℝ) / n - 2 * (δ : ℝ)) := by
              rw [div_self (ne_of_gt hden)]
      _ = ((1 - (k : ℝ) / n - 2 * (δ : ℝ)) + (δ : ℝ)) /
            (1 - (k : ℝ) / n - 2 * (δ : ℝ)) := by rw [add_div]
      _ = (1 - (k : ℝ) / n - (δ : ℝ)) /
            (1 - (k : ℝ) / n - 2 * (δ : ℝ)) := by ring
  have hdzratio : (dz : ℝ) ≤
      (1 - (k : ℝ) / n - (δ : ℝ)) /
        (1 - (k : ℝ) / n - 2 * (δ : ℝ)) := by
    calc
      (dz : ℝ) ≤ 1 + (e : ℝ) / gap := hdz_cast
      _ ≤ 1 + (δ : ℝ) / (1 - (k : ℝ) / n - 2 * (δ : ℝ)) := by gcongr
      _ = _ := hident
  have hfloorNN : δ * (n : ℝ≥0) < (e : ℝ≥0) + 1 := by
    simpa [e] using (Nat.lt_floor_add_one (δ * (n : ℝ≥0)))
  have hfloorR : (δ : ℝ) * n < (e : ℝ) + 1 := by exact_mod_cast hfloorNN
  have hbxSum : bx + e + 1 = n := by
    dsimp [bx]
    omega
  have hbxSumR : (bx : ℝ) + e + 1 = n := by exact_mod_cast hbxSum
  have hbxratio : (bx : ℝ) / n < 1 - (δ : ℝ) := by
    rw [div_lt_iff₀ hnR_pos]
    calc
      (bx : ℝ) = n - ((e : ℝ) + 1) := by linarith only [hbxSumR]
      _ < n - (δ : ℝ) * n := sub_lt_sub_left hfloorR n
      _ = (1 - (δ : ℝ)) * n := by ring
  have hnum_eq :
      1 - (k : ℝ) / n - (δ : ℝ) =
        (1 - (k : ℝ) / n - 2 * (δ : ℝ)) + (δ : ℝ) := by ring
  have hnumpos : 0 < 1 - (k : ℝ) / n - (δ : ℝ) := by
    rw [hnum_eq]
    positivity
  have hfirstpos : 0 <
      (1 - (k : ℝ) / n - (δ : ℝ)) /
        ((δ : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ))) :=
    div_pos hnumpos (mul_pos hdeltaR hden)
  have hdzdiv : (dz : ℝ) / (δ : ℝ) ≤
      (1 - (k : ℝ) / n - (δ : ℝ)) /
        ((δ : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ))) := by
    calc
      (dz : ℝ) / (δ : ℝ) ≤
          ((1 - (k : ℝ) / n - (δ : ℝ)) /
            (1 - (k : ℝ) / n - 2 * (δ : ℝ))) / (δ : ℝ) := by gcongr
      _ = (1 - (k : ℝ) / n - (δ : ℝ)) /
          ((δ : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ))) := by
            rw [div_div, mul_comm]
  exact {
    n_pos := hn_pos
    k_pos := hk
    delta_pos := hdelta
    e_eq_floor := rfl
    k_two_e_margin := hmargin
    gap_pos := hgap_pos
    dz_pos := hdz_pos
    ceil_cover := hcover
    ax_add_pred_k := haxadd
    ax_le_bx := haxle
    bx_sub_ax := hbxsub
    bx_lt_remaining := hbxrem
    bx_lt_n := hbxn
    error_add_ax := herr
    dimension_strict := hdim
    ratio_denom_pos := hden
    bx_ratio_lt := hbxratio
    dz_ratio_le := hdzratio
    first_threshold_pos := hfirstpos
    dz_div_delta_le := hdzdiv }

private noncomputable def bchks_poly_of_matrix {K : Type} [Semiring K] [DecidableEq K]
    (dy dx : ℕ) (a : Matrix (Fin dy) (Fin dx) K) : Polynomial (Polynomial K) :=
  Polynomial.ofFn dy (fun s => Polynomial.ofFn dx (a s))

private noncomputable def bchks_interpolant_pair {K : Type} [Semiring K] [DecidableEq K]
    (ax bx dz : ℕ)
    (ab : Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K) :
    Polynomial (Polynomial K) × Polynomial (Polynomial K) :=
  (bchks_poly_of_matrix dz (ax + 1) ab.1,
    bchks_poly_of_matrix (dz + 1) (bx + 1) ab.2)

private theorem bchks_poly_of_matrix_coeff {K : Type} [Semiring K] [DecidableEq K]
    (dy dx : ℕ) (a : Matrix (Fin dy) (Fin dx) K) (s : ℕ) :
    (bchks_poly_of_matrix dy dx a).coeff s =
      if hs : s < dy then Polynomial.ofFn dx (a ⟨s, hs⟩) else 0 := by
  unfold bchks_poly_of_matrix
  split_ifs with hs
  · exact Polynomial.ofFn_coeff_eq_val_of_lt _ hs
  · exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hs)

private theorem bchks_poly_of_matrix_degree_x_le {K : Type} [Semiring K] [DecidableEq K]
    (dy dx : ℕ) (hdx : 0 < dx) (a : Matrix (Fin dy) (Fin dx) K) :
    Polynomial.Bivariate.degreeX (bchks_poly_of_matrix dy dx a) ≤ dx - 1 := by
  unfold Polynomial.Bivariate.degreeX
  refine Finset.sup_le_iff.2 ?_
  intro n hn
  have hnlt : n < dy := by
    by_contra hnot
    have hzero : (bchks_poly_of_matrix dy dx a).coeff n = 0 := by
      unfold bchks_poly_of_matrix
      exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hnot)
    have hne : (bchks_poly_of_matrix dy dx a).coeff n ≠ 0 := by
      exact Polynomial.mem_support_iff.mp hn
    exact hne hzero
  rw [show (bchks_poly_of_matrix dy dx a).coeff n = Polynomial.ofFn dx (a ⟨n, hnlt⟩) by
    unfold bchks_poly_of_matrix
    exact Polynomial.ofFn_coeff_eq_val_of_lt _ hnlt]
  exact Nat.le_pred_of_lt
    (Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hdx.ne') (a ⟨n, hnlt⟩))

open scoped BigOperators in
private theorem bchks_poly_of_matrix_eval_x_coeff {K : Type} [Field K] [DecidableEq K]
    (dy dx : ℕ) (a : Matrix (Fin dy) (Fin dx) K) (x : K) (s : ℕ) :
    (Polynomial.Bivariate.evalX x (bchks_poly_of_matrix dy dx a)).coeff s =
      if hs : s < dy then ∑ j : Fin dx, a ⟨s, hs⟩ j * x ^ (j : ℕ) else 0 := by
  rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.coeff_map, bchks_poly_of_matrix_coeff]
  split_ifs with hs
  · let v : Fin dx → K := fun j => a ⟨s, hs⟩ j
    change (Polynomial.ofFn dx v).eval x = ∑ j : Fin dx, v j * x ^ (j : ℕ)
    rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Polynomial.eval_monomial]
  · simp

private theorem bchks_poly_of_matrix_injective {K : Type} [Semiring K] [DecidableEq K]
    (dy dx : ℕ) : Function.Injective (bchks_poly_of_matrix (K := K) dy dx) := by
  intro a b hab
  funext s
  apply Polynomial.injective_ofFn dx
  have hs := congrArg (fun p : Polynomial (Polynomial K) => p.coeff (s : ℕ)) hab
  change
    (Polynomial.ofFn dy (fun t => Polynomial.ofFn dx (a t))).coeff (s : ℕ) =
      (Polynomial.ofFn dy (fun t => Polynomial.ofFn dx (b t))).coeff (s : ℕ) at hs
  rw [Polynomial.ofFn_coeff_eq_val_of_lt _ s.isLt,
    Polynomial.ofFn_coeff_eq_val_of_lt _ s.isLt] at hs
  exact hs

private theorem bchks_interpolant_pair_injective {K : Type} [Semiring K] [DecidableEq K]
    (ax bx dz : ℕ) : Function.Injective (bchks_interpolant_pair (K := K) ax bx dz) := by
  intro ab cd h
  apply Prod.ext
  · apply bchks_poly_of_matrix_injective dz (ax + 1)
    exact congrArg Prod.fst h
  · apply bchks_poly_of_matrix_injective (dz + 1) (bx + 1)
    exact congrArg Prod.snd h

private theorem bchks_poly_of_matrix_nat_degree_y_le {K : Type} [Semiring K] [DecidableEq K]
    (dy dx : ℕ) (hdy : 0 < dy) (a : Matrix (Fin dy) (Fin dx) K) :
    Polynomial.Bivariate.natDegreeY (bchks_poly_of_matrix dy dx a) ≤ dy - 1 := by
  unfold Polynomial.Bivariate.natDegreeY bchks_poly_of_matrix
  exact Nat.le_pred_of_lt
    (Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hdy.ne')
      (fun s => Polynomial.ofFn dx (a s)))

private theorem bchks_interpolant_pair_degree_bounds {K : Type} [Semiring K] [DecidableEq K]
    (ax bx dz : ℕ) (hdz : 0 < dz)
    (ab : Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K) :
    let AB := bchks_interpolant_pair ax bx dz ab
    Polynomial.Bivariate.degreeX AB.1 ≤ ax ∧
      Polynomial.Bivariate.natDegreeY AB.1 ≤ dz - 1 ∧
      Polynomial.Bivariate.degreeX AB.2 ≤ bx ∧
      Polynomial.Bivariate.natDegreeY AB.2 ≤ dz := by
  dsimp [bchks_interpolant_pair]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using bchks_poly_of_matrix_degree_x_le dz (ax + 1) (by omega) ab.1
  · exact bchks_poly_of_matrix_nat_degree_y_le dz (ax + 1) hdz ab.1
  · simpa using bchks_poly_of_matrix_degree_x_le (dz + 1) (bx + 1) (by omega) ab.2
  · simpa using bchks_poly_of_matrix_nat_degree_y_le (dz + 1) (bx + 1) (by omega) ab.2

private theorem bchks_affine_mul_coeff {K : Type} [Field K] (c₀ c₁ : K)
    (P : Polynomial K) (s : ℕ) :
    (((Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁) * P).coeff s) =
      c₀ * P.coeff s + (if _hs : 0 < s then c₁ * P.coeff (s - 1) else 0) := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  have hlin : Polynomial.X * Polynomial.C c₁ * P =
      Polynomial.C c₁ * (Polynomial.X * P) := by ring
  rw [hlin, Polynomial.coeff_C_mul]
  cases s with
  | zero =>
      simp only [Polynomial.coeff_X_mul_zero, lt_self_iff_false, ↓reduceDIte, mul_zero, add_zero]
  | succ t =>
      rw [Polynomial.coeff_X_mul]
      simp only [Nat.zero_lt_succ, ↓reduceDIte, Nat.succ_sub_one]

open scoped BigOperators in
private theorem bchks_constraint_eq_coeff {ι K : Type} [Field K] [DecidableEq K]
    (domain : ι → K) (u : Fin 2 → ι → K) (ax bx dz : ℕ)
    (ab : Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K)
    (i : ι) (s : Fin (dz + 1)) :
    bchks_constraint domain u ax bx dz ab i s =
      (Polynomial.Bivariate.evalX (domain i) (bchks_interpolant_pair ax bx dz ab).2 -
        (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
          Polynomial.Bivariate.evalX (domain i)
            (bchks_interpolant_pair ax bx dz ab).1).coeff s := by
  unfold bchks_constraint bchks_interpolant_pair
  rw [Polynomial.coeff_sub]
  rw [bchks_poly_of_matrix_eval_x_coeff (dz + 1) (bx + 1) ab.2 (domain i) (s : ℕ)]
  simp only [s.isLt, ↓reduceDIte]
  rw [bchks_affine_mul_coeff]
  by_cases hs : (s : ℕ) < dz
  · rw [bchks_poly_of_matrix_eval_x_coeff dz (ax + 1) ab.1 (domain i) (s : ℕ)]
    simp only [hs, ↓reduceDIte]
    by_cases hpos : 0 < (s : ℕ)
    · have hprev : (s : ℕ) - 1 < dz := by omega
      rw [bchks_poly_of_matrix_eval_x_coeff dz (ax + 1) ab.1 (domain i) ((s : ℕ) - 1)]
      simp only [hpos, hprev, ↓reduceDIte]
      ring
    · simp only [hpos, ↓reduceDIte, add_zero, sub_zero]
  · rw [bchks_poly_of_matrix_eval_x_coeff dz (ax + 1) ab.1 (domain i) (s : ℕ)]
    simp only [hs, ↓reduceDIte]
    by_cases hpos : 0 < (s : ℕ)
    · have hprev : (s : ℕ) - 1 < dz := by omega
      rw [bchks_poly_of_matrix_eval_x_coeff dz (ax + 1) ab.1 (domain i) ((s : ℕ) - 1)]
      simp only [hpos, hprev, ↓reduceDIte]
      ring
    · simp only [hpos, ↓reduceDIte, mul_zero, add_zero, sub_zero]

private theorem bchks_interpolant_pair_vertical_identity {ι K : Type} [Fintype ι]
    [Field K] [DecidableEq K] (domain : ι → K) (u : Fin 2 → ι → K)
    (ax bx dz : ℕ)
    (ab : Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K)
    (hab : ab ∈ LinearMap.ker (bchks_constraint_map domain u ax bx dz)) :
    let AB := bchks_interpolant_pair ax bx dz ab
    ∀ i : ι, Polynomial.Bivariate.evalX (domain i) AB.2 =
      (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
        Polynomial.Bivariate.evalX (domain i) AB.1 := by
  dsimp
  intro i
  apply Polynomial.ext
  intro s
  by_cases hs : s < dz + 1
  · let sf : Fin (dz + 1) := ⟨s, hs⟩
    have hzero := bchks_constraint_map_eq_zero_of_mem_ker domain u ax bx dz ab hab i sf
    rw [bchks_constraint_eq_coeff] at hzero
    rw [Polynomial.coeff_sub] at hzero
    exact sub_eq_zero.mp hzero
  · have hsB :
        (Polynomial.Bivariate.evalX (domain i)
          (bchks_poly_of_matrix (dz + 1) (bx + 1) ab.2)).coeff s = 0 := by
      rw [bchks_poly_of_matrix_eval_x_coeff]
      simp only [hs, ↓reduceDIte]
    rw [show (bchks_interpolant_pair ax bx dz ab).2 =
      bchks_poly_of_matrix (dz + 1) (bx + 1) ab.2 by rfl, hsB]
    rw [bchks_affine_mul_coeff]
    have hsA :
        (Polynomial.Bivariate.evalX (domain i)
          (bchks_poly_of_matrix dz (ax + 1) ab.1)).coeff s = 0 := by
      rw [bchks_poly_of_matrix_eval_x_coeff]
      split_ifs with hsd
      · omega
      · rfl
    rw [show (bchks_interpolant_pair ax bx dz ab).1 =
      bchks_poly_of_matrix dz (ax + 1) ab.1 by rfl, hsA]
    by_cases hpos : 0 < s
    · have hprev : ¬ s - 1 < dz := by omega
      rw [bchks_poly_of_matrix_eval_x_coeff dz (ax + 1) ab.1 (domain i) (s - 1)]
      simp only [hpos, hprev, ↓reduceDIte, mul_zero, add_zero]
    · omega

open scoped BigOperators in
private theorem bchks_interpolant_pair_fst_ne_zero
    {ι K : Type} [Fintype ι] [Field K] [DecidableEq K]
    (domain : ι ↪ K) (u : Fin 2 → ι → K) (ax bx dz : ℕ)
    (ab : Matrix (Fin dz) (Fin (ax + 1)) K × Matrix (Fin (dz + 1)) (Fin (bx + 1)) K)
    (hab_ne : ab ≠ 0)
    (hab_ker : ab ∈ LinearMap.ker (bchks_constraint_map domain u ax bx dz))
    (hbx : bx < Fintype.card ι) :
    (bchks_interpolant_pair ax bx dz ab).1 ≠ 0 := by
  intro hA
  have hEvalB : ∀ i : ι,
      Polynomial.Bivariate.evalX (domain i) (bchks_interpolant_pair ax bx dz ab).2 = 0 := by
    intro i
    have h := bchks_interpolant_pair_vertical_identity domain u ax bx dz ab hab_ker i
    rw [hA] at h
    calc
      Polynomial.Bivariate.evalX (domain i) (bchks_interpolant_pair ax bx dz ab).2 =
          (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
            Polynomial.Bivariate.evalX (domain i) (0 : Polynomial (Polynomial K)) := h
      _ = 0 := by
        rw [Polynomial.Bivariate.evalX_eq_map, Polynomial.map_zero, mul_zero]
  have hrow : ∀ s : Fin (dz + 1), Polynomial.ofFn (bx + 1) (ab.2 s) = 0 := by
    intro s
    let p : Polynomial K := Polynomial.ofFn (bx + 1) (ab.2 s)
    have hp_eval : ∀ i : ι, p.eval (domain i) = 0 := by
      intro i
      have hc := congrArg (fun q : Polynomial K => q.coeff (s : ℕ)) (hEvalB i)
      rw [show (bchks_interpolant_pair ax bx dz ab).2 =
        bchks_poly_of_matrix (dz + 1) (bx + 1) ab.2 by rfl] at hc
      rw [bchks_poly_of_matrix_eval_x_coeff] at hc
      simp only [s.isLt, ↓reduceDIte] at hc
      rw [show p = Polynomial.ofFn (bx + 1) (ab.2 s) by rfl,
        Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
      simpa [Polynomial.eval_monomial, mul_comm] using hc
    have hp_deg : p.natDegree < Fintype.card ι := by
      have hlt : p.natDegree < bx + 1 := by
        exact Polynomial.ofFn_natDegree_lt (by omega) (ab.2 s)
      omega
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p domain.injective hp_eval hp_deg
  have hab2 : ab.2 = 0 := by
    funext s j
    have hc := congrArg (fun p : Polynomial K => p.coeff (j : ℕ)) (hrow s)
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt] at hc
    simpa using hc
  have hab1 : ab.1 = 0 := by
    apply bchks_poly_of_matrix_injective dz (ax + 1)
    change (bchks_interpolant_pair ax bx dz ab).1 = bchks_poly_of_matrix dz (ax + 1) 0
    rw [hA]
    apply Polynomial.ext
    intro s
    rw [bchks_poly_of_matrix_coeff]
    split_ifs with hs
    · change 0 = Polynomial.ofFn (ax + 1) (0 : Fin (ax + 1) → K)
      exact (map_zero (Polynomial.ofFn (R := K) (ax + 1))).symm
    · rfl
  apply hab_ne
  exact Prod.ext hab1 hab2

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem rs_exists_oversized_bivariate_ab (domain : ι ↪ F) (u : Fin 2 → ι → F)
    (n k e gap ax bx dz : ℕ) (δ : NNReal)
    (hn : n = Fintype.card ι)
    (hfacts : BchksParameterFacts n k e gap ax bx dz δ) :
    ∃ A B : Polynomial (Polynomial F),
      A ≠ 0 ∧
      Polynomial.Bivariate.degreeX A ≤ ax ∧
      Polynomial.Bivariate.natDegreeY A ≤ dz - 1 ∧
      Polynomial.Bivariate.degreeX B ≤ bx ∧
      Polynomial.Bivariate.natDegreeY B ≤ dz ∧
      (∀ i : ι,
        Polynomial.Bivariate.evalX (domain i) B =
          (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
            Polynomial.Bivariate.evalX (domain i) A) := by
  classical
  have hdim : Fintype.card ι * (dz + 1) <
      dz * (ax + 1) + (dz + 1) * (bx + 1) := by
    simpa [hn] using hfacts.dimension_strict
  obtain ⟨ab, hab_ne, hab_ker⟩ :=
    bchks_constraint_map_exists_nonzero_ker (domain : ι → F) u ax bx dz hdim
  let AB := bchks_interpolant_pair ax bx dz ab
  have hbx : bx < Fintype.card ι := by
    simpa [hn] using hfacts.bx_lt_n
  have hA0 : AB.1 ≠ 0 := by
    exact bchks_interpolant_pair_fst_ne_zero domain u ax bx dz ab hab_ne hab_ker hbx
  have hdeg := bchks_interpolant_pair_degree_bounds ax bx dz hfacts.dz_pos ab
  have hvert := bchks_interpolant_pair_vertical_identity (domain : ι → F) u ax bx dz ab hab_ker
  exact ⟨AB.1, AB.2, hA0, hdeg.1, hdeg.2.1, hdeg.2.2.1, hdeg.2.2.2, hvert⟩

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem rs_exists_oversized_bivariate_ab_of_dimension
    (domain : ι ↪ F) (u : Fin 2 → ι → F) (ax bx dz : ℕ)
    (hdz : 0 < dz) (hbx : bx < Fintype.card ι)
    (hdim : Fintype.card ι * (dz + 1) <
      dz * (ax + 1) + (dz + 1) * (bx + 1)) :
    ∃ A B : Polynomial (Polynomial F),
      A ≠ 0 ∧
      Polynomial.Bivariate.degreeX A ≤ ax ∧
      Polynomial.Bivariate.natDegreeY A ≤ dz - 1 ∧
      Polynomial.Bivariate.degreeX B ≤ bx ∧
      Polynomial.Bivariate.natDegreeY B ≤ dz ∧
      (∀ i : ι,
        Polynomial.Bivariate.evalX (domain i) B =
          (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
            Polynomial.Bivariate.evalX (domain i) A) := by
  classical
  obtain ⟨ab, hab_ne, hab_ker⟩ :=
    bchks_constraint_map_exists_nonzero_ker (domain : ι → F) u ax bx dz hdim
  let AB := bchks_interpolant_pair ax bx dz ab
  have hA0 : AB.1 ≠ 0 :=
    bchks_interpolant_pair_fst_ne_zero domain u ax bx dz ab hab_ne hab_ker hbx
  have hdeg := bchks_interpolant_pair_degree_bounds ax bx dz hdz ab
  have hvert := bchks_interpolant_pair_vertical_identity (domain : ι → F) u ax bx dz ab hab_ker
  exact ⟨AB.1, AB.2, hA0, hdeg.1, hdeg.2.1, hdeg.2.2.1, hdeg.2.2.2, hvert⟩

private theorem bchks_eval_x_eval_eq_eval_y_eval {K : Type} [Field K]
    (x z : K) (f : Polynomial (Polynomial K)) :
    (Polynomial.Bivariate.evalX x f).eval z =
      (Polynomial.Bivariate.evalY z f).eval x := by
  calc
    (Polynomial.Bivariate.evalX x f).eval z
        = (f.map (Polynomial.evalRingHom x)).eval z := by
            simp only [ps_eval_x_eq_map]
    _ = f.eval₂ (Polynomial.evalRingHom x) z := by
          simpa using (Polynomial.eval_map (f := Polynomial.evalRingHom x) (p := f) (x := z))
    _ = (Polynomial.eval (Polynomial.C z) f).eval x := by
          simpa using
            (Polynomial.eval₂_at_apply
              (p := f) (f := Polynomial.evalRingHom x) (r := Polynomial.C z))
    _ = (Polynomial.Bivariate.evalY z f).eval x := by
          rfl

open scoped BigOperators in
private theorem bchks_eval_y_nat_degree_le_degree_x {K : Type} [Field K]
    (z : K) (f : Polynomial (Polynomial K)) :
    (Polynomial.Bivariate.evalY z f).natDegree ≤ Polynomial.Bivariate.degreeX f := by
  have heval :
      Polynomial.Bivariate.evalY z f =
        ∑ j ∈ f.support, f.coeff j * (Polynomial.C z : Polynomial K) ^ j := by
    simp [Polynomial.Bivariate.evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [heval]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := f.support)
    (f := fun j => f.coeff j * (Polynomial.C z : Polynomial K) ^ j)
    (n := Polynomial.Bivariate.degreeX f) ?_
  intro j hj
  have hj_le : (f.coeff j).natDegree ≤ Polynomial.Bivariate.degreeX f :=
    Polynomial.Bivariate.coeff_natDegree_le_degreeX f j
  have hmul :
      (f.coeff j * (Polynomial.C z : Polynomial K) ^ j).natDegree ≤
        (f.coeff j).natDegree := by
    simpa only [Polynomial.C_pow] using
      (Polynomial.natDegree_mul_C_le (f := f.coeff j) (a := z ^ j))
  exact le_trans hmul hj_le

omit [DecidableEq ι] in
private theorem bchks_good_polynomial_horizontal_identity {k n e gap ax bx dz : ℕ} [NeZero k]
    (domain : ι ↪ F) (u : Fin 2 → ι → F) (δ : NNReal)
    (hn : n = Fintype.card ι)
    (hfacts : BchksParameterFacts n k e gap ax bx dz δ)
    (A B : Polynomial (Polynomial F))
    (hA_degX : Polynomial.Bivariate.degreeX A ≤ ax)
    (hB_degX : Polynomial.Bivariate.degreeX B ≤ bx)
    (hAB : ∀ i : ι,
      Polynomial.Bivariate.evalX (domain i) B =
        (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
          Polynomial.Bivariate.evalX (domain i) A)
    (z : F)
    (hz : z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ) :
    Polynomial.Bivariate.evalY z B =
      bchks_good_polynomial (k := k) domain u δ z * Polynomial.Bivariate.evalY z A := by
  classical
  let Pz := bchks_good_polynomial (k := k) domain u δ z
  have hPz := bchks_good_polynomial_spec domain u δ z hz
  have hdist : hammingDist (u 0 + z • u 1) (Pz.eval ∘ domain) ≤ e := by
    simpa [Pz, hfacts.e_eq_floor, hn] using hPz.2
  obtain ⟨Tz, hTz_card, hTz_agree⟩ :=
    (Code.closeToWord_iff_exists_agreementCols
      (u := u 0 + z • u 1) (v := Pz.eval ∘ domain) (e := e)).1 hdist
  let Dz : Polynomial F :=
    Polynomial.Bivariate.evalY z B - Pz * Polynomial.Bivariate.evalY z A
  have hDz_eval : ∀ x ∈ Tz.image domain, Dz.eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hiTz, rfl⟩
    have hi_eq : u 0 i + z * u 1 i = Pz.eval (domain i) := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hTz_agree i).1 hiTz
    have hEq_eval :
        (Polynomial.Bivariate.evalY z B).eval (domain i) =
          (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
      calc
        (Polynomial.Bivariate.evalY z B).eval (domain i) =
            (Polynomial.Bivariate.evalX (domain i) B).eval z := by
              symm
              exact bchks_eval_x_eval_eq_eval_y_eval (domain i) z B
        _ = (((Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
              Polynomial.Bivariate.evalX (domain i) A)).eval z := by
              simpa using congrArg (fun p : Polynomial F => p.eval z) (hAB i)
        _ = ((Polynomial.C (u 0 i)).eval z +
              (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
              (Polynomial.Bivariate.evalX (domain i) A).eval z := by
              rw [Polynomial.eval_mul, Polynomial.eval_add]
        _ = (u 0 i + (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
              (Polynomial.Bivariate.evalX (domain i) A).eval z := by simp
        _ = (u 0 i + z * u 1 i) *
              (Polynomial.Bivariate.evalX (domain i) A).eval z := by
              rw [Polynomial.eval_mul]
              simp
        _ = Pz.eval (domain i) *
              (Polynomial.Bivariate.evalY z A).eval (domain i) := by
              rw [hi_eq, bchks_eval_x_eval_eq_eval_y_eval]
        _ = (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
              rw [Polynomial.eval_mul]
    simpa [Dz, sub_eq_zero] using hEq_eval
  have hDz_deg : Dz.natDegree ≤ bx := by
    have hB_eval : (Polynomial.Bivariate.evalY z B).natDegree ≤ bx :=
      le_trans (bchks_eval_y_nat_degree_le_degree_x z B) hB_degX
    have hA_eval : (Polynomial.Bivariate.evalY z A).natDegree ≤ ax :=
      le_trans (bchks_eval_y_nat_degree_le_degree_x z A) hA_degX
    have hprod : (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤ bx := by
      calc
        (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤
            Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ (k - 1) + ax := Nat.add_le_add (Nat.le_pred_of_lt hPz.1) hA_eval
        _ = ax + (k - 1) := Nat.add_comm _ _
        _ = bx := hfacts.ax_add_pred_k
    exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hB_eval hprod)
  have hdeg_lt : Dz.natDegree < (Tz.image domain).card := by
    have hcard : n - e ≤ Tz.card := by
      simpa [hn, hfacts.e_eq_floor] using hTz_card
    have hlt : bx < Tz.card := lt_of_lt_of_le hfacts.bx_lt_remaining hcard
    have himg : (Tz.image domain).card = Tz.card :=
      Finset.card_image_of_injective _ domain.injective
    exact lt_of_le_of_lt hDz_deg (by simpa [himg] using hlt)
  have hzero : Dz = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (p := Dz) (s := Tz.image domain) hDz_eval hdeg_lt
  simpa [Dz, Pz, sub_eq_zero] using hzero

omit [DecidableEq ι] in
private theorem bchks_good_polynomial_horizontal_identity_basic {k n e ax bx : ℕ} [NeZero k]
    (domain : ι ↪ F) (u : Fin 2 → ι → F) (δ : NNReal)
    (hn : n = Fintype.card ι)
    (he : e = Nat.floor (δ * n))
    (hax : ax + (k - 1) = bx)
    (hbx : bx < n - e)
    (A B : Polynomial (Polynomial F))
    (hA_degX : Polynomial.Bivariate.degreeX A ≤ ax)
    (hB_degX : Polynomial.Bivariate.degreeX B ≤ bx)
    (hAB : ∀ i : ι,
      Polynomial.Bivariate.evalX (domain i) B =
        (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
          Polynomial.Bivariate.evalX (domain i) A)
    (z : F)
    (hz : z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ) :
    Polynomial.Bivariate.evalY z B =
      bchks_good_polynomial (k := k) domain u δ z * Polynomial.Bivariate.evalY z A := by
  classical
  let Pz := bchks_good_polynomial (k := k) domain u δ z
  have hPz := bchks_good_polynomial_spec domain u δ z hz
  have hdist : hammingDist (u 0 + z • u 1) (Pz.eval ∘ domain) ≤ e := by
    simpa [Pz, he, hn] using hPz.2
  obtain ⟨Tz, hTz_card, hTz_agree⟩ :=
    (Code.closeToWord_iff_exists_agreementCols
      (u := u 0 + z • u 1) (v := Pz.eval ∘ domain) (e := e)).1 hdist
  let Dz : Polynomial F :=
    Polynomial.Bivariate.evalY z B - Pz * Polynomial.Bivariate.evalY z A
  have hDz_eval : ∀ x ∈ Tz.image domain, Dz.eval x = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hiTz, rfl⟩
    have hi_eq : u 0 i + z * u 1 i = Pz.eval (domain i) := by
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hTz_agree i).1 hiTz
    have hEq_eval :
        (Polynomial.Bivariate.evalY z B).eval (domain i) =
          (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
      calc
        (Polynomial.Bivariate.evalY z B).eval (domain i) =
            (Polynomial.Bivariate.evalX (domain i) B).eval z := by
              symm
              exact bchks_eval_x_eval_eq_eval_y_eval (domain i) z B
        _ = (((Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
              Polynomial.Bivariate.evalX (domain i) A)).eval z := by
              simpa using congrArg (fun p : Polynomial F => p.eval z) (hAB i)
        _ = ((Polynomial.C (u 0 i)).eval z +
              (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
              (Polynomial.Bivariate.evalX (domain i) A).eval z := by
              rw [Polynomial.eval_mul, Polynomial.eval_add]
        _ = (u 0 i + (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
              (Polynomial.Bivariate.evalX (domain i) A).eval z := by simp
        _ = (u 0 i + z * u 1 i) *
              (Polynomial.Bivariate.evalX (domain i) A).eval z := by
              rw [Polynomial.eval_mul]
              simp
        _ = Pz.eval (domain i) *
              (Polynomial.Bivariate.evalY z A).eval (domain i) := by
              rw [hi_eq, bchks_eval_x_eval_eq_eval_y_eval]
        _ = (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
              rw [Polynomial.eval_mul]
    simpa [Dz, sub_eq_zero] using hEq_eval
  have hDz_deg : Dz.natDegree ≤ bx := by
    have hB_eval : (Polynomial.Bivariate.evalY z B).natDegree ≤ bx :=
      le_trans (bchks_eval_y_nat_degree_le_degree_x z B) hB_degX
    have hA_eval : (Polynomial.Bivariate.evalY z A).natDegree ≤ ax :=
      le_trans (bchks_eval_y_nat_degree_le_degree_x z A) hA_degX
    have hprod : (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤ bx := by
      calc
        (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤
            Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ (k - 1) + ax := Nat.add_le_add (Nat.le_pred_of_lt hPz.1) hA_eval
        _ = ax + (k - 1) := Nat.add_comm _ _
        _ = bx := hax
    exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hB_eval hprod)
  have hdeg_lt : Dz.natDegree < (Tz.image domain).card := by
    have hcard : n - e ≤ Tz.card := by
      simpa [hn] using hTz_card
    have hlt : bx < Tz.card := lt_of_lt_of_le hbx hcard
    have himg : (Tz.image domain).card = Tz.card :=
      Finset.card_image_of_injective _ domain.injective
    exact lt_of_le_of_lt hDz_deg (by simpa [himg] using hlt)
  have hzero : Dz = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (p := Dz) (s := Tz.image domain) hDz_eval hdeg_lt
  simpa [Dz, Pz, sub_eq_zero] using hzero

omit [DecidableEq ι] in
private theorem bchks_exists_global_affine_quotient_basic
    {k n e ax bx dz : ℕ} [NeZero k]
    (domain : ι ↪ F) (u : Fin 2 → ι → F) (δ : NNReal)
    (hn : n = Fintype.card ι) (he : e = Nat.floor (δ * n))
    (hax : ax + (k - 1) = bx) (haxle : ax ≤ bx) (hbx : bx < n - e)
    (hdz : 0 < dz)
    (A B : Polynomial (Polynomial F))
    (hA0 : A ≠ 0)
    (hA_degX : Polynomial.Bivariate.degreeX A ≤ ax)
    (hA_degY : Polynomial.Bivariate.natDegreeY A ≤ dz - 1)
    (hB_degX : Polynomial.Bivariate.degreeX B ≤ bx)
    (hB_degY : Polynomial.Bivariate.natDegreeY B ≤ dz)
    (hAB : ∀ i : ι,
      Polynomial.Bivariate.evalX (domain i) B =
        (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
          Polynomial.Bivariate.evalX (domain i) A)
    (hgood : 0 < (ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ).card)
    (hratio :
      (bx : ℚ) / (n : ℚ) +
        (dz : ℚ) /
          ((ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ).card : ℚ) < 1) :
    ∃ P : Polynomial (Polynomial F),
      ∃ Qx : Finset F,
        B = P * A ∧
        Polynomial.Bivariate.degreeX P ≤ k - 1 ∧
        Polynomial.Bivariate.natDegreeY P ≤ 1 ∧
        n - ax ≤ Qx.card ∧
        Qx ⊆ Finset.univ.map domain ∧
        ∀ x ∈ Qx,
          Polynomial.Bivariate.evalX x P = bchks_horizontal_quotient domain u x := by
  classical
  let good := ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ
  let Px : Finset F := Finset.univ.map domain
  let Py : Finset F := good
  have hnpos : 0 < n := by simp [hn]
  have : Nonempty Px := by
    apply Finset.Nonempty.to_subtype
    simp [Px]
  have : Nonempty Py := by
    apply Finset.Nonempty.to_subtype
    exact Finset.card_pos.mp (by simpa [Py, good] using hgood)
  have hcardx : (⟨n, hnpos⟩ : ℕ+) ≤ Px.card := by
    simp [Px, hn]
  have hcardy : (⟨good.card, by simpa [good] using hgood⟩ : ℕ+) ≤ Py.card := by
    simp [Py]
  have hquotx : ∀ z ∈ Py,
      (bchks_good_polynomial (k := k) domain u δ z).natDegree ≤ bx - ax ∧
      Polynomial.Bivariate.evalY z B =
        bchks_good_polynomial (k := k) domain u δ z * Polynomial.Bivariate.evalY z A := by
    intro z hz
    have hzgood : z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ := by
      simpa [Py, good] using hz
    refine ⟨?_, bchks_good_polynomial_horizontal_identity_basic domain u δ hn he hax hbx
      A B hA_degX hB_degX hAB z hzgood⟩
    have hp := (bchks_good_polynomial_spec domain u δ z hzgood).1
    have hle : (bchks_good_polynomial (k := k) domain u δ z).natDegree ≤ k - 1 :=
      Nat.le_pred_of_lt hp
    have heq : bx - ax = k - 1 := by omega
    simpa [heq] using hle
  have hquoty : ∀ x ∈ Px,
      (bchks_horizontal_quotient domain u x).natDegree ≤ dz - (dz - 1) ∧
      Polynomial.Bivariate.evalX x B =
        bchks_horizontal_quotient domain u x * Polynomial.Bivariate.evalX x A := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
    refine ⟨?_, ?_⟩
    · have hle := bchks_horizontal_quotient_nat_degree_le_one domain u (domain i)
      have heq : dz - (dz - 1) = 1 := by omega
      simpa [heq] using hle
    · simpa [bchks_horizontal_quotient_domain] using hAB i
  have hratio' :
      (bx : ℚ) / ((⟨n, hnpos⟩ : ℕ+) : ℚ) +
        (dz : ℚ) / ((⟨good.card, by simpa [good] using hgood⟩ : ℕ+) : ℚ) < 1 := by
    simpa [good] using hratio
  obtain ⟨P, hBA, hPX, hPY, ⟨Qx, hQcard, hQsub, hQeval⟩, _⟩ :=
    polishchuk_spielman
      (a_x := ax) (a_y := dz - 1) (b_x := bx) (b_y := dz)
      (n_x := ⟨n, hnpos⟩)
      (n_y := ⟨good.card, by simpa [good] using hgood⟩)
      (h_bx_ge_ax := haxle) (h_by_ge_ay := by omega)
      (A := A) (B := B) hA0 hA_degX hB_degX hA_degY hB_degY
      Px Py (bchks_good_polynomial (k := k) domain u δ)
      (bchks_horizontal_quotient domain u) hcardx hcardy hquotx hquoty hratio'
  have hPX' : Polynomial.Bivariate.degreeX P ≤ k - 1 := by
    have heq : bx - ax = k - 1 := by omega
    simpa [heq] using hPX
  have hPY' : Polynomial.Bivariate.natDegreeY P ≤ 1 := by
    have heq : dz - (dz - 1) = 1 := by omega
    simpa [heq] using hPY
  exact ⟨P, Qx, hBA, hPX', hPY', hQcard, by simpa [Px] using hQsub,
    by simpa using hQeval⟩

private theorem bchks_ps_ratio_lt_one_basic (n bx dz a : ℕ) (δ : ℝ)
    (hbx : (bx : ℝ) / n < 1 - δ)
    (hdz : (dz : ℝ) / a < δ) :
    (bx : ℚ) / (n : ℚ) + (dz : ℚ) / (a : ℚ) < 1 := by
  have hreal : (bx : ℝ) / n + (dz : ℝ) / a < 1 := by linarith
  apply (Rat.cast_lt (K := ℝ)).mp
  norm_num
  exact hreal

open scoped NNReal in
private theorem bchks_second_threshold_card_facts (a : ℕ) (δ_fld δ_int : ℝ≥0)
    (hlt : δ_fld < δ_int)
    (hsecond : (δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ)) < (a : ℝ)) :
    1 < a ∧
      (a : ℝ) * (δ_fld : ℝ) < ((a : ℝ) - 1) * (δ_int : ℝ) := by
  have hltR : (δ_fld : ℝ) < (δ_int : ℝ) := by exact_mod_cast hlt
  have hden : 0 < (δ_int : ℝ) - (δ_fld : ℝ) := sub_pos.mpr hltR
  have hden_le : (δ_int : ℝ) - (δ_fld : ℝ) ≤ (δ_int : ℝ) := by
    exact sub_le_self _ δ_fld.coe_nonneg
  have honeR : (1 : ℝ) < a := by
    calc
      (1 : ℝ) = ((δ_int : ℝ) - (δ_fld : ℝ)) /
          ((δ_int : ℝ) - (δ_fld : ℝ)) := by
            rw [div_self (ne_of_gt hden)]
      _ ≤ (δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ)) := by
            exact div_le_div_of_nonneg_right hden_le hden.le
      _ < (a : ℝ) := hsecond
  have ha : 1 < a := by exact_mod_cast honeR
  have hmul : (δ_int : ℝ) < (a : ℝ) * ((δ_int : ℝ) - (δ_fld : ℝ)) :=
    (div_lt_iff₀ hden).mp hsecond
  refine ⟨ha, ?_⟩
  nlinarith

private theorem mem_bchks_pair_disagreements {ι K : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq K] (u p : Fin 2 → ι → K) (i : ι) :
    i ∈ bchks_pair_disagreements u p ↔ u 0 i ≠ p 0 i ∨ u 1 i ≠ p 1 i := by
  simp only [bchks_pair_disagreements, Finset.mem_union, Code.mem_disagreementCols]

private theorem affine_hamming_dist_le_pair_disagreements_card {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] [DecidableEq K]
    (u p : Fin 2 → ι → K) (z : K) :
    hammingDist (u 0 + z • u 1) (p 0 + z • p 1) ≤
      (bchks_pair_disagreements u p).card := by
  rw [Code.hammingDist_eq_disagreementCols_card]
  apply Finset.card_le_card
  intro i hi
  rw [mem_bchks_pair_disagreements]
  by_contra hnot
  simp only [not_or] at hnot
  have h0 : u 0 i = p 0 i := of_not_not hnot.1
  have h1 : u 1 i = p 1 i := of_not_not hnot.2
  apply (Code.mem_disagreementCols.mp hi)
  simp [Pi.add_apply, Pi.smul_apply, h0, h1]

open scoped BigOperators in
private theorem bchks_affine_close_double_count {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [DecidableEq K] (good : Finset K) (u p : Fin 2 → ι → K) (e : ℕ)
    (_hgood : 1 < good.card)
    (hclose : ∀ z ∈ good,
      hammingDist (u 0 + z • u 1) (p 0 + z • p 1) ≤ e) :
    (good.card - 1) * (bchks_pair_disagreements u p).card ≤ good.card * e := by
  classical
  let D : Finset ι := bchks_pair_disagreements u p
  let count : ι → ℕ := fun i =>
    (good.filter (fun z =>
      (u 0 + z • u 1) i ≠ (p 0 + z • p 1) i)).card
  have hsum_upper :
      good.sum (fun z => hammingDist (u 0 + z • u 1) (p 0 + z • p 1)) ≤
        good.card * e := by
    calc
      good.sum (fun z => hammingDist (u 0 + z • u 1) (p 0 + z • p 1))
          ≤ good.sum (fun _ => e) := Finset.sum_le_sum (fun z hz => hclose z hz)
      _ = good.card * e := by simp
  have hsum_eq :
      good.sum (fun z => hammingDist (u 0 + z • u 1) (p 0 + z • p 1)) =
        Finset.univ.sum count := by
    calc
      good.sum (fun z => hammingDist (u 0 + z • u 1) (p 0 + z • p 1))
          = good.sum (fun z =>
              (Finset.univ.filter (fun i : ι =>
                (u 0 + z • u 1) i ≠ (p 0 + z • p 1) i)).card) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Code.hammingDist_eq_disagreementCols_card]
              rfl
      _ = good.sum (fun z => ∑ i : ι,
              if (u 0 + z • u 1) i ≠ (p 0 + z • p 1) i then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Finset.card_filter]
      _ = ∑ i : ι, good.sum (fun z =>
              if (u 0 + z • u 1) i ≠ (p 0 + z • p 1) i then 1 else 0) := by
              rw [Finset.sum_comm]
      _ = Finset.univ.sum count := by
              apply Finset.sum_congr rfl
              intro i hi
              unfold count
              rw [Finset.card_filter]
  have heq_card_le_one (i : ι) (hiD : i ∈ D) :
      (good.filter (fun z =>
        (u 0 + z • u 1) i = (p 0 + z • p 1) i)).card ≤ 1 := by
    have hi : u 0 i ≠ p 0 i ∨ u 1 i ≠ p 1 i := by
      simpa [D] using (mem_bchks_pair_disagreements u p i).mp hiD
    by_cases hslope : u 1 i = p 1 i
    · have hbase : u 0 i ≠ p 0 i := by
        rcases hi with h0 | h1
        · exact h0
        · exact (h1 hslope).elim
      have hempty : good.filter (fun z =>
          (u 0 + z • u 1) i = (p 0 + z • p 1) i) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨hzgood, heq⟩
        apply hbase
        have heq' : u 0 i + z * u 1 i = p 0 i + z * p 1 i := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using heq
        calc
          u 0 i = (u 0 i + z * u 1 i) - z * u 1 i := by ring
          _ = (p 0 i + z * p 1 i) - z * u 1 i := by rw [heq']
          _ = p 0 i := by rw [hslope]; ring
      rw [hempty]
      simp
    · exact Finset.card_le_one.mpr fun z₁ hz₁ z₂ hz₂ => by
        have heq₁ : u 0 i + z₁ * u 1 i = p 0 i + z₁ * p 1 i := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
            (Finset.mem_filter.mp hz₁).2
        have heq₂ : u 0 i + z₂ * u 1 i = p 0 i + z₂ * p 1 i := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
            (Finset.mem_filter.mp hz₂).2
        have hmul : (z₁ - z₂) * (u 1 i - p 1 i) = 0 := by
          calc
            (z₁ - z₂) * (u 1 i - p 1 i) =
                ((u 0 i + z₁ * u 1 i) - (p 0 i + z₁ * p 1 i)) -
                ((u 0 i + z₂ * u 1 i) - (p 0 i + z₂ * p 1 i)) := by ring
            _ = 0 := by rw [sub_eq_zero.mpr heq₁, sub_eq_zero.mpr heq₂]; ring
        rcases mul_eq_zero.mp hmul with hz | hs
        · exact sub_eq_zero.mp hz
        · exact (hslope (sub_eq_zero.mp hs)).elim
  have hcount_lower (i : ι) (hiD : i ∈ D) : good.card - 1 ≤ count i := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := good) (fun z => (u 0 + z • u 1) i = (p 0 + z • p 1) i)
    have heq := heq_card_le_one i hiD
    have hpart' :
        (good.filter (fun z =>
          (u 0 + z • u 1) i = (p 0 + z • p 1) i)).card + count i = good.card := by
      simpa [count] using hpart
    omega
  have hsum_lower :
      (good.card - 1) * D.card ≤ Finset.univ.sum count := by
    calc
      (good.card - 1) * D.card = D.sum (fun _ => good.card - 1) := by
        simp [Nat.mul_comm]
      _ ≤ D.sum count := Finset.sum_le_sum (fun i hi => hcount_lower i hi)
      _ ≤ Finset.univ.sum count :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ D)
  calc
    (good.card - 1) * (bchks_pair_disagreements u p).card =
        (good.card - 1) * D.card := by rfl
    _ ≤ Finset.univ.sum count := hsum_lower
    _ = good.sum (fun z => hammingDist (u 0 + z • u 1) (p 0 + z • p 1)) := hsum_eq.symm
    _ ≤ good.card * e := hsum_upper

omit [Fintype F] in
private theorem bchks_affine_pair_seed_of_global_quotient {k n ax : ℕ} [NeZero k]
    (domain : ι ↪ F) (u : Fin 2 → ι → F)
    (hn : n = Fintype.card ι)
    (P : Polynomial (Polynomial F)) (Qx : Finset F)
    (hPX : Polynomial.Bivariate.degreeX P ≤ k - 1)
    (hQcard : n - ax ≤ Qx.card)
    (hQsub : Qx ⊆ Finset.univ.map domain)
    (hQeval : ∀ x ∈ Qx,
      Polynomial.Bivariate.evalX x P = bchks_horizontal_quotient domain u x) :
    ∃ p : Fin 2 → ι → F,
      (∀ j, p j ∈ ReedSolomon.code domain k) ∧
      (bchks_pair_disagreements u p).card ≤ ax := by
  classical
  let S0 : Finset ι := Qx.preimage domain domain.injective.injOn
  have hmap : S0.map domain = Qx := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact Finset.mem_preimage.mp hi
    · intro hx
      rcases Finset.mem_map.mp (hQsub hx) with ⟨i, -, rfl⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_preimage.mpr hx, rfl⟩
  have hScard : S0.card = Qx.card := by
    calc
      S0.card = (S0.map domain).card := by symm; simp
      _ = Qx.card := by rw [hmap]
  let p : Fin 2 → ι → F := fun j => (P.coeff (j : ℕ)).eval ∘ domain
  have hp_mem (j : Fin 2) : p j ∈ ReedSolomon.code domain k := by
    have hcoeff : (P.coeff (j : ℕ)).natDegree ≤ k - 1 :=
      le_trans (Polynomial.Bivariate.coeff_natDegree_le_degreeX P (j : ℕ)) hPX
    have hlt : (P.coeff (j : ℕ)).natDegree < k :=
      lt_of_le_of_lt hcoeff (Nat.pred_lt (NeZero.ne k))
    exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
      (P.coeff (j : ℕ)) hlt (by intro i; rfl)
  have hagree (j : Fin 2) (i : ι) (hi : i ∈ S0) : p j i = u j i := by
    have hiQ : domain i ∈ Qx := Finset.mem_preimage.mp hi
    have hEval := hQeval (domain i) hiQ
    rw [bchks_horizontal_quotient_domain] at hEval
    fin_cases j
    · have hc := congrArg (fun q : Polynomial F => q.coeff 0) hEval
      simpa [p, Polynomial.Bivariate.evalX, Polynomial.coeff] using hc
    · have hc := congrArg (fun q : Polynomial F => q.coeff 1) hEval
      simpa [p, Polynomial.Bivariate.evalX, Polynomial.coeff] using hc
  have hDsub : bchks_pair_disagreements u p ⊆ S0ᶜ := by
    intro i hiD
    rw [Finset.mem_compl]
    intro hiS
    rcases (mem_bchks_pair_disagreements u p i).mp hiD with h0 | h1
    · exact h0 (hagree 0 i hiS).symm
    · exact h1 (hagree 1 i hiS).symm
  have hcomp : S0ᶜ.card ≤ ax := by
    rw [Finset.card_compl]
    have hS : n - ax ≤ S0.card := by simpa [hScard] using hQcard
    rw [← hn]
    omega
  exact ⟨p, hp_mem, le_trans (Finset.card_le_card hDsub) hcomp⟩

private theorem joint_proximity_of_pair_disagreements_card_le {ι K : Type} [Fintype ι]
    [Nonempty ι] [DecidableEq ι] [Field K] [DecidableEq K]
    (C : LinearCode ι K) (u p : Fin 2 → ι → K) (δ : NNReal)
    (hp : ∀ j, p j ∈ C)
    (hD : (bchks_pair_disagreements u p).card ≤ Nat.floor (δ * Fintype.card ι)) :
    Code.jointProximity (C := (C : Set (ι → K))) (u := u) δ := by
  classical
  rw [← Code.jointAgreement_iff_jointProximity]
  let D := bchks_pair_disagreements u p
  refine ⟨Dᶜ, (Code.relDist_floor_bound_iff_complement_bound _ _ _).mp ?_, p, ?_⟩
  · rw [Finset.card_compl]
    exact Nat.sub_le_sub_left (by simpa only [D] using hD) _
  · intro j
    refine ⟨hp j, ?_⟩
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    have hiD : i ∉ D := by simpa only [Finset.mem_compl] using hi
    simp only [D, mem_bchks_pair_disagreements, not_or] at hiD
    fin_cases j
    · exact (of_not_not hiD.1).symm
    · exact (of_not_not hiD.2).symm

open scoped NNReal in
private theorem affine_many_close_implies_joint_proximity {ι K : Type} [Fintype ι]
    [Nonempty ι] [Field K] [DecidableEq K]
    (C : LinearCode ι K) (good : Finset K) (u p : Fin 2 → ι → K)
    (δ_fld δ_int : ℝ≥0)
    (hp : ∀ j, p j ∈ C)
    (hgood : 1 < good.card)
    (hclose : ∀ z ∈ good,
      hammingDist (u 0 + z • u 1) (p 0 + z • p 1) ≤
        Nat.floor (δ_fld * Fintype.card ι))
    (hgap : (good.card : ℝ) * (δ_fld : ℝ) <
      ((good.card : ℝ) - 1) * (δ_int : ℝ)) :
    Code.jointProximity (C := (C : Set (ι → K))) (u := u) δ_int := by
  classical
  let e : ℕ := Nat.floor (δ_fld * Fintype.card ι)
  let D : Finset ι := bchks_pair_disagreements u p
  have hdc : (good.card - 1) * D.card ≤ good.card * e := by
    simpa [D, e] using bchks_affine_close_double_count good u p e hgood
      (by simpa [e] using hclose)
  have heNN : (e : ℝ≥0) ≤ δ_fld * Fintype.card ι := by
    simpa [e] using (Nat.floor_le (show (0 : ℝ≥0) ≤ δ_fld * Fintype.card ι by positivity))
  have heR : (e : ℝ) ≤ (δ_fld : ℝ) * Fintype.card ι := by
    exact_mod_cast heNN
  have ha1 : 1 ≤ good.card := Nat.le_of_lt hgood
  have hpred_cast : ((good.card - 1 : ℕ) : ℝ) = (good.card : ℝ) - 1 := by
    rw [Nat.cast_sub ha1]
    norm_num
  have hdcR :
      ((good.card : ℝ) - 1) * (D.card : ℝ) ≤
        (good.card : ℝ) * (e : ℝ) := by
    have h := show (((good.card - 1) * D.card : ℕ) : ℝ) ≤
        ((good.card * e : ℕ) : ℝ) by exact_mod_cast hdc
    push_cast at h
    simpa [hpred_cast] using h
  have hnR_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hae : (good.card : ℝ) * (e : ℝ) ≤
      (good.card : ℝ) * ((δ_fld : ℝ) * Fintype.card ι) := by
    exact mul_le_mul_of_nonneg_left heR (by positivity)
  have hgapn :
      (good.card : ℝ) * ((δ_fld : ℝ) * Fintype.card ι) <
        ((good.card : ℝ) - 1) * ((δ_int : ℝ) * Fintype.card ι) := by
    nlinarith [mul_lt_mul_of_pos_right hgap hnR_pos]
  have hprod :
      ((good.card : ℝ) - 1) * (D.card : ℝ) <
        ((good.card : ℝ) - 1) * ((δ_int : ℝ) * Fintype.card ι) :=
    lt_of_le_of_lt (le_trans hdcR hae) hgapn
  have hfactor : (0 : ℝ) < (good.card : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hgood)
  have hDlt : (D.card : ℝ) < (δ_int : ℝ) * Fintype.card ι :=
    lt_of_mul_lt_mul_left hprod hfactor.le
  have hDNN : (D.card : ℝ≥0) ≤ δ_int * Fintype.card ι := by
    exact_mod_cast (le_of_lt hDlt)
  have hDfloor : D.card ≤ Nat.floor (δ_int * Fintype.card ι) :=
    Nat.le_floor hDNN
  exact joint_proximity_of_pair_disagreements_card_le C u p δ_int hp
    (by simpa [D] using hDfloor)

open scoped NNReal in
private theorem rs_all_good_close_to_affine_pair
    {k n e gap ax bx dz : ℕ} [NeZero k]
    (domain : ι ↪ F) (u p : Fin 2 → ι → F) (δ : ℝ≥0)
    (hn : n = Fintype.card ι)
    (hfacts : BchksParameterFacts n k e gap ax bx dz δ)
    (hp : ∀ j, p j ∈ ReedSolomon.code domain k)
    (hD : (bchks_pair_disagreements u p).card ≤ ax) :
    ∀ z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ,
      hammingDist (u 0 + z • u 1) (p 0 + z • p 1) ≤ e := by
  intro z hz
  let Pz := bchks_good_polynomial (k := k) domain u δ z
  have hPz_close : hammingDist (u 0 + z • u 1) (Pz.eval ∘ domain) ≤ e := by
    simpa [Pz, hfacts.e_eq_floor, hn] using
      (bchks_good_polynomial_spec domain u δ z hz).2
  have hPz_mem : Pz.eval ∘ domain ∈ ReedSolomon.code domain k := by
    simpa [Pz] using bchks_good_polynomial_mem_code domain u δ z hz
  have hAff_mem : p 0 + z • p 1 ∈ ReedSolomon.code domain k := by
    exact (ReedSolomon.code domain k).add_mem (hp 0)
      ((ReedSolomon.code domain k).smul_mem z (hp 1))
  have hAff_close : hammingDist (u 0 + z • u 1) (p 0 + z • p 1) ≤ ax :=
    le_trans (affine_hamming_dist_le_pair_disagreements_card u p z) hD
  have htri : hammingDist (Pz.eval ∘ domain) (p 0 + z • p 1) ≤ e + ax := by
    calc
      hammingDist (Pz.eval ∘ domain) (p 0 + z • p 1) ≤
          hammingDist (Pz.eval ∘ domain) (u 0 + z • u 1) +
            hammingDist (u 0 + z • u 1) (p 0 + z • p 1) :=
        hammingDist_triangle _ _ _
      _ = hammingDist (u 0 + z • u 1) (Pz.eval ∘ domain) +
            hammingDist (u 0 + z • u 1) (p 0 + z • p 1) := by
          rw [hammingDist_comm (Pz.eval ∘ domain) (u 0 + z • u 1)]
      _ ≤ e + ax := Nat.add_le_add hPz_close hAff_close
  have hk_card : k ≤ Fintype.card ι := by
    have hm := hfacts.k_two_e_margin
    rw [← hn]
    omega
  have hmin : Code.minDist (ReedSolomon.code domain k : Set (ι → F)) = n - k + 1 := by
    simpa [hn] using
      (ReedSolomon.minDist_of_le (α := domain) (n := k) hk_card)
  have heq : Pz.eval ∘ domain = p 0 + z • p 1 := by
    by_contra hne
    have hmd := Code.minDist_le_dist hPz_mem hAff_mem hne
    rw [hmin] at hmd
    have herr := hfacts.error_add_ax
    omega
  rw [← heq]
  exact hPz_close

open scoped NNReal in
omit [DecidableEq ι] in
private theorem rs_exists_affine_pair_of_many_good_coeffs_pos
    {k n e gap ax bx dz : ℕ} [NeZero k]
    (domain : ι ↪ F) (u : Fin 2 → ι → F) (δ : ℝ≥0)
    (hn : n = Fintype.card ι)
    (hfacts : BchksParameterFacts n k e gap ax bx dz δ)
    (hfirst :
      (1 - (k : ℝ) / n - (δ : ℝ)) /
          ((δ : ℝ) * (1 - (k : ℝ) / n - 2 * (δ : ℝ))) <
        ((ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ).card : ℝ)) :
    ∃ p : Fin 2 → ι → F,
      (∀ j, p j ∈ ReedSolomon.code domain k) ∧
      ∀ z ∈ ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ,
        hammingDist (u 0 + z • u 1) (p 0 + z • p 1) ≤ e := by
  classical
  let good := ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ
  have hgoodR : (0 : ℝ) < good.card := by
    exact lt_trans hfacts.first_threshold_pos (by simpa [good] using hfirst)
  have hgood : 0 < good.card := by exact_mod_cast hgoodR
  have hdeltaR : (0 : ℝ) < δ := by exact_mod_cast hfacts.delta_pos
  have hdz_delta_card : (dz : ℝ) / (δ : ℝ) < (good.card : ℝ) :=
    lt_of_le_of_lt hfacts.dz_div_delta_le (by simpa [good] using hfirst)
  have hdz_card : (dz : ℝ) / (good.card : ℝ) < (δ : ℝ) := by
    rw [div_lt_iff₀ hgoodR]
    have hmul : (dz : ℝ) < (good.card : ℝ) * (δ : ℝ) := by
      exact (div_lt_iff₀ hdeltaR).mp hdz_delta_card
    simpa [mul_comm] using hmul
  have hratio :
      (bx : ℚ) / (n : ℚ) + (dz : ℚ) / (good.card : ℚ) < 1 :=
    bchks_ps_ratio_lt_one_basic n bx dz good.card (δ : ℝ)
      hfacts.bx_ratio_lt hdz_card
  obtain ⟨A, B, hA0, hAX, hAY, hBX, hBY, hAB⟩ :=
    rs_exists_oversized_bivariate_ab domain u n k e gap ax bx dz δ hn hfacts
  obtain ⟨P, Qx, hBA, hPX, hPY, hQcard, hQsub, hQeval⟩ :=
    bchks_exists_global_affine_quotient_basic
      (k := k) (n := n) (e := e) (ax := ax) (bx := bx) (dz := dz)
      domain u δ hn hfacts.e_eq_floor hfacts.ax_add_pred_k hfacts.ax_le_bx
      hfacts.bx_lt_remaining hfacts.dz_pos A B hA0 hAX hAY hBX hBY hAB
      (by simpa [good] using hgood) (by simpa [good] using hratio)
  obtain ⟨p, hp, hD⟩ :=
    bchks_affine_pair_seed_of_global_quotient
      (k := k) (n := n) (ax := ax) domain u hn P Qx hPX hQcard hQsub hQeval
  refine ⟨p, hp, ?_⟩
  exact rs_all_good_close_to_affine_pair domain u p δ hn hfacts hp hD

open scoped NNReal in
omit [DecidableEq ι] in
private theorem rs_zero_pair_close_of_good_coeff (domain : ι ↪ F)
    (u : Fin 2 → ι → F) (δ : ℝ≥0) (z : F)
    (hz : z ∈ ProximityGap.RS_goodCoeffs (deg := 0) (domain := domain) u δ) :
    hammingDist (u 0 + z • u 1) (0 : ι → F) ≤
      Nat.floor (δ * Fintype.card ι) := by
  classical
  have hz_rel : δᵣ(u 0 + z • u 1, ReedSolomon.code domain 0) ≤ δ := by
    simpa [ProximityGap.RS_goodCoeffs] using (Finset.mem_filter.mp hz).2
  have hz_zero : δᵣ(u 0 + z • u 1, (0 : ι → F)) ≤ δ := by
    rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist] at hz_rel
    rcases hz_rel with ⟨w, hwmem, hwdist⟩
    have hw : w = 0 := by simpa [ReedSolomon.code_zero] using hwmem
    simpa [hw] using hwdist
  rw [Code.pairRelDist_le_iff_pairDist_le] at hz_zero
  exact hz_zero

open scoped NNReal in
omit [DecidableEq ι] in
private theorem rs_exists_affine_pair_of_many_good_coeffs_zero (domain : ι ↪ F)
    (u : Fin 2 → ι → F) (δ : ℝ≥0) :
    ∃ p : Fin 2 → ι → F,
      (∀ j, p j ∈ ReedSolomon.code domain 0) ∧
      ∀ z ∈ ProximityGap.RS_goodCoeffs (deg := 0) (domain := domain) u δ,
        hammingDist (u 0 + z • u 1) (p 0 + z • p 1) ≤
          Nat.floor (δ * Fintype.card ι) := by
  classical
  let p : Fin 2 → ι → F := fun _ => 0
  refine ⟨p, ?_, ?_⟩
  · intro j
    exact (ReedSolomon.code domain 0).zero_mem
  · intro z hz
    simpa [p] using rs_zero_pair_close_of_good_coeff domain u δ z hz

open scoped NNReal in
omit [DecidableEq ι] in
private theorem rs_good_coeffs_card_le_max_threshold_of_not_joint_proximity
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (u : Fin 2 → ι → F)
    (h_ud : (δ_fld : ℝ) ≤
      (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
      / Fintype.card ι / 3 ≤ δ_fld)
    (h_lt : δ_fld < δ_int)
    (hjoint : ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int) :
    ((ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ_fld).card : ℝ) ≤
      max
        ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
          ((δ_fld : ℝ) *
            (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ))))
        ((δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ))) := by
  classical
  let good := ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ_fld
  let T₁ : ℝ :=
    (1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
      ((δ_fld : ℝ) *
        (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)))
  let T₂ : ℝ := (δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ))
  change (good.card : ℝ) ≤ max T₁ T₂
  by_contra hnot
  have hmax : max T₁ T₂ < (good.card : ℝ) := lt_of_not_ge hnot
  have hfirst : T₁ < (good.card : ℝ) := lt_of_le_of_lt (le_max_left T₁ T₂) hmax
  have hsecond : T₂ < (good.card : ℝ) := lt_of_le_of_lt (le_max_right T₁ T₂) hmax
  have hsecond' :
      (δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ)) < (good.card : ℝ) := by
    simpa [T₂] using hsecond
  obtain ⟨hgood, hgap⟩ :=
    bchks_second_threshold_card_facts good.card δ_fld δ_int h_lt hsecond'
  by_cases hk0 : k = 0
  · subst k
    obtain ⟨p, hp, hclose⟩ :=
      rs_exists_affine_pair_of_many_good_coeffs_zero domain u δ_fld
    apply hjoint
    exact affine_many_close_implies_joint_proximity
      (ReedSolomon.code domain 0) good u p δ_fld δ_int hp hgood
      (by simpa [good] using hclose) hgap
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let : NeZero k := ⟨hk0⟩
    let n : ℕ := Fintype.card ι
    let e : ℕ := Nat.floor (δ_fld * n)
    let gap : ℕ := n - k - 2 * e + 1
    let ax : ℕ := n - k - e
    let bx : ℕ := n - e - 1
    let dz : ℕ := bchks_dz n k e
    have hfacts : BchksParameterFacts n k e gap ax bx dz δ_fld := by
      simpa [n, e, gap, ax, bx, dz] using
        bchks_parameter_facts_of_target_hypotheses domain k δ_fld hk h_ud h_dmin
    have hfirst' :
        (1 - (k : ℝ) / n - (δ_fld : ℝ)) /
            ((δ_fld : ℝ) * (1 - (k : ℝ) / n - 2 * (δ_fld : ℝ))) <
          (good.card : ℝ) := by
      simpa [T₁, n] using hfirst
    obtain ⟨p, hp, hclose⟩ :=
      rs_exists_affine_pair_of_many_good_coeffs_pos
        (k := k) (n := n) (e := e) (gap := gap) (ax := ax) (bx := bx) (dz := dz)
        domain u δ_fld (by rfl) hfacts (by simpa [good] using hfirst')
    apply hjoint
    exact affine_many_close_implies_joint_proximity
      (ReedSolomon.code domain k) good u p δ_fld δ_int hp hgood
      (by
        intro z hz
        simpa [good, e, n] using hclose z hz)
      hgap

open scoped NNReal ProbabilityTheory in
omit [DecidableEq ι] in
private theorem rs_fold_probability_le_bound_of_not_joint_proximity
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (h_ud : (δ_fld : ℝ) ≤
      (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
      / Fintype.card ι / 3 ≤ δ_fld)
    (h_lt : δ_fld < δ_int)
    (u : Fin 2 → ι → F)
    (hjoint : ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int) :
    Pr_{let z ← $ᵖ F}[
      δᵣ(u 0 + z • u 1, ReedSolomon.code domain k) ≤ δ_fld] ≤
      ENNReal.ofReal
        (max
          ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
            ((δ_fld : ℝ) *
              (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
              Fintype.card F))
          ((δ_int : ℝ) /
            (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))) := by
  classical
  let good := ProximityGap.RS_goodCoeffs (deg := k) (domain := domain) u δ_fld
  let T₁ : ℝ :=
    (1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
      ((δ_fld : ℝ) *
        (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)))
  let T₂ : ℝ := (δ_int : ℝ) / ((δ_int : ℝ) - (δ_fld : ℝ))
  have hcard : (good.card : ℝ) ≤ max T₁ T₂ := by
    simpa [good, T₁, T₂] using
      rs_good_coeffs_card_le_max_threshold_of_not_joint_proximity
        domain k δ_fld δ_int u h_ud h_dmin h_lt hjoint
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  change (good.card : ℝ) / Fintype.card F ≤
    max
      ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
        ((δ_fld : ℝ) *
          (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
          Fintype.card F))
      ((δ_int : ℝ) /
        (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F))
  calc
    (good.card : ℝ) / Fintype.card F ≤
        max T₁ T₂ / Fintype.card F :=
      div_le_div_of_nonneg_right hcard hq.le
    _ = max (T₁ / Fintype.card F) (T₂ / Fintype.card F) := by
      symm
      exact max_div_div_right hq.le T₁ T₂
    _ = max
        ((1 - (k : ℝ) / Fintype.card ι - (δ_fld : ℝ)) /
          ((δ_fld : ℝ) *
            (1 - (k : ℝ) / Fintype.card ι - 2 * (δ_fld : ℝ)) *
            Fintype.card F))
        ((δ_int : ℝ) /
          (((δ_int : ℝ) - (δ_fld : ℝ)) * Fintype.card F)) := by
      apply congrArg₂ max
      · simp only [T₁]
        rw [div_div]
      · simp only [T₂]
        rw [div_div]

open scoped NNReal in
open scoped ProbabilityTheory in
omit [DecidableEq ι] in
/-- Bounds Reed--Solomon CA error when `δ_fld` lies between one third of the minimum
distance and the finite-length unique-decoding radius, and `δ_fld < δ_int`. -/
theorem rs_epsCa_le_in_unique_decoding_range
    (domain : ι ↪ F) (k : ℕ) (δ_fld δ_int : ℝ≥0)
    (_h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (_h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (_h_lt : δ_fld < δ_int) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((δ_int : ℝ) / ((δ_int - δ_fld) * Fintype.card F))
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int ≤
      ENNReal.ofReal bound := by
  classical
  dsimp
  unfold epsCa
  refine iSup_le fun u => ?_
  by_cases hj : Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ_int
  · rw [if_pos hj]
    exact zero_le
  · rw [if_neg hj]
    exact rs_fold_probability_le_bound_of_not_joint_proximity
      domain k δ_fld δ_int _h_ud _h_dmin _h_lt u hj

end ReedSolomon

end CodingTheory

set_option linter.style.longFile 1800

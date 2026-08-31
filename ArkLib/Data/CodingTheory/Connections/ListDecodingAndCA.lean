/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA.BCHKS25
import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA.CS25
import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA.GCXK25
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Connections between list decoding and correlated agreement

This module relates the maximized list size `Code.Lambda` to the numeric CA and MCA errors. It
contains source-facing bounds for general linear and Reed--Solomon codes, together with one
in-tree real-radius corollary of the integer-radius CS25 statement.

## Main statements

- `linear_mcaError_le_of_Lambda_le` turns a list-size bound below the relative minimum distance
  into an affine-line MCA bound.
- `rs_Lambda_le_card_of_epsCa_lt` bounds an RS list by the field size from a small CA error.
- `rs_Lambda_extended_le_of_epsCa_int_radius` is the integer-radius CS25 bound for a related RS
  code; `rs_Lambda_extended_le_of_epsCa` is its real-radius corollary.
- `rs_epsCa_large_below_johnson_radius` separates list decoding from CA for characteristic-two
  Reed--Solomon codes.

Real-valued numeric bounds are embedded into `ENNReal` with `ENNReal.ofReal`. MCA statements use
the real-radius `mcaError`; CA statements use the nonnegative-radius `epsCa` interface.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [GCXK25] Theorem 3 in their paper.
- [BCHKS25] Theorem 1.9.
- [CS25] Theorem 2.
- [BenSassonGKS20] Lemma 3.3.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code CoreDefinitions ProximityGap

section ListImpliesMCA

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

end ListImpliesMCA

section CAImpliesList

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `ε_ca` is never `⊤`: each branch of the supremum is `0` or a `PMF` probability
(`≤ 1`). Derivation infrastructure for `rs_Lambda_extended_le_of_epsCa`. -/
private lemma epsCa_ne_top (C : Set (ι → F)) (δ_fld δ_int : ℝ≥0) :
    epsCa (F := F) (A := F) C δ_fld δ_int ≠ ⊤ := by
  classical
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  unfold epsCa
  refine iSup_le fun u => ?_
  split_ifs
  · exact zero_le_one
  · exact PMF.coe_le_one _ _

/-- `Nat.floor` commutes with the `ℝ≥0 → ℝ` coercion. Derivation infrastructure for
`rs_Lambda_extended_le_of_epsCa`. -/
private lemma nat_floor_coe_nnreal (x : ℝ≥0) : Nat.floor (x : ℝ) = Nat.floor x :=
  le_antisymm
    (Nat.le_floor (by exact_mod_cast Nat.floor_le x.coe_nonneg))
    (Nat.le_floor (by exact_mod_cast Nat.floor_le (zero_le (α := ℝ≥0))))

/-- `Λ(C, ·)` is `1/n`-quantised: relative Hamming distance takes values in
`{0, 1/n, …, 1}`, so the list size at a real radius `δ ≥ 0` equals the list size at the
grid point `⌊δ·n⌋/n`. `Lambda` analogue of `ProximityGap.epsCa_eq_of_floor_eq`;
derivation infrastructure for `rs_Lambda_extended_le_of_epsCa`. -/
private lemma Lambda_eq_floor_div_card (C : Set (ι → F)) {δ : ℝ} (hδ : 0 ≤ δ) :
    Lambda C δ
      = Lambda C ((⌊δ * Fintype.card ι⌋₊ : ℝ) / Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos (α := ι)
  have hset : ∀ y : ι → F,
      closeCodewordsRel C y δ
        = closeCodewordsRel C y ((⌊δ * Fintype.card ι⌋₊ : ℝ) / Fintype.card ι) := by
    intro y
    ext c
    simp only [closeCodewordsRel, relHammingBall, Set.mem_ofPred_eq, and_congr_right_iff,
      Code.relHammingDist]
    intro _
    push_cast
    rw [div_le_iff₀ hn, div_le_iff₀ hn, div_mul_cancel₀ _ hn.ne', Nat.cast_le,
      ← Nat.le_floor_iff (by positivity)]
  unfold Lambda
  exact iSup_congr fun y => by rw [hset y]

/-- A real-radius corollary of `rs_Lambda_extended_le_of_epsCa_int_radius`. For
`δ ∈ (0, (n-k-1)/n)` and `η ∈ [0,1)`, if

  `ε_ca(C, δ) ≤ η · (1/k - n/(k·|F|))`

then `Λ(RS(k+1), δ) ≤ ⌈|F|/(1-η) · ε_ca(C, δ)⌉`. The proof uses the `1/n` quantization
of `epsCa` and `Lambda`. The strict radius bound and `n < |F|` ensure that the integer theorem's
radius and denominator hypotheses hold. -/
theorem rs_Lambda_extended_le_of_epsCa
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (η : ℝ)
    (hk_pos : 0 < k)
    (hδ_pos : 0 < δ)
    (hδ_radius : δ < ((Fintype.card ι : ℝ) - k - 1) / Fintype.card ι)
    (_hη_lo : 0 ≤ η) (hη_lt : η < 1)
    (hn_lt_F : Fintype.card ι < Fintype.card F)
    (hε_ca :
        (epsCa (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            δ.toNNReal δ.toNNReal).toReal ≤
          η * (1 / k - Fintype.card ι / (k * Fintype.card F))) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ ≤
      (Nat.ceil
        ((Fintype.card F : ℝ) / (1 - η)
          * (epsCa (F := F) (A := F)
                ((ReedSolomon.code domain k : Set (ι → F)))
                δ.toNNReal δ.toNNReal).toReal) : ℕ∞) := by
  classical
  set C : Set (ι → F) := (ReedSolomon.code domain k : Set (ι → F)) with hC
  set ε : ℝ := (epsCa (F := F) (A := F) C δ.toNNReal δ.toNNReal).toReal with hε
  set n : ℕ := Fintype.card ι with hn
  set q : ℕ := Fintype.card F with hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos (α := ι)
  have hqR : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos (α := F)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hX : (0 : ℝ) < (q : ℝ) - n := by
    have : (n : ℝ) < q := by exact_mod_cast hn_lt_F
    linarith
  have hη1 : (0 : ℝ) < 1 - η := by linarith
  have hε_nonneg : 0 ≤ ε := ENNReal.toReal_nonneg
  -- The tex margin `1/k - n/(kq)` is the source margin `(q-n)/(kq)`.
  have hmargin : η * (1 / (k : ℝ) - n / (k * q)) = η * (((q : ℝ) - n) / (k * q)) := by
    field_simp
  have hε_le : ε ≤ η * (((q : ℝ) - n) / (k * q)) := hmargin ▸ hε_ca
  have hε_lt : ε < ((q : ℝ) - n) / (k * q) := by
    refine lt_of_le_of_lt hε_le ?_
    have hpos : (0 : ℝ) < ((q : ℝ) - n) / (k * q) := by positivity
    nlinarith [mul_pos (sub_pos.mpr hη_lt) hpos]
  -- The integer radius `f := ⌊δ·n⌋` is in the source regime `f < n - k - 1`.
  set f : ℕ := ⌊δ * n⌋₊ with hf
  have hf_le : (f : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hf_lt : f + k + 1 < n := by
    have hδn : δ * n < (n : ℝ) - k - 1 := by
      have h := mul_lt_mul_of_pos_right hδ_radius hnR
      rwa [div_mul_cancel₀ _ hnR.ne'] at h
    have : ((f + k + 1 : ℕ) : ℝ) < n := by push_cast; linarith
    exact_mod_cast this
  -- `ε_ca` at the grid point `f/n` is dominated by `ε_ca` at `δ` (quantisation +
  -- monotonicity in `δ_fld`).
  have hnNN : ((n : ℝ≥0)) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ι)).ne'
  have hfn_le : ((f : ℝ≥0) / n) ≤ δ.toNNReal := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal _ hδ_pos.le]
    exact (div_le_iff₀ hnR).mpr hf_le
  have hfloor_eq :
      Nat.floor (((f : ℝ≥0) / n) * n) = Nat.floor (δ.toNNReal * (n : ℝ≥0)) := by
    rw [div_mul_cancel₀ _ hnNN, Nat.floor_natCast, ← nat_floor_coe_nnreal]
    have hcoe : ((δ.toNNReal * (n : ℝ≥0) : ℝ≥0) : ℝ) = δ * n := by
      push_cast
      rw [Real.coe_toNNReal _ hδ_pos.le]
    rw [hcoe]
  have h_eps_le :
      epsCa (F := F) (A := F) C ((f : ℝ≥0) / n) ((f : ℝ≥0) / n)
        ≤ epsCa (F := F) (A := F) C δ.toNNReal δ.toNNReal := by
    calc epsCa (F := F) (A := F) C ((f : ℝ≥0) / n) ((f : ℝ≥0) / n)
        = epsCa (F := F) (A := F) C ((f : ℝ≥0) / n) δ.toNNReal :=
          epsCa_eq_of_floor_eq C _ _ _ hfloor_eq
      _ ≤ epsCa (F := F) (A := F) C δ.toNNReal δ.toNNReal :=
          epsCa_mono_left C _ hfn_le
  have h_eps_toReal :
      (epsCa (F := F) (A := F) C ((f : ℝ≥0) / n) ((f : ℝ≥0) / n)).toReal ≤ ε :=
    ENNReal.toReal_mono (epsCa_ne_top C _ _) h_eps_le
  -- Apply the source-native theorem at `f` and `ε`.
  have hmain :=
    rs_Lambda_extended_le_of_epsCa_int_radius
      (domain := domain) (k := k) (f := f) (ε := ε)
      hk_pos hf_lt hε_lt h_eps_toReal
  -- `Λ` at `δ` equals `Λ` at the grid point `f/n`.
  have hΛ :
      Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) δ
        = Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) ((f : ℝ) / n) :=
    Lambda_eq_floor_div_card _ hδ_pos.le
  -- Ceiling comparison: the source list bound is dominated by the tex bound.
  have hkεq : ε * ((k : ℝ) * q) ≤ η * ((q : ℝ) - n) := by
    have h := mul_le_mul_of_nonneg_right hε_le (mul_pos hkR hqR).le
    rwa [mul_assoc, div_mul_cancel₀ _ (mul_pos hkR hqR).ne'] at h
  have hD : (1 - η) * ((q : ℝ) - n) ≤ (q : ℝ) - n - k * ε * q := by nlinarith [hkεq]
  have hDpos : (0 : ℝ) < (1 - η) * ((q : ℝ) - n) := by positivity
  have hceil :
      Nat.ceil (ε * q * ((q : ℝ) - n) / ((q : ℝ) - n - k * ε * q))
        ≤ Nat.ceil ((q : ℝ) / (1 - η) * ε) := by
    refine Nat.ceil_le_ceil ?_
    calc ε * q * ((q : ℝ) - n) / ((q : ℝ) - n - k * ε * q)
        ≤ ε * q * ((q : ℝ) - n) / ((1 - η) * ((q : ℝ) - n)) := by
          gcongr
      _ = (q : ℝ) / (1 - η) * ε := by
          field_simp
  rw [hΛ]
  exact hmain.trans (by exact_mod_cast hceil)

end CAImpliesList

section ListVsCAseparation

/-- A characteristic-two Reed--Solomon family separating list decoding from CA. For the
full-domain code of rate `ρ = 1/8`,

  `ε_ca(C, 1 - ρ^{1/3}) ≥ 1 - 1/|F|` .

The interleaved threshold is strictly below `1 - ρ^{2/3}`, because the source supplies joint
distance equal to that boundary while `epsCa` uses a non-strict guard. -/
theorem rs_epsCa_large_below_johnson_radius
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (_hF_eq_ι : Fintype.card F = Fintype.card ι)
    -- Without `|F| ≥ 8` the dimension `k = ⌊|F| / 8⌋` truncates to 0,
    -- giving the trivial code `{0}` for which the conclusion's
    -- `ε_ca(C, _) ≥ 1 - 1/|F|` is not the intended separation result.
    -- The paper implicitly assumes `|F|` large enough for a meaningful
    -- rate-`1/8` code; we surface that hypothesis explicitly.
    (_hF_ge : 8 ≤ Fintype.card F) (δ_int : ℝ≥0)
    (_hδ_int : (δ_int : ℝ) < 1 - (1 / 8 : ℝ) ^ ((2 : ℝ) / 3))
    (domain : ι ↪ F) :
    let k : ℕ := Fintype.card F / 8
    let ρ : ℝ := 1 / 8
    let C := ReedSolomon.code domain k
    epsCa (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - ρ ^ ((1 : ℝ) / 3)).toNNReal)
        δ_int ≥
      ENNReal.ofReal (1 - 1 / Fintype.card F) := by
  sorry -- ABF26-T5.4; external admit [BenSassonGKS20 Lem 3.3].

end ListVsCAseparation

end CodingTheory

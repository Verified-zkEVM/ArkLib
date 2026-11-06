/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.CertificateWitnesses
public import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA

/-!
# Unsafe-side witnesses for `RS[512, 128]` at `ε* = 2⁻¹²⁸`

Let `ω` be a primitive `512`-th root of unity in a finite field `F`. For the Reed--Solomon code
`RS[F, (ωⁱ)ᵢ, 128]` at threshold `ε* = 2⁻¹²⁸`, this file instantiates
`GrandChallenges.CertificateWitnesses` at `δ = 377/512`:

* `listUpperWitness`: a `ListUpperWitness` for every interleaving `m ≥ 1`, when
  `|F| < cosetListSize · 2 ¹²⁸`;
* `mcaUpperWitness`: a `McaUpperWitness`, when `1024 ≤ |F|` and
  `2 |F| < (cosetListSize - 1) · 2 ¹²⁸`.

Here `cosetListSize = ⌊C(127, 33) / 128⌋ ≈ 2 ^ 94.3` is the size of the coset list of
`ReedSolomon.CosetList.exists_le_encard_closeCodewordsRel` at `s = 4`, `r = 33`: agreement
`135 = 512 - 377`. Both hypotheses hold for a field with `p ^ 3` elements,
`p = 2 ^ 64 - 2 ^ 32 + 1`.

On the domain of powers of `ω`, together with `Goldilocks512.Lower`, every boundary index `kStar`
of a `GrandMcaResolution` satisfies `273 ≤ kStar < 377`.

## References

* [Kin26] for the coset construction on multiplicative subgroups;
* [CS25] for the transfer from list size to correlated-agreement error;
* [ABF26] for the grand-challenge formulation.
-/

@[expose] public section

open Polynomial ReedSolomon Finset
open scoped NNReal

namespace ProximityGap.GrandChallenges.Goldilocks512

/-- The list-size lower bound `⌊C(127, 33) / 128⌋`, named so that `simp` does not evaluate the
binomial coefficient. -/
def cosetListSize : ℕ := Nat.choose 127 33 / 128

variable {F : Type} [Field F] {ω : F}

/-- Unsafe-side witness for the list-decoding grand challenge at `δ = 377/512`, for every
interleaving `m ≥ 1`, on the domain of powers of a primitive `512`-th root of unity, when
`|F| < cosetListSize · 2 ¹²⁸`.

It is `noncomputable` because the received word is chosen by `Classical.choose`. -/
noncomputable def listUpperWitness [Fintype F] [SampleableType F] [DecidableEq F]
    (hω : IsPrimitiveRoot ω 512) (hcard : Fintype.card F < cosetListSize * 2 ^ 128) (m : ℕ)
    (hm : 1 ≤ m) :
    ListUpperWitness (ReedSolomon.code (primitiveRootDomain hω) 128 : Set (Fin 512 → F)) m
      (1 / 2 ^ 128) :=
  ListUpperWitness.ofCosetList hω (s := 4) (r := 33) (δ := 377 / 512) (by norm_num) (by norm_num)
    (by norm_num) (by push_cast; norm_num) m hm (by
      have e : Nat.choose (512 / 4 - 1) 33 / (512 / 4) = cosetListSize := by
        rw [show (512 : ℕ) / 4 - 1 = 127 by norm_num, show (512 : ℕ) / 4 = 128 by norm_num]
        rfl
      rw [e, ← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_natCast cosetListSize,
        ← ENNReal.coe_mul, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
      have h := (Nat.cast_lt (α := ℝ)).mpr hcard
      push_cast at h ⊢
      linarith)

/-- The coset list at `n = 512`, `s = 4`, `r = 33`, taken in `RS[F, (ωⁱ)ᵢ, 129]`. -/
private theorem lambda129_ge (hω : IsPrimitiveRoot ω 512) :
    ((cosetListSize : ℕ) : ℕ∞) ≤
      Code.Lambda (ReedSolomon.code (primitiveRootDomain hω) 129 : Set (Fin 512 → F))
        (377 / 512) := by
  classical
  obtain ⟨w, hw⟩ := CosetList.exists_le_encard_closeCodewordsRel hω (s := 4) (r := 33) (k := 129)
    (by norm_num) (by norm_num) (by norm_num)
  have h : (((512 : ℕ) : ℝ) - ((4 * 33 + 4 - 1 : ℕ) : ℝ)) / ((512 : ℕ) : ℝ) = 377 / 512 := by
    norm_num
  rw [h, show (512 : ℕ) / 4 - 1 = 127 by norm_num, show (512 : ℕ) / 4 = 128 by norm_num] at hw
  exact hw.trans (Code.encard_closeCodewordsRel_le_Lambda _ _ w)

/-- The CA error of `RS[F, (ωⁱ)ᵢ, 128]` at `δ = 377/512` exceeds `2⁻¹²⁸` when `1024 ≤ |F|` and
`2 |F| < (cosetListSize - 1) · 2 ¹²⁸`. -/
theorem epsCa_gt [Fintype F] [SampleableType F] [DecidableEq F] (hω : IsPrimitiveRoot ω 512)
    (hF : 1024 ≤ Fintype.card F) (hcard : 2 * Fintype.card F < (cosetListSize - 1) * 2 ^ 128) :
    ((1 / 2 ^ 128 : ℝ≥0) : ENNReal) <
      ProximityGap.epsCa (F := F) (A := F)
        (ReedSolomon.code (primitiveRootDomain hω) 128 : Set (Fin 512 → F))
        (377 / 512 : ℝ).toNNReal (377 / 512 : ℝ).toNNReal := by
  set ε := ProximityGap.epsCa (F := F) (A := F)
    (ReedSolomon.code (primitiveRootDomain hω) 128 : Set (Fin 512 → F))
    (377 / 512 : ℝ).toNNReal (377 / 512 : ℝ).toNNReal with hε
  set N := cosetListSize with hNdef
  have hF' : (1024 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF
  have hc1 : 1 ≤ N := by
    rw [hNdef]; unfold cosetListSize; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel
  have hbig : 2 * (Fintype.card F : ℝ) < ((N : ℝ) - 1) * 2 ^ 128 := by
    have h := (Nat.cast_lt (α := ℝ)).mpr hcard
    push_cast [Nat.cast_sub hc1] at h
    linarith
  have hreal : ((2 : ℝ) ^ 128)⁻¹ < ε.toReal := by
    refine lt_of_not_ge fun hcon ↦ ?_
    have hsmall : (512 : ℝ) / (128 * (Fintype.card F : ℝ)) ≤ 1 / 256 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hL := CodingTheory.rs_Lambda_extended_le_of_epsCa (primitiveRootDomain hω) 128
      (377 / 512) (1 / 2) (by norm_num) (by norm_num) (by rw [Fintype.card_fin]; norm_num)
      (by norm_num) (by norm_num) (by rw [Fintype.card_fin]; omega) (by
        rw [Fintype.card_fin]
        refine hcon.trans ?_
        push_cast
        have h2 : ((2 : ℝ) ^ 128)⁻¹ ≤ 1 / 2 * (1 / 128 - 1 / 256) := by norm_num
        linarith)
    have hN : N ≤ ⌈(Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal⌉₊ := by
      have := (lambda129_ge hω).trans hL
      exact_mod_cast this
    have hx0 : 0 ≤ (Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal := by positivity
    have h1 : (N : ℝ) < (Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal + 1 :=
      lt_of_le_of_lt (by exact_mod_cast hN) (Nat.ceil_lt_add_one hx0)
    have hx : (Fintype.card F : ℝ) / (1 - 1 / 2) * ε.toReal =
        2 * (Fintype.card F : ℝ) * ε.toReal := by ring
    rw [hx] at h1
    have hε1 : ε.toReal * 2 ^ 128 ≤ 1 := by
      calc ε.toReal * 2 ^ 128 ≤ ((2 : ℝ) ^ 128)⁻¹ * 2 ^ 128 :=
            mul_le_mul_of_nonneg_right hcon (by positivity)
        _ = 1 := inv_mul_cancel₀ (by positivity)
    have hA := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < 2 ^ 128)
    have hB := mul_le_mul_of_nonneg_left hε1
      (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card F : ℝ))
    linarith
  have hne : ε ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hreal
    exact absurd hreal (not_lt.mpr (by positivity))
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hne]
  push_cast
  simpa [one_div] using hreal

/-- Unsafe-side witness for the mutual-correlated-agreement grand challenge at `δ = 377/512`, on
the domain of powers of a primitive `512`-th root of unity, when `1024 ≤ |F|` and
`2 |F| < (cosetListSize - 1) · 2 ¹²⁸`.

It is `noncomputable` because the witness carries real-valued error bounds. -/
noncomputable def mcaUpperWitness [Fintype F] [SampleableType F] [DecidableEq F]
    (hω : IsPrimitiveRoot ω 512) (hF : 1024 ≤ Fintype.card F)
    (hcard : 2 * Fintype.card F < (cosetListSize - 1) * 2 ^ 128) :
    McaUpperWitness (ReedSolomon.code (primitiveRootDomain hω) 128) (1 / 2 ^ 128) :=
  McaUpperWitness.ofEpsCaGt (δ := (377 / 512 : ℝ).toNNReal)
    (by rw [Real.toNNReal_le_one]; norm_num) (epsCa_gt hω hF hcard)

end ProximityGap.GrandChallenges.Goldilocks512

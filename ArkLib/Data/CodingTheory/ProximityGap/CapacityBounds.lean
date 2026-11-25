/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.Errors
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Entropy
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Frs
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonCa
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonLower
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonMca
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.NearCapacity
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Powers
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Sampling
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Subfield
public import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.UniqueDecoding
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.FullCode
public import ArkLib.Data.CodingTheory.Basic.Entropy
public import ArkLib.Data.CodingTheory.HammingBallVolume
public import ArkLib.Data.CodingTheory.SubspaceDesign
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Capacity-regime bounds for CA and MCA

This module collects numeric upper and lower bounds for `epsCa` and `mcaError`. The statements
use ArkLib's canonical error carriers and retain source-side endpoint, integrality, and code-family
hypotheses. Longer proofs are split into focused modules and re-exported here.

## Numeric bounds in `ENNReal`

Real-valued bounds are embedded into `ENNReal` with `ENNReal.ofReal`.

## Proximity-radius conventions

`mcaError` accepts real radii, while `epsCa` uses nonnegative radii.

## Main statements

### General linear codes

- `linear_mcaError_le_one_point_five_johnson` — ABF26 Theorem 4.11 [GaoKL24 Thm 3]: `ε_mca` bound
  in the "1.5-Johnson" regime `δ ≤ 1 - ∛(1 - δ_min(C) + η)`.
- `linear_epsCa_le_one_point_five_johnson` — ABF26 Theorem 4.11
  [BenSassonGKS20 Lem 3.2]: `ε_ca` bound with proximity loss `η`, valid in the same
  1.5-Johnson regime.

### Reed-Solomon codes

- `rs_epsCa_le_in_unique_decoding_range` — ABF26 Theorem 4.9 Item 2 [BCHKS25 Thm 1.3]:
  RS `ε_ca` bound
  in the `δ_min/3`-to-Johnson regime.
- `rs_epsCa_le_of_no_radius_level_crossing` — the derived small-proximity-loss form, under the
  necessary no-grid-crossing hypothesis.
- `rs_mcaError_le_johnsonExceptionCount` — the sharper [DKT26] exception-count bound on any
  finite coordinate type.
- `rs_mcaError_le_in_johnson_range` — the printed line bound of [BCHKS25 Thm 4.6], proved
  from [DKT26], for RS codes at every `0 ≤ δ < 1 - √((k-1)/n)`.

### Lower bounds near capacity

- `exists_rs_epsCa_large_near_capacity_of_prime` — ABF26 Theorem 4.16 [KKH26 Prop 3]: for every
  large `K` and every prime `p ≡ 1 (mod 2^K)` with `p ≥ n^{c+2}`, `n = 2^K`, a smooth RS code
  over `ZMod p` of length `n` for which `ε_ca` at distance `1 - ρ - slack` is at least `n^c / p`,
  with the `slack` pinned to `Θ(1/log₂ n)` via explicit uniform constants (Lean lacks a generic
  `Θ` notation).
- `exists_rs_epsCa_large_near_capacity_of_primes` — the source's family statement, with
  `|F| = Θ(n^β)`, given primes `p ≡ 1 (mod 2^K)` in `[n^β, 2n^β]` for one `β > max(c+2, 12/5)`
  and infinitely many `K`. ArkLib does not prove that supply of primes: it is a prime number
  theorem in arithmetic progressions, which no proof system in ArkLib needs.
- `rs_epsCa_eq_one_of_entropy_rate` — ABF26 Theorem 4.17 [CS25 Cor 1]: complete CA breakdown
  for RS codes when the rate sits inside an entropy-defined band, stated at the source's
  integer error radius.
- `subfield_epsCa_lower_bound` — a subfield/extension-field CA lower bound near capacity, using
  the helper `subfieldCaFactor`.
- `exists_rs_epsCa_large_at_johnson_radius` — ABF26 Theorem 4.18 [BCHKS25 Cor 1.7]: jump in
  `ε_ca` exactly at the Johnson bound, witnessed by characteristic-2 RS codes.
- `linear_close_probability_le_epsCa` — ABF26 Lemma 4.19 [DG25dist Thm 2.5]: `ε_ca(C, δ)`
  is bounded below by `((q-1)/q) · Pr{u}[Δ(u, C) ≤ δ]`.

### Subspace-design / FRS MCA up to capacity (§4.2.2)

- `subspace_design_mcaError_le` — ABF26 T4.13 [GG25 Cor 4.9]: τ-subspace-design code
  has explicit `ε_mca` bound at `1 - τ(2t) - 3/(2t)`.
- `frs_mcaError_le` — ABF26 T4.14 [GG25 Cor 4.10]: folded RS up to capacity
  has the integer-native bound `ε_mca(C, 1 - ρ - 2/t) ≤ (nt+3t³)/|F|`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [GaoKL24] Theorem 3 in their paper.
- [BenSassonGKS20] Lemma 3.2 in their paper.
- [BCHKS25] Theorem 4.6 / Corollary 1.7 in their paper.
- [DKT26] The characteristic-free Johnson-range Reed–Solomon agreement bound.
- [KKH26] Krachun-Kazanin-Haböck (source of Theorem 4.16; proved the bound that
  [BCHKS25]/[KK25] had under a conjecture).
- [CS25] Crites–Stewart, *On Reed–Solomon Proximity Gaps Conjectures*, ePrint 2025/2046.
  Corollary 1 = source of Theorem 4.17; Theorem 2 = source of T5.3
  (`ListDecodingAndCA.lean`); Theorem 3 = source of `thm:base-field-ca-lowerbound`
  (`subfield_epsCa_lower_bound`, `CapacityBounds/Subfield.lean`).
- [DG25dist] Theorem 2.5, source of Lemma 4.19.
-/

@[expose] public section

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]

omit [DecidableEq ι] in
/-- A small-proximity-loss corollary of `rs_epsCa_le_in_unique_decoding_range`. If shifting the
interleaved radius by `γ/n` does not cross a Hamming-distance grid level, then

  `ε_mca(C, δ_fld) = ε_ca(C, δ_fld) = ε_ca(C, δ_fld, δ_fld + γ/n) ≤`
  `  max{ (1-ρ-δ_fld) / (δ_fld·(1-ρ-2·δ_fld)·|F|), (n·δ_fld + γ) / (γ·|F|) }`

The grid condition lets `epsCa_eq_of_floor_eq` identify the shifted and unshifted interleaved
radii. This theorem is proved from that identity and `rs_epsCa_le_in_unique_decoding_range`. -/
theorem rs_epsCa_le_of_no_radius_level_crossing
    (domain : ι ↪ F) (k : ℕ) (δ_fld : ℝ≥0) (γ : ℝ≥0)
    (_h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (_h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (_hγ_pos : 0 < γ)
    (_h_no_cross :
        Nat.floor ((δ_fld + γ / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0))
          = Nat.floor ((δ_fld : ℝ≥0) * (Fintype.card ι : ℝ≥0))) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let bound : ℝ :=
      max ((1 - ρ - δ_fld) / (δ_fld * (1 - ρ - 2 * δ_fld) * Fintype.card F))
          ((n * δ_fld + γ) / (γ * Fintype.card F))
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_fld ≤
      ENNReal.ofReal bound := by
  classical
  intro n ρ bound
  -- `n = |ι| > 0`.
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_ne0 : (Fintype.card ι : ℝ≥0) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have hn_ne0R : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  -- Interleaved distance `δ_int := δ_fld + γ/n`.
  set δ_int : ℝ≥0 := δ_fld + γ / (Fintype.card ι : ℝ≥0) with hδ_int
  -- `γ/n > 0`, so `δ_fld < δ_int`.
  have hγn_pos : (0 : ℝ≥0) < γ / (Fintype.card ι : ℝ≥0) :=
    div_pos _hγ_pos (by exact_mod_cast hn_pos)
  have hlt : δ_fld < δ_int := by rw [hδ_int]; exact lt_add_of_pos_right _ hγn_pos
  -- Collapse `ε_ca(δ_fld, δ_fld) = ε_ca(δ_fld, δ_int)` via R4.2 and `_h_no_cross`.
  have hcollapse :
      epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_fld
        = epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_int :=
    epsCa_eq_of_floor_eq (F := F) (A := F) _ δ_fld δ_fld δ_int _h_no_cross.symm
  rw [hcollapse]
  -- Apply T4.9.2 at `δ_int`.
  have hT492 :=
    rs_epsCa_le_in_unique_decoding_range (F := F) domain k δ_fld δ_int _h_ud _h_dmin hlt
  simp only at hT492
  refine le_trans hT492 ?_
  -- Reduce to real-number equality of the two `max` bounds and monotonicity of `ENNReal.ofReal`.
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  -- The first max-branch is syntactically identical; only the second branch changes.
  refine congrArg₂ max rfl ?_
  -- `(δ_int : ℝ) = δ_fld + γ/n` and `(δ_int : ℝ) - δ_fld = γ/n`.
  have hδ_int_coe : (δ_int : ℝ) = (δ_fld : ℝ) + (γ : ℝ) / (Fintype.card ι : ℝ) := by
    rw [hδ_int]; push_cast [NNReal.coe_div]; ring
  -- Second branch of T4.9.2: `δ_int / ((δ_int - δ_fld) * |F|)`.
  -- Second branch of the goal: `(n·δ_fld + γ) / (γ · |F|)`.
  rw [hδ_int_coe]
  have hsub : (δ_fld : ℝ) + (γ : ℝ) / (Fintype.card ι : ℝ) - (δ_fld : ℝ)
      = (γ : ℝ) / (Fintype.card ι : ℝ) := by ring
  rw [hsub]
  -- Now: `(δ_fld + γ/n) / ((γ/n) · |F|) = (n·δ_fld + γ) / (γ · |F|)`.
  change ((δ_fld : ℝ) + (γ : ℝ) / (Fintype.card ι : ℝ))
      / (((γ : ℝ) / (Fintype.card ι : ℝ)) * (Fintype.card F : ℝ))
    = ((Fintype.card ι : ℝ) * (δ_fld : ℝ) + (γ : ℝ)) / ((γ : ℝ) * (Fintype.card F : ℝ))
  have hγ_ne0R : (γ : ℝ) ≠ 0 := by exact_mod_cast _hγ_pos.ne'
  field_simp

omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
open ReedSolomon.HiddenDerivative in
/-- The [DKT26] Johnson affine-line MCA bound on any finite coordinate type, retaining the
exception count and the cap at one. The degree bound is `k`, so the reduced rate is `(k-1)/n`.
The full-rate case is covered separately by `ReedSolomon.mcaError_eq_zero_of_card_le`. -/
theorem rs_mcaError_le_johnsonExceptionCount
    (domain : ι ↪ F) (k : ℕ) (η : ℝ)
    (hk : 1 < k) (hkn : k < Fintype.card ι) (hη : 0 < η) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain k)
        (1 - (Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card ι) + η)) ≤
      min 1 (ENNReal.ofReal
        (johnsonExceptionCount (Fintype.card ι) (k - 1)
          ⌈johnsonAgreement (Fintype.card ι) (k - 1) η * Fintype.card ι⌉₊ η /
            (Fintype.card F : ℝ))) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let domain' := e.toEmbedding.trans domain
  rw [← mcaError_comp_equiv (AffineLineGenerator F) (ReedSolomon.code domain k)
    (ReedSolomon.code domain' k) e (ReedSolomon.mem_code_comp_equiv e domain k)]
  simpa only [johnsonAgreement, johnsonRhoMinus, show k - 1 + 1 = k by omega] using
    ReedSolomon.mcaError_affineLine_johnson_le (D := k - 1) domain' (by omega) (by omega) hη

omit [DecidableEq ι] [DecidableEq F] [Nonempty ι] in
open ReedSolomon.HiddenDerivative in
/-- An affine-line MCA bound for a Reed--Solomon code in the Johnson range. Set the reduced rate
to `ρ := (k-1)/n` and, for `0 ≤ δ < 1-√ρ`, let

  `m := max(⌈√ρ/(1-√ρ-δ)⌉, 3)`.

Then

  `ε_mca(C, δ) ≤ (1/|F|) · ((2(m+½)⁵ + 3(m+½)·δ·ρ)/(3ρ^{3/2})·n
                              + (m+½)/√ρ)`.

The reduced rate `(k-1)/n` accounts for ArkLib's degree-`< k` convention.

The multiplicity `m` and the displayed constant are the printed choice of [BCHKS25, Theorem 4.6].
The proof uses the sharper [DKT26] exception count in `rs_mcaError_le_johnsonExceptionCount`
and its comparison estimate. This also proves the bound used by every Johnson-range
`McaLowerWitness.ofJohnsonRangeBound` constructor. -/
theorem rs_mcaError_le_in_johnson_range
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (_hk : 1 < k)
    (_hδ :
        (δ : ℝ) <
          1 - ((((k - 1 : ℕ) : ℝ) / Fintype.card ι) ^ ((1 : ℝ) / 2))) :
    mcaError (AffineLineGenerator F) (ReedSolomon.code domain k) (δ : ℝ) ≤
      ENNReal.ofReal
        (let n : ℝ := Fintype.card ι
         let ρ : ℝ := (k - 1 : ℕ) / n
         let m : ℝ := max ⌈(ρ ^ ((1 : ℝ) / 2)) /
           (1 - ρ ^ ((1 : ℝ) / 2) - δ)⌉ 3
         ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ)
            / (3 * ρ ^ ((3 : ℝ) / 2)) * n
          + (m + 1/2) / ρ ^ ((1 : ℝ) / 2))
           / (Fintype.card F : ℝ)) := by
  classical
  by_cases hfull : Fintype.card ι ≤ k
  · rw [ReedSolomon.mcaError_eq_zero_of_card_le _ domain hfull]
    exact bot_le
  have hkn : k < Fintype.card ι := lt_of_not_ge hfull
  -- Match the DKT26 agreement threshold to the requested radius.
  let n := Fintype.card ι
  let D := k - 1
  let ρ : ℝ := (D : ℝ) / n
  let η : ℝ := 1 - Real.sqrt ρ - δ
  have hsqrt : Real.sqrt ρ = ρ ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hη : 0 < η := by
    dsimp [η]
    rw [hsqrt]
    exact sub_pos.mpr _hδ
  have ha : johnsonAgreement n D η = 1 - δ := by
    dsimp [johnsonAgreement,
      johnsonRhoMinus, η, ρ]
    ring
  have ha_le : johnsonAgreement n D η ≤ 1 := by
    rw [ha]
    exact sub_le_self _ δ.coe_nonneg
  have hradius : 1 - (Real.sqrt ρ + η) = (δ : ℝ) := by dsimp [η]; ring
  have hbound := rs_mcaError_le_johnsonExceptionCount domain k η _hk hkn hη
  change mcaError _ _ (1 - (Real.sqrt ρ + η)) ≤ _ at hbound
  rw [hradius] at hbound
  refine (hbound.trans (min_le_right _ _)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  -- Compare the raw exception count with the printed constant.
  have hcount := johnsonExceptionCount_le_comparisonEstimate
    (n := n) (D := D) (by dsimp [D, n]; omega)
    hη ha_le (Nat.le_ceil _)
  refine (div_le_div_of_nonneg_right hcount (by positivity)).trans_eq ?_
  -- Identify the natural ceiling and square-root notation with the statement.
  have hceil : (⌈Real.sqrt ρ / η⌉₊ : ℝ) = (⌈Real.sqrt ρ / η⌉ : ℝ) :=
    natCast_ceil_eq_intCast_ceil (by positivity)
  have hshift : johnsonComparisonShift n D η =
      max (⌈ρ ^ ((1 : ℝ) / 2) / (1 - ρ ^ ((1 : ℝ) / 2) - δ)⌉ : ℝ) 3 + 1 / 2 := by
    change (max ⌈Real.sqrt ρ / η⌉₊ 3 : ℕ) + (1 / 2 : ℝ) = _
    rw [Nat.cast_max, Nat.cast_ofNat, hceil, hsqrt]
    simp only [η, hsqrt]
  dsimp only
  change johnsonComparisonEstimate n D η / _ = _
  unfold johnsonComparisonEstimate
  dsimp only
  change ((2 * johnsonComparisonShift n D η ^ 5 +
      3 * johnsonComparisonShift n D η *
        johnsonGamma n D η * ρ) / (3 * Real.sqrt ρ ^ 3) * n +
      johnsonComparisonShift n D η / Real.sqrt ρ) / _ = _
  rw [hshift, sqrt_cube_eq_rpow_three_halves]
  simp only [johnsonGamma, ha, sub_sub_cancel, hsqrt]
  rfl

end ReedSolomon

end CodingTheory

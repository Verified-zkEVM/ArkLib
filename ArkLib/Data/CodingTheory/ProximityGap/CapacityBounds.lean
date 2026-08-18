/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Entropy
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Frs
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonCa
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonLower
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.JohnsonMca
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Powers
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Sampling
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Subfield
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.UniqueDecoding
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
- `rs_mcaError_le_in_johnson_range` — source-native line case of [BCHKS25 Thm 4.6]:
  explicit `ε_mca` bound for RS codes at every `0 < δ < 1 - √((k-1)/n)`.

### Lower bounds near capacity

- `exists_rs_epsCa_large_near_capacity` — ABF26 Theorem 4.16 [KKH26]:
  existence of RS codes for which `ε_ca` at distance `1 - ρ - slack` is at
  least `n^c / |F|`, with the `slack` pinned to `Θ(1/log₂ n)` via explicit uniform
  constants (Lean lacks a generic `Θ` notation).
- `rs_epsCa_eq_one_of_entropy_rate` — ABF26 Theorem 4.17 [CS25 Cor 1]: complete CA breakdown
  for RS codes when the rate sits inside an entropy-defined band, stated at the source's
  integer error radius.
- `subfield_epsCa_lower_bound` — a subfield/extension-field CA lower bound near capacity, using
  the helper `subfieldCaFactor`.
- `exists_rs_epsCa_large_at_johnson_radius` — ABF26 Theorem 4.18 [BCHKS25 Cor 1.7]: jump in
  `ε_ca` exactly at the Johnson bound, witnessed by characteristic-2 RS codes.
- `linear_close_probability_le_epsCa` — ABF26 Lemma 4.19 [DG25dist Thm 2.5]: `ε_ca(C, δ)`
  is bounded below by `((q-1)/q) · Pr_{u}[Δ(u, C) ≤ δ]`.

### Subspace-design / FRS MCA up to capacity (§4.2.2)

- `subspace_design_mcaError_le` — ABF26 T4.13 [GG25 Cor 4.9]: τ-subspace-design code
  has explicit `ε_mca` bound at `1 - τ(t+1) - 3/(2t)`.
- `frs_mcaError_le` — ABF26 T4.14 [GG25 Cor 4.10]: folded RS up to capacity
  has the integer-native bound `ε_mca(C, 1 - ρ - 2/t) ≤ (nt+3t³)/|F|`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [GaoKL24] Theorem 3 in their paper.
- [BenSassonGKS20] Lemma 3.2 in their paper.
- [BCHKS25] Theorem 4.6 / Corollary 1.7 in their paper.
- [KKH26] Krachun-Kazanin-Haböck (source of Theorem 4.16; proved the bound that
  [BCHKS25]/[KK25] had under a conjecture).
- [CS25] Crites–Stewart, *On Reed–Solomon Proximity Gaps Conjectures*, ePrint 2025/2046.
  Corollary 1 = source of Theorem 4.17; Theorem 2 = source of T5.3
  (`ListDecodingAndCA.lean`); Theorem 3 = source of `thm:base-field-ca-lowerbound`
  (`subfield_epsCa_lower_bound`, `CapacityBounds/Subfield.lean`).
- [DG25dist] Theorem 2.5, source of Lemma 4.19.
-/

-- Pre-existing external admits below (not touched by this diff) have statements carrying
-- unused `Fintype`/`DecidableEq` hypotheses; scoped narrowly once those admits are resolved.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

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
    (_hγ_pos : 0 < γ) (_hγ_lt : (γ : ℝ) < 1)
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

/-- An affine-line MCA bound for a Reed--Solomon code in the Johnson range. Set the reduced rate
to `ρ := (k-1)/n` and, for `0 < δ < 1-√ρ`, let

  `m := max(⌈√ρ/(1-√ρ-δ)⌉, 3)`.

Then

  `ε_mca(C, δ) ≤ (1/|F|) · ((2(m+½)⁵ + 3(m+½)·δ·ρ)/(3ρ^{3/2})·n
                              + (m+½)/√ρ)`.

The reduced rate `(k-1)/n` accounts for ArkLib's degree-`< k` convention.

The multiplicity `m` is the source's printed, deliberately loose choice; the source's own proof
(its §3.2 derivation of `D_X ≤ (1-δ)·m·n`) supports the tighter `m = ⌈√ρ/(2·(1-√ρ-δ))⌉`, a factor
`2` smaller and hence `2⁵` smaller in the leading term. The admit stays pinned to the printed
statement; a proof may establish the tighter constant as a separate result.

This is the only theorem standing under every Johnson-range `McaLowerWitness` constructor
(`McaLowerWitness.ofJohnsonRangeBound`); until it is proved, every Johnson-range Grand-MCA
witness in the tree is admit-backed. -/
theorem rs_mcaError_le_in_johnson_range
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (_hk : 1 < k) (_hδ_pos : 0 < δ)
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
  sorry -- ABF26-T4.12; external admit [BCHKS25 Thm 4.6].

/-- For every `c > 0` and `ρ ∈ (0,1/2)`, there are arbitrarily large smooth Reed--Solomon
codes over prime fields whose rate is within `O(1/log n)` of `ρ` and for which

  `ε_ca(C, 1 - ρ - Θ(1/log n)) ≥ n^c / |F|`

The uniform constants record the `O(1/log₂ n)` rate control, `Θ(1/log₂ n)` capacity slack, and
two-sided `|F| = Θ(n^β)` field growth. Quantifying over every lower length bound makes this a
family statement rather than a single-instance asymptotic claim. -/
theorem exists_rs_epsCa_large_near_capacity
    (c : ℝ≥0) (_hc : 0 < c) (ρ : ℝ≥0) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < (1 / 2 : ℝ≥0)) :
    ∃ Kρ K₁ K₂ : ℝ, 0 < Kρ ∧ 0 < K₁ ∧ K₁ ≤ K₂ ∧
    ∃ β Kq_lo Kq_hi : ℝ,
    max ((c : ℝ) + 2) (12 / 5) < β ∧ 0 < Kq_lo ∧ Kq_lo ≤ Kq_hi ∧
    ∀ n₀ : ℕ,
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (_ : ReedSolomon.Smooth domain) (k : ℕ) (slack : ℝ≥0),
      -- arbitrarily large block length:
      n₀ ≤ Fintype.card ιC ∧
      -- `F` is a prime field (paper's "prime field" claim):
      (∃ p : ℕ, p.Prime ∧ CharP FC p ∧ Fintype.card FC = p) ∧
      -- `|F| = Θ(n^β)` uniformly in the family:
      Kq_lo * (Fintype.card ιC : ℝ) ^ β ≤ Fintype.card FC ∧
      (Fintype.card FC : ℝ) ≤ Kq_hi * (Fintype.card ιC : ℝ) ^ β ∧
      -- KKH26 controls the code distance, hence its rate, only up to `O(1/log n)`:
      |(k : ℝ) / Fintype.card ιC - (ρ : ℝ)|
        ≤ Kρ / Real.logb 2 (Fintype.card ιC) ∧
      -- slack pinned to `Θ(1/log₂ n)`:
      K₁ / Real.logb 2 (Fintype.card ιC) ≤ (slack : ℝ) ∧
      (slack : ℝ) ≤ K₂ / Real.logb 2 (Fintype.card ιC) ∧
      epsCa (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
          (1 - ρ - slack) (1 - ρ - slack) ≥
        ((Fintype.card ιC : ENNReal) ^ (c : ℝ)) / (Fintype.card FC : ENNReal) := by
  sorry -- ABF26-T4.16; external admit [KKH26].


/-- Threshold form of `rs_epsCa_le_of_no_radius_level_crossing`: any target `ε_star` that the
two-branch no-grid-crossing budget clears at the instantiated parameters is a genuine CA bound.
The numeric budget check is a hypothesis, so the contentful-range condition is discharged at
the use site. -/
theorem rs_epsCa_le_of_no_radius_level_crossing_of_budget
    (domain : ι ↪ F) (k : ℕ) (δ_fld : ℝ≥0) (γ : ℝ≥0)
    (h_ud : (δ_fld : ℝ) ≤ (1 - (k : ℝ) / Fintype.card ι) / 2 - 1 / Fintype.card ι)
    (h_dmin : (Code.minDist ((ReedSolomon.code domain k : Set (ι → F))) : ℝ)
                / Fintype.card ι / 3 ≤ δ_fld)
    (hγ_pos : 0 < γ) (hγ_lt : (γ : ℝ) < 1)
    (h_no_cross :
        Nat.floor ((δ_fld + γ / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0))
          = Nat.floor ((δ_fld : ℝ≥0) * (Fintype.card ι : ℝ≥0)))
    (ε_star : ℝ≥0)
    (hbudget : ENNReal.ofReal
        (max ((1 - (k : ℝ) / Fintype.card ι - δ_fld)
                / (δ_fld * (1 - (k : ℝ) / Fintype.card ι - 2 * δ_fld) * Fintype.card F))
             (((Fintype.card ι : ℝ) * δ_fld + γ) / (γ * Fintype.card F)))
      ≤ (ε_star : ENNReal)) :
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_fld ≤
      (ε_star : ENNReal) := by
  have h : epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ_fld δ_fld ≤
      ENNReal.ofReal
        (max ((1 - (k : ℝ) / Fintype.card ι - δ_fld)
                / (δ_fld * (1 - (k : ℝ) / Fintype.card ι - 2 * δ_fld) * Fintype.card F))
             (((Fintype.card ι : ℝ) * δ_fld + γ) / (γ * Fintype.card F))) :=
    rs_epsCa_le_of_no_radius_level_crossing domain k δ_fld γ h_ud h_dmin hγ_pos hγ_lt h_no_cross
  exact le_trans h hbudget

end ReedSolomon

section SubspaceDesignFRS

/-- An affine-line MCA bound for a `τ`-subspace-design code:

  `ε_mca(C, 1 - τ(t+1) - 3/(2t)) ≤ (t·n + 4·t³) / |F|`

The cubic term is the affine specialization of the source's general generator bound. -/
theorem subspace_design_mcaError_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (t : ℕ) (_ht : 0 < t) :
    mcaError (AffineLineGenerator F) C
        (1 - τ (t + 1) - 3 / (2 * t)) ≤
      ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 3) / Fintype.card F) := by
  sorry -- ABF26-T4.13; external admit [GG25 Cor 4.9].


end SubspaceDesignFRS

end CodingTheory

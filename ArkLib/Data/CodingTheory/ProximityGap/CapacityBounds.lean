/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Capacity-regime upper and lower bounds for ε_ca and ε_mca (ABF26 §4.2, §4.3)

External-admit *statements* for the §4 results that bound `ε_ca` and `ε_mca` from above
in the Johnson regime and from below in the capacity regime. From
*Open Problems in List Decoding and Correlated Agreement* (Arnon-Boneh-Fenzi,
April 8, 2026), §§4.2.2 and 4.3.

These theorems sit immediately above the Grand MCA Challenge in ABF26 §1: each one
either produces a witness `δ_C*` for `ε_mca(C, δ_C*) ≤ ε*` (upper bounds), or rules out
witnesses above a given threshold (lower bounds). They are mostly cited from external
papers ([GaoKL24], [BenSassonGKS20], [BCHKS25], [KKH26], [CS25], [DG25dist], etc.); we state them
here in ArkLib's `ε_ca` / `ε_mca` form and admit the proofs as external results.

## Numeric bounds in `ENNReal`

The RHS of each upper bound is a real-valued numeric expression. To match the
`ENNReal`-valued error functions, we wrap the bound with
`ENNReal.ofReal`. The lower bounds use the same wrapping for symmetry. This keeps
the bounds well-defined even when the bracketing real expression is negative or
exceeds 1 (in which case `ENNReal.ofReal` either truncates to `0` or stays in `[0, ∞]`).

## Proximity-radius conventions

The canonical generator-level `mcaError` accepts a real radius, so MCA statements preserve
the source's displayed real expression directly, even if it is negative. Legacy CA statements
use `epsCa` and therefore retain nonnegative-real radii. This distinction avoids silently
strengthening source hypotheses merely to justify an `ℝ → ℝ≥0` truncation.

## Main statements

Most of these are external-admit *statements*; the exceptions are noted inline (e.g.
R4.10 is *derived in-tree* from R4.2 + the admitted T4.9.2, so it carries no admit of
its own beyond the inherited T4.9.2 `sorry`).

### General linear codes

- `linear_epsMCA_1_5_johnson_gkl24` — ABF26 Theorem 4.11 [GaoKL24 Thm 3]: `ε_mca` bound
  in the "1.5-Johnson" regime `δ ≤ 1 - ∛(1 - δ_min(C) + η)`.
- `linear_epsCA_1_5_johnson_bgks20` — ABF26 Theorem 4.11 [BenSassonGKS20 Lem 3.2]: `ε_ca` bound
  with proximity loss `η`, valid in the same 1.5-Johnson regime.

### Reed-Solomon codes

- `rs_epsCA_bchks25_item2` — ABF26 Theorem 4.9 Item 2 [BCHKS25 Thm 1.3]: RS `ε_ca` bound
  in the `δ_min/3`-to-Johnson regime (external admit).
- `rs_epsCA_small_loss_r4_10` — ABF26 Remark 4.10: small-proximity-loss (`δ_int - δ_fld =
  γ/n`) simplification of T4.9.2. **Derived in-tree** from R4.2 (`epsCa_eq_of_floor_eq`,
  proven) + T4.9.2 (admitted), under an added no-level-set-crossing hypothesis; its only
  `sorry` dependency is the one inherited from T4.9.2.
- `rs_epsMCA_johnson_range_bchks25` — source-native line case of [BCHKS25 Thm 4.6]:
  explicit `ε_mca` bound for RS codes at every `0 < δ < 1 - √((k-1)/n)`.

### Lower bounds near capacity

- `rs_epsCA_lower_capacity_kkh26` — ABF26 Theorem 4.16 [KKH26]:
  existence of RS codes for which `ε_ca` at distance `1 - ρ - slack` is at
  least `n^c / |F|`, with the `slack` pinned to `Θ(1/log₂ n)` via explicit uniform
  constants (Lean lacks a generic `Θ` notation).
- `rs_epsCA_breakdown_cs25` — ABF26 Theorem 4.17 [CS25 Cor 1]: complete CA breakdown
  for RS codes when the rate sits inside an entropy-defined band.
- `rs_epsCA_subfield_lower_cs25_thm3` — ABF26 `thm:base-field-ca-lowerbound` [CS25 Thm 3]:
  subfield/extension-field CA lower bound near capacity for `RS[F, L, k]` with `L ⊆ B ⊆ F`.
  The third, distinct CS25 result (Cor 1 = T4.17 above; Thm 2 = T5.3 in
  `ListDecodingAndCA.lean`). Uses the helper `cs25SubfieldFactor` (`a(x)` in the paper).
- `rs_epsCA_johnson_jump_bchks25` — ABF26 Theorem 4.18 [BCHKS25 Cor 1.7]: jump in
  `ε_ca` exactly at the Johnson bound, witnessed by characteristic-2 RS codes.
- `linear_epsCA_ge_sampling_dg25` — ABF26 Lemma 4.19 [DG25dist Thm 2.5]: `ε_ca(C, δ)`
  is bounded below by `((q-1)/q) · Pr_{u}[Δ(u, C) ≤ δ]`.

### Subspace-design / FRS MCA up to capacity (§4.2.2)

- `subspaceDesign_epsMCA_gg25` — ABF26 T4.13 [GG25 Cor 4.9]: τ-subspace-design code
  has explicit `ε_mca` bound at `1 - τ(t+1) - 3/(2t)`.
- `frs_epsMCA_capacity_gg25` — ABF26 T4.14 [GG25 Cor 4.10]: folded RS up to capacity
  has `ε_mca(C, 1 - ρ - η) ≤ O(n/(η|F|) + 1/(η³|F|))`.

## Deferred statements

- ABF26 Theorem 4.15 [GG25 Thm 5.15] (random RS MCA up to capacity) — blocked on a
  uniform distribution over size-`n` subsets of `F`.

These are tracked in `docs/kb/ABF26_PLAN.md` §7 and will be stated alongside the corresponding
code-family definitions in Phase 3.

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
  (`rs_epsCA_subfield_lower_cs25_thm3`, this file).
- [DG25dist] Theorem 2.5, source of Lemma 4.19.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **ABF26 Theorem 4.11, Item 1 [GaoKL24 Thm 3].** For any linear error-correcting code
`C ⊆ F^n`, parameter `η > 0`, and `δ ≤ 1 - ∛(1 - δ_min(C) + η)`:

  `ε_mca(C, δ) ≤ ((n+6)/η + 2 / (η · (∛(1 - δ_min + η) - √(1 - δ_min + η))) ) · (1/|F|)`

The "1.5-Johnson regime" refers to the fact that `1 - ∛(1 - δ_min)` lies strictly above
the classical Johnson bound `1 - √(1 - δ_min)` and strictly below capacity. The bound is
admitted from the cited paper.

**Implicit hypothesis `η < δ_min`.** For the bound's denominator `∛x − √x` (with
`x := 1 - δ_min + η`) to be strictly positive we need `x < 1`, i.e. `η < δ_min`. The
paper's 1.5-Johnson regime is exactly this `η`-as-slack-below-δ_min picture; without it
the bound becomes vacuous (or numerically infinite) and `δ ≤ 1 − ∛x` may not even
restrict the parameter range. Added as an explicit hypothesis. -/
theorem linear_epsMCA_1_5_johnson_gkl24
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_δ_min : η < δ_min)
    (_hδ_pos : 0 < δ)
    (_hδ : (δ : ℝ) ≤ 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      ENNReal.ofReal
        ((((Fintype.card ι : ℝ) + 6) / η
          + 2 / ((η : ℝ) *
              ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3)
                - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 2)))
         ) / (Fintype.card F : ℝ)) := by
  sorry -- ABF26-T4.11 Item 1; external admit [GaoKL24 Thm 3].

/-- **ABF26 Theorem 4.11, Item 2 [BenSassonGKS20 Lem 3.2].** For any linear error-correcting code
`C ⊆ F^n`, parameter `η > 0`, and `δ ≤ 1 - ∛(1 - δ_min(C) + η)`:

  `ε_ca(C, δ_fld := δ, δ_int := δ + η) ≤ 2 / (η² · |F|)`

Same regime as the GKL24 form but stated in CA-with-proximity-loss shape. Tighter when the
GKL24 bound is dominated by its second term. Admitted from the cited paper.

**Source hypotheses.** BGKS20 Lemma 3.2 (positive form) is stated for a linear code
`V ⊆ F_q^D` of distance `λ` and parameters `ε, δ > 0` with `ε < 1/3` and
`δ < 1 − (1 − λ + ε)^{1/3}` (strict): if
`Pr_x[Δ(u* + x·u, V) < δ] ≥ 2/(ε²·q)` then `u, u*` jointly agree with codewords on a
set of density `≥ 1 − δ − ε`. Notation map: the source's `ε` is our `η` (the joint
agreement set of density `1 − δ − ε` is exactly interleaved radius `δ_int = δ + η`),
its `λ` is our `δ_min`, its `δ` is our `δ_fld`.

All three strict positivity/range assumptions are retained here. The additional
`η < δ_min` hypothesis matches the common ABF26 Theorem 4.11 regime. -/
theorem linear_epsCA_1_5_johnson_bgks20
    (C : ModuleCode ι F A) (δ_min η δ : ℝ≥0)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_third : (η : ℝ) < 1 / 3) (_hη_lt_δ_min : η < δ_min)
    (_hδ_pos : 0 < δ)
    (_hδ : (δ : ℝ) < 1 - ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / 3))) :
    epsCa (F := F) (A := A) ((C : Set (ι → A))) δ (δ + η) ≤
      ((2 : ENNReal) / ((η : ENNReal) ^ 2 * (Fintype.card F : ENNReal))) := by
  sorry -- ABF26-T4.11 Item 2; external admit [BenSassonGKS20 Lem 3.2].

end General

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Theorem 4.9 Item 2 [BCHKS25 Theorem 1.3].** Reed-Solomon CA bound in the
`δ_min/3`-to-half-distance regime. Let `C := RS[F, L, k]` with rate `ρ`. BCHKS25
Theorem 1.3's regime is `γ ∈ [δ/3, δ/2 − 1/n]` (with `δ := 1 − k/n`) — the upper end is
**strictly inside** half-distance by the finite-length margin `1/n`. We state the
source's `δ_fld ≤ (1-ρ)/2 − 1/n`; Item 2 additionally requires
`δ_min(C)/3 ≤ δ_fld < δ_int`:

  `ε_ca(C, δ_fld, δ_int) ≤`
  `  max{ (1-ρ-δ_fld) / (δ_fld·(1-ρ-2·δ_fld)·|F|), δ_int / ((δ_int-δ_fld)·|F|) }`

**Why the `− 1/n` matters (2026-07-18 fix).** ABF26's `thm:ud-rs` header prints the
regime as `δ_fld ≤ (1-ρ)/2`, *including* the endpoint at which the first max-branch's
denominator factor `1-ρ-2·δ_fld` is `0`. In Lean's totalized arithmetic `x/0 = 0`, so at
that endpoint the branch silently collapses to `0` and the admitted statement becomes
false (reproduced by the 2026-07-17 review's kernel probe `SemanticBoundaries.lean`).
The source's margin gives `1-ρ-2·δ_fld ≥ 2/n > 0`, restoring denominator positivity.
The dropped margin is also recorded upstream as `PAPER_REVS.md` finding #9.
Tighter than T4.8 (AHIV17) in the regime `δ_fld ≥ δ_min/3`. Admitted as an external
result; regime re-derived from the BCHKS25 PDF, not the ABF26 tex. -/
theorem rs_epsCA_bchks25_item2
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
  sorry -- ABF26-T4.9.2; external admit [BCHKS25 Thm 1.3].

/-- **ABF26 Remark 4.10.** Small-proximity-loss simplification of T4.9.2 via R4.2.
For `δ_int - δ_fld = γ/n` with `γ ∈ (0, 1)` (so that `R4.2` collapses `ε_ca` to its
`δ_int := δ_fld` value):

  `ε_mca(C, δ_fld) = ε_ca(C, δ_fld) = ε_ca(C, δ_fld, δ_fld + γ/n) ≤`
  `  max{ (1-ρ-δ_fld) / (δ_fld·(1-ρ-2·δ_fld)·|F|), (n·δ_fld + γ) / (γ·|F|) }`

The `(n·δ_fld + γ) / γ` term dominates the original `δ_int / (δ_int - δ_fld)` term
once `δ_int - δ_fld` is below `1/n`. We state the resulting bound on
`ε_ca(C, δ_fld, δ_fld)`; the equality with `ε_mca` follows from L4.6 in the
unique-decoding regime, which is itself an external admit.

As with T4.9.2 (`rs_epsCA_bchks25_item2`), this inherits the source's enclosing
hypothesis `δ_fld ≤ (1-ρ)/2 − 1/n` (BCHKS25 Thm 1.3's regime, with the finite-length
margin restored 2026-07-18 — see the T4.9.2 docstring) — the remark is a specialisation
of Item 2 and is only asserted inside that unique-decoding scope.

**This proof is machine-checked in-tree** from R4.2 (`epsCa_eq_of_floor_eq`, which is
*proven*, sorry-free) plus T4.9.2 (`rs_epsCA_bchks25_item2`, an external admit). The only
`sorryAx` this theorem depends on is the one inherited from T4.9.2; R4.2 contributes none.

**Added no-level-set-crossing hypothesis `_h_no_cross`.** The paper's R4.2 "shift by
`β ∈ [0, 1/n)`" idiom silently assumes the shifted interval does not cross a multiple of
`1/n`. Concretely, collapsing `ε_ca(C, δ_fld, δ_fld) = ε_ca(C, δ_fld, δ_fld + γ/n)` via R4.2
requires `⌊δ_fld·n + γ⌋ = ⌊δ_fld·n⌋`, which *fails* whenever `fract(δ_fld·n) + γ ≥ 1`. In
that case no equal-floor `δ_int` with gap `≥ γ/n` exists, and since `x ↦ (a+x)/x` is
decreasing the achievable second max-branch is strictly *worse* than the claimed
`(n·δ_fld + γ)/(γ·|F|)` (recall `epsCa` is antitone in `δ_int`, `Errors.lean:269`, the wrong
direction to transfer the bound from a larger `δ_int`). So the γ-bound is *not* derivable
from T4.9.2 without this hypothesis. It holds automatically whenever `δ_fld·n` is an integer
— the paper's implicit reading — and is exactly the caveat documented on
`epsCa_eq_of_floor_eq` (R4.2) in `Errors.lean` ("that form follows … whenever the interval
does not cross a multiple of `1/n` — in particular when `δ` is itself such a multiple"). We
keep `_hγ_lt : γ < 1` for hypothesis-parity with the paper even though `_h_no_cross` implies
it. -/
theorem rs_epsCA_small_loss_r4_10
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
  have hT492 := rs_epsCA_bchks25_item2 (F := F) domain k δ_fld δ_int _h_ud _h_dmin hlt
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

/-- **[BCHKS25 Theorem 4.6], affine-line instance corresponding to ABF26 Theorem 4.12.**
For ArkLib's dimension-`k` Reed--Solomon code, set the source's reduced rate to
`ρ := (k-1)/n`. At every `0 < δ < 1-√ρ`, let

  `m := max(⌈√ρ/(1-√ρ-δ)⌉, 3)`.

Then

  `ε_mca(C, δ) ≤ (1/|F|) · ((2(m+½)⁵ + 3(m+½)·δ·ρ)/(3ρ^{3/2})·n
                              + (m+½)/√ρ)`.

BCHKS25 states a degree-`M` polynomial-curve exceptional-set bound. Taking `M = 1`
and dividing the exceptional-set cardinality by `|F|` gives the canonical affine-line
`mcaError`. The reduced-rate convention is essential: the source's RS code has dimension
one greater than its degree parameter, hence `(k-1)/n` for `ReedSolomon.code domain k`.

ABF26 prints a slack-parameter extraction with a different rate and `m`; that expression
is not a direct specialization of BCHKS25 Theorem 4.6. This declaration therefore records
the source-licensed form. Admitted as an external result. -/
theorem rs_epsMCA_johnson_range_bchks25
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

/-- **ABF26 Theorem 4.16 (`thm:ca-lower-bound`) [KKH26].** Existence: for every `c > 0`
and target rate `ρ ∈ (0, 1/2)` there exist arbitrarily large powers of two `n ∈ ℕ` and
Reed-Solomon codes `C := RS[F, L, k]` whose rate is within `O(1/log n)` of `ρ`,
over a prime field `F` with
`|F| = poly(n)` and smooth `L` of size `n` such that

  `ε_ca(C, 1 - ρ - Θ(1/log n)) ≥ n^c / |F|`

**Attribution.** The canonical `.tex` (≈ lines 1847–1857) now attributes this theorem
to [KKH26] (Krachun–Kazanin–Haböck), which *proved* (and improved) the variant that
[BCHKS25] had shown under a conjecture (see also [CGHLL26], [Kambire26]); the earlier
"BCHKS25 + KK25 under conjecture" citation is stale.

**Encoding of the asymptotics.** Three knobs are pinned so the statement keeps the
paper's content (none of them can be vacuously discharged):

- *Rate control.* The source supplies only `|k/n-ρ| = O(1/log n)`, encoded by one
  uniform positive constant `Kρ`. A tighter `1/n` rounding band would not be source-licensed.
- *Slack `Θ(1/log n)`.* Uniform constants `K₁, K₂` are fixed *before* the code family,
  with `K₁/log₂ n ≤ slack ≤ K₂/log₂ n` per instance. NB (2026-06-10 re-review): the
  CS25 breakdown band of T4.17 itself extends to slack `≲ h_q(δ)/ln q = Θ(1/log n)`
  for `|F| = poly(n)` (`.tex` ~1880), so even with the lower pin this statement is
  in principle dischargeable from T4.17 alone (pick `K₁ = K₂` small) — it
  *under-pins* the [KKH26] content. We keep the faithful Θ-form of the paper's
  statement rather than over-constraining; the genuinely-KKH26 content (explicit
  constants, smoothness) lives in the planned Appendix-C templates. The upper side
  keeps the advertised
  "distance `Θ(1/log n)` from capacity" scale. Logs are base 2 (`Real.logb 2`),
  matching the paper's convention.
- *Family, not a single code.* The paper's `∃ n` plus `Θ(1/log n)` is only meaningful
  for an infinite family, so we quantify `∀ n₀, ∃ … n₀ ≤ n` (arbitrarily large
  witnesses) with the `Θ`-constants and the `|F| = poly(n)` exponents `(a, b)` shared
  across the family — for a single instance both would be vacuous.

The power-of-two/smoothness of `L` is carried by the `ReedSolomon.Smooth domain`
instance. Admitted as an external result. -/
theorem rs_epsCA_lower_capacity_kkh26
    (c : ℝ≥0) (_hc : 0 < c) (ρ : ℝ≥0) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < (1 / 2 : ℝ≥0)) :
    ∃ Kρ K₁ K₂ : ℝ, 0 < Kρ ∧ 0 < K₁ ∧ K₁ ≤ K₂ ∧
    ∃ a b : ℕ,
    ∀ n₀ : ℕ,
    ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
      (FC : Type) (_ : Field FC) (_ : Fintype FC) (_ : DecidableEq FC)
      (domain : ιC ↪ FC) (_ : ReedSolomon.Smooth domain) (k : ℕ) (slack : ℝ≥0),
      -- arbitrarily large block length:
      n₀ ≤ Fintype.card ιC ∧
      -- `F` is a prime field (paper's "prime field" claim):
      (∃ p : ℕ, p.Prime ∧ CharP FC p ∧ Fintype.card FC = p) ∧
      -- `|F| = poly(n)` — polynomially bounded in `n = |L|`, uniformly in the family:
      Fintype.card FC ≤ a * (Fintype.card ιC) ^ b ∧
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

/-- **ABF26 Theorem 4.17 [CS25 Cor 1].** Complete CA breakdown for Reed-Solomon codes.
Let `C := RS[F, L, k]` with `q = |F| ≥ 10`, rate `ρ`, and `δ` satisfying:

  `1 - H_q(δ) + 2/n + √((H_q(δ) - δ)/n) ≤ ρ ≤ 1 - δ - 2/n`

Then `ε_ca(C, δ) = 1`. Uses `qEntropy` (ABF26 Definition 2.2, defined in
`Basic/Entropy.lean`). Admitted as an external result. -/
theorem rs_epsCA_breakdown_cs25
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (_hq_ge : 10 ≤ Fintype.card F)
    (_hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (_hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ)) :
    epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ = 1 := by
  sorry -- ABF26-T4.17; external admit [CS25 Cor 1].

/-- **The factor `a(x)` from ABF26 `thm:base-field-ca-lowerbound` [CS25 Theorem 3].**

  `a(x) := exp(x)` if `x ≤ 3/2`, else `exp(2√x) / √(2π·⌊√x⌋)`.

This is the analytic factor appearing in the subfield CA lower bound
(`rs_epsCA_subfield_lower_cs25_thm3`). For `x > 3/2` we have `√x > 1`, so `⌊√x⌋₊ ≥ 1`
and the denominator `√(2π·⌊√x⌋)` is strictly positive (well-defined). -/
noncomputable def cs25SubfieldFactor (x : ℝ) : ℝ :=
  if x ≤ 3 / 2 then Real.exp x
  else Real.exp (2 * Real.sqrt x) / Real.sqrt (2 * Real.pi * ⌊Real.sqrt x⌋₊)

/-- **ABF26 `thm:base-field-ca-lowerbound` [CS25 Theorem 3].** Subfield/extension-field CA
lower bound near capacity. Let `C := RS[F, L, k]` be a Reed-Solomon code where `B ⊆ F` are
finite fields, `L ⊆ B`, `n := |L|`, and fix `δ ∈ (0, 1 - ρ(C))`. Then

  `ε_ca(C, δ) ≥ 1 − [ |F| · |B|^{n(1−ρ−δ)} · a(δ(1−δ)n²/|B|) ] / C(n, δn)`

where `a(x) := exp(x)` if `x ≤ 3/2`, else `a(x) := exp(2√x)/√(2π·⌊√x⌋)`
(the helper `cs25SubfieldFactor`).

**Disambiguation of the three formalized CS25 results.** [CS25] = Crites–Stewart,
*On Reed–Solomon Proximity Gaps Conjectures*, ePrint 2025/2046. Three of its results are
formalized in ArkLib and must not be conflated:

- [CS25 Corollary 1] = `rs_epsCA_breakdown_cs25` (T4.17, this file) — complete CA breakdown
  in an entropy-defined rate band.
- [CS25 Theorem 2] = `rs_epsCA_implies_lambda_cs25_int` (native integer-radius admit,
  `ListDecodingAndCA.lean`), from which the ABF26-shaped T5.3
  `rs_epsCA_implies_lambda_extended_cs25` is derived in-tree.
- [CS25 Theorem 3] = **this declaration** — the third, distinct result: the
  subfield/extension-field CA lower bound near capacity.

**Prize relevance.** This bound powers the attack table `tab:cs25-ca-lowerbound`
(`.tex` ~L2845), and the subfield regime `L ⊆ B ⊆ F` matches the koala instantiation of the
toy protocol (an extension field over a small base field).

**Encoding choices (matching this file's conventions).**
- *Subfield.* `B : Subfield F` with `_h_dom : ∀ i, domain i ∈ B` encoding `L ⊆ B`; `|B|` is
  `Nat.card B` (avoids a `DecidablePred (· ∈ B)`/`Fintype` synthesis dependency; over the
  finite field `F` it equals the cardinality of the subfield).
- *`|B|` power.* `|B|^{n(1−ρ−δ)}` uses `Real.rpow` (real exponent).
- *Binomial `C(n, δn)`.* Encoded as `Nat.choose n ⌊δ·n⌋₊`, guarded by the integrality
  hypothesis `_h_int : (⌊δ·n⌋₊ : ℝ) = δ·n` so the admitted statement cannot silently drift
  from the paper's `C(n, δn)` at non-integral `δn` (same conservatism as the file's other
  satisfiability guards).
- *`a(x)` helper.* `cs25SubfieldFactor` above.

Admitted as an external result. -/
theorem rs_epsCA_subfield_lower_cs25_thm3
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (B : Subfield F)
    (_h_dom : ∀ i, domain i ∈ B)
    (_h_int : ((⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ)) = (δ : ℝ) * Fintype.card ι)
    (_hδ_pos : 0 < δ)
    (_hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    ENNReal.ofReal
        (1 - (Fintype.card F * (Nat.card B : ℝ) ^ (n * (1 - ρ - δ) : ℝ)
              * cs25SubfieldFactor ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2
                  / Nat.card B))
            / (Nat.choose (Fintype.card ι) ⌊(δ : ℝ) * Fintype.card ι⌋₊)) ≤
      epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ := by
  sorry -- ABF26 thm:base-field-ca-lowerbound; external admit [CS25 Thm 3].

/-- **[BCHKS25 Corollary 1.7], the Johnson-jump result cited by ABF26 Theorem 4.18.**
For every fixed `ε ∈ (0,1)` and every sufficiently large characteristic-two field,
there is a Reed--Solomon code of relative minimum distance `15/16` for which

  `ε_ca(C, 3/4, δ_int) ≥ n^{2(1-ε)}/|F|`

for every `δ_int < 7/8`. Here `3/4 = 1-√(1-15/16)` is the Johnson radius. The strict
upper bound on `δ_int` is the direct consequence of the source's pair-distance witness
`≥ 7/8`; no additional `1/n` margin is claimed. The source is asymptotic, so the field
condition is encoded by an existential threshold `q₀`. Its construction-specific length
scaling is not needed for this CA consequence and is not asserted here.

Admitted as an external result. -/
theorem rs_epsCA_johnson_jump_bchks25
    (ε : ℝ≥0) (_hε : 0 < ε) (_hε_lt : (ε : ℝ) < 1) :
    ∃ q₀ : ℕ,
    ∀ {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2],
      q₀ ≤ Fintype.card FC →
      ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
        (domain : ιC ↪ FC) (k : ℕ),
        (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
            / Fintype.card ιC = (15 : ℝ) / 16 ∧
        ∀ δ_int : ℝ≥0, (δ_int : ℝ) < 7 / 8 →
          epsCa (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
              (3 / 4 : ℝ≥0) δ_int ≥
            ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
              / (Fintype.card FC : ENNReal) := by
  sorry -- ABF26-T4.18; external admit [BCHKS25 Cor 1.7].

end ReedSolomon

section Sampling

open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Lemma 4.19 [DG25dist Thm 2.5].** Let `C ⊆ F^n` be a linear code and let
`δ' := max_{u ∈ F^n} Δ(u, C)` be the (relative) covering radius. For every
`δ ∈ (0, δ')`:

  `ε_ca(C, δ) ≥ ((q-1)/q) · Pr_{u ← F^n}[Δ(u, C) ≤ δ]`

The probability is over a uniform word in `F^n`, expressed via the `Pr_{...}[...]`
notation. Admitted as an external result. -/
theorem linear_epsCA_ge_sampling_dg25
    (C : LinearCode ι F) (δ δ' : ℝ≥0)
    (_h_δ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < δ') :
    ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
        * Pr_{let u ← $ᵖ (ι → F)}[δᵣ(u, (C : Set (ι → F))) ≤ δ] ≤
      epsCa (F := F) (A := F) ((C : Set (ι → F))) δ δ := by
  sorry -- ABF26-L4.19; external admit [DG25dist Thm 2.5].

end Sampling

section SubspaceDesignFRS

/-- **ABF26 Theorem 4.13 [GG25 Corollary 4.9].** τ-subspace-design codes have MCA bounds.
Let `C : F^k → (F^s)^n` be a τ-subspace-design code. For every `t ∈ ℕ`:

  `ε_mca(C, 1 - τ(t+1) - 3/(2t)) ≤ (t·n + 4·t³) / |F|`

**Constant is `4t³`, not `4t²`** (2026-07-05 faithfulness audit): GG25 Corollary 4.9
states MCA `(ℓ, 1 − τ(t·ℓ+ℓ) − 3/2t, t·ℓ·(n + 2t²(ℓ+1))/|F|)`; the ABF26 affine case
`ℓ = 1` gives `t·(n + 4t²)/|F| = (t·n + 4t³)/|F|`, which is exactly the constant used in
ABF26's own application (`.tex` L2929, `4r³`). ABF26's *theorem statement* (`.tex` L1830)
has a `4t²` transcription typo; we follow the source-backed `4t³` (safe/weaker for `t ≥ 2`).

Combined with `IsSubspaceDesign` (D2.16) and `subspaceDesign_tau_lower` (L2.17), this
gives MCA up to capacity for subspace-design codes. Admitted as an external result. -/
theorem subspaceDesign_epsMCA_gg25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (t : ℕ) (_ht : 0 < t) :
    mcaError (AffineLineGenerator F) C
        (1 - τ (t + 1) - 3 / (2 * t)) ≤
      ENNReal.ofReal (((t : ℝ) * Fintype.card ι + 4 * t ^ 3) / Fintype.card F) := by
  sorry -- ABF26-T4.13; external admit [GG25 Cor 4.9].

/-- **ABF26 Theorem 4.14 [GG25 Corollary 4.10].** Folded Reed-Solomon codes have MCA
up to capacity. Let `η ∈ (0, 1)` and `C := FRS[F, L, k, s, ω]` be a folded RS code
with `s > 16/η²`. Then:

  `ε_mca(C, 1 - ρ - η) ≤ 2n/(η·|F|) + 24/(η³·|F|)`

**Rate convention.** The FRS code `FRS[F, L, k, s, ω] ⊆ (F^s)^n` has rate
`ρ = k / (s·n)` per ABF26 Definition 2.5 (the alphabet is `F^s`), **not** `k/n` —
with `k/n` the radius `1 - ρ - η` would undershoot capacity by a factor-`s` error.

**Folding admissibility (2026-07-18 fix).** GG25 Corollary 4.10 quantifies over
`s`-folded RS codes *per its Definition 2.18 [GR08]*, which is not `frsCode` for an
arbitrary `ω`: it requires (i) a field with `|F| > s·n`, and (ii) distinct evaluation
points `α₁, …, α_n` with pairwise-disjoint `ω`-orbits (`αᵢ·ωᵗ ≠ αⱼ` for all `i ≠ j`,
`t < s`). This statement previously took `frsCode domain k s ω` raw, with *no*
hypotheses on `ω` or the domain, so it claimed the GG25 bound for degenerate folds —
e.g. `ω = 0` or `ω` of multiplicative order `< s`, where a fold's `s`-tuple repeats
entries and the subspace-design structure underlying the proof chain
(GG25 Thm 2.19 [GK16] → Thm 4.8 → Cor 4.9/4.10) breaks — codes the source does not
cover. We now carry the source hypotheses: `ReedSolomon.Folded.Admissible`
(ArkLib's GR08 injectivity condition — GG25's inter-orbit clause plus the intra-orbit
`ω`-order-`≥ s` strengthening documented in `ReedSolomon/Folded.lean`, exactly the
condition used by `dim_frsCode`/`minDist_frsCode`), `ω ≠ 0`, and `|F| > s·n`
(Definition 2.18's `q > sn`).

A corollary of T4.13 via T2.18 (FRS is τ-subspace-design). Admitted as an external
result.

**Generator hypothesis (2026-07-21 Phase-A merge audit).** `_hω_gen : ω` generates `F×`
is carried because this bound's proof chain runs through T2.18
(`frs_is_subspaceDesign_gk16`), whose unguarded form is FALSE for low-order `ω`
(counterexample `ω = -1` over `𝔽₁₀₁`, order 2 — admissibility only forces
`ord(ω) ≥ s`; see the T2.18 docstring). GG25's own Def 2.18/Thm 2.19 restatement
(`q > sn` only) is falsified by the same counterexample, so the generator condition is
treated as the implicit source assumption inherited from [GK16 Lemma 12]; recorded
upstream as PAPER_REVS #13. -/
theorem frs_epsMCA_capacity_gg25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hω : ω ≠ 0)
    (_hω_gen : orderOf ω = Fintype.card F - 1)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (_hcard : s * Fintype.card ι < Fintype.card F)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt : η < 1)
    (_hs_gt : (s : ℝ) > 16 / η ^ 2) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    mcaError (AffineLineGenerator F) (ReedSolomon.Folded.frsCode domain k s ω)
        (1 - ρ - η) ≤
      ENNReal.ofReal (2 * n / (η * Fintype.card F)
        + 24 / (η ^ 3 * Fintype.card F)) := by
  sorry -- ABF26-T4.14; external admit [GG25 Cor 4.10].

/-- The univariate-powers generator `x ↦ (1,x,…,x^k)`. -/
def univariatePowersGenerator (F : Type) [Field F] (k : ℕ) :
    Generator F (Fin (k + 1)) F :=
  fun x i => x ^ (i : ℕ)

/-- **[BCGM25 Theorem 8.2 + Definition 8.1], univariate-powers MCA instance.**
For any `F`-linear code `C ⊆ A^n` (with any finite `F`-module alphabet `A`,
matching [BCGM25]'s `Σ`), degree `k ≥ 1` with `|F| ≥ k + 1`, tradeoff `η ∈ (0, δ_min)`,
and radius `δ ≤ 1 - (ρ_C + η)^{1/(k+2)}` (where `ρ_C := 1 - δ_min`):

  `mcaError(G_k, C, δ) ≤ (n·γ_k/η)·(k/|F|)
      + max( 2k / (η·((ρ_C+η)^{1/(k+2)} - (ρ_C+η)^{1/(k+1)})·|F|),
             (k+1)·(k+2) / (η·|F|) )`,   `γ_k := 1 - (ρ_C+η)^{1/(k+1)}`.

This is [BCGM25]'s error function `ξ_{C,k,|F|}` (Definition 8.1, middle branch) for the
univariate-powers generator `G_k : x ↦ (1, x, …, x^k)`, instantiated at `S = F`
via Theorem 8.2 (`s = 1`, `d₁ = k`; its hypothesis `|S| ≥ d + 1` is
`|F| ≥ k + 1`). ArkLib's canonical generator-parametric MCA error lets the conclusion
be stated directly as `mcaError G_k C δ`. The `η < δ_min` hypothesis keeps
`ρ_C + η < 1`, so the branch guard is non-vacuous and the bound's inner denominator
`(ρ_C+η)^{1/(k+2)} - (ρ_C+η)^{1/(k+1)}` is strictly positive.

**History (2026-07-18).** This replaces a tracked placeholder
(`subspaceDesign_epsCA_curves_polynomial_generators_bcgm25`) that borrowed the GG25
affine bound `(t·n + 4t³)/|F|` with a `k`-independent RHS — **false** for large curve
degree `k` (exact counterexample at `n=1, t=1, q=7, k=6`: `ε ≥ 6/7 > 5/7`), as flagged
by both 2026-07 reviews. [BCGM25]'s true error necessarily grows with `k`. [BCGM25] =
ePrint 2025/2051 (Bordage–Chiesa–Guan–Manzur, "All Polynomial Generators Preserve
Distance with Mutual Correlated Agreement"); statement checked against Definition 8.1
and Theorem 8.2 in the primary PDF. -/
theorem linear_mcaError_powers_bcgm25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ) (δ_min η δ : ℝ≥0)
    (_hk : 1 ≤ k)
    (_hcard : k + 1 ≤ Fintype.card F)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_δ_min : η < δ_min)
    (_hδ : (δ : ℝ) ≤ 1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2))) :
    mcaError (univariatePowersGenerator F k) C (δ : ℝ) ≤
      ENNReal.ofReal
        (((Fintype.card ι : ℝ)
              * (1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1))) / η)
            * ((k : ℝ) / Fintype.card F)
          + max
              (2 * (k : ℝ) /
                ((η : ℝ)
                  * ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2))
                      - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1)))
                  * Fintype.card F))
              (((k : ℝ) + 1) * ((k : ℝ) + 2) / ((η : ℝ) * Fintype.card F))) := by
  sorry -- external admit [BCGM25 Thm 8.2 + Def 8.1] (univariate-powers MCA form).

end SubspaceDesignFRS

end CodingTheory

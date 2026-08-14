/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Connections between list decoding and correlated agreement (ABF26 §5)

External-admit *statements* for the §5 theorems that link list-size bounds to
correlated-agreement error bounds and vice versa. From ABF26 (Arnon-Boneh-Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, 2026), §5.

These four theorems directly bridge the Grand List Decoding Challenge and the
Grand MCA Challenge of §1. T5.1 turns a list-size bound into an MCA bound;
T5.2 / T5.3 turn CA bounds into list-size bounds; T5.4 demonstrates that the
implication "list-decoding ⇒ CA" cannot be tight in general.

## Main statements (external admits)

- `linear_mcaError_le_of_Lambda_le` — ABF26 T5.1 [GCXK25 Thm 3]: list decoding at
  `δ` (below the relative minimum distance of `C`, per the source) with list size `L`
  implies `ε_mca(C, 1 - √(1-δ+η)) ≤ (L²·δ·n + 1/η)/|F|`.
- `rs_Lambda_le_card_of_epsCa_lt` — ABF26 T5.2 [BCHKS25 Thm 1.9]:
  `ε_ca < 1/(2n)` below the source's joint-distance boundary implies
  `|Λ(C, δ)| ≤ |F|`.
- `rs_Lambda_extended_le_of_epsCa_intRadius` — [CS25 Thm 2], the source's native
  integer-radius form: CA for `RS[F, L, k]` at radius `f/n` with `f < n-k-1` and error
  parameter `ε < (|F|-n)/(k·|F|)` implies `|Λ(RS[F, L, k+1], f/n)| ≤ ⌈ε|F|(|F|-n) /
  (|F|-n-kε|F|)⌉`. This is the external admit.
- `rs_Lambda_extended_le_of_epsCa` — ABF26 T5.3 [CS25 Thm 2]: small `ε_ca` for
  `RS[F, L, k]` implies a quantitative list-size bound for the related code
  `RS[F, L, k+1]`. **Not an admit**: derived in-tree from the native form above
  (radius regime corrected to the source's `δ < (n-k-1)/n`; PAPER_REVS.md finding #8).
- `rs_epsCa_large_below_johnsonRadius` — ABF26 T5.4 [BenSassonGKS20 Lem 3.3]:
  characteristic-2 RS
  codes with rate `1/8` have `ε_ca(C, 1 - ρ^{1/3}) ≥ 1 - 1/|F|`, separating list
  decoding from CA.

## Coercion conventions

Each statement bounds an `ENNReal`-valued error (or `Lambda`) in terms of a real-valued
numeric expression. To wire real expressions into the formal APIs we use:

- `ENNReal.ofReal x` when `x : ℝ` is the RHS of a `≤` / `<` / `=`. This truncates
  negative `x` to `0`, which only matters in degenerate parameter regimes where the
  paper's bound is vacuous anyway.
- `mcaError` directly at real radii for MCA statements, preserving the source expression.
- `x.toNNReal` only where a CA statement uses the legacy `epsCa` interface and its radius
  is provably nonnegative in the source regime.

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

/-- **ABF26 Theorem 5.1 [GCXK25 Theorem 3].** List decoding implies MCA.

Let `C ⊆ F^n` be a linear code and let `δ, η ∈ (0, 1)`. If `|Λ(C, δ)| ≤ L`, then

  `ε_mca(C, 1 - √(1 - δ + η)) ≤ (L²·δ·n + 1/η) / |F|`

The conclusion's proximity radius `1 - √(1 - δ + η)` is the "Johnson lift" of `δ`
(plus the `η` slack). For Reed-Solomon codes this implies MCA up to the "2 Johnson"
regime via Corollary 3.3; for random RS codes (which list-decode to capacity by
Theorem 3.6) it implies MCA for random RS up to the Johnson bound.

The conclusion uses the canonical real-radius `mcaError` directly. In particular, no
`toNNReal` truncation or extra `η ≤ δ` hypothesis is needed when the displayed Johnson
lift is negative; this preserves the source's quantifiers over `δ, η ∈ (0,1)`.

**2026-07-18 fix (review finding B01) — restored source hypothesis
`δ < Δ_C`.** GCXK25 Theorem 3 reads: "Let `C ⊆ F_q^n` be a linear code
with minimum relative distance `Δ_C`. `p < Δ_C` and suppose `C` is
`(p, L)` list-decodable. `ε > 0`, `δ ≤ 1 - √(1 - p + ε)`. […] Then
`|Bad(π₁, π₂, δ)| < L²·p·n + 1/ε`." (Notation map: paper `p` = our `δ`,
paper `ε` = our `η`, paper's `(p, L)` list-decodability [GCXK25 Def 5]
= `Λ(C, δ) ≤ L`, paper `Δ_C` [GCXK25 Def 3, min relative distance over
distinct codeword pairs] = `Code.minDist C / n`.) The requirement
`p < Δ_C` is part of the source theorem; ABF26's restatement
(tex `thm:list-decoding-implies-mca`, which only assumes
`δ, η ∈ (0, 1)`) omits it, and this admit had mirrored the omission.
The hypothesis `_hδ_lt_dist` restores the source form. PAPER_REVS.md
finding #7 records the upstream (tex) omission.

**Kept conservatively (2026-07-21 review).** `_hδ_lt_dist` is retained, not broadened
back to the tex's `δ, η ∈ (0,1)`: the paper's printed form has not been verified true
without it (above the code distance the list radius/`Λ(C,δ)` behaviour is exactly what
GCXK25's `p < Δ_C` guards), so it is treated as an implicit source assumption rather than
a droppable one. Do not drop it without a first-hand GCXK25 re-derivation.

Admitted as an external result. -/
theorem linear_mcaError_le_of_Lambda_le
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδ_lt_dist :
        δ < (Code.minDist ((C : Set (ι → F))) : ℝ) / Fintype.card ι)
    (_hη_pos : 0 < η) (_hη_lt : η < 1)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞)) :
    mcaError (AffineLineGenerator F) C
        (1 - (1 - δ + η) ^ ((1 : ℝ) / 2)) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  sorry -- ABF26-T5.1; external admit [GCXK25 Thm 3].

end ListImpliesMCA

section CAImpliesList

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Theorem 5.2 [BCHKS25 Theorem 1.9].** Small CA error implies small list size.

Let `C := RS[F, L, k]` be a Reed-Solomon code with rate `ρ` and let `δ ∈ (0, 1-ρ)`.
If

  `ε_ca(C, δ_fld = δ + 2/n, δ_int) < 1/(2n)`

then

  `|Λ(C, δ)| ≤ |F|` .

The source defines the list-decoding radius using list size `≤ L`, so taking `L = |F|`
licenses a non-strict conclusion. Its witness has joint distance
`≥ 1 - ρ - 1/n`; therefore the interleaved threshold is an explicit parameter strictly
below that boundary, rather than the unsafe endpoint printed by ABF26. Admitted as an
external result. -/
theorem rs_Lambda_le_card_of_epsCa_lt
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ) (δ_int : ℝ≥0)
    (_hδ_pos : 0 < δ)
    (_hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι)
    (_hδ_int : (δ_int : ℝ) <
      1 - (k : ℝ) / Fintype.card ι - 1 / Fintype.card ι)
    (_hε_ca :
        epsCa (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((δ + 2 / Fintype.card ι).toNNReal)
            δ_int <
          ENNReal.ofReal (1 / (2 * Fintype.card ι))) :
    Lambda ((ReedSolomon.code domain k : Set (ι → F))) δ ≤ (Fintype.card F : ℕ∞) := by
  sorry -- ABF26-T5.2; external admit [BCHKS25 Thm 1.9].

/-- **[CS25 Theorem 2], native integer-radius form.** CS25 Theorem 2 reads: "If
`RS(F_q, D, k)` satisfies correlated agreement over lines with `f < n - k - 1` errors
with error parameter `ε < (q - n)/kq`, then `RS(F_q, D, k + 1)` is `(f/n, L)`-list
decodable, where `L = ⌈εq(q - n) / (q - n - kεq)⌉`."

Notation map: `q = |F|`, `n = |D| = |ι|`; CS25's `RS(F, D, k)` is evaluations of
polynomials of degree at most `k - 1` = `ReedSolomon.code domain k`; "satisfies
correlated agreement over lines with `f` errors with error parameter `ε`" (cf. CS25
Thm 1.4 / Def 2: `Pr_z[Δ(u₀ + z·u₁, C) ≤ f] > ε` implies joint agreement on a
subdomain of density `≥ 1 - f/n`) = `ε_ca(C, f/n, f/n) ≤ ε` (see
`δ_ε_correlatedAgreementAffineLines_iff_epsCA_le`); `(f/n, L)`-list decodability
(CS25 Def 1: every Hamming ball of radius `f/n·n = f` contains `≤ L` codewords)
= `Λ(RS[F, L, k+1], f/n) ≤ L`.

The integer hypothesis `f < n - k - 1` is stated as `f + k + 1 < n` (same statement
over `ℤ`, avoiding truncated `ℕ` subtraction). Note that `0 ≤ ε` (forced by the
`toReal ≤ ε` hypothesis) together with `ε < (q-n)/(kq)` forces `n < q`, so the
conclusion's denominator `q - n - kεq > 0` and the bound is never a `/0 = 0` artifact.

This is the source-faithful admit backing ABF26 Theorem 5.3; the paper-shaped
real-radius corollary `rs_Lambda_extended_le_of_epsCa` is *derived* from it
below (2026-07-18, review finding B02; PAPER_REVS.md finding #8). Admitted as an
external result. -/
theorem rs_Lambda_extended_le_of_epsCa_intRadius
    (domain : ι ↪ F) (k f : ℕ) (ε : ℝ)
    (_hk_pos : 0 < k)
    (_hf_lt : f + k + 1 < Fintype.card ι)
    (_hε_lt : ε < ((Fintype.card F : ℝ) - Fintype.card ι) / (k * Fintype.card F))
    (_hε_ca :
        (epsCa (F := F) (A := F)
            ((ReedSolomon.code domain k : Set (ι → F)))
            ((f : ℝ≥0) / Fintype.card ι) ((f : ℝ≥0) / Fintype.card ι)).toReal ≤ ε) :
    Lambda ((ReedSolomon.code domain (k + 1) : Set (ι → F))) ((f : ℝ) / Fintype.card ι) ≤
      (Nat.ceil
        (ε * Fintype.card F * ((Fintype.card F : ℝ) - Fintype.card ι)
          / ((Fintype.card F : ℝ) - Fintype.card ι - k * ε * Fintype.card F)) : ℕ∞) := by
  sorry -- ABF26-T5.3 source form; external admit [CS25 Thm 2].

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
    simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, and_congr_right_iff,
      Code.relHammingDist]
    intro _
    push_cast
    rw [div_le_iff₀ hn, div_le_iff₀ hn, div_mul_cancel₀ _ hn.ne', Nat.cast_le,
      ← Nat.le_floor_iff (by positivity)]
  unfold Lambda
  exact iSup_congr fun y => by rw [hset y]

/-- **ABF26 Theorem 5.3 [CS25 Theorem 2].** CA error converts to list size for related RS.

Let `C := RS[F, L, k]` and `C⁺ := RS[F, L, k+1]` be Reed-Solomon codes with `|L| = n`.
For `δ ∈ (0, (n-k-1)/n)` and `η ∈ [0, 1)`, if

  `ε_ca(C, δ) ≤ η · (1/k - n/(k·|F|))`

then

  `|Λ(C⁺, δ)| ≤ ⌈|F|/(1-η) · ε_ca(C, δ)⌉`

Pivots CA on `C` to a list-size bound on the extended code `C⁺`.

**Not an external admit** (2026-07-18, review finding B02): this is derived in-tree
from the source-native `rs_Lambda_extended_le_of_epsCa_intRadius` by instantiating the integer
radius at `f := ⌊δ·n⌋` and `ε := ε_ca(C, δ)`, using the `1/n`-quantisation of both
`ε_ca` (`epsCa_eq_of_floor_eq` + `epsCa_mono_left`) and `Λ`
(`Lambda_eq_floor_div_card`), plus ceiling monotonicity for the bound
`εq(q-n)/(q-n-kεq) ≤ q/(1-η)·ε` (valid because `ε_ca ≤ η(q-n)/(kq)`).

**Paper divergences** (PAPER_REVS.md finding #8):
- ABF26's tex states the radius regime as `δ ∈ (0, δ_min(C))` with
  `δ_min = (n-k+1)/n`; CS25 Theorem 2 only licenses the integer radius `f < n-k-1`,
  i.e. `δ < (n-k-1)/n` — two `1/n` grid steps tighter. The hypothesis `hδ_radius`
  uses the source's regime. Otherwise the tex form matches the source: the tex
  hypothesis `ε_ca ≤ η(1/k - n/(k|F|)) = η(q-n)/(kq)` with `η < 1` implies the
  source's strict `ε < (q-n)/(kq)`, and the tex conclusion `⌈q/(1-η)·ε_ca⌉` dominates
  the source's `⌈εq(q-n)/(q-n-kεq)⌉`.
- Added hypothesis `n < |F|` (the evaluation domain is a *proper* subset of the
  field): the tex leaves it implicit, but the strictness step above needs
  `(q-n)/(kq) > 0`. At `n = |F|` the tex hypothesis would force `ε_ca = 0`, which no
  proper code attains (`ε_ca ≥ 1/|F|` via the `γ = 0` point of a line through a word
  far from the code), so no non-vacuous instance is lost.

**Kept conservatively (2026-07-21 review).** The `(n-k-1)/n` radius is retained, not
widened to the tex's `δ_min`. This theorem is *derived* (not admitted) from the
source-native integer form, so the source regime is also the regime in which the
derivation is valid — the two extra `1/n` grid steps the tex allows are not merely
unverified but sit at the unique-decoding boundary where CS25 gives no guarantee.
Widening the radius would make the derivation fail, not silently admit a falsehood. -/
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
    rs_Lambda_extended_le_of_epsCa_intRadius
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

/-- **ABF26 Theorem 5.4 [BenSassonGKS20 Lemma 3.3].** List decoding does **not** tightly imply CA.

For all fields `F` of characteristic 2, the Reed-Solomon code `C := RS[F, F, |F|/8]`
of rate `ρ = 1/8` (using `F` itself as the evaluation domain — a "full-domain" RS)
satisfies

  `ε_ca(C, 1 - ρ^{1/3}) ≥ 1 - 1/|F|` .

In particular `1 - ρ^{1/3} = 1 - (1/8)^{1/3} = 0.5`; the Johnson bound for the same
code sits at `1 - √ρ - η ≈ 0.55`, where the list size is `≈ 40` (constant in `|F|`).
This witnesses a code that is list-decodable at the Johnson radius yet has CA error
≈ 1 at a smaller radius — separating list decoding from CA in general.

The source's two distinguished words both have distance exactly `1 - ρ^{2/3}` from
the code. Since `epsCa` guards on non-strict joint distance, the source licenses every
interleaved threshold strictly below that boundary. The no-loss radius
`δ_int = 1 - ρ^{1/3}` is a special case by monotonicity. Admitted as an external result. -/
theorem rs_epsCa_large_below_johnsonRadius
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

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness

/-!
# List-decoding bounds from ABF26 §3

External-admit *statements* for the §3 list-decoding bounds from ABF26
(Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026).
Each theorem is admitted as an external result with a tagged `sorry`, matching the
pattern established by `ProximityGap.CapacityBounds`. The statements use the
`ListDecodable.Lambda` function (block-maximised list size) introduced in
`ListDecodability.lean`, plus `qEntropy` from `Basic/Entropy.lean` and
`hammingBallVolume` from `HammingBallVolume.lean`.

These bounds sit immediately above the Grand List Decoding Challenge in ABF26 §1:
upper bounds (T3.2, C3.3) give candidate witnesses `δ_C*` for `|Λ(C^≡m, δ_C*)| ≤ ε*·|F|`,
while lower bounds (L3.7, C3.8, T3.9–T3.14) rule out witnesses above a threshold.

## Quantification conventions

The §3.2 / §3.2 RS theorems quantify over "infinitely many `q`", existentially-bound
codes, and "sufficiently large `n`". We capture these uniformly as follows:

- *Type-level data* (alphabet `F`, index type `ι`) is **universally** quantified at the
  theorem's outermost binder. The user instantiates at the call site.
- *Numeric quantifiers* ("there exists `α > 0`", "there exists `γ > 0`",
  "for infinitely many `q`") stay inside the theorem body using `∃` on numeric data.
- *Sufficiently large `n`* is captured as an explicit existential threshold `n₀ : ℕ`
  followed by `n₀ ≤ Fintype.card ι`. This matches Mathlib's `Filter.eventually`
  shape without dragging filters into a pure statement.
- *Infinitely many `q`* is captured as `∃ qs : ℕ → ℕ, StrictMono qs ∧ ∀ i, P (qs i)`.

## Main statements (external admits)

### Lower bounds — general codes (§3.2)

- `linear_lambda_ge_elias_volume_eli57` — ABF26 L3.7 [Eli57]: `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^{n-k}`.
- `linear_lambda_ge_entropy_volume` — ABF26 C3.8: `|Λ(C, δ)| ≥ q^{n(ρ-1+H_q(δ))} / √(8nδ(1-δ))`.
- `linear_C_le_generalized_singleton_st20` — ABF26 T3.9 [ST20 Thm 1.2]: bound on `|C|`
  when `|Λ(C, δ)| ≤ ℓ`.
- `large_alphabet_barrier_bdg24_agl23` — ABF26 T3.10: any code attaining the generalized
  Singleton bound requires exponential-in-`1/η` alphabet.
- `random_linear_lambda_lower_glmrsw22` — ABF26 T3.11 [GLMRSW22 Thm 4.1]: random linear
  code of appropriate rate has list size lower-bounded with high probability.

### Lower bounds — Reed-Solomon (§3.2)

- `rs_lambda_superpoly_extension_bkr06` — ABF26 T3.12 [BKR06 Cor 2.2]: superpolynomial
  list-size for RS over extension fields.
- `rs_lambda_large_prime_ghsz02` — ABF26 T3.13 [GHSZ02 Cor 20]: large list-size for RS
  over prime fields.
- `rs_lambda_high_rate_jh01` — ABF26 T3.14 [JH01 Thm 2]: large-rate RS list-size
  separation.

### Subspace-design upper bounds (§3.1)

- `subspaceDesign_list_decoding_cz25` — ABF26 T3.4 [CZ25 Thm B.5]: τ-subspace-design
  codes are list-decodable up to capacity.
- `frs_list_decoding_capacity_cz25` — ABF26 C3.5 [CZ25 Cor 2.21]: folded RS codes
  are list-decodable up to capacity (corollary of T3.4 via T2.18).

## Deferred statements

- ABF26 T3.6 [AGL24 Thm 1.1] — random Reed-Solomon list decoding near capacity; blocked
  on a uniform distribution over size-`n` subsets of `F` (same blocker as T4.15).
- ABF26 T3.15 [CW07] — algorithmic hardness barrier (discrete-log reduction). Out of
  scope per `docs/kb/ABF26_PLAN.md` §7 D2 (we formalise combinatorial statements only).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Eli57] Elias. (Lemma 3.7 in ABF26 cites the original Elias paper).
- [ST20] Shangguan-Tamo. Theorem 1.2.
- [BDG24], [AGL23] (Theorem 3.10 in ABF26).
- [GLMRSW22] (Theorem 4.1, source of T3.11).
- [BKR06] Cor 2.2, source of T3.12.
- [GHSZ02] Cor 20, source of T3.13.
- [JH01] Theorem 2, source of T3.14.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

section LowerBounds_General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Hamming-ball fiber count.** For a fixed centre `c`, the number of words `f` within
absolute distance `⌊δ · n⌋` of `c` equals `Vol_q(δ, n)` (independent of `c`), via the
existing `hammingBallVolume_eq_ncard_hammingBall` bridge. -/
theorem card_filter_hammingDist_le_eq_hammingBallVolume
    (c : ι → F) (δ : ℝ) :
    (Finset.univ.filter (fun f : ι → F => hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊)).card
      = hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
  rw [hammingBallVolume_eq_ncard_hammingBall δ c]
  have hfin : (hammingBall (F := F) c ⌊δ * Fintype.card ι⌋₊).Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  apply Finset.card_bij (fun x _ => x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Set.Finite.mem_toFinset, hammingBall, Set.mem_setOf_eq]
    convert hx using 2
  · intros; assumption
  · intro x hx
    rw [Set.Finite.mem_toFinset, hammingBall, Set.mem_setOf_eq] at hx
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    convert hx using 2

/-- **Relative-distance close-codeword set as an explicit absolute-distance set.** -/
theorem closeCodewordsRel_eq_setOf
    (C : Submodule F (ι → F)) (δ : ℝ) (hδ : 0 ≤ δ) (f : ι → F) :
    closeCodewordsRel ((C : Set (ι → F))) f δ =
      {c : ι → F | c ∈ C ∧ hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊} := by
  have h_n_pos : 0 < Fintype.card ι := Fintype.card_pos
  ext c
  simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, SetLike.mem_coe,
    Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
  refine and_congr_right (fun _ => ?_)
  rw [div_le_iff₀ (by exact_mod_cast h_n_pos), ← Nat.le_floor_iff (by positivity)]
  rw [hammingDist_comm c f]
  constructor <;> intro h <;> · convert h using 2

open Classical in
/-- **Averaging identity (Fubini).** Summing the point-list size `|Λ(C, δ, f)|` over all
centres `f` gives `|C| · Vol_q(δ, n)`: swap the order of summation and use that each
codeword `c ∈ C` is counted once per centre in its `⌊δ·n⌋`-ball, of which there are
exactly `Vol_q(δ, n)`. -/
theorem sum_ncard_closeCodewordsRel_eq
    (C : Submodule F (ι → F)) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑ f : ι → F, (closeCodewordsRel ((C : Set (ι → F))) f δ).ncard
      = (C : Set (ι → F)).ncard * hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
  have hsummand : ∀ f : ι → F, (closeCodewordsRel ((C : Set (ι → F))) f δ).ncard
      = (Finset.univ.filter
          (fun c : ι → F => c ∈ C ∧ hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊)).card := by
    intro f
    rw [closeCodewordsRel_eq_setOf C δ hδ f, ← Set.ncard_coe_finset]
    congr 1
    ext c
    simp
  simp_rw [hsummand, Finset.card_filter]
  rw [Finset.sum_comm]
  have hstep : ∀ c : ι → F,
      (∑ f : ι → F, if c ∈ C ∧ hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊ then 1 else 0)
        = if c ∈ C then hammingBallVolume (Fintype.card F) δ (Fintype.card ι) else 0 := by
    intro c
    by_cases hc : c ∈ C
    · simp only [hc, true_and, if_true]
      rw [← Finset.card_filter]
      exact card_filter_hammingDist_le_eq_hammingBallVolume c δ
    · simp [hc]
  simp_rw [hstep]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext c; simp

/-- **ABF26 Lemma 3.7 [Eli57].** Elias volume lower bound on list size:

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |F|`, `n = |ι|`, and `k = dim(C)` is the dimension of the linear code `C`
(so `|C| = q^k`). **Now proved in-tree** by the paper's averaging argument: the mean of
the point-list size `|Λ(C, δ, f)|` over uniformly random centres `f` is
`|C| · Vol / q^n = Vol / q^{n-k}` (`sum_ncard_closeCodewordsRel_eq`), so some centre
attains at least the mean, and `Lambda` is the supremum over centres. Uses
`hammingBallVolume` (ABF26 D2.4) from `HammingBallVolume.lean`. -/
theorem linear_lambda_ge_elias_volume_eli57
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  classical
  set q : ℕ := Fintype.card F with hq
  set n : ℕ := Fintype.card ι with hn
  set k : ℕ := Module.finrank F C with hk
  set Vol : ℕ := hammingBallVolume q δ n with hVol
  have hq_pos : 0 < q := Fintype.card_pos
  have hq_pos_real : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt _hδ_pos
  set cnt : (ι → F) → ℕ := fun f => (closeCodewordsRel ((C : Set (ι → F))) f δ).ncard with hcnt
  -- `|C| = q ^ k` as naturals.
  have hcard_C : (C : Set (ι → F)).ncard = q ^ k := by
    have h1 : (C : Set (ι → F)).ncard = Nat.card C := by
      rw [← Nat.card_coe_set_eq]; rfl
    rw [h1, hq, hk, ← Nat.card_eq_fintype_card (α := F)]
    exact Module.natCard_eq_pow_finrank (K := F) (V := C)
  -- Total count over all centres `= |C| · Vol = q^k · Vol`.
  have hsum : ∑ f : ι → F, cnt f = q ^ k * Vol := by
    rw [hcnt]
    rw [sum_ncard_closeCodewordsRel_eq C δ hδ_nonneg, hcard_C]
  -- Number of centres is `q ^ n`.
  have hcard_univ : (Finset.univ : Finset (ι → F)).card = q ^ n := by
    rw [Finset.card_univ, hq, hn, Fintype.card_fun]
  -- Real arithmetic identity `q^n · (Vol / q^(n-k)) = q^k · Vol`.
  have h_arith : (q : ℝ) ^ n * ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) = (q : ℝ) ^ k * Vol := by
    rw [Real.rpow_sub hq_pos_real, Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  -- A centre `f₀` whose point list realises at least the mean.
  have hmean_le : ∃ f₀ : ι → F,
      ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) ≤ (cnt f₀ : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hsum_real : (∑ f : ι → F, (cnt f : ℝ)) = (q : ℝ) ^ k * Vol := by
      have : ((∑ f : ι → F, cnt f : ℕ) : ℝ) = ((q ^ k * Vol : ℕ) : ℝ) := by exact_mod_cast hsum
      push_cast at this ⊢
      convert this using 2
    have hlt : (∑ f : ι → F, (cnt f : ℝ))
        < ∑ _f : ι → F, ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty
      · intro f _; exact hcon f
    rw [Finset.sum_const, hcard_univ, hsum_real] at hlt
    have : (q : ℝ) ^ k * Vol < (q : ℝ) ^ k * Vol := by
      calc (q : ℝ) ^ k * Vol < (q ^ n : ℕ) • ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) := hlt
        _ = (q : ℝ) ^ n * ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) := by
              rw [nsmul_eq_mul]; push_cast; ring
        _ = (q : ℝ) ^ k * Vol := h_arith
    exact lt_irrefl _ this
  obtain ⟨f₀, hf₀⟩ := hmean_le
  -- Conclude: `Lambda ≥ |Λ(C, δ, f₀)| ≥ ofReal(mean)`.
  have hLam : ((cnt f₀ : ℕ∞) : ENNReal) ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
    apply ENat.toENNReal_mono
    rw [hcnt]
    exact le_iSup (fun f => ((closeCodewordsRel ((C : Set (ι → F))) f δ).ncard : ℕ∞)) f₀
  calc ENNReal.ofReal ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k))
      ≤ ENNReal.ofReal (cnt f₀ : ℝ) := ENNReal.ofReal_le_ofReal hf₀
    _ = ((cnt f₀ : ℕ∞) : ENNReal) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
    _ ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := hLam

/-- **ABF26 Corollary 3.8.** Elias's list-size lower bound (L3.7) made explicit via the
MS77 volume estimate `Vol_q(δ, n) ≥ q^{n·H_q(δ)} / √(8·n·δ·(1-δ))`: dividing by
`q^{n-k}` and writing `ρ := k/n` gives the list-size bound

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`.

Uses `qEntropy` (ABF26 D2.2). Admitted as an external result.

The hypothesis `_hδn_int` (the radius `δ·n` is an integer) is the regime in which the
MS77 single-term Stirling estimate is stated; the paper's corollary inherits it
implicitly. Without it the bound is false at small `δ`: for `0 < δ·n < 1` the relative
ball collapses to Hamming radius `0`, so the list is `{f} ∩ C` while the entropy-volume
RHS can exceed `1`. -/
theorem linear_lambda_ge_entropy_volume
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδn_int : ∃ d : ℕ, (d : ℝ) = δ * Fintype.card ι) :
    let q : ℕ := Fintype.card F
    let n : ℕ := Fintype.card ι
    let k : ℕ := Module.finrank F C
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  sorry -- ABF26-C3.8; external admit, uses MS77 volume estimate.

/-- **ABF26 Theorem 3.9 [ST20 Thm 1.2].** Generalized Singleton bound for list decoding.
Let `F` be a finite field, `0 < ℓ < |F|`, `δ ∈ (0, 1)`, and let `C ⊆ F^n` be a linear
error-correcting code of rate `ρ` with `|Λ(C, δ)| ≤ ℓ`. Then:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}`

Equivalently, `δ ≤ ℓ/(ℓ+1) · (1-ρ)`.

**Rate hypothesis `_hδ_bound` (2026-07-24 fix).** The cardinality form of the bound
requires the rate–radius relation `δ ≤ ℓ/(ℓ+1)·(1-ρ)` (with `ρ = dim C / n`), which ST20
*derives* from `ℓ`-list-decodability. Carrying only the list-decoding premise `_hΛ` is
**not** enough for the cardinality conclusion: the ternary length-3 repetition code
`C = {000,111,222}` over `𝔽₃` is `(δ=1/2, ℓ=1)`-list-decodable (minimum distance 3, so the
radius-`⌊δn⌋ = 1` balls are disjoint, giving `|Λ| ≤ 1`), yet
`⌊(ℓ+1)/ℓ·δ·n⌋ = ⌊3⌋ = 3` forces the RHS to `3^0 = 1 < 3 = |C|`. The obstruction is the
floor/integer-radius quantisation — `_hΛ` alone does not pin `δ·n` to the lattice on which
the pigeonhole exponent is meaningful (flagged by external review, 2026-07-24). We therefore
carry the equivalent rate–radius relation `_hδ_bound` as a hypothesis; under it the
cardinality bound is a direct consequence of `|C| = |F|^{dim C}` and
`⌊(ℓ+1)/ℓ·δ·n⌋ ≤ n - dim C`, so this leaf is now **proved in-tree** (axiom-clean) rather
than admitted. The list-decoding premise `_hΛ` is retained to document the ST20 context in
which `_hδ_bound` arises. -/
theorem linear_C_le_generalized_singleton_st20
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hδ_bound : δ ≤ (ℓ : ℝ) / (ℓ + 1) *
      (1 - (Module.finrank F C : ℝ) / Fintype.card ι))
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  classical
  set q : ℕ := Fintype.card F with hq
  set n : ℕ := Fintype.card ι with hn
  set k : ℕ := Module.finrank F C with hk
  -- `|C| = q ^ k` (linearity), reusing the idiom from `linear_lambda_ge_volume`.
  have hcard_C : (C : Set (ι → F)).ncard = q ^ k := by
    have h1 : (C : Set (ι → F)).ncard = Nat.card C := by
      rw [← Nat.card_coe_set_eq]; rfl
    rw [h1, hq, hk, ← Nat.card_eq_fintype_card (α := F)]
    exact Module.natCard_eq_pow_finrank (K := F) (V := C)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 < q := hq ▸ Fintype.one_lt_card
    exact_mod_cast this.le
  have hnpos : (0 : ℝ) < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast _hℓ_pos
  -- `k ≤ n` (rank of a subspace of `F^n` is at most `n`).
  have hkn : k ≤ n := by
    rw [hk, hn]
    have h := Submodule.finrank_le C
    rwa [Module.finrank_fintype_fun_eq_card] at h
  -- From `_hδ_bound`, `(ℓ+1)/ℓ · δ ≤ 1 - k/n`, hence `(ℓ+1)/ℓ · δ · n ≤ n - k`.
  have hmid : ((ℓ : ℝ) + 1) / ℓ * δ ≤ 1 - (k : ℝ) / n := by
    have hfac : (0 : ℝ) < ((ℓ : ℝ) + 1) / ℓ := by positivity
    calc ((ℓ : ℝ) + 1) / ℓ * δ
        ≤ ((ℓ : ℝ) + 1) / ℓ * ((ℓ : ℝ) / ((ℓ : ℝ) + 1) * (1 - (k : ℝ) / n)) :=
          mul_le_mul_of_nonneg_left hδ_bound (le_of_lt hfac)
      _ = 1 - (k : ℝ) / n := by field_simp
  have hstep : ((ℓ : ℝ) + 1) / ℓ * δ * n ≤ (n : ℝ) - k := by
    calc ((ℓ : ℝ) + 1) / ℓ * δ * n
        = (((ℓ : ℝ) + 1) / ℓ * δ) * n := by ring
      _ ≤ (1 - (k : ℝ) / n) * n := mul_le_mul_of_nonneg_right hmid (le_of_lt hnpos)
      _ = (n : ℝ) - k := by field_simp
  have hfloor : Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) ≤ n - k := by
    rw [← Nat.cast_sub hkn] at hstep
    calc Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n)
        ≤ Nat.floor (((n - k : ℕ) : ℝ)) := Nat.floor_le_floor hstep
      _ = n - k := Nat.floor_natCast _
  -- Conclude: `q^k ≤ q^(n - ⌊…⌋)` since the exponent is `≥ k`.
  have hexp : (k : ℝ) ≤ (n : ℝ) - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) : ℝ) := by
    have hle : (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) : ℝ) ≤ (n : ℝ) - k := by
      have := hfloor
      rw [← Nat.cast_sub hkn]
      exact_mod_cast this
    linarith
  rw [hcard_C]
  calc ((q ^ k : ℕ) : ℝ)
      = (q : ℝ) ^ (k : ℝ) := by rw [Nat.cast_pow, Real.rpow_natCast]
    _ ≤ (q : ℝ) ^ ((n : ℝ) - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hq1 hexp

end LowerBounds_General

section LargeAlphabetBarrier

/-- **ABF26 Theorem 3.10 [BDG24, AGL23].** Large-alphabet barrier for generalized
Singleton attainment. For every `ℓ ≥ 2` and `ρ ∈ (0, 1)` there exists a constant
`α_ℓρ > 0` such that for every `η > 0` and every sufficiently large `n`, every linear
error-correcting code `C ⊆ F^n` of rate `ρ` with `|Λ(C, ℓ/(ℓ+1) · (1-ρ-η))| ≤ ℓ`
satisfies:

  `|F| ≥ 2^{α_ℓρ / η}`

i.e. attaining the generalized Singleton bound up to `η` slack requires alphabet size
exponential in `1/η`. We existentially package the "sufficiently large" threshold as
an explicit `n₀` parameter rather than relying on Lean's `eventually` API. Per AGR23
Theorem 1.1 the threshold is `n ≥ Ω_{ℓ,ρ}(1/η)`, so `n₀` is (correctly) bound *inside*
the `∀ η` quantifier.

**Rate hypothesis (2026-07-18 source-fidelity fix).** Phrased as the exact pin
`Module.finrank F C = ρ · n`, matching the sources' quantifier structure. Both sources
prove the barrier for codes of a *fixed* rate `ρ`: AGR23 Theorem 1.1 reads "Let `C` be
a code of rate `R`" with the constant `α_{L,R}` and the threshold `n ≥ Ω_{L,R}(1/ε)`
depending on that exact rate, and BDG24 (the `ℓ = 2` progenitor) is stated for
`[n, k]`-MDS codes of fixed dimension. The previous `finrank ≥ ρ·n` reading asserted a
single uniform `α`/`n₀` for *all* rates above `ρ` — an uniformization neither source
proves (their radius `ℓ/(ℓ+1)·(1−ρ−η)` is calibrated to the code's own rate, and a
higher-rate code admits no valid `ε` re-parameterisation once `finrank/n ≥ ρ + η`);
flagged as H01 in the 2026-07-17 review. For irrational `ρ` the equality is
unsatisfiable and the statement is vacuous — as in the sources, whose asymptotic
statements fix `ρ` as a constant and quantify over lengths realising it; instantiate
at rational `ρ = finrank/n`.

Admitted as an external result. -/
theorem large_alphabet_barrier_bdg24_agl23
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (η : ℝ), 0 < η →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F]
            (C : Submodule F (ι → F)),
            n₀ ≤ Fintype.card ι →
            (Module.finrank F C : ℝ) = ρ * Fintype.card ι →
            Lambda ((C : Set (ι → F))) ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  sorry -- ABF26-T3.10; external admit [BrakensiekDG24, AlrabiahGR23] (tex L1460).

end LargeAlphabetBarrier

section RandomLinear

/-- **ABF26 Theorem 3.11 [GLMRSW22 Thm 4.1].** Random linear code lower bound —
source-faithful high-probability (counting) form. GLMRSW22 Theorem 4.1 (verbatim, their
variables): "Fix a prime power `q`, fix `p ∈ (0, 1 − 1/q)`, and fix `δ ∈ (0, 1)`. There
exists `ε_{p,q,δ} > 0` such that for all `ε ∈ (0, ε_{p,q,δ})` and `n` sufficiently
large, a random linear code in `F_q^n` of rate `1 − h_q(p) − ε` is not
`(p, ⌊h_q(p)/ε − δ⌋)`-list-decodable with probability `1 − q^{−Ω(n)}`." Their random
model (§1.2): "a uniformly random subspace of `F_q^n` of certain dimension" (their
working model samples `Rn` uniform generator rows; total-variation-exponentially close,
and of dimension exactly `Rn` with probability `1 − exp(−Ω(n))`).

Variable map (ABF26 T3.11 = the form below): GLMRSW22's radius `p` is our `δ`, their
slack `δ` is our `ε`, their `ε_{p,q,δ}` is our `γ`, and their rate `1 − h_q(p) − ε`
is our `ρ` (so their `ε = 1 − H_q(δ) − ρ`, giving the list bound
`⌊H_q(δ)/(1 − H_q(δ) − ρ) − ε⌋`).

**Probability as counting (2026-07-18 source-fidelity fix).** ArkLib has no probability
distribution over linear codes, so the `1 − q^{−Ω(n)}` statement is carried in the
equivalent finite counting form over the uniform family
`{C : Submodule F (ι → F) | finrank C = k}`:

  `#{C : finrank C = k ∧ |Λ(C, δ)| ≤ ⌊…⌋} ≤ q^{−c·n} · #{C : finrank C = k}`

with `c > 0` the `Ω(n)` constant (dependence on `q, δ, ε, ρ` allowed by its binder
position). The previous statement recorded only the bare existence of one witness code,
losing the high-probability content (2026-07-17 review, SOURCE_LEDGER #8); the
existence form is now *derived* in-tree as
`random_linear_lambda_lower_exists_glmrsw22` below.

**Dimension pin.** The paper's code has rate exactly `ρ`, with dimension `ρ·n` treated
as an integer "for exposition". Exact real equality `k/n = ρ` is unsatisfiable for
irrational `ρ`, so the dimension is pinned two-sidedly into the band
`ρ ≤ k/n ≤ ρ + 1/n` (admitting exactly `k = ⌈ρ·n⌉` up to the boundary case), matching
the pre-existing convention of this file. -/
theorem random_linear_lambda_lower_glmrsw22
    (q : ℕ) (_hq_pp : IsPrimePow q)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (_hε_pos : 0 < ε) (_hε_lt : ε < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q → n₀ ≤ Fintype.card ι →
            ∀ k : ℕ,
              ρ ≤ (k : ℝ) / Fintype.card ι →
              (k : ℝ) / Fintype.card ι ≤ ρ + 1 / Fintype.card ι →
              (({C : Submodule F (ι → F) | Module.finrank F C = k ∧
                  Lambda ((C : Set (ι → F))) δ ≤
                    ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) :
                      ℕ∞)}.ncard : ℝ))
                ≤ (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) *
                    (({C : Submodule F (ι → F) | Module.finrank F C = k}.ncard : ℝ)) := by
  sorry -- ABF26-T3.11; external admit [GLMRSW22 Thm 4.1].

/-- **Existence corollary of ABF26 T3.11 [GLMRSW22 Thm 4.1]** (derived in-tree from the
high-probability counting form `random_linear_lambda_lower_glmrsw22`): some linear code
`C ⊆ F^n` with dimension in the band `ρ ≤ finrank/n ≤ ρ + 1/n` satisfies

  `|Λ(C, δ)| > ⌊H_q(δ) / (1 - H_q(δ) - ρ) - ε⌋` .

This is the bare-existence statement the file previously admitted directly; it is now a
*theorem*: the bad-event count is `< 1` of the family, the family
`{C | finrank C = ⌈ρ·n⌉}` is nonempty (a coordinate-kernel subspace realises any
dimension `≤ n`), so a good code exists.

The extra hypothesis `0 ≤ ρ` (trivially true in the source's regime, where rates
approach capacity `1 − H_q(δ) ≥ ρ > 1 − H_q(δ) − γ` from below with `γ` small) is
needed here only because `Entropy.lean` does not yet prove `H_q(δ) < 1` for
`δ < 1 − 1/q`, which would let `γ` be shrunk below `1 − H_q(δ)`. -/
theorem random_linear_lambda_lower_exists_glmrsw22
    (q : ℕ) (hq_pp : IsPrimePow q)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 0 ≤ ρ → 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q → n₀ ≤ Fintype.card ι →
            ∃ C : Submodule F (ι → F),
              ρ ≤ (Module.finrank F C : ℝ) / Fintype.card ι ∧
              (Module.finrank F C : ℝ) / Fintype.card ι ≤ ρ + 1 / Fintype.card ι ∧
              ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) : ℕ∞) <
                Lambda ((C : Set (ι → F))) δ := by
  obtain ⟨γ, hγ_pos, hmain⟩ :=
    random_linear_lambda_lower_glmrsw22 q hq_pp δ hδ_pos hδ_lt ε hε_pos hε_lt
  refine ⟨γ, hγ_pos, fun ρ hρ0 hργ hρH => ?_⟩
  obtain ⟨c, hc_pos, n₀, hbound⟩ := hmain ρ hργ hρH
  refine ⟨n₀, fun {ι} _ _ _ {F} _ _ _ hcard hn => ?_⟩
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_posR : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hn_pos
  -- `ρ ≤ 1` via `0 ≤ H_q(δ)`.
  have hH_nonneg : 0 ≤ qEntropy q δ := by
    rw [qEntropy_eq_qaryEntropy_div_log]
    have hδ1 : δ ≤ 1 := by
      have hq_inv : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
      linarith
    exact div_nonneg
      (Real.qaryEntropy_nonneg hδ_pos.le hδ1)
      (Real.log_natCast_nonneg q)
  have hρ1 : ρ ≤ 1 := hρH.le.trans (by linarith)
  -- The paper's dimension: `k = ⌈ρ·n⌉`, which sits in the band.
  set k : ℕ := ⌈ρ * (Fintype.card ι : ℝ)⌉₊ with hk_def
  have hband1 : ρ ≤ (k : ℝ) / (Fintype.card ι : ℝ) := by
    rw [le_div_iff₀ hn_posR]
    exact Nat.le_ceil _
  have hband2 : (k : ℝ) / (Fintype.card ι : ℝ) ≤ ρ + 1 / (Fintype.card ι : ℝ) := by
    rw [div_le_iff₀ hn_posR]
    have h1 : (k : ℝ) < ρ * (Fintype.card ι : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (ρ + 1 / (Fintype.card ι : ℝ)) * (Fintype.card ι : ℝ)
        = ρ * (Fintype.card ι : ℝ) + 1 := by
      field_simp
    rw [h2]
    linarith
  have hkn : k ≤ Fintype.card ι := Nat.ceil_le.mpr (by nlinarith)
  -- The family `{C | finrank C = k}` is nonempty: a coordinate-kernel subspace works.
  obtain ⟨t, -, htcard⟩ := Finset.exists_subset_card_eq
    (show Fintype.card ι - k ≤ (Finset.univ : Finset ι).card by
      simp only [Finset.card_univ]; omega)
  have hwitness : ∃ C₀ : Submodule F (ι → F), Module.finrank F C₀ = k := by
    refine ⟨LinearMap.ker (LinearMap.funLeft F F (fun x : ↥t => (x : ι))), ?_⟩
    have hsurj : Function.Surjective (LinearMap.funLeft F F (fun x : ↥t => (x : ι))) :=
      LinearMap.funLeft_surjective_of_injective F F _ Subtype.val_injective
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.funLeft F F (fun x : ↥t => (x : ι)))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi,
      Module.finrank_pi, Fintype.card_coe, htcard] at h1
    omega
  -- Bad-event count is strictly below the family count, so a good code exists.
  set B : ℕ∞ :=
    ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) : ℕ∞) with hB_def
  set bad : Set (Submodule F (ι → F)) :=
    {C | Module.finrank F C = k ∧ Lambda ((C : Set (ι → F))) δ ≤ B} with hbad_def
  set full : Set (Submodule F (ι → F)) := {C | Module.finrank F C = k} with hfull_def
  have hsub : bad ⊆ full := fun C hC => hC.1
  have hfull_pos : 0 < full.ncard := by
    obtain ⟨C₀, hC₀⟩ := hwitness
    exact (Set.ncard_pos (Set.toFinite full)).mpr ⟨C₀, hC₀⟩
  have hlt : (bad.ncard : ℝ) < (full.ncard : ℝ) := by
    have hkey := hbound hcard hn k hband1 hband2
    have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hq_pp.two_le
    have hrpow : (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq1 (by nlinarith)
    calc (bad.ncard : ℝ)
        ≤ (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) * (full.ncard : ℝ) := hkey
      _ < 1 * (full.ncard : ℝ) :=
          mul_lt_mul_of_pos_right hrpow (by exact_mod_cast hfull_pos)
      _ = (full.ncard : ℝ) := one_mul _
  have hssub : bad ⊂ full := by
    refine ⟨hsub, fun habs => ?_⟩
    have : full.ncard ≤ bad.ncard := Set.ncard_le_ncard habs (Set.toFinite bad)
    have : (full.ncard : ℝ) ≤ (bad.ncard : ℝ) := by exact_mod_cast this
    linarith
  obtain ⟨C, hCfull, hCbad⟩ := Set.exists_of_ssubset hssub
  have hCk : Module.finrank F C = k := hCfull
  refine ⟨C, ?_, ?_, ?_⟩
  · rw [hCk]; exact hband1
  · rw [hCk]; exact hband2
  · by_contra hle
    exact hCbad ⟨hCk, not_lt.mp hle⟩

end RandomLinear

section ReedSolomonBounds

/-- **ABF26 Theorem 3.12 [BKR06 Cor 2.2].** Reed-Solomon superpolynomial list-size over
extension fields. Fix `0 < α < β < 1`. For infinitely many prime powers `q` there exists
a Reed-Solomon code `C := RS[F_q, F_q, ⌊q^α⌋]` and a word `w : F_q → F_q` such that:

  `|Λ(C, 1 - q^{β-1}, w)| ≥ q^{(α - β²) · log₂ q}`

**Log base.** The paper's logs are base 2: its display continues
`q^{(α-β²)·log q} = 2^{(α-β²)·(log q)²}`, which is an identity precisely when
`log = log₂` (`q^x = 2^{x·log₂ q}`). Encoded as `Real.logb 2 q` (a natural-log
`Real.log q` here would weaken the exponent by a factor `1/ln 2`).

Admitted as an external result. -/
theorem rs_lambda_superpoly_extension_bkr06
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < β) (_hβ_lt : β < 1) :
    -- `qs` carries the prime-power requirement as a *conjunct* alongside
    -- `StrictMono`. The previous shape `∀ i, IsPrimePow (qs i) → P i` was
    -- vacuously satisfied by any non-prime-power sequence; we now require
    -- *every* `qs i` to be a prime power up front.
    ∃ qs : ℕ → ℕ, StrictMono qs ∧ (∀ i, IsPrimePow (qs i)) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = qs i →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let q : ℕ := qs i
            let k : ℕ := Nat.floor ((q : ℝ) ^ α)
            let δ : ℝ := 1 - (q : ℝ) ^ (β - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) ≥
              (q : ℝ) ^ ((α - β ^ 2) * Real.logb 2 q) := by
  sorry -- ABF26-T3.12; external admit [BKR06 Cor 2.2].

/-- **ABF26 Theorem 3.13 [GHSZ02 Cor 20].** Reed-Solomon large list-size over prime
fields. Fix `0 < α, β < 1`. For all sufficiently large primes `p`, there exists
`C := RS[F_p, F_p, ⌊p^α⌋]` and a word `w : F_p → F_p` such that:

  `|Λ(C, 1 - ((1-β)/α) · p^{α-1}, w)| > Ω(p^{p^α · β/2})`

Admitted as an external result. -/
theorem rs_lambda_large_prime_ghsz02
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < 1) (_hβ_pos : 0 < β) (_hβ_lt : β < 1) :
    ∃ (c : ℝ) (_ : 0 < c) (p₀ : ℕ),
      ∀ p : ℕ, Nat.Prime p → p₀ ≤ p →
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = p → Fintype.card ι = p →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let k : ℕ := Nat.floor ((p : ℝ) ^ α)
            let δ : ℝ := 1 - ((1 - β) / α) * (p : ℝ) ^ (α - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) >
              c * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) := by
  sorry -- ABF26-T3.13; external admit [GHSZ02 Cor 20].

/-- **ABF26 Theorem 3.14 [JH01 Thm 2].** Large-rate Reed-Solomon lower bound. Fix an
integer `j ≥ 2`. For infinitely many prime powers `q` with `q ≡ 1 (mod j+1)`, there
exists `C := RS[F_q, L, k]` with `|L| = j + 1` and rate `ρ ≈ (j-1)/(j+1)` together
with a word `w : L → F_q` such that:

  `|Λ(C, 1/(j+1), w)| > j`

Witnesses that high-rate RS codes cannot be list-decoded beyond `1/(j+1)` with list
size `j`.

**Encoding of the paper's parameters.** The paper's `|L| = j + 1` is the *block
length* (size of the evaluation domain), encoded here as `Fintype.card ι = j + 1`.
The dimension is pinned to `k := j` in ArkLib's `ReedSolomon.code domain k`
(= polynomials of degree `< k`, dimension `k`) convention: JH01's "rate
`≈ (j-1)/(j+1)`" refers to its own degree-`≤ k` convention (`k_JH = j - 1`,
dimension `j`). The pin matters in *both* directions:
* `k = j - 1` (dimension `j - 1`) is **unsatisfiable**: min distance
  `n - k + 1 = 3` while radius `1/(j+1)` permits a single error, so two list
  members would be within distance `2 < 3` — the list size is at most `1`,
  never `> j` (2026-06-10 re-review finding).
* an unconstrained `∃ k` would let degenerate dimensions (e.g. `k = j + 1`,
  `C = F^L`) satisfy the conclusion trivially.
With `k = j` the min distance is `2` and the `j + 1` drop-one-coordinate
interpolants of `w` realise a list of size `j + 1 > j` — JH01's construction.

Admitted as an external result. -/
theorem rs_lambda_high_rate_jh01
    (j : ℕ) (_hj_ge : 2 ≤ j) :
    -- Prime-power and modular requirements moved out of `→`-implications
    -- into conjuncts of the outer existential so the sequence cannot be
    -- vacuously satisfied by non-prime-powers (or values not ≡ 1 mod j+1).
    ∃ qs : ℕ → ℕ, StrictMono qs ∧
      (∀ i, IsPrimePow (qs i)) ∧ (∀ i, qs i % (j + 1) = 1) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = j + 1 →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let C := ReedSolomon.code domain j
            (j : ℕ∞) < (closeCodewordsRel ((C : Set (ι → F))) w (1 / (j + 1 : ℝ))).ncard := by
  sorry -- ABF26-T3.14; external admit [JH01 Thm 2].

end ReedSolomonBounds

section SubspaceDesignUpperBounds

/-- **ABF26 Theorem 3.4 [CZ25 Theorem B.5]** — source-native one-integer-parameter
form. CZ25 Theorem B.5 (verbatim, their variables): "Given a `F`-linear code
`C ⊆ (F^s)^n` of block length `n` and rate `R = k/sn`. Assume that `C ⊆ (F^s)^n` is a
`(ℓ, ℓ(k−1)/(s−ℓ+1))`-strong subspace designable code for all `ℓ ≤ s`. Then, `C` is
`(L/(L+1) · (1 − sR/(s−L+1)), L)` (average-radius) list-decodable for any `L ≤ s`."

In ABF26's τ-subspace-design abstraction (D2.16, `IsSubspaceDesign`; CZ25's strong
subspace-designable premise corresponds to the profile `τ(ℓ) = sR/(s−ℓ+1)` of T2.18,
up to `k` vs `k−1`), the statement reads: for every integer `1 ≤ L ≤ s`,

  `|Λ(C, L/(L+1) · (1 − τ(L)))| ≤ L` .

Note the source has ONE integer parameter `L`, appearing in both the radius and the
list bound. The ABF26 tex instead prints the `η`-form `|Λ(C, 1 − τ(1/η) − η)| ≤
(1 − τ(1/η))/η` with `τ` applied to the *real* argument `1/η` — ill-typed for a
profile `τ : ℕ → ℝ` whenever `1/η ∉ ℕ` (PAPER_REVS.md finding #10). A previous
version of this admit mirrored the tex by inventing a mixed rounding (radius at
`τ(⌈1/η⌉)`, bound at `τ(⌊1/η⌋)`) that no source licenses (2026-07-17 review, B08);
as of 2026-07-18 the admit is the source's integer statement above, and the `η`-form
is *derived* in-tree with one consistent rounding — see
`subspaceDesign_list_decoding_eta_cz25` (and the generic
`subspaceDesign_list_decoding_profile_le_cz25`).

`1 ≤ L` is implicit in CZ25 (their proof derives a contradiction from `L + 1 ≥ 2`
distinct polynomials; at `L = 0` the claim would fail for any word equal to a
codeword), and `L ≤ s` is their stated range.

Admitted as an external result. -/
theorem subspaceDesign_list_decoding_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (L : ℕ) (_hL_pos : 1 ≤ L) (_hL_le : L ≤ s) :
    Lambda ((C : Set (ι → Fin s → F)))
        ((L : ℝ) / (L + 1) * (1 - τ L)) ≤ (L : ℕ∞) := by
  sorry -- ABF26-T3.4; external admit [CZ25 Thm B.5].

/-- **Generic profile-domination corollary of ABF26 T3.4 [CZ25 Thm B.5]** (derived
in-tree from the integer admit `subspaceDesign_list_decoding_cz25`). If `t` dominates
the profile `τ` on the integers `1 ≤ L ≤ 1/η` (and `1/η ≤ s` keeps the chosen integer
inside CZ25's range), then

  `|Λ(C, 1 − t − η)| ≤ (1 − t)/η` .

This is the engine behind both the `⌊1/η⌋`-rounded `η`-form (T3.4 as printed in the
tex, `subspaceDesign_list_decoding_eta_cz25`) and the folded-RS corollary C3.5
(`frs_list_decoding_capacity_cz25`, where `t` is the *real-argument* FRS profile value
`sρ/(s − 1/η + 1)`). The proof instantiates the integer theorem at
`L := ⌊(1 − t)/η⌋` and uses monotonicity of `Λ` in the radius: `L + 1 > (1 − t)/η`
makes the integer radius `L/(L+1)·(1 − τ(L))` at least `1 − t − η`, and `L ≤ (1 − t)/η`
is the claimed list bound. This mirrors CZ25's own derivation of their Corollary 2.21
from their Theorem 1.3. -/
theorem subspaceDesign_list_decoding_profile_le_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (η t : ℝ) (hη_pos : 0 < η) (ht_nonneg : 0 ≤ t)
    (hτ_le : ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ 1 / η → τ L ≤ t)
    (hs : 1 / η ≤ (s : ℝ)) :
    (Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - t) / η) := by
  by_cases hquot : (1 : ℝ) ≤ (1 - t) / η
  · -- Main case: `L := ⌊(1 − t)/η⌋ ≥ 1`.
    set L : ℕ := ⌊(1 - t) / η⌋₊ with hL_def
    have hL_pos : 1 ≤ L := Nat.floor_pos.mpr hquot
    have hquot_nonneg : (0 : ℝ) ≤ (1 - t) / η := zero_le_one.trans hquot
    have hLle : (L : ℝ) ≤ (1 - t) / η := Nat.floor_le hquot_nonneg
    have hL_inv : (L : ℝ) ≤ 1 / η := hLle.trans (by gcongr; linarith)
    have hτL : τ L ≤ t := hτ_le L hL_pos hL_inv
    have hLs : L ≤ s := by exact_mod_cast hL_inv.trans hs
    have key := subspaceDesign_list_decoding_cz25 s τ C h L hL_pos hLs
    -- Radius comparison: `1 − t − η ≤ L/(L+1) · (1 − τ(L))`.
    have hfloor : (1 - t) / η < (L : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1t : 1 - t < η * ((L : ℝ) + 1) := by
      rw [div_lt_iff₀ hη_pos] at hfloor
      linarith
    have hrad : 1 - t - η ≤ (L : ℝ) / (L + 1) * (1 - τ L) := by
      have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hL1]
      have hmul : (L : ℝ) * τ L ≤ (L : ℝ) * t :=
        mul_le_mul_of_nonneg_left hτL (by positivity)
      nlinarith [hmul, h1t]
    have hchain : Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) ≤ (L : ℕ∞) :=
      (Lambda_mono hrad).trans key
    calc (Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) : ENNReal)
        ≤ ((L : ℕ∞) : ENNReal) := ENat.toENNReal_le.mpr hchain
      _ = (L : ENNReal) := ENat.toENNReal_coe L
      _ ≤ ENNReal.ofReal ((1 - t) / η) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hLle
  · -- Degenerate case: `(1 − t)/η < 1` forces a negative radius and an empty list.
    have hrad_neg : 1 - t - η < 0 := by
      rw [not_le, div_lt_one hη_pos] at hquot
      linarith
    have hempty : ∀ f : ι → Fin s → F,
        closeCodewordsRel ((C : Set (ι → Fin s → F))) f (1 - t - η) = ∅ := by
      intro f
      ext c
      simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hball
      exact absurd (hball.trans_lt hrad_neg) (not_lt.mpr (by positivity))
    have hzero : Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) = 0 := by
      have hrfl : Lambda ((C : Set (ι → Fin s → F))) (1 - t - η)
          = ⨆ f : ι → Fin s → F,
              (((closeCodewordsRel ((C : Set (ι → Fin s → F))) f (1 - t - η)).ncard :
                ℕ∞)) := rfl
      rw [hrfl]
      simp [hempty]
    rw [hzero]
    simp

/-- **ABF26 Theorem 3.4 [CZ25 Thm B.5] — `η`-form with one consistent rounding**
(derived in-tree from the integer admit `subspaceDesign_list_decoding_cz25`). For a
τ-subspace-design code `C ⊆ (F^s)^n` with `τ` non-decreasing and non-negative on
`{1, 2, …}`, and any `0 < η ≤ 1` with `1/η ≤ s`:

  `|Λ(C, 1 − τ(⌊1/η⌋) − η)| ≤ (1 − τ(⌊1/η⌋))/η` .

The ABF26 tex prints this with the ill-typed real argument `τ(1/η)` (PAPER_REVS.md
finding #10); here `1/η` is rounded ONE way (down) in both the radius and the bound,
and the derivation from the integer theorem is carried out by
`subspaceDesign_list_decoding_profile_le_cz25` with `t := τ(⌊1/η⌋)`, using
`MonotoneOn τ (Set.Ici 1)` to dominate `τ` at the smaller instantiation point
`⌊(1 − t)/η⌋ ≤ ⌊1/η⌋`. (`τ ≥ 0` — a design profile is a fraction of a dimension, cf.
`subspaceDesign_tau_lower` — keeps that point below `⌊1/η⌋`; `η ≤ 1` keeps both points
in `Ici 1`; `1/η ≤ s` keeps them in CZ25's range `L ≤ s`, a hypothesis the tex's
abstract statement omits but its only instantiation C3.5 carries as `1/η < s`.) -/
theorem subspaceDesign_list_decoding_eta_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C)
    (hτ_mono : MonotoneOn τ (Set.Ici 1)) (hτ_nonneg : ∀ r, 0 ≤ τ r)
    (η : ℝ) (hη_pos : 0 < η) (hη_le_one : η ≤ 1) (hηs : 1 / η ≤ (s : ℝ)) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) := by
  have hm : 1 ≤ ⌊1 / η⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hη_pos, one_mul]
    exact hη_le_one
  refine subspaceDesign_list_decoding_profile_le_cz25 s τ C h η (τ ⌊1 / η⌋₊) hη_pos
    (hτ_nonneg _) (fun L hL1 hLle => ?_) hηs
  exact hτ_mono (Set.mem_Ici.mpr hL1) (Set.mem_Ici.mpr hm) (Nat.le_floor hLle)

/-- **ABF26 Corollary 3.5 [CZ25 Corollary 2.21].** Folded Reed-Solomon codes are
list-decodable up to capacity. Let `C := FRS[F, L, k, s, ω]` be a folded RS code of
rate `ρ`. For any `η > 0` with `1/η < s`:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))`

When `η ≥ √(3/s)`, the bound simplifies to `|Λ(C, 1 - ρ - η)| ≤ 1/η`.

**Derived in-tree (2026-07-18).** No longer a separate external admit: this is proved
from T3.4's integer admit (`subspaceDesign_list_decoding_cz25`, via
`subspaceDesign_list_decoding_profile_le_cz25` at the real-argument profile value
`t := ρ·s/(s − 1/η + 1)`) together with T2.18 (`frs_is_subspaceDesign_gk16`, FRS is
τ-subspace-design) — the same route CZ25 use to derive their Corollary 2.21 from their
Theorem 1.3, and ABF26 to derive C3.5 from T3.4 + T2.18. Note the bound equals
`(1 − t)/η` verbatim: `1 − sρ/(s−1/η+1) = (s(1−ρ)+1−1/η)/(s+1−1/η)`. The hypothesis
`_hFn : n < |F|` is inherited from T2.18 (and implicit in CZ25's setting, where the
`s·n` distinct evaluation points `α_i·γ^j` force `|F| > s·n > n`).

**Rate convention.** The FRS code `FRS[F, L, k, s, ω] ⊆ (F^s)^n` has rate
`ρ = k / (s·n)` per ABF26 Definition 2.5 (the alphabet is `F^s`), **not** `k/n`.
With this `ρ` both the radius and the list bound are the paper's expressions
verbatim; e.g. the radius numerator `ρ·s = k/n`.

**Admissibility.** The paper's FRS definition (ABF26 Definition 2.15) bakes
`(L, s)`-admissibility of `ω` into the code; ArkLib's `frsCode` deliberately does not,
so this statement must carry it as the hypothesis `_hadm` (in the in-tree strengthened
GR08 form) together with `_hω : ω ≠ 0` (which admissibility alone does not imply when
`0 ∉ L`). Without them the fold degenerates — e.g. at `ω = 0` or `ω = 1` all folds
collapse — and the capacity bound is false.

**Generator hypothesis (2026-07-21 Phase-A merge audit).** `_hω_gen : ω` generates `F×`
is inherited from the T2.18 leaf `frs_is_subspaceDesign_gk16`, whose unguarded form was
shown FALSE for low-order `ω` (counterexample `ω = -1` over `𝔽₁₀₁`; see that decl's
docstring and PAPER_REVS #13). It is also the classical folded-RS setting of CZ25 /
Guruswami–Rudra (fold element a primitive/generator element). -/
theorem frs_list_decoding_capacity_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (_hFn : Fintype.card ι < Fintype.card F)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (_hω : ω ≠ 0)
    (_hω_gen : orderOf ω = Fintype.card F - 1)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt_s : 1 / η < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  intro n ρ δ bound
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hs_posR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr _hs_pos
  have hdenom_pos : (0 : ℝ) < (s : ℝ) - 1 / η + 1 := by linarith
  -- T2.18: FRS is τ-subspace-design for the explicit profile.
  have hdesign : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then (k : ℝ) / Fintype.card ι / (s - r + 1) else 1)
      (ReedSolomon.Folded.frsCode domain k s ω) :=
    frs_is_subspaceDesign_gk16 domain k s ω (Finset.univ.map domain)
      (fun i => Finset.mem_map_of_mem domain (Finset.mem_univ i)) _hFn _hadm _hω _hω_gen
  -- The real-argument profile value `t = ρ·s/(s − 1/η + 1) = (k/n)/(s − 1/η + 1)`.
  have hρs : ρ * s = (k : ℝ) / n := by
    have hs0 : (s : ℝ) ≠ 0 := hs_posR.ne'
    have hn0 : n ≠ 0 := hn_pos.ne'
    change (k : ℝ) / ((s : ℝ) * n) * s = (k : ℝ) / n
    field_simp
  have ht_nonneg : 0 ≤ ρ * s / ((s : ℝ) - 1 / η + 1) := by
    rw [hρs]
    positivity
  have key := subspaceDesign_list_decoding_profile_le_cz25 s
    (fun r => if r ∈ Finset.Icc 1 s then (k : ℝ) / Fintype.card ι / (s - r + 1) else 1)
    (ReedSolomon.Folded.frsCode domain k s ω) hdesign η
    (ρ * s / ((s : ℝ) - 1 / η + 1)) _hη_pos ht_nonneg
    (fun L hL1 hLle => ?_) _hη_lt_s.le
  · -- Convert `key` to the paper-display radius and bound.
    have hδ_eq : δ = 1 - ρ * s / ((s : ℝ) - 1 / η + 1) - η := rfl
    have hbound_eq : bound = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η := by
      have hd2 : ((s : ℝ) - 1 / η + 1) ≠ 0 := hdenom_pos.ne'
      have hη0 : η ≠ 0 := _hη_pos.ne'
      -- The `1/η` nested inside `s ± 1/η ± 1` clears to `s·η + η − 1`; field_simp needs
      -- *that* nonzero to fully cancel, so supply it (from `hdenom_pos · η`).
      have hd3 : (-1 + (s : ℝ) * η + η) ≠ 0 := by
        have hmul := mul_pos hdenom_pos _hη_pos
        have heq : ((s : ℝ) - 1 / η + 1) * η = -1 + (s : ℝ) * η + η := by
          field_simp; ring
        rw [heq] at hmul; exact hmul.ne'
      change (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
        = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η
      have hkey : (-1 + (s : ℝ) * η + η) * (-1 + (s : ℝ) * η + η)⁻¹ = 1 :=
        mul_inv_cancel₀ hd3
      field_simp
      linear_combination hkey
    rw [hδ_eq, hbound_eq]
    exact key
  · -- Profile domination on `1 ≤ L ≤ 1/η`.
    have hLs : (L : ℝ) < (s : ℝ) := lt_of_le_of_lt hLle _hη_lt_s
    have hLs' : L ≤ s := le_of_lt (by exact_mod_cast hLs)
    have hmem : L ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨hL1, hLs'⟩
    simp only [hmem, if_true]
    rw [hρs]
    have hn_eq : (Fintype.card ι : ℝ) = n := rfl
    rw [hn_eq]
    exact div_le_div_of_nonneg_left (by positivity) hdenom_pos (by linarith)

end SubspaceDesignUpperBounds

end CodingTheory

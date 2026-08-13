/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness

/-!
# Combinatorial bounds on the maximised list size

Upper and lower bounds on `ListDecodable.Lambda` — the block-maximised list size of a code at a
given relative radius. The two families answer opposite questions about the same quantity:

* **Upper bounds** exhibit a radius at which the list is provably small, so they certify list
  decodability. The one here is for codes carrying a *subspace-design* profile
  (`CodingTheory.IsSubspaceDesign`), which is the abstraction folded Reed-Solomon codes satisfy;
  its two code-family consequences are `frs_lambda_le_capacity` and `um_lambda_le_capacity`, for
  folded Reed-Solomon and univariate multiplicity codes. A second upper bound,
  `rs_random_domain_lambda_le`, is probabilistic: a Reed-Solomon code on a *uniformly random*
  evaluation domain is list-decodable near capacity with high probability.
* **Lower bounds** exhibit a radius at which the list is provably large, so they rule out list
  decodability above a threshold: a volume/averaging bound valid for every linear code
  (`linear_lambda_ge_elias_volume`, and its entropy form), a bound on random linear codes, and
  Reed-Solomon-specific separations
  (`rs_lambda_superpoly_extension`, `rs_lambda_large_prime`, `rs_lambda_high_rate`).
* **Neither** is `linear_card_le_generalized_singleton`, which bounds `|C|` rather than a list and
  belongs to a third group with `large_alphabet_lambda_lower`: constraints on the *code* implied by
  a list-size bound. Its arithmetic half, with no list-decoding premise at all, is
  `linear_card_le_of_rate_radius`; the barrier's own consequence — attaining the generalized
  Singleton bound *exactly* forces an exponentially large alphabet — is
  `large_alphabet_card_ge_exp_of_inv_length`.

Together they bracket the largest radius at which a code family can be list-decoded with a given
list size — the quantity the Grand List Decoding Challenge of [ABF26] asks about.

## Quantification conventions

The asymptotic statements below quantify over "infinitely many `q`", existentially-bound codes,
and "sufficiently large `n`". These are captured uniformly:

* *Type-level data* (alphabet `F`, index type `ι`) is **universally** quantified, at the theorem's
  outermost binder when the statement holds for every instantiation, and *inside* an existential
  when the source constructs the code. The caller instantiates.
* *Numeric quantifiers* ("there exists `α > 0`") stay inside the statement as `∃` on numeric data.
* *Sufficiently large `n`* becomes an explicit existential threshold `n₀ : ℕ` followed by
  `n₀ ≤ Fintype.card ι`. This is the `Filter.Eventually` shape without a filter in a pure
  statement.
* *Infinitely many `q`* becomes `∃ qs : ℕ → ℕ, StrictMono qs ∧ ∀ i, P (qs i)` — note the
  prime-power requirement is a **conjunct**, never the antecedent of an implication, which a
  non-prime-power sequence would satisfy vacuously.
* *Exact rates* `k = ρ · n` are unsatisfiable for irrational `ρ`. Where a source treats `ρ · n` as
  an integer "for exposition", the dimension is pinned two-sidedly into the band
  `ρ ≤ k/n ≤ ρ + 1/n`, admitting `k = ⌈ρ·n⌉`. Where a source's constants genuinely depend on the
  exact rate, the equality is kept and the statement is vacuous at irrational `ρ` — as in the
  source, whose asymptotic form fixes `ρ` and quantifies over lengths realising it.

## External admits

Nine statements are admitted with a tagged `sorry`, never an `axiom`: the entropy-volume corollary,
the generalized Singleton bound, the large-alphabet barrier, the random-linear-code bound, the
random-evaluation-domain bound, the three Reed-Solomon separations, and the subspace-design theorem.
Each admit's docstring carries the source statement verbatim, the variable map into ArkLib's
vocabulary, and a note on every place the formalised statement differs from the printed one.

Everything else in this file is proved: six derivations from admitted statements
(`random_linear_lambda_lower_exists`, `large_alphabet_card_ge_exp_of_inv_length`,
`subspaceDesign_lambda_le_of_profile_le`, `subspaceDesign_lambda_le_of_eta`,
`frs_lambda_le_capacity`, `um_lambda_le_capacity` — each therefore reachable-`sorryAx` and
carrying no more information than its input), the volume/averaging lower bound
`linear_lambda_ge_elias_volume`, the arithmetic half `linear_card_le_of_rate_radius` of the
generalized Singleton bound, and three supporting counting lemmas.

Two source-side weakenings apply throughout and are not repeated on each declaration: [CZ25] and
[AGL24] both state *average-radius* list-decodability, of which the plain `Λ` bound formalised here
is a consequence; and where a source constructs a code, the Lean existentially binds it rather than
reproducing the construction.

Two statements from [ABF26] §3 are absent, one by decision and one not yet attempted.

* The algorithmic hardness barrier (Theorem 3.16, [CW07]) is **deliberately** absent: it needs a
  computational-hardness framework ArkLib does not have — an adversary/advantage/running-time
  layer — and without one, a statement of it would be vacuous or would be about something other than
  hardness.
* Theorem 3.15, the [KKH26] asymptotic Reed-Solomon lower bound near minimum distance, is simply not
  formalised. It postdates the cached [ABF26] build, which stops at Theorem 3.14 and numbers the
  [CW07] barrier as 3.15; the numbering used throughout this file follows the current tex, in which
  [KKH26] is 3.15 and [CW07] is 3.16. Its statement depends on the paper's appendix restatement of
  [KKH26], also unformalised.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  §3 is the source of every statement in this file.
* [Eli57] Elias. *List decoding for noisy channels*. 1957. The volume/averaging lower bound.
* [MS77] MacWilliams, Sloane. *The Theory of Error-Correcting Codes*. 1977. The Hamming-ball
  volume estimate behind the entropy form.
* [ST20] Shangguan, Tamo. *Combinatorial list-decoding of Reed-Solomon codes beyond the Johnson
  radius*. 2020. Theorem 1.2, the generalized Singleton bound.
* [BDG24] Brakensiek, Dhar, Gopi. *Improved field size bounds for higher order MDS codes*. IEEE
  Trans. Inf. Theory 70(10), 2024. Cited by [ABF26] at "Corollary 1.7, Thm 1.8" for the `ℓ = 2`
  case. **Locator unverified:** in the arXiv version (2212.11262v2) those numbers are a statement
  about MR tensor codes and an average-radius `LD-MDS(≤2)` corollary, and all of its items are
  `ε`-free *exact*-achievement results rather than the `η`-parameterized form; the journal version
  may renumber. Only [AGL23] visibly supports the `η`-form, of which [BDG24] is the `ε = 0`,
  `ℓ = 2`, linear-MDS corner. Check the journal PDF before relying on these locators.
* [AGL23] Alrabiah, Guruswami, Li. *AG codes have no list-decoding friends: approaching the
  generalized Singleton bound requires exponential alphabets*. arXiv:2308.13424, 2023. Generalizes
  [BDG24] to all `ℓ`; together they are the large-alphabet barrier.
* [GLMRSW22] Guruswami, Li, Mosheiff, Resch, Silas, Wootters. *Bounds for list-decoding and
  list-recovery of random linear codes*. 2022. Theorem 4.1.
* [BKR06] Ben-Sasson, Kopparty, Radhakrishnan. *Subspace polynomials and list decoding of
  Reed-Solomon codes*. 2006. Corollary 2.2.
* [GHSZ02] Guruswami, Håstad, Sudan, Zuckerman. *Combinatorial bounds for list decoding*. 2002.
  Corollary 20.
* [JH01] Justesen, Høholdt. *Bounds on list decoding of MDS codes*. 2001. Theorem 2.
* [CZ25] Chen, Zhang. *Explicit folded Reed-Solomon and multiplicity codes achieve relaxed
  generalized Singleton bounds*. 2025. Theorem B.5 and Corollary 2.21.
* [AGL24] Alrabiah, Guruswami, Li. *Randomly punctured Reed-Solomon codes achieve list-decoding
  capacity over linear-sized fields*. STOC 2024. Theorem 1.1 is `rs_random_domain_lambda_le`. Its
  predecessors, cited by [ABF26] as context, are [BGM23] Brakensiek, Gopi, Makam, *Generic
  Reed-Solomon codes achieve list-decoding capacity*, STOC 2023 (exponential alphabet); [GZ23] Guo,
  Zhang, *Randomly punctured Reed-Solomon codes achieve the list decoding capacity over
  polynomial-size alphabets*, FOCS 2023; and [AGGLZ25] Alrabiah, Guo, Guruswami, Li, Zhang, *Random
  Reed-Solomon codes achieve list-decoding capacity with linear-sized alphabets*, Advances in
  Combinatorics, 2025, which combines the two.
* [CW07] Cheng, Wan. *On the list and bounded distance decodability of Reed-Solomon codes*. SIAM J.
  Comput. 37(1), 2007. Not formalised, see above.
* [DG25dist] Diamond, Gruen. *On the distribution of the distances of random words*. ePrint
  2025/2010, 2025. Refines the volume estimate. **Not** ArkLib's existing `DG25`, which is the same
  authors' *Proximity Gaps in Interleaved Codes* — a different paper.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
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
  rw [hammingBallVolume_eq_ncard_hammingBall δ c, ← Set.ncard_coe_finset]
  congr 1
  ext f
  -- Both sides are `hammingDist c f ≤ ⌊δ·n⌋`; the two `DecidableEq F` instances differ
  -- (`Code.hammingBall` carries a classical one), which `congr!` discharges.
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
    Code.mem_hammingBall_iff]
  congr!

/-- **Relative-distance close-codeword set as an explicit absolute-distance set.** -/
theorem closeCodewordsRel_eq_setOf
    (C : Submodule F (ι → F)) (δ : ℝ) (hδ : 0 ≤ δ) (f : ι → F) :
    closeCodewordsRel ((C : Set (ι → F))) f δ =
      {c : ι → F | c ∈ C ∧ hammingDist c f ≤ ⌊δ * Fintype.card ι⌋₊} := by
  have h_n_pos : 0 < Fintype.card ι := Fintype.card_pos
  ext c
  simp only [closeCodewordsRel, Code.relHammingBall, Set.mem_setOf_eq, SetLike.mem_coe,
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

/-- **The volume lower bound on list size** ([ABF26] Lemma 3.7, after [Eli57]):

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |F|`, `n = |ι|`, and `k = dim C`, so `|C| = q^k`.

Proved by the source's averaging argument: the mean over uniformly random centres `f` of the
point-list size `|Λ(C, δ, f)|` is `|C| · Vol / q^n = Vol / q^{n-k}`
(`sum_ncard_closeCodewordsRel_eq`), so some centre attains at least the mean, and `Lambda` is the
supremum over centres. No entropy estimate is involved — for that see
`linear_lambda_ge_entropy_volume`.

**Narrower than the source, and needlessly so.** [ABF26] states this for an arbitrary code
`C : Σ^k → Σ^n` over an arbitrary alphabet; this is the linear-over-a-field case. Linearity enters
the proof exactly once, at `Module.natCard_eq_pow_finrank`, to get `|C| = q^k`. Restating over
`C : Code ι A` for a finite alphabet `A` with `C.ncard = q ^ k` as a hypothesis would give the
source's generality with this as a one-line corollary — the generic-core-plus-field-wrapper shape
`mds_johnson_lambda_le_of_rate_distance` already uses. Left as a follow-up rather than done here. -/
theorem linear_lambda_ge_elias_volume
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
  have hfin : (closeCodewordsRel ((C : Set (ι → F))) f₀ δ).Finite := Set.toFinite _
  have hLam : ((cnt f₀ : ℕ∞) : ENNReal) ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
    apply ENat.toENNReal_mono
    calc ((cnt f₀ : ℕ) : ℕ∞)
        = (closeCodewordsRel ((C : Set (ι → F))) f₀ δ).encard := hfin.cast_ncard_eq
      _ ≤ Lambda ((C : Set (ι → F))) δ :=
          encard_closeCodewordsRel_le_Lambda ((C : Set (ι → F))) δ f₀
  calc ENNReal.ofReal ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k))
      ≤ ENNReal.ofReal (cnt f₀ : ℝ) := ENNReal.ofReal_le_ofReal hf₀
    _ = ((cnt f₀ : ℕ∞) : ENNReal) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
    _ ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := hLam

/-- **The entropy form of the volume lower bound** ([ABF26] Corollary 3.8). Feeding the
[MS77] Hamming-ball volume estimate `Vol_q(δ, n) ≥ q^{n·H_q(δ)} / √(8·n·δ·(1-δ))` into
`linear_lambda_ge_elias_volume`, dividing by `q^{n-k}` and writing `ρ := k/n`, gives

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`.

External admit: what is missing is the volume estimate itself, an analytic single-term Stirling
bound. [DG25dist] gives refinements of it. As with `linear_lambda_ge_elias_volume`, [ABF26] states
this for an arbitrary code over an arbitrary alphabet (`C : Σ^k → Σ^n`); the linear-over-a-field
case below is a special case, which is the safe direction for an admit but is a coverage gap.

The hypothesis `_hδn_int` (the radius `δ·n` is an integer) is the regime in which the [MS77]
estimate is stated, and the corollary inherits it implicitly. It is not decoration: without it the
bound is **false** at small `δ`, since for `0 < δ·n < 1` the relative ball collapses to Hamming
radius `0`, so the list is `{f} ∩ C` while the entropy-volume right-hand side can exceed `1`. -/
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
  sorry -- external admit: the [MS77] Hamming-ball volume estimate.

/-- **The cardinality bound from the rate–radius relation** — the arithmetic half of [ABF26]
Theorem 3.9. Given `δ ≤ ℓ/(ℓ+1) · (1-ρ)` for a linear code `C ⊆ F^n` of rate `ρ`,

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}` ,

by `|C| = |F|^{dim C}` and `⌊(ℓ+1)/ℓ·δ·n⌋ ≤ n - dim C`.

This is deliberately *not* named for [ST20] Theorem 1.2: that theorem's content is the implication
`ℓ`-list-decodable ⇒ the rate–radius relation, which is the admit
`linear_card_le_generalized_singleton` below. Splitting the two keeps the proved part honest about
what it proves — the arithmetic step, with no list-decoding premise at all. -/
theorem linear_card_le_of_rate_radius
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ)
    (hδ_bound : δ ≤ (ℓ : ℝ) / (ℓ + 1) *
      (1 - (Module.finrank F C : ℝ) / Fintype.card ι)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  classical
  set q : ℕ := Fintype.card F with hq
  set n : ℕ := Fintype.card ι with hn
  set k : ℕ := Module.finrank F C with hk
  -- `|C| = q ^ k` (linearity).
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
  -- From `hδ_bound`, `(ℓ+1)/ℓ · δ ≤ 1 - k/n`, hence `(ℓ+1)/ℓ · δ · n ≤ n - k`.
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

/-- **The generalized Singleton bound for list decoding** ([ABF26] Theorem 3.9, after
[ST20, Theorem 1.2]). For a finite field `F`, `0 < ℓ < |F|`, `δ ∈ (0, 1)` with `δ·n` an integer, and
a linear code `C ⊆ F^n` with `|Λ(C, δ)| ≤ ℓ`:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}` ,

whence `δ ≤ ℓ/(ℓ+1) · (1-ρ)` via `linear_card_le_of_rate_radius`'s converse arithmetic. The content
is the *implication* from list decodability; the arithmetic step is `linear_card_le_of_rate_radius`.

**`_hδn_int` is [ST20]'s own hypothesis, not an ArkLib convenience.** Their proof of Theorem 1.2
opens "Let `a := ⌊(L+1)rn/L⌋ = rn + ⌊rn/L⌋` (**assuming `rn` is an integer**)", and the identity it
records is false otherwise. [ABF26]'s printing drops the hypothesis, and without it the statement is
**false**: the ternary length-3 repetition code `C = {000, 111, 222}` over `𝔽₃` is
`(δ = 1/2, ℓ = 1)`-list-decodable — its minimum distance is `3`, so the radius-`⌊δn⌋ = 1` balls are
disjoint — yet `⌊(ℓ+1)/ℓ·δ·n⌋ = ⌊3⌋ = 3` forces the right-hand side to `3^0 = 1 < 3 = |C|`. ([ST20]
separately assume `rn/L ∈ ℤ` "for ease of presentation", which only removes the floor.)

**`_hexp_nonneg` is a second hypothesis both papers omit, and it is also necessary.** [ST20]'s
pigeonhole needs `a ≤ n`, there being `q^{n−a}` prefixes only then. Without it the statement is
false for the zero code: `C = ⊥` with `n = 10`, `δ = 9/10` and `ℓ = 1` has `Λ(C, δ) = 1 ≤ ℓ` and
`δ·n = 9 ∈ ℕ`, while `a = ⌊2·9⌋ = 18 > n` makes the right-hand side `q^{−8} < 1 = |C|`. The same
omission voids [ABF26]'s "Consequently `δ ≤ ℓ/(ℓ+1)·(1−ρ)`" for `C = ⊥`.

**Narrower than [ST20] in one direction.** Their Theorem 1.2 has a first, alphabet-generic half
`|C| ≤ L·q^{n−a}` for arbitrary `C ⊆ Q^n`; the `L`-free form below is their linear refinement, which
is what `_hℓ_lt : ℓ < |F|` buys and what [ABF26] prints. -/
theorem linear_card_le_generalized_singleton
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδn_int : ∃ e : ℕ, (e : ℝ) = δ * Fintype.card ι)
    (_hexp_nonneg : Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) ≤ Fintype.card ι)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  sorry -- external admit: [ST20, Theorem 1.2].

end LowerBounds_General

section LargeAlphabetBarrier

/-- **Attaining the generalized Singleton bound forces a large alphabet** ([ABF26] Theorem 3.10,
after [BDG24] and [AGL23]). For every `ℓ ≥ 2` and `ρ ∈ (0, 1)` there is a constant `α > 0` such
that for every `η > 0` and every sufficiently large `n`, every linear code `C ⊆ F^n` of rate `ρ`
with `|Λ(C, ℓ/(ℓ+1) · (1-ρ-η))| ≤ ℓ` satisfies

  `|F| ≥ 2^{α / η}` ,

so approaching the generalized Singleton bound to within `η` costs alphabet size exponential in
`1/η`. Per [AGL23, Theorem 1.1] the length threshold is `n ≥ Ω_{ℓ,ρ}(1/η)`, which is why `n₀` is
bound *inside* the `∀ η`.

**The rate is pinned by equality, which is faithful but partly vacuous.** [AGL23] states the
barrier for a code "of rate `R`" — Theorem 1.1 as *printed* omits the rate hypothesis altogether,
which is a defect in that paper; the hypothesis appears in its abstract and in the worked
Propositions 3.2/3.3 — and [BDG24] (the `ℓ = 2` progenitor) is stated for `[n, k]`-MDS codes of
fixed dimension. Equality is therefore the faithful reading. The price is that at irrational `ρ` the
statement is vacuous, and at rational `ρ = a/b` it is inhabited only for `b ∣ n`; instantiate at
`ρ = finrank/n`.

A two-sided band `ρ ≤ finrank/n ≤ ρ + 1/n`, as `random_linear_lambda_lower` uses and this file's
own quantification convention prescribes, would remove that vacuity and is supported by [AGL23]'s
*proof*: it rounds `R` down to a multiple of `3/n` and passes to a subcode ("Taking `C′` to be any
subcode of `C` of rate `R′`", Prop. 3.2; "Subcode `C′` has rate at least `R′ = R − (1/n)`",
Prop. 3.3). It is not implied by the printed equality form, though — recovering rate exactly `ρ·n`
from a code of rate in the band needs `ρ·n ∈ ℤ` — so it would be a mild strengthening, and the
choice is left as recorded rather than made.

**The length threshold is the source's, and the quantifier order is load-bearing.** [AGL23] state
`n ≥ Ω_{ℓ,ρ}(1/η)`, i.e. one threshold constant for all `η`; their Theorem 4.3 spells it out as
"there exists `n₀ = n₀(L,R)` such that the following holds for all `n ≥ n₀` **and `ε ≥ 1/n`**". Both
conditions are reproduced below, with `n₀` bound *outside* `∀ η` and `1/η ≤ n` as a hypothesis. A
weaker `∃ n₀` *inside* `∀ η` — letting the threshold depend on `η` arbitrarily — would be the safe
direction, but it would make this theorem's only intended consequence unreachable: instantiating at
`η := c/n` fixes `n` first and then needs `n₀(c/n) ≤ n`, which nothing supplies. That consequence is
`large_alphabet_card_ge_exp_of_inv_length`, and it is the reason this theorem exists in [ABF26] —
the paper never cross-references the theorem itself.

**Two further divergences, both recorded rather than repaired.** (i) [ABF26] states this for an
arbitrary code `C : Σ^k → Σ^n`, and dropping linearity is precisely [AGL23]'s headline advance over
[BDG24]; the admit below is the linear-over-a-field case, so it does not capture the cited result in
full. (ii) `η` is unguarded, and for `η > 1 − ρ` the radius `ℓ/(ℓ+1)·(1−ρ−η)` is negative, so
`Λ = 0 ≤ ℓ` holds for every code and the statement demands `|F| ≥ 2^(α/η)` unconditionally. Letting
`η ↓ (1−ρ)` therefore forces `α ≤ 1 − ρ`, since `𝔽₂` carries rate-`ρ` codes of every admissible
length. That does not make the statement false — `α := min (α_source) (1−ρ)` still works, shrinking
`α` only weakening the conclusion — but a prover will meet the constraint, and the sources plainly
intend `η` in the meaningful range. -/
theorem large_alphabet_lambda_lower
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (η : ℝ), 0 < η →
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F]
            (C : Submodule F (ι → F)),
            n₀ ≤ Fintype.card ι →
            1 / η ≤ (Fintype.card ι : ℝ) →
            (Module.finrank F C : ℝ) = ρ * Fintype.card ι →
            Lambda ((C : Set (ι → F))) ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  sorry -- external admit: [BDG24], [AGL23].

/-- **Attaining the generalized Singleton bound exactly forces an exponentially large alphabet** —
the consequence [ABF26] draws from Theorem 3.10, and the only use it puts that theorem to: "*this
shows that achieving exactly the generalized singleton bound (which implies the case when
`η = Θ(1/n)`) requires an alphabet of exponential size, which is undesirable.*"

At `η := c/n` the barrier's `2^{α/η}` becomes `2^{(α/c)·n}`, so for every `ℓ ≥ 2`, `ρ ∈ (0,1)` and
`c ≥ 1` there is `α > 0` with

  `|Λ(C, ℓ/(ℓ+1) · (1 − ρ − c/n))| ≤ ℓ  ⟹  |F| ≥ 2^{α·n}`

for every rate-`ρ` linear code of sufficiently large length `n`.

**Derived in-tree** from `large_alphabet_lambda_lower`, which is admitted, so this inherits the
admit. `1 ≤ c` is exactly [AGL23]'s `ε ≥ 1/n` at `η = c/n`, and it is the meaningful range: relative
radii are `1/n`-quantised, so `η < 1/n` asks for a radius finer than the lattice the list size lives
on. -/
theorem large_alphabet_card_ge_exp_of_inv_length
    (ℓ : ℕ) (hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {F : Type} [Field F] [Fintype F] [DecidableEq F]
        (C : Submodule F (ι → F)),
        n₀ ≤ Fintype.card ι →
        (Module.finrank F C : ℝ) = ρ * Fintype.card ι →
        Lambda ((C : Set (ι → F)))
            ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - c / Fintype.card ι)) ≤ (ℓ : ℕ∞) →
        (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α * Fintype.card ι) := by
  obtain ⟨α, hα_pos, n₀, hmain⟩ := large_alphabet_lambda_lower ℓ hℓ_ge ρ hρ_pos hρ_lt
  have hc_pos : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  refine ⟨α / c, div_pos hα_pos hc_pos, n₀, fun {ι} _ _ _ {F} _ _ _ C hn hrate hΛ => ?_⟩
  have hn_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  -- Instantiate the barrier at `η := c/n`, whose two length conditions are `n₀ ≤ n` and `1/η ≤ n`.
  have hη_pos : (0 : ℝ) < c / Fintype.card ι := div_pos hc_pos hn_pos
  have hinv : 1 / (c / (Fintype.card ι : ℝ)) ≤ (Fintype.card ι : ℝ) := by
    rw [one_div_div, div_le_iff₀ hc_pos]
    nlinarith
  have hkey := hmain (c / Fintype.card ι) hη_pos C hn hinv hrate hΛ
  -- `α / (c/n) = (α/c) · n`.
  rwa [show α / (c / (Fintype.card ι : ℝ)) = α / c * Fintype.card ι by
    field_simp] at hkey

end LargeAlphabetBarrier

section RandomLinear

def qEntropy_lt_one_of_lt_one_sub_inv
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ0 : 0 ≤ β)
    (hβlt : β < 1 - 1 / q) : qEntropy q β < 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hmax0 : (0 : ℝ) ≤ 1 - 1 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  rw [← qEntropy_one_sub_inv hq]
  exact (qEntropy_strictMonoOn hq) ⟨hβ0, hβlt.le⟩ ⟨hmax0, le_rfl⟩ hβlt

open scoped BigOperators in
def rlExactType (n : ℕ) (α : Type) [Fintype α] : Type :=
  {t : α → ℕ // ∑ x, t x = n}

open scoped BigOperators in
noncomputable def rlExactTypeColumnMarginal
    (n m : ℕ) {F : Type} [Fintype F]
    (t : rlExactType n (F × (Fin m → F))) :
    rlExactType n (Fin m → F) := by
  classical
  refine ⟨fun v => ∑ a : F, t.1 (a, v), ?_⟩
  calc
    (∑ v : Fin m → F, ∑ a : F, t.1 (a, v)) =
        ∑ a : F, ∑ v : Fin m → F, t.1 (a, v) := Finset.sum_comm
    _ = ∑ x : F × (Fin m → F), t.1 x :=
      (Fintype.sum_prod_type (fun x : F × (Fin m → F) => t.1 x)).symm
    _ = n := t.2

def rlExactTypeFullSupport
    (n : ℕ) {α : Type} [Fintype α] (t : rlExactType n α) : Prop :=
  ∀ x : α, 0 < t.1 x

open scoped BigOperators in
def rlExactTypeColumnMarginal_fullSupport
    (n m : ℕ) {F : Type} [Field F] [Fintype F]
    (t : rlExactType n (F × (Fin m → F)))
    (ht : rlExactTypeFullSupport n t) :
    rlExactTypeFullSupport n (rlExactTypeColumnMarginal n m t) := by
  classical
  intro v
  change 0 < ∑ a : F, t.1 (a, v)
  apply Finset.sum_pos'
  · intro a _ha
    exact Nat.zero_le _
  · exact ⟨0, Finset.mem_univ 0, ht (0, v)⟩

noncomputable def rlExactTypeWeight
    (n : ℕ) {α : Type} [Fintype α] (t : rlExactType n α) (x : α) : ℝ :=
  (t.1 x : ℝ) / (n : ℝ)

open scoped BigOperators in
noncomputable def rlExactTypePushforwardWeight
    (n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (f : α → κ) (y : κ) : ℝ :=
  ∑ x : α, if f x = y then rlExactTypeWeight n t x else 0

open scoped BigOperators in
def rlExactTypeWeight_columnMarginal
    (n m : ℕ) {F : Type} [Fintype F]
    (t : rlExactType n (F × (Fin m → F))) (v : Fin m → F) :
    rlExactTypeWeight n (rlExactTypeColumnMarginal n m t) v =
      ∑ a : F, rlExactTypeWeight n t (a, v) := by
  unfold rlExactTypeWeight rlExactTypeColumnMarginal
  push_cast
  rw [Finset.sum_div]

open scoped BigOperators in
def rlExactTypeWeight_le_one
    (n : ℕ) {α : Type} [Fintype α]
    (t : rlExactType n α) :
    ∀ x, rlExactTypeWeight n t x ≤ 1 := by
  intro x
  have hcount : t.1 x ≤ n := by
    calc
      t.1 x ≤ ∑ y : α, t.1 y :=
        Finset.single_le_sum (fun y _hy => Nat.zero_le (t.1 y))
          (Finset.mem_univ x)
      _ = n := t.2
  unfold rlExactTypeWeight
  by_cases hn : n = 0
  · subst n
    have hx : t.1 x = 0 := by omega
    rw [hx]
    norm_num
  · rw [div_le_one (by positivity)]
    exact_mod_cast hcount

def rlExactTypeWeight_nonneg
    (n : ℕ) {α : Type} [Fintype α]
    (t : rlExactType n α) :
    ∀ x, 0 ≤ rlExactTypeWeight n t x := by
  intro x
  unfold rlExactTypeWeight
  positivity

open scoped BigOperators in
noncomputable def rlFiniteConditionalMapLeftWeight
    {α β κ ζ : Type} [Fintype α] [DecidableEq β]
    (p : (α × κ) × ζ → ℝ) (f : α → β)
    (z : (β × κ) × ζ) : ℝ :=
  ∑ x : α, if f x = z.1.1 then p ((x, z.1.2), z.2) else 0

open scoped BigOperators in
def rlFiniteConditionalMapLeftWeight_nonneg
    {α β κ ζ : Type} [Fintype α] [DecidableEq β]
    (p : (α × κ) × ζ → ℝ) (hp : ∀ z, 0 ≤ p z)
    (f : α → β) :
    ∀ z, 0 ≤ rlFiniteConditionalMapLeftWeight p f z := by
  intro z
  unfold rlFiniteConditionalMapLeftWeight
  apply Finset.sum_nonneg
  intro x _hx
  by_cases hfx : f x = z.1.1
  · rw [if_pos hfx]
    exact hp ((x, z.1.2), z.2)
  · rw [if_neg hfx]

open scoped BigOperators in
noncomputable def rlFiniteEntropy
    (q : ℕ) {α : Type} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ x : α, p x * Real.logb q (p x)

noncomputable def rlExactTypeEntropy
    (q n : ℕ) {α : Type} [Fintype α] (t : rlExactType n α) : ℝ :=
  rlFiniteEntropy q (rlExactTypeWeight n t)

noncomputable def rlExactTypeProjectedEntropy
    (q n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (f : α → κ) : ℝ :=
  rlFiniteEntropy q (rlExactTypePushforwardWeight n t f)

open scoped BigOperators in
noncomputable def rlExactTypeNotImplicitlyRare
    (q n : ℕ) (γ : ℝ) (m : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType n (F × (Fin m → F))) : Prop :=
  ∀ (r : ℕ) (A : (Fin m → F) →ₗ[F] (Fin r → F)),
    Function.Surjective A →
      γ * (r : ℝ) ≤
        rlExactTypeProjectedEntropy q n t (fun x => A x.2)

open scoped BigOperators in
noncomputable def rlFiniteConditionalMutualInfo
    (q : ℕ) {α κ ζ : Type}
    [Fintype α] [Fintype κ] [Fintype ζ]
    (p : (α × κ) × ζ → ℝ) : ℝ :=
  rlFiniteEntropy q
      (fun xz : α × ζ => ∑ y : κ, p ((xz.1, y), xz.2)) +
    rlFiniteEntropy q
      (fun yz : κ × ζ => ∑ x : α, p ((x, yz.1), yz.2)) -
    rlFiniteEntropy q
      (fun z : ζ => ∑ x : α, ∑ y : κ, p ((x, y), z)) -
    rlFiniteEntropy q p

open scoped BigOperators in
def rlFiniteEntropy_congr
    (q : ℕ) {α : Type} [Fintype α] (p r : α → ℝ)
    (h : ∀ x, p x = r x) : rlFiniteEntropy q p = rlFiniteEntropy q r := by
  unfold rlFiniteEntropy
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro x _hx
  rw [h x]

open scoped BigOperators in
def rlFiniteEntropy_equiv
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α → ℝ) (e : α ≃ κ) :
    rlFiniteEntropy q p = rlFiniteEntropy q (fun y => p (e.symm y)) := by
  unfold rlFiniteEntropy
  apply congrArg Neg.neg
  apply Fintype.sum_equiv e
  intro x
  simp only [Equiv.symm_apply_apply]

open scoped BigOperators in
def rlFiniteEntropy_nonneg
    (q : ℕ) (hq : 2 ≤ q) {α : Type} [Fintype α]
    (p : α → ℝ) (hp : ∀ x, p x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ rlFiniteEntropy q p := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  unfold rlFiniteEntropy
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro x _hx
  exact mul_nonpos_of_nonneg_of_nonpos (hp x).1
    (Real.logb_nonpos hqR (hp x).1 (hp x).2)

open scoped BigOperators in
def rlFiniteEntropy_uniform
    (q : ℕ) (hq : 2 ≤ q) {F : Type} [Fintype F]
    (hF : Fintype.card F = q) :
    rlFiniteEntropy q (fun _x : F => 1 / (Fintype.card F : ℝ)) = 1 := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  unfold rlFiniteEntropy
  rw [hF]
  simp_rw [one_div, Real.logb_inv, Real.logb_self_eq_one hqR]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul, Finset.card_univ, hF]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

open scoped BigOperators in
noncomputable def rlFiniteMapLeftWeight
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq β] (p : α × κ → ℝ) (f : α → β)
    (z : β × κ) : ℝ :=
  ∑ x : α, if f x = z.1 then p (x, z.2) else 0

open scoped BigOperators in
def rlFiniteMapLeftWeight_nonneg
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq β] (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z)
    (f : α → β) : ∀ z, 0 ≤ rlFiniteMapLeftWeight p f z := by
  intro z
  unfold rlFiniteMapLeftWeight
  apply Finset.sum_nonneg
  intro x _hx
  by_cases hfx : f x = z.1
  · rw [if_pos hfx]
    exact hp (x, z.2)
  · rw [if_neg hfx]

open scoped BigOperators in
noncomputable def rlFiniteMarginalLeft
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (x : α) : ℝ :=
  ∑ y : κ, p (x, y)

open scoped BigOperators in
def rlFiniteMarginalLeft_ge
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (x : α) (y : κ) :
    p (x, y) ≤ rlFiniteMarginalLeft p x := by
  classical
  unfold rlFiniteMarginalLeft
  rw [← Finset.add_sum_erase (Finset.univ : Finset κ)
    (fun y' => p (x, y')) (Finset.mem_univ y)]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun y' _hy' => hp (x, y'))

open scoped BigOperators in
def rlFiniteMarginalLeft_log_sum
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) :
    (∑ z : α × κ,
      p z * Real.logb q (rlFiniteMarginalLeft p z.1)) =
      ∑ x : α,
        rlFiniteMarginalLeft p x *
          Real.logb q (rlFiniteMarginalLeft p x) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _hx
  unfold rlFiniteMarginalLeft
  rw [Finset.sum_mul]

open scoped BigOperators in
def rlFiniteMarginalLeft_nonneg
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z) :
    ∀ x, 0 ≤ rlFiniteMarginalLeft p x := by
  intro x
  unfold rlFiniteMarginalLeft
  exact Finset.sum_nonneg fun y _hy => hp (x, y)

open scoped BigOperators in
noncomputable def rlFiniteMarginalRight
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (y : κ) : ℝ :=
  ∑ x : α, p (x, y)

noncomputable def rlFiniteConditionalEntropy
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) : ℝ :=
  rlFiniteEntropy q p - rlFiniteEntropy q (rlFiniteMarginalRight p)

def rlFiniteEntropy_chain_rule_right
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) :
    rlFiniteEntropy q p =
      rlFiniteEntropy q (rlFiniteMarginalRight p) +
        rlFiniteConditionalEntropy q p := by
  unfold rlFiniteConditionalEntropy
  ring

open scoped BigOperators in
def rlFiniteMarginalRight_ge
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (x : α) (y : κ) :
    p (x, y) ≤ rlFiniteMarginalRight p y := by
  classical
  unfold rlFiniteMarginalRight
  rw [← Finset.add_sum_erase (Finset.univ : Finset α)
    (fun x' => p (x', y)) (Finset.mem_univ x)]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun x' _hx' => hp (x', y))

open scoped BigOperators in
def rlFiniteMarginalRight_log_sum
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) :
    (∑ z : α × κ,
      p z * Real.logb q (rlFiniteMarginalRight p z.2)) =
      ∑ y : κ,
        rlFiniteMarginalRight p y *
          Real.logb q (rlFiniteMarginalRight p y) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _hy
  unfold rlFiniteMarginalRight
  rw [Finset.sum_mul]

open scoped BigOperators in
def rlFiniteMarginalRight_nonneg
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z) :
    ∀ y, 0 ≤ rlFiniteMarginalRight p y := by
  intro y
  unfold rlFiniteMarginalRight
  exact Finset.sum_nonneg fun x _hx => hp (x, y)

noncomputable def rlFiniteMutualInfo
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) : ℝ :=
  rlFiniteEntropy q (rlFiniteMarginalLeft p) +
    rlFiniteEntropy q (rlFiniteMarginalRight p) - rlFiniteEntropy q p

def rlFiniteMutualInfo_eq_left_sub_conditional
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) :
    rlFiniteMutualInfo q p =
      rlFiniteEntropy q (rlFiniteMarginalLeft p) -
        rlFiniteConditionalEntropy q p := by
  unfold rlFiniteMutualInfo rlFiniteConditionalEntropy
  ring

noncomputable def rlFiniteReassocWeight
    {α κ ζ : Type} (p : (α × κ) × ζ → ℝ)
    (z : (α × ζ) × κ) : ℝ :=
  p ((z.1.1, z.2), z.1.2)

open scoped BigOperators in
noncomputable def rlFiniteZYWeight
    {α κ ζ : Type} [Fintype α]
    (p : (α × κ) × ζ → ℝ) (z : ζ × κ) : ℝ :=
  ∑ x : α, p ((x, z.2), z.1)

open scoped BigOperators in
def rlFiniteConditionalMapLeft_ZY_eq
    {α β κ ζ : Type} [Fintype α] [Fintype β]
    [DecidableEq β]
    (p : (α × κ) × ζ → ℝ) (f : α → β) :
    rlFiniteZYWeight (rlFiniteConditionalMapLeftWeight p f) =
      rlFiniteZYWeight p := by
  funext z
  rcases z with ⟨z, y⟩
  unfold rlFiniteZYWeight rlFiniteConditionalMapLeftWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  exact Fintype.sum_ite_eq (f x)
    (fun _b : β => p ((x, y), z))

open scoped BigOperators in
def rlFiniteConditionalMutualInfo_eq_mutualInfo_sub
    (q : ℕ) {α κ ζ : Type}
    [Fintype α] [Fintype κ] [Fintype ζ]
    (p : (α × κ) × ζ → ℝ) :
    rlFiniteConditionalMutualInfo q p =
      rlFiniteMutualInfo q (rlFiniteReassocWeight p) -
        rlFiniteMutualInfo q (rlFiniteZYWeight p) := by
  classical
  let e : ((α × κ) × ζ) ≃ ((α × ζ) × κ) :=
    { toFun := fun z => ((z.1.1, z.2), z.1.2)
      invFun := fun z => ((z.1.1, z.2), z.1.2)
      left_inv := by rintro ⟨⟨x, y⟩, z⟩; rfl
      right_inv := by rintro ⟨⟨x, z⟩, y⟩; rfl }
  have hreassoc :
      rlFiniteEntropy q (rlFiniteReassocWeight p) =
        rlFiniteEntropy q p := by
    have he := rlFiniteEntropy_equiv q p e
    change rlFiniteEntropy q p =
      rlFiniteEntropy q (rlFiniteReassocWeight p) at he
    exact he.symm
  have hxz :
      rlFiniteEntropy q
          (rlFiniteMarginalLeft (rlFiniteReassocWeight p)) =
        rlFiniteEntropy q
          (fun xz : α × ζ => ∑ y : κ, p ((xz.1, y), xz.2)) := by
    apply rlFiniteEntropy_congr
    intro xz
    rfl
  have hy :
      rlFiniteEntropy q
          (rlFiniteMarginalRight (rlFiniteReassocWeight p)) =
        rlFiniteEntropy q
          (rlFiniteMarginalRight (rlFiniteZYWeight p)) := by
    apply rlFiniteEntropy_congr
    intro y
    unfold rlFiniteMarginalRight rlFiniteReassocWeight rlFiniteZYWeight
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hz :
      rlFiniteEntropy q (rlFiniteMarginalLeft (rlFiniteZYWeight p)) =
        rlFiniteEntropy q
          (fun z : ζ => ∑ x : α, ∑ y : κ, p ((x, y), z)) := by
    apply rlFiniteEntropy_congr
    intro z
    unfold rlFiniteMarginalLeft rlFiniteZYWeight
    rw [Finset.sum_comm]
  have hzy :
      rlFiniteEntropy q (rlFiniteZYWeight p) =
        rlFiniteEntropy q
          (fun yz : κ × ζ => ∑ x : α, p ((x, yz.1), yz.2)) := by
    have he := rlFiniteEntropy_equiv q (rlFiniteZYWeight p)
      (Equiv.prodComm ζ κ)
    change rlFiniteEntropy q (rlFiniteZYWeight p) =
      rlFiniteEntropy q
        (fun yz : κ × ζ => ∑ x : α, p ((x, yz.1), yz.2)) at he
    exact he
  unfold rlFiniteConditionalMutualInfo rlFiniteMutualInfo
  rw [hxz, hy, hreassoc, hz, hzy]
  ring

noncomputable def rlFinrankSubmodules
    (k : ℕ) (ι F : Type)
    [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F] :
    Finset (Submodule F (ι → F)) :=
  Finset.univ.filter (fun C => Module.finrank F C = k)

def rlHasExactType
    {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (t : rlExactType (Fintype.card ι) α) (R : ι → α) : Prop :=
  ∀ x : α, (Finset.univ.filter (fun i => R i = x)).card = t.1 x

noncomputable def rlExactTypeClass
    {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (t : rlExactType (Fintype.card ι) α) : Finset (ι → α) := by
  classical
  exact Finset.univ.filter (fun R => rlHasExactType t R)

def mem_rlExactTypeClass
    {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (t : rlExactType (Fintype.card ι) α) (R : ι → α) :
    R ∈ rlExactTypeClass t ↔ rlHasExactType t R := by
  classical
  simp only [rlExactTypeClass, Finset.mem_filter, Finset.mem_univ, true_and]

open scoped BigOperators in
def rlExactTypeFullSupport_columnType_linearIndependent
    (m : ℕ) {ι F : Type} [Fintype ι]
    [Field F] [Fintype F] [DecidableEq F]
    (u : rlExactType (Fintype.card ι) (Fin m → F))
    (hu : rlExactTypeFullSupport (Fintype.card ι) u)
    (V : ι → (Fin m → F)) (hV : rlHasExactType u V) :
    LinearIndependent F (fun j : Fin m => fun i => V i j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  by_contra hgj
  let v : Fin m → F := fun l => if l = j then 1 else 0
  have hvpos : 0 < u.1 v := hu v
  have hcountpos :
      0 < (Finset.univ.filter (fun i => V i = v)).card := by
    rw [hV v]
    exact hvpos
  rcases Finset.card_pos.mp hcountpos with ⟨i, hi⟩
  have hVi : V i = v := (Finset.mem_filter.mp hi).2
  have hgi := congrFun hg i
  have hsumzero : (∑ l : Fin m, g l * V i l) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hgi
  rw [hVi] at hsumzero
  have hgj0 : g j = 0 := by
    simpa only [v, mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq'] using hsumzero
  exact hgj hgj0

def rlExactTypeFullSupport_columns_injective
    (m : ℕ) {ι F : Type} [Fintype ι]
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (ht : rlExactTypeFullSupport (Fintype.card ι) t)
    (R : ι → F × (Fin m → F)) (hR : rlHasExactType t R) :
    Function.Injective (fun j : Fin m => fun i => (R i).2 j) := by
  classical
  intro j k hcols
  by_contra hjk
  let v : Fin m → F := fun l => if l = j then 0 else 1
  let x : F × (Fin m → F) := (0, v)
  have htpos : 0 < t.1 x := ht x
  have hcountpos :
      0 < (Finset.univ.filter (fun i => R i = x)).card := by
    rw [hR x]
    exact htpos
  rcases Finset.card_pos.mp hcountpos with ⟨i, hi⟩
  have hRi : R i = x := (Finset.mem_filter.mp hi).2
  have hval := congrFun hcols i
  change (R i).2 j = (R i).2 k at hval
  have hkj : k ≠ j := fun h => hjk h.symm
  rw [hRi] at hval
  have hzeroone : (0 : F) = 1 := by
    simpa only [x, v, if_pos rfl, if_neg hkj] using hval
  exact zero_ne_one hzeroone

open scoped BigOperators in
def rlExactTypeFullSupport_columns_linearIndependent
    (m : ℕ) {ι F : Type} [Fintype ι]
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (ht : rlExactTypeFullSupport (Fintype.card ι) t)
    (R : ι → F × (Fin m → F)) (hR : rlHasExactType t R) :
    LinearIndependent F (fun j : Fin m => fun i => (R i).2 j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  by_contra hgj
  let v : Fin m → F := fun l => if l = j then 1 else 0
  let x : F × (Fin m → F) := (0, v)
  have htpos : 0 < t.1 x := ht x
  have hcountpos :
      0 < (Finset.univ.filter (fun i => R i = x)).card := by
    rw [hR x]
    exact htpos
  rcases Finset.card_pos.mp hcountpos with ⟨i, hi⟩
  have hRi : R i = x := (Finset.mem_filter.mp hi).2
  have hgi := congrFun hg i
  have hsumzero : (∑ l : Fin m, g l * (R i).2 l) = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using hgi
  rw [hRi] at hsumzero
  have hgj0 : g j = 0 := by
    simpa only [x, v, mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq'] using hsumzero
  exact hgj hgj0

open scoped BigOperators in
def rlHasExactType_column_marginal
    {ι F : Type} [Fintype ι] [Fintype F] [DecidableEq F]
    (m : ℕ)
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (R : ι → F × (Fin m → F)) (hR : rlHasExactType t R) :
    rlHasExactType (rlExactTypeColumnMarginal (Fintype.card ι) m t)
      (fun i => (R i).2) := by
  classical
  intro v
  let s : Finset ι := Finset.univ.filter (fun i => (R i).2 = v)
  have hpart :
      s.card = ∑ a : F,
        (s.filter (fun i => (R i).1 = a)).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (f := fun i => (R i).1) (s := s) (t := Finset.univ)
      (by intro i hi; exact Finset.mem_univ _)
  change s.card = ∑ a : F, t.1 (a, v)
  calc
    s.card = ∑ a : F,
        (s.filter (fun i => (R i).1 = a)).card := hpart
    _ = ∑ a : F,
        (Finset.univ.filter (fun i => R i = (a, v))).card := by
      apply Finset.sum_congr rfl
      intro a _ha
      congr 1
      ext i
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hsnd, hfst⟩
        exact Prod.ext hfst hsnd
      · intro hpair
        exact ⟨congrArg Prod.snd hpair, congrArg Prod.fst hpair⟩
    _ = ∑ a : F, t.1 (a, v) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact hR (a, v)

noncomputable def rlHasExactType_exists
    {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (t : rlExactType (Fintype.card ι) α) :
    ∃ R : ι → α, rlHasExactType t R := by
  classical
  let e : ι ≃ Sigma (fun x : α => Fin (t.1 x)) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact t.2.symm)
  let R : ι → α := fun i => (e i).1
  refine ⟨R, ?_⟩
  intro x
  let ex : {i : ι // R i = x} ≃ Fin (t.1 x) :=
    (e.subtypeEquivOfSubtype (p := fun s => s.1 = x)).trans
      (Equiv.sigmaSubtype x)
  have hcard := Fintype.card_congr ex
  simpa only [Fintype.card_subtype, Fintype.card_fin] using hcard

noncomputable def rlExactTypeClass_nonempty
    {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (t : rlExactType (Fintype.card ι) α) :
    (rlExactTypeClass t).Nonempty := by
  rcases rlHasExactType_exists t with ⟨R, hR⟩
  exact ⟨R, (mem_rlExactTypeClass t R).2 hR⟩

noncomputable def rlKLFun (x : ℝ) : ℝ :=
  x * Real.log x + 1 - x

open scoped BigOperators in
noncomputable def rlFiniteKL
    (q : ℕ) {α : Type} [Fintype α]
    (p r : α → ℝ) : ℝ :=
  (∑ x : α, r x * rlKLFun (p x / r x)) / Real.log q

open scoped BigOperators in
def rlFiniteKL_eq_log_ratio
    (q : ℕ) {α : Type} [Fintype α]
    (p r : α → ℝ)
    (hp_sum : (∑ x, p x) = 1) (hr_sum : (∑ x, r x) = 1)
    (hac : ∀ x, r x = 0 → p x = 0) :
    rlFiniteKL q p r =
      ∑ x : α, p x * Real.logb q (p x / r x) := by
  have hterm (x : α) :
      r x * rlKLFun (p x / r x) =
        p x * Real.log (p x / r x) + r x - p x := by
    by_cases hr0 : r x = 0
    · have hp0 : p x = 0 := hac x hr0
      rw [hr0, hp0]
      norm_num [rlKLFun]
    · unfold rlKLFun
      field_simp [hr0]
  unfold rlFiniteKL
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp_sum, hr_sum]
  simp only [add_sub_cancel_right]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _hx
  unfold Real.logb
  ring

def rlKLFun_convexOn :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) rlKLFun := by
  unfold rlKLFun
  exact
    ((Real.strictConvexOn_mul_log.add_convexOn
      (convexOn_const (1 : ℝ) (convex_Ici (0 : ℝ)))).sub_concaveOn
        (concaveOn_id (convex_Ici (0 : ℝ)))).convexOn

def rlKLFun_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ rlKLFun x := by
  by_cases hx0 : x = 0
  · subst x
    simp only [rlKLFun, zero_mul, Real.log_zero, add_zero, sub_zero]
    norm_num
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hlog := Real.one_sub_inv_le_log_of_pos hxpos
    have hmul := mul_le_mul_of_nonneg_left hlog hx
    rw [mul_sub, mul_one, mul_inv_cancel₀ hx0] at hmul
    unfold rlKLFun
    linarith

open scoped BigOperators in
def rlFiniteKL_nonneg
    (q : ℕ) (hq : 2 ≤ q) {α : Type} [Fintype α]
    (p r : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hr : ∀ x, 0 ≤ r x) :
    0 ≤ rlFiniteKL q p r := by
  unfold rlFiniteKL
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _hx =>
      mul_nonneg (hr x)
        (rlKLFun_nonneg (p x / r x) (div_nonneg (hp x) (hr x)))
  · have hqR : (1 : ℝ) < q := by exact_mod_cast hq
    exact (Real.log_pos hqR).le

noncomputable def rlNoiseWeight
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F] (x : F) : ℝ :=
  if x = 0 then 1 - β else β / ((Fintype.card F : ℝ) - 1)

open scoped BigOperators in
def rlFiniteEntropy_noise_eq_qEntropy
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ0 : 0 < β)
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q) :
    rlFiniteEntropy q (rlNoiseWeight (F := F) β) = qEntropy q β := by
  classical
  have hmem : (0 : F) ∈ (Finset.univ : Finset F) := Finset.mem_univ 0
  have hd : (Fintype.card F : ℝ) - 1 ≠ 0 := by
    have hcard : (1 : ℝ) < Fintype.card F := by
      rw [hF]
      exact_mod_cast hq
    linarith
  unfold rlFiniteEntropy
  rw [← Finset.add_sum_erase (Finset.univ : Finset F)
    (fun x => rlNoiseWeight β x * Real.logb q (rlNoiseWeight β x)) hmem]
  rw [show (∑ x ∈ (Finset.univ : Finset F).erase 0,
      rlNoiseWeight β x * Real.logb q (rlNoiseWeight β x)) =
      ∑ _x ∈ (Finset.univ : Finset F).erase 0,
        (β / ((Fintype.card F : ℝ) - 1)) *
          Real.logb q (β / ((Fintype.card F : ℝ) - 1)) by
    apply Finset.sum_congr rfl
    intro x hx
    unfold rlNoiseWeight
    rw [if_neg (Finset.mem_erase.mp hx).1]]
  unfold rlNoiseWeight
  rw [if_pos rfl, Finset.sum_const]
  simp only [nsmul_eq_mul]
  have herase : (((Finset.univ : Finset F).erase 0).card : ℝ) =
      (Fintype.card F : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
    norm_num
  rw [herase, hF]
  have hdq : (q : ℝ) - 1 ≠ 0 := by
    have hqR : (1 : ℝ) < q := by exact_mod_cast hq
    linarith
  rw [qEntropy_eq_logb_form]
  rw [Real.logb_div hβ0.ne' hdq]
  field_simp [hdq]
  ring

def rlNoiseWeight_mul_ne_zero
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (a x : F) (ha : a ≠ 0) :
    rlNoiseWeight β (a * x) = rlNoiseWeight β x := by
  by_cases hx : x = 0
  · subst x
    simp only [mul_zero]
  · have hax : a * x ≠ 0 := mul_ne_zero ha hx
    unfold rlNoiseWeight
    rw [if_neg hax, if_neg hx]

def rlNoiseWeight_nonneg
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∀ x : F, 0 ≤ rlNoiseWeight β x := by
  intro x
  unfold rlNoiseWeight
  split_ifs
  · linarith
  · apply div_nonneg hβ0
    have : (1 : ℝ) < Fintype.card F := by exact_mod_cast hF
    linarith

def rlNoiseWeight_parameter_continuous
    {F : Type} [Field F] [Fintype F] [DecidableEq F] (x : F) :
    Continuous (fun β : ℝ => rlNoiseWeight β x) := by
  unfold rlNoiseWeight
  split_ifs
  · fun_prop
  · fun_prop

def rlNoiseWeight_pos
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ x : F, 0 < rlNoiseWeight β x := by
  intro x
  unfold rlNoiseWeight
  split_ifs
  · linarith
  · apply div_pos hβ0
    have hcard : (1 : ℝ) < Fintype.card F := by exact_mod_cast hF
    linarith

def rlNoiseWeight_ringEquiv
    (β : ℝ) {F K : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [DecidableEq K]
    (e : F ≃+* K) (x : F) :
    rlNoiseWeight (F := K) β (e x) = rlNoiseWeight (F := F) β x := by
  by_cases hx : x = 0
  · subst x
    unfold rlNoiseWeight
    rw [map_zero, if_pos rfl, if_pos rfl]
  · have hex : e x ≠ 0 := (map_ne_zero e).2 hx
    unfold rlNoiseWeight
    rw [if_neg hex, if_neg hx]
    rw [← Fintype.card_congr e.toEquiv]

def rlNoiseWeight_uniform
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (a : F) :
    rlNoiseWeight (1 - 1 / (Fintype.card F : ℝ)) a =
      1 / (Fintype.card F : ℝ) := by
  unfold rlNoiseWeight
  split_ifs
  · ring
  · have hcard : (Fintype.card F : ℝ) ≠ 0 := by positivity
    have hsub : (Fintype.card F : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < Fintype.card F := by exact_mod_cast hF
      linarith
    field_simp

def rlNoiseWeight_uniform_lower
    (q : ℕ) (β : ℝ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q) (x : F) :
    min (1 - β) (β / ((q : ℝ) - 1)) ≤ rlNoiseWeight β x := by
  unfold rlNoiseWeight
  by_cases hx : x = 0
  · rw [if_pos hx]
    exact min_le_left _ _
  · rw [if_neg hx, hF]
    exact min_le_right _ _

def rlParityCheckAnnihilates
    (m s : ℕ) {ι F : Type} [Fintype ι]
    [Field F] [Fintype F] [DecidableEq F]
    (H : (ι → F) →ₗ[F] (Fin s → F))
    (R : ι → F × (Fin m → F)) : Prop :=
  ∀ j : Fin m, H (fun i => (R i).2 j) = 0

noncomputable def rlProductWeight
    {α κ : Type} (p : α → ℝ) (r : κ → ℝ) (x : α × κ) : ℝ :=
  p x.1 * r x.2

noncomputable def rlFiniteEntropyProduct
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α → ℝ) (r : κ → ℝ) : ℝ :=
  rlFiniteEntropy q (rlProductWeight p r)

open scoped BigOperators in
def rlFiniteEntropyProduct_add
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α → ℝ) (r : κ → ℝ)
    (hp_pos : ∀ x, 0 < p x) (hr_pos : ∀ y, 0 < r y)
    (hp_sum : (∑ x, p x) = 1) (hr_sum : (∑ y, r y) = 1) :
    rlFiniteEntropyProduct q p r =
      rlFiniteEntropy q p + rlFiniteEntropy q r := by
  classical
  have hinner₁ (x : α) :
      (∑ y : κ, p x * r y * Real.logb q (p x)) =
        p x * Real.logb q (p x) := by
    calc
      (∑ y : κ, p x * r y * Real.logb q (p x)) =
          (p x * Real.logb q (p x)) * ∑ y : κ, r y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        ring
      _ = p x * Real.logb q (p x) := by rw [hr_sum, mul_one]
  have hinner₂ (x : α) :
      (∑ y : κ, p x * r y * Real.logb q (r y)) =
        p x * ∑ y : κ, r y * Real.logb q (r y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  unfold rlFiniteEntropyProduct rlFiniteEntropy rlProductWeight
  rw [Fintype.sum_prod_type]
  simp_rw [Real.logb_mul (ne_of_gt (hp_pos _)) (ne_of_gt (hr_pos _)), mul_add,
    Finset.sum_add_distrib, hinner₁, hinner₂]
  have hfactor :
      (∑ x : α, p x * ∑ y : κ, r y * Real.logb q (r y)) =
        ∑ y : κ, r y * Real.logb q (r y) := by
    rw [← Finset.sum_mul, hp_sum, one_mul]
  rw [hfactor]
  ring

open scoped BigOperators in
def rlFiniteEntropyProduct_add_nonneg
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α → ℝ) (r : κ → ℝ)
    (_hp_nonneg : ∀ x, 0 ≤ p x) (_hr_nonneg : ∀ y, 0 ≤ r y)
    (hp_sum : (∑ x, p x) = 1) (hr_sum : (∑ y, r y) = 1) :
    rlFiniteEntropyProduct q p r =
      rlFiniteEntropy q p + rlFiniteEntropy q r := by
  classical
  have hlog (x : α) (y : κ) :
      p x * r y * Real.logb q (p x * r y) =
        p x * r y * Real.logb q (p x) +
          p x * r y * Real.logb q (r y) := by
    by_cases hx : p x = 0
    · rw [hx]
      ring
    · by_cases hy : r y = 0
      · rw [hy]
        ring
      · rw [Real.logb_mul hx hy]
        ring
  have hinner₁ (x : α) :
      (∑ y : κ, p x * r y * Real.logb q (p x)) =
        p x * Real.logb q (p x) := by
    calc
      (∑ y : κ, p x * r y * Real.logb q (p x)) =
          (p x * Real.logb q (p x)) * ∑ y : κ, r y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        ring
      _ = p x * Real.logb q (p x) := by rw [hr_sum, mul_one]
  have hinner₂ (x : α) :
      (∑ y : κ, p x * r y * Real.logb q (r y)) =
        p x * ∑ y : κ, r y * Real.logb q (r y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    ring
  unfold rlFiniteEntropyProduct rlFiniteEntropy rlProductWeight
  rw [Fintype.sum_prod_type]
  simp_rw [hlog, Finset.sum_add_distrib, hinner₁, hinner₂]
  have hfactor :
      (∑ x : α, p x * ∑ y : κ, r y * Real.logb q (r y)) =
        ∑ y : κ, r y * Real.logb q (r y) := by
    rw [← Finset.sum_mul, hp_sum, one_mul]
  rw [hfactor]
  ring

def rlFiniteProduct_support
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (x : α) (y : κ)
    (hzero : rlProductWeight (rlFiniteMarginalLeft p)
      (rlFiniteMarginalRight p) (x, y) = 0) :
    p (x, y) = 0 := by
  by_contra hp0
  have hppos : 0 < p (x, y) :=
    lt_of_le_of_ne (hp (x, y)) (Ne.symm hp0)
  have hleft : 0 < rlFiniteMarginalLeft p x :=
    lt_of_lt_of_le hppos (rlFiniteMarginalLeft_ge p hp x y)
  have hright : 0 < rlFiniteMarginalRight p y :=
    lt_of_lt_of_le hppos (rlFiniteMarginalRight_ge p hp x y)
  have hprod :
      0 < rlProductWeight (rlFiniteMarginalLeft p)
        (rlFiniteMarginalRight p) (x, y) := by
    unfold rlProductWeight
    exact mul_pos hleft hright
  rw [hzero] at hprod
  exact (lt_irrefl 0) hprod

def rlFinite_log_ratio_product_pointwise
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z) (z : α × κ) :
    p z * Real.logb q
        (p z / rlProductWeight (rlFiniteMarginalLeft p)
          (rlFiniteMarginalRight p) z) =
      p z * Real.logb q (p z) -
        p z * Real.logb q (rlFiniteMarginalLeft p z.1) -
          p z * Real.logb q (rlFiniteMarginalRight p z.2) := by
  rcases z with ⟨x, y⟩
  by_cases hp0 : p (x, y) = 0
  · rw [hp0]
    ring
  · have hppos : 0 < p (x, y) :=
      lt_of_le_of_ne (hp (x, y)) (Ne.symm hp0)
    have hleft : 0 < rlFiniteMarginalLeft p x :=
      lt_of_lt_of_le hppos (rlFiniteMarginalLeft_ge p hp x y)
    have hright : 0 < rlFiniteMarginalRight p y :=
      lt_of_lt_of_le hppos (rlFiniteMarginalRight_ge p hp x y)
    unfold rlProductWeight
    rw [Real.logb_div hp0 (mul_ne_zero hleft.ne' hright.ne'),
      Real.logb_mul hleft.ne' hright.ne']
    ring

noncomputable def rlProfileColumnSpan
    (m : ℕ) {ι F : Type} [Fintype ι]
    [Field F] [Fintype F] [DecidableEq F]
    (R : ι → F × (Fin m → F)) : Submodule F (ι → F) :=
  Submodule.span F (Set.range (fun j : Fin m => fun i => (R i).2 j))

def rlExactTypeFullSupport_columnSpan_finrank
    (m : ℕ) {ι F : Type} [Fintype ι]
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (ht : rlExactTypeFullSupport (Fintype.card ι) t)
    (R : ι → F × (Fin m → F)) (hR : rlHasExactType t R) :
    Module.finrank F (rlProfileColumnSpan m R) = m := by
  unfold rlProfileColumnSpan
  simpa only [Fintype.card_fin] using
    (finrank_span_eq_card
      (rlExactTypeFullSupport_columns_linearIndependent m t ht R hR))

noncomputable def rlProfileExactRealized
    (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (C : Submodule F (ι → F)) : Prop :=
  ∃ R : ι → F × (Fin m → F),
    rlHasExactType t R ∧
      Function.Injective (fun j : Fin m => fun i => (R i).2 j) ∧
      ∀ j : Fin m, (fun i => (R i).2 j) ∈ C

noncomputable def rlProfilePairColumnSpan
    (m : ℕ) {ι F : Type} [Fintype ι]
    [Field F] [Fintype F] [DecidableEq F]
    (R S : ι → F × (Fin m → F)) : Submodule F (ι → F) :=
  Submodule.span F
    (Set.range (fun j : Fin m => fun i => (R i).2 j) ∪
      Set.range (fun j : Fin m => fun i => (S i).2 j))

open scoped BigOperators in
noncomputable def rlPushforwardWeight
    {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (p : α → ℝ) (f : α → κ) (y : κ) : ℝ :=
  ∑ x : α, if f x = y then p x else 0

open scoped BigOperators in
def rlFiniteMapLeftWeight_eq_pushforward_pair
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq β] [DecidableEq κ]
    (p : α × κ → ℝ) (f : α → β) (z : β × κ) :
    rlPushforwardWeight p (fun t : α × κ => (f t.1, t.2)) z =
      rlFiniteMapLeftWeight p f z := by
  classical
  rcases z with ⟨b, z⟩
  unfold rlPushforwardWeight rlFiniteMapLeftWeight
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hfx : f x = b
  · rw [if_pos hfx]
    simpa only [Prod.mk.injEq, hfx, true_and] using
      (Fintype.sum_ite_eq' z (fun y : κ => p (x, y)))
  · rw [if_neg hfx]
    apply Finset.sum_eq_zero
    intro y _hy
    rw [if_neg]
    intro hpair
    exact hfx (congrArg Prod.fst hpair)

open scoped BigOperators in
def rlFiniteMapLeftWeight_marginals
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq β] (p : α × κ → ℝ) (f : α → β) :
    (∀ y : β,
      rlFiniteMarginalLeft (rlFiniteMapLeftWeight p f) y =
        rlPushforwardWeight (rlFiniteMarginalLeft p) f y) ∧
    (∀ z : κ,
      rlFiniteMarginalRight (rlFiniteMapLeftWeight p f) z =
        rlFiniteMarginalRight p z) := by
  classical
  constructor
  · intro y
    unfold rlFiniteMarginalLeft rlFiniteMapLeftWeight rlPushforwardWeight
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _hx
    by_cases hxy : f x = y
    · simp only [if_pos hxy]
    · simp only [if_neg hxy, Finset.sum_const_zero]
  · intro z
    unfold rlFiniteMarginalRight rlFiniteMapLeftWeight
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _hx
    exact Fintype.sum_ite_eq (f x) (fun _y : β => p (x, z))

open scoped BigOperators in
def rlFiniteMapLeftWeight_product
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq β]
    (p : α × κ → ℝ) (f : α → β) (z : β × κ) :
    rlFiniteMapLeftWeight
        (rlProductWeight (rlFiniteMarginalLeft p)
          (rlFiniteMarginalRight p)) f z =
      rlProductWeight
        (rlFiniteMarginalLeft (rlFiniteMapLeftWeight p f))
        (rlFiniteMarginalRight (rlFiniteMapLeftWeight p f)) z := by
  classical
  rcases z with ⟨b, z⟩
  unfold rlFiniteMapLeftWeight rlProductWeight
  calc
    (∑ x : α, if f x = b then
        rlFiniteMarginalLeft p x * rlFiniteMarginalRight p z else 0) =
        (∑ x : α, if f x = b then rlFiniteMarginalLeft p x else 0) *
          rlFiniteMarginalRight p z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hfx : f x = b
      · rw [if_pos hfx, if_pos hfx]
      · rw [if_neg hfx, if_neg hfx, zero_mul]
    _ = rlPushforwardWeight (rlFiniteMarginalLeft p) f b *
        rlFiniteMarginalRight p z := by rfl
    _ = rlFiniteMarginalLeft (rlFiniteMapLeftWeight p f) b *
        rlFiniteMarginalRight (rlFiniteMapLeftWeight p f) z := by
      rw [(rlFiniteMapLeftWeight_marginals p f).1 b,
        (rlFiniteMapLeftWeight_marginals p f).2 z]

noncomputable def rlPushforwardEntropy
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (p : α → ℝ) (f : α → κ) : ℝ :=
  rlFiniteEntropy q (rlPushforwardWeight p f)

def rlExactTypeProjectedEntropy_eq_pushforward
    (q n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (f : α → κ) :
    rlExactTypeProjectedEntropy q n t f =
      rlPushforwardEntropy q (rlExactTypeWeight n t) f := by
  rfl

open scoped BigOperators in
def rlPushforwardWeight_le_one
    {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : (∑ x : α, p x) = 1) (f : α → κ) :
    ∀ y, rlPushforwardWeight p f y ≤ 1 := by
  intro y
  unfold rlPushforwardWeight
  calc
    (∑ x : α, if f x = y then p x else 0) ≤ ∑ x : α, p x := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hxy : f x = y
      · rw [if_pos hxy]
      · rw [if_neg hxy]
        exact hp x
    _ = 1 := hsum

open scoped BigOperators in
def rlPushforwardWeight_nonneg
    {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (f : α → κ) :
    ∀ y, 0 ≤ rlPushforwardWeight p f y := by
  intro y
  unfold rlPushforwardWeight
  apply Finset.sum_nonneg
  intro x _hx
  by_cases hxy : f x = y
  · rw [if_pos hxy]
    exact hp x
  · rw [if_neg hxy]

def rlExactTypePushforwardWeight_nonneg
    (n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (f : α → κ) :
    ∀ y, 0 ≤ rlExactTypePushforwardWeight n t f y := by
  exact rlPushforwardWeight_nonneg (rlExactTypeWeight n t)
    (rlExactTypeWeight_nonneg n t) f

open scoped BigOperators in
def rlFiniteKL_fiber_pushforward_le
    {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (p r : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hr : ∀ x, 0 ≤ r x)
    (hac : ∀ x, r x = 0 → p x = 0) (f : α → κ) (y : κ) :
    rlPushforwardWeight r f y *
        rlKLFun (rlPushforwardWeight p f y / rlPushforwardWeight r f y) ≤
      ∑ x : α, if f x = y then r x * rlKLFun (p x / r x) else 0 := by
  classical
  let R : ℝ := rlPushforwardWeight r f y
  let P : ℝ := rlPushforwardWeight p f y
  by_cases hR0 : R = 0
  · change R * rlKLFun (P / R) ≤ _
    rw [hR0, zero_mul]
    apply Finset.sum_nonneg
    intro x _hx
    by_cases hxy : f x = y
    · rw [if_pos hxy]
      exact mul_nonneg (hr x)
        (rlKLFun_nonneg (p x / r x) (div_nonneg (hp x) (hr x)))
    · rw [if_neg hxy]
  · have hRnonneg : 0 ≤ R :=
      rlPushforwardWeight_nonneg r hr f y
    let w : α → ℝ := fun x => if f x = y then r x / R else 0
    let u : α → ℝ := fun x => p x / r x
    have hw_nonneg : ∀ x, 0 ≤ w x := by
      intro x
      change 0 ≤ if f x = y then r x / R else 0
      by_cases hxy : f x = y
      · rw [if_pos hxy]
        exact div_nonneg (hr x) hRnonneg
      · rw [if_neg hxy]
    have hw_sum : (∑ x : α, w x) = 1 := by
      calc
        (∑ x : α, w x) =
            ∑ x : α, (if f x = y then r x else 0) / R := by
          apply Finset.sum_congr rfl
          intro x _hx
          change (if f x = y then r x / R else 0) =
            (if f x = y then r x else 0) / R
          by_cases hxy : f x = y
          · rw [if_pos hxy, if_pos hxy]
          · rw [if_neg hxy, if_neg hxy, zero_div]
        _ = (∑ x : α, if f x = y then r x else 0) / R := by
          rw [Finset.sum_div]
        _ = R / R := by rfl
        _ = 1 := div_self hR0
    have hu_nonneg : ∀ x, u x ∈ Set.Ici (0 : ℝ) := by
      intro x
      exact div_nonneg (hp x) (hr x)
    have havg : (∑ x : α, w x • u x) = P / R := by
      change (∑ x : α, w x * u x) = P / R
      calc
        (∑ x : α, w x * u x) =
            ∑ x : α, if f x = y then p x / R else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          change (if f x = y then r x / R else 0) * (p x / r x) =
            if f x = y then p x / R else 0
          by_cases hxy : f x = y
          · rw [if_pos hxy, if_pos hxy]
            by_cases hr0 : r x = 0
            · have hp0 : p x = 0 := hac x hr0
              rw [hr0, hp0]
              norm_num
            · field_simp [hR0, hr0]
          · rw [if_neg hxy, if_neg hxy, zero_mul]
        _ = ∑ x : α, (if f x = y then p x else 0) / R := by
          apply Finset.sum_congr rfl
          intro x _hx
          change (if f x = y then p x / R else 0) =
            (if f x = y then p x else 0) / R
          by_cases hxy : f x = y
          · rw [if_pos hxy, if_pos hxy]
          · rw [if_neg hxy, if_neg hxy, zero_div]
        _ = (∑ x : α, if f x = y then p x else 0) / R := by
          rw [Finset.sum_div]
        _ = P / R := by rfl
    have hjensen :
        rlKLFun (∑ x : α, w x • u x) ≤
          ∑ x : α, w x • rlKLFun (u x) := by
      exact rlKLFun_convexOn.map_sum_le
        (fun x _hx => hw_nonneg x) hw_sum
        (fun x _hx => hu_nonneg x)
    change R * rlKLFun (P / R) ≤ _
    rw [← havg]
    calc
      R * rlKLFun (∑ x : α, w x • u x) ≤
          R * ∑ x : α, w x • rlKLFun (u x) :=
        mul_le_mul_of_nonneg_left hjensen hRnonneg
      _ = ∑ x : α,
          if f x = y then r x * rlKLFun (p x / r x) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        change R * ((if f x = y then r x / R else 0) *
          rlKLFun (p x / r x)) =
            if f x = y then r x * rlKLFun (p x / r x) else 0
        by_cases hxy : f x = y
        · rw [if_pos hxy, if_pos hxy]
          field_simp [hR0]
        · rw [if_neg hxy, if_neg hxy, zero_mul, mul_zero]

open scoped BigOperators in
def rlFiniteKL_pushforward_le
    (q : ℕ) (hq : 2 ≤ q)
    {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (p r : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hr : ∀ x, 0 ≤ r x)
    (hac : ∀ x, r x = 0 → p x = 0) (f : α → κ) :
    rlFiniteKL q (rlPushforwardWeight p f) (rlPushforwardWeight r f) ≤
      rlFiniteKL q p r := by
  classical
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  unfold rlFiniteKL
  apply (div_le_div_iff_of_pos_right hlog).2
  calc
    (∑ y : κ,
        rlPushforwardWeight r f y *
          rlKLFun (rlPushforwardWeight p f y /
            rlPushforwardWeight r f y)) ≤
        ∑ y : κ, ∑ x : α,
          if f x = y then r x * rlKLFun (p x / r x) else 0 := by
      apply Finset.sum_le_sum
      intro y _hy
      exact rlFiniteKL_fiber_pushforward_le p r hp hr hac f y
    _ = ∑ x : α, r x * rlKLFun (p x / r x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      exact Fintype.sum_ite_eq (f x)
        (fun _y : κ => r x * rlKLFun (p x / r x))

open scoped BigOperators in
noncomputable def rlShiftWeight
    (β θ : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F] (v : Fin d → F) : ℝ :=
  ∑ a : F, rlNoiseWeight θ a * ∏ j, rlNoiseWeight β (v j - a)

noncomputable def rlShiftEntropy
    (q : ℕ) (β θ : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F] : ℝ :=
  rlFiniteEntropy q (rlShiftWeight (F := F) β θ d)

open scoped BigOperators in
def rlShiftWeight_parameter_continuous
    (d : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (v : Fin d → F) :
    Continuous (fun β : ℝ => rlShiftWeight (F := F) β β d v) := by
  unfold rlShiftWeight
  apply continuous_finset_sum Finset.univ
  intro a _ha
  apply Continuous.mul
  · exact rlNoiseWeight_parameter_continuous a
  · apply continuous_finset_prod Finset.univ
    intro j _hj
    exact rlNoiseWeight_parameter_continuous (v j - a)

open scoped BigOperators in
def rlShiftWeight_ringEquiv
    (β θ : ℝ) (d : ℕ) {F K : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [DecidableEq K]
    (e : F ≃+* K) (v : Fin d → F) :
    rlShiftWeight (F := K) β θ d (fun j => e (v j)) =
      rlShiftWeight (F := F) β θ d v := by
  unfold rlShiftWeight
  symm
  apply Fintype.sum_equiv e.toEquiv
  intro a
  change rlNoiseWeight (F := F) θ a *
      ∏ j, rlNoiseWeight (F := F) β (v j - a) =
    rlNoiseWeight (F := K) θ (e a) *
      ∏ j, rlNoiseWeight (F := K) β (e (v j) - e a)
  rw [rlNoiseWeight_ringEquiv θ e a]
  congr 1
  apply Finset.prod_congr rfl
  intro j _hj
  rw [← map_sub, rlNoiseWeight_ringEquiv β e (v j - a)]

def rlShiftEntropy_ringEquiv
    (q : ℕ) (β θ : ℝ) (d : ℕ) {F K : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [DecidableEq K]
    (e : F ≃+* K) :
    rlShiftEntropy (F := K) q β θ d =
      rlShiftEntropy (F := F) q β θ d := by
  let E : (Fin d → F) ≃ (Fin d → K) :=
    Equiv.piCongrRight (fun _ => e.toEquiv)
  unfold rlShiftEntropy
  calc
    rlFiniteEntropy q (rlShiftWeight (F := K) β θ d) =
        rlFiniteEntropy q
          (fun w : Fin d → K =>
            rlShiftWeight (F := F) β θ d (E.symm w)) := by
      apply rlFiniteEntropy_congr
      intro w
      simpa [E] using
        (rlShiftWeight_ringEquiv β θ d e (E.symm w))
    _ = rlFiniteEntropy q (rlShiftWeight (F := F) β θ d) :=
      (rlFiniteEntropy_equiv q
        (rlShiftWeight (F := F) β θ d) E).symm

open scoped BigOperators in
noncomputable def rlTranslatedRowWeight
    (β : ℝ) (m : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (x : F × (Fin m → F)) : ℝ :=
  (1 / (Fintype.card F : ℝ)) * ∏ j, rlNoiseWeight β (x.2 j - x.1)

noncomputable def rlExactTypeApproximates
    (β : ℝ) (m n : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType n (F × (Fin m → F))) : Prop :=
  ∀ x : F × (Fin m → F),
    |rlExactTypeWeight n t x - rlTranslatedRowWeight β m x| ≤ 1 / (n : ℝ)

open scoped BigOperators in
def rlExactTypePushforwardWeight_error_le
    (β : ℝ) (m n : ℕ) {F κ : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype κ] [DecidableEq κ]
    (t : rlExactType n (F × (Fin m → F)))
    (ht : rlExactTypeApproximates β m n t)
    (f : F × (Fin m → F) → κ) (y : κ) :
    |rlExactTypePushforwardWeight n t f y -
        rlPushforwardWeight (rlTranslatedRowWeight β m) f y| ≤
      (Fintype.card (F × (Fin m → F)) : ℝ) / (n : ℝ) := by
  classical
  unfold rlExactTypePushforwardWeight rlPushforwardWeight
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x : F × (Fin m → F),
        ((if f x = y then rlExactTypeWeight n t x else 0) -
          (if f x = y then rlTranslatedRowWeight β m x else 0))| ≤
        ∑ x : F × (Fin m → F),
          |(if f x = y then rlExactTypeWeight n t x else 0) -
            (if f x = y then rlTranslatedRowWeight β m x else 0)| := by
      simpa only using
        (Finset.abs_sum_le_sum_abs
          (fun x : F × (Fin m → F) =>
            (if f x = y then rlExactTypeWeight n t x else 0) -
              (if f x = y then rlTranslatedRowWeight β m x else 0))
          Finset.univ)
    _ ≤ ∑ _x : F × (Fin m → F), 1 / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hxy : f x = y
      · simp only [if_pos hxy]
        exact ht x
      · simp only [if_neg hxy, sub_self, abs_zero]
        positivity
    _ = (Fintype.card (F × (Fin m → F)) : ℝ) / (n : ℝ) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul, Finset.card_univ]
      ring

noncomputable def rlProfileApprox
    (β : ℝ) (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (R : ι → F × (Fin m → F)) : Prop :=
  ∀ x : F × (Fin m → F),
    |((Finset.univ.filter (fun i => R i = x)).card : ℝ) /
          (Fintype.card ι : ℝ) - rlTranslatedRowWeight β m x| ≤
      1 / (Fintype.card ι : ℝ)

def rlProfileApprox_of_exactType
    (β : ℝ) (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (ht : rlExactTypeApproximates β m (Fintype.card ι) t)
    (R : ι → F × (Fin m → F)) (hR : rlHasExactType t R) :
    rlProfileApprox β m R := by
  unfold rlProfileApprox
  intro x
  rw [hR x]
  simpa only [rlExactTypeWeight] using ht x

noncomputable def rlProfileRealized
    (β : ℝ) (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : Submodule F (ι → F)) : Prop :=
  ∃ R : ι → F × (Fin m → F),
    rlProfileApprox β m R ∧
      Function.Injective (fun j : Fin m => fun i => (R i).2 j) ∧
      ∀ j : Fin m, (fun i => (R i).2 j) ∈ C

def rlProfileExactRealized_to_realized
    (β : ℝ) (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (ht : rlExactTypeApproximates β m (Fintype.card ι) t)
    (C : Submodule F (ι → F)) :
    rlProfileExactRealized m t C → rlProfileRealized β m C := by
  rintro ⟨R, htype, hinj, hmem⟩
  exact ⟨R, rlProfileApprox_of_exactType β m t ht R htype, hinj, hmem⟩

def rlProfileExactType_fullSupport_to_realized
    (β : ℝ) (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType (Fintype.card ι) (F × (Fin m → F)))
    (htApprox : rlExactTypeApproximates β m (Fintype.card ι) t)
    (htFull : rlExactTypeFullSupport (Fintype.card ι) t)
    (C : Submodule F (ι → F))
    (h : ∃ R : ι → F × (Fin m → F),
      rlHasExactType t R ∧
        ∀ j : Fin m, (fun i => (R i).2 j) ∈ C) :
    rlProfileRealized β m C := by
  rcases h with ⟨R, htype, hmem⟩
  refine ⟨R, rlProfileApprox_of_exactType β m t htApprox R htype, ?_, hmem⟩
  exact rlExactTypeFullSupport_columns_injective m t htFull R htype

open scoped BigOperators in
noncomputable def rlProjectedEntropy
    (q : ℕ) (β : ℝ) (m r : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (A : (Fin m → F) →ₗ[F] (Fin r → F)) : ℝ :=
  -∑ y : Fin r → F,
      let p := ∑ x : F × (Fin m → F),
        if A x.2 = y then rlTranslatedRowWeight β m x else 0
      p * Real.logb q p

noncomputable def rlProfileNotImplicitlyRare
    (q : ℕ) (γ β : ℝ) (m : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (r : ℕ) (A : (Fin m → F) →ₗ[F] (Fin r → F)),
    Function.Surjective A →
      γ * (r : ℝ) ≤ rlProjectedEntropy q β m r A

noncomputable def rlProfileNotImplicitlyRareOn
    (q : ℕ) (γ β : ℝ) (m : ℕ) (F : Type)
    [Field F] [Fintype F] [DecidableEq F] : Prop :=
  rlProfileNotImplicitlyRare (F := F) q γ β m

noncomputable def rlProfileParametersConclusion
    (q : ℕ) (δ ε : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
    ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ →
      ρ < 1 - qEntropy q δ →
        ∃ β η : ℝ, 0 < ρ ∧ 0 < β ∧ β < δ ∧ 0 < η ∧
          ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q →
              rlProfileNotImplicitlyRare (F := F) q (1 - ρ + η) β
                (Nat.floor (qEntropy q δ /
                  (1 - qEntropy q δ - ρ) - ε) + 1)

noncomputable def rlProfileUnrealizedCountConclusion
    (q : ℕ) (ρ β η : ℝ) (m : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F],
      Fintype.card F = q → n₀ ≤ Fintype.card ι →
      rlProfileNotImplicitlyRare (F := F) q (1 - ρ + η) β m →
      ∀ k : ℕ,
        ρ ≤ (k : ℝ) / Fintype.card ι →
        (k : ℝ) / Fintype.card ι ≤ ρ + 1 / Fintype.card ι →
        (({C : Submodule F (ι → F) | Module.finrank F C = k ∧
            ¬ rlProfileRealized β m C}.ncard : ℝ))
          ≤ (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) *
              (({C : Submodule F (ι → F) |
                Module.finrank F C = k}.ncard : ℝ))

def rlProjectedEntropy_eq_pushforward
    (q : ℕ) (β : ℝ) (m r : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (A : (Fin m → F) →ₗ[F] (Fin r → F)) :
    rlProjectedEntropy q β m r A =
      rlPushforwardEntropy q (rlTranslatedRowWeight β m)
        (fun x : F × (Fin m → F) => A x.2) := by
  rfl

noncomputable def rlRealizationCount
    (β : ℝ) (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : Submodule F (ι → F)) : ℕ :=
  {R : ι → F × (Fin m → F) |
    rlProfileApprox β m R ∧
      Function.Injective (fun j : Fin m => fun i => (R i).2 j) ∧
      ∀ j : Fin m, (fun i => (R i).2 j) ∈ C}.ncard

open scoped BigOperators in
def rlTranslatedRowWeight_nonneg
    (β : ℝ) (m : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∀ x : F × (Fin m → F), 0 ≤ rlTranslatedRowWeight β m x := by
  intro x
  unfold rlTranslatedRowWeight
  apply mul_nonneg
  · positivity
  · exact Finset.prod_nonneg fun j _ =>
      rlNoiseWeight_nonneg β hF hβ0 hβ1 (x.2 j - x.1)

open scoped BigOperators in
def rlTranslatedRowWeight_parameter_continuous
    (m : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (x : F × (Fin m → F)) :
    Continuous (fun β : ℝ => rlTranslatedRowWeight β m x) := by
  unfold rlTranslatedRowWeight
  apply Continuous.mul
  · fun_prop
  · apply continuous_finset_prod Finset.univ
    intro j _hj
    exact rlNoiseWeight_parameter_continuous (x.2 j - x.1)

open scoped BigOperators in
def rlTranslatedRowWeight_pos
    (β : ℝ) (m : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ x : F × (Fin m → F), 0 < rlTranslatedRowWeight β m x := by
  intro x
  unfold rlTranslatedRowWeight
  apply mul_pos
  · positivity
  · exact Finset.prod_pos fun j _ =>
      rlNoiseWeight_pos β hF hβ0 hβ1 (x.2 j - x.1)

open scoped BigOperators in
def rlTranslatedRowWeight_ringEquiv
    (β : ℝ) (m : ℕ) {F K : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [DecidableEq K]
    (e : F ≃+* K) (x : F × (Fin m → F)) :
    rlTranslatedRowWeight (F := K) β m
        (e x.1, fun j => e (x.2 j)) =
      rlTranslatedRowWeight (F := F) β m x := by
  unfold rlTranslatedRowWeight
  rw [← Fintype.card_congr e.toEquiv]
  congr 1
  apply Finset.prod_congr rfl
  intro j _hj
  rw [← map_sub, rlNoiseWeight_ringEquiv β e]

open scoped BigOperators in
def rlTranslatedRowWeight_uniform_lower
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (m : ℕ)
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q) (x : F × (Fin m → F)) :
    (1 / (q : ℝ)) *
        (min (1 - β) (β / ((q : ℝ) - 1))) ^ m ≤
      rlTranslatedRowWeight β m x := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hden : (0 : ℝ) < q - 1 := sub_pos.mpr hqR
  have hbase0 :
      0 ≤ min (1 - β) (β / ((q : ℝ) - 1)) := by
    exact le_min (sub_nonneg.mpr hβ1.le) (div_nonneg hβ0.le hden.le)
  unfold rlTranslatedRowWeight
  rw [hF]
  apply mul_le_mul_of_nonneg_left
  · rw [show (min (1 - β) (β / ((q : ℝ) - 1))) ^ m =
        ∏ _j : Fin m, min (1 - β) (β / ((q : ℝ) - 1)) by simp]
    apply Finset.prod_le_prod
    · intro j _hj
      exact hbase0
    · intro j _hj
      exact rlNoiseWeight_uniform_lower q β hF (x.2 j - x.1)
  · positivity

open scoped BigOperators in
def rlExactTypeApproximates_fullSupport_eventually
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (m : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F],
        Fintype.card F = q →
        ∀ t : rlExactType n (F × (Fin m → F)),
          rlExactTypeApproximates β m n t →
          rlExactTypeFullSupport n t := by
  let a : ℝ := min (1 - β) (β / ((q : ℝ) - 1))
  let L : ℝ := (1 / (q : ℝ)) * a ^ m
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hqR
  have hden : (0 : ℝ) < q - 1 := sub_pos.mpr hqR
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (sub_pos.mpr hβ1) (div_pos hβ0 hden)
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos (div_pos zero_lt_one hq0) (pow_pos ha m)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / L)
  refine ⟨n₀, ?_⟩
  intro n hn F _ _ _ hF t ht x
  have hn₀pos : 0 < n₀ := by
    have : (0 : ℝ) < 1 / L := div_pos zero_lt_one hL
    exact_mod_cast (lt_trans this hn₀)
  have hnpos : 0 < n := lt_of_lt_of_le hn₀pos hn
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hinv : 1 / (n : ℝ) < L := by
    rw [div_lt_iff₀ hnRpos]
    have hone : (1 : ℝ) < (n₀ : ℝ) * L := by
      calc
        (1 : ℝ) = (1 / L) * L := by field_simp [hL.ne']
        _ < (n₀ : ℝ) * L := mul_lt_mul_of_pos_right hn₀ hL
    calc
      (1 : ℝ) < (n₀ : ℝ) * L := hone
      _ ≤ L * (n : ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hnR hL.le
  have hideal : L ≤ rlTranslatedRowWeight β m x := by
    dsimp [L, a]
    exact rlTranslatedRowWeight_uniform_lower q hq β hβ0 hβ1 m hF x
  have happrox := (abs_le.mp (ht x)).1
  have hweight : 0 < rlExactTypeWeight n t x := by
    linarith
  by_contra hx
  have hx0 : t.1 x = 0 := Nat.eq_zero_of_not_pos hx
  unfold rlExactTypeWeight at hweight
  rw [hx0] at hweight
  norm_num at hweight

open scoped BigOperators in
noncomputable def rlUniformShiftWeight
    (β : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F] (v : Fin d → F) : ℝ :=
  ∑ a : F, (1 / (Fintype.card F : ℝ)) *
    ∏ j, rlNoiseWeight β (v j - a)

open scoped BigOperators in
def rlShiftWeight_uniform_eq
    (β : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (v : Fin d → F) :
    rlShiftWeight (F := F) β (1 - 1 / (Fintype.card F : ℝ)) d v =
      rlUniformShiftWeight (F := F) β d v := by
  unfold rlShiftWeight rlUniformShiftWeight
  apply Finset.sum_congr rfl
  intro a _ha
  rw [rlNoiseWeight_uniform hF a]

noncomputable def rlUniformShiftEntropy
    (q : ℕ) (β : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F] : ℝ :=
  rlFiniteEntropy q (rlUniformShiftWeight (F := F) β d)

def rlShiftEntropy_uniform_eq
    (q : ℕ) (β : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) :
    rlShiftEntropy (F := F) q β (1 - 1 / (Fintype.card F : ℝ)) d =
      rlUniformShiftEntropy (F := F) q β d := by
  unfold rlShiftEntropy rlUniformShiftEntropy
  congr 1
  funext v
  exact rlShiftWeight_uniform_eq β d hF v

open scoped BigOperators in
def rlUniformShiftWeight_parameter_continuous
    (d : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (v : Fin d → F) :
    Continuous (fun β : ℝ => rlUniformShiftWeight (F := F) β d v) := by
  unfold rlUniformShiftWeight
  apply continuous_finset_sum Finset.univ
  intro a _ha
  apply Continuous.mul
  · fun_prop
  · apply continuous_finset_prod Finset.univ
    intro j _hj
    exact rlNoiseWeight_parameter_continuous (v j - a)

open scoped BigOperators in
def rlUniformShiftWeight_ringEquiv
    (β : ℝ) (d : ℕ) {F K : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [DecidableEq K]
    (e : F ≃+* K) (v : Fin d → F) :
    rlUniformShiftWeight (F := K) β d (fun j => e (v j)) =
      rlUniformShiftWeight (F := F) β d v := by
  unfold rlUniformShiftWeight
  rw [← Fintype.card_congr e.toEquiv]
  symm
  apply Fintype.sum_equiv e.toEquiv
  intro a
  change (1 / (Fintype.card F : ℝ)) *
      ∏ j, rlNoiseWeight (F := F) β (v j - a) =
    (1 / (Fintype.card F : ℝ)) *
      ∏ j, rlNoiseWeight (F := K) β (e (v j) - e a)
  congr 1
  apply Finset.prod_congr rfl
  intro j _hj
  rw [← map_sub, rlNoiseWeight_ringEquiv β e (v j - a)]

def rlUniformShiftEntropy_ringEquiv
    (q : ℕ) (β : ℝ) (d : ℕ) {F K : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Field K] [Fintype K] [DecidableEq K]
    (e : F ≃+* K) :
    rlUniformShiftEntropy (F := K) q β d =
      rlUniformShiftEntropy (F := F) q β d := by
  let E : (Fin d → F) ≃ (Fin d → K) :=
    Equiv.piCongrRight (fun _ => e.toEquiv)
  unfold rlUniformShiftEntropy
  calc
    rlFiniteEntropy q (rlUniformShiftWeight (F := K) β d) =
        rlFiniteEntropy q
          (fun w : Fin d → K =>
            rlUniformShiftWeight (F := F) β d (E.symm w)) := by
      apply rlFiniteEntropy_congr
      intro w
      simpa [E] using
        (rlUniformShiftWeight_ringEquiv β d e (E.symm w))
    _ = rlFiniteEntropy q (rlUniformShiftWeight (F := F) β d) :=
      (rlFiniteEntropy_equiv q
        (rlUniformShiftWeight (F := F) β d) E).symm

def rl_continuous_neg_mul_logb (q : ℕ) :
    Continuous (fun x : ℝ => -(x * Real.logb q x)) := by
  have h :=
    Real.continuous_negMulLog.div_const (Real.log (q : ℝ))
  convert h using 1
  funext x
  rw [Real.negMulLog_eq_neg]
  unfold Real.logb
  ring

open scoped BigOperators in
def rlProjectedEntropy_parameter_continuous
    (q m r : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (A : (Fin m → F) →ₗ[F] (Fin r → F)) :
    Continuous (fun β : ℝ => rlProjectedEntropy q β m r A) := by
  unfold rlProjectedEntropy
  rw [show (fun β : ℝ =>
      -∑ y : Fin r → F,
        let p := ∑ x : F × (Fin m → F),
          if A x.2 = y then rlTranslatedRowWeight β m x else 0
        p * Real.logb q p) =
      (fun β : ℝ =>
        ∑ y : Fin r → F,
          -(let p := ∑ x : F × (Fin m → F),
              if A x.2 = y then rlTranslatedRowWeight β m x else 0
            p * Real.logb q p)) by
    funext β
    rw [Finset.sum_neg_distrib]]
  apply continuous_finset_sum Finset.univ
  intro y _hy
  apply (rl_continuous_neg_mul_logb q).comp
  apply continuous_finset_sum Finset.univ
  intro x _hx
  by_cases hxy : A x.2 = y
  · simp only [if_pos hxy]
    exact rlTranslatedRowWeight_parameter_continuous m x
  · simp only [if_neg hxy]
    fun_prop

open scoped BigOperators in
def rlShiftEntropy_parameter_continuous
    (q d : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    Continuous (fun β : ℝ => rlShiftEntropy (F := F) q β β d) := by
  unfold rlShiftEntropy rlFiniteEntropy
  rw [show (fun β : ℝ =>
      -∑ v : Fin d → F,
        rlShiftWeight (F := F) β β d v *
          Real.logb q (rlShiftWeight (F := F) β β d v)) =
      (fun β : ℝ =>
        ∑ v : Fin d → F,
          -(rlShiftWeight (F := F) β β d v *
            Real.logb q (rlShiftWeight (F := F) β β d v))) by
    funext β
    rw [Finset.sum_neg_distrib]]
  apply continuous_finset_sum Finset.univ
  intro v _hv
  exact (rl_continuous_neg_mul_logb q).comp
    (rlShiftWeight_parameter_continuous d v)

open scoped BigOperators in
def rlUniformShiftEntropy_parameter_continuous
    (q d : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    Continuous (fun β : ℝ => rlUniformShiftEntropy (F := F) q β d) := by
  unfold rlUniformShiftEntropy rlFiniteEntropy
  rw [show (fun β : ℝ =>
      -∑ v : Fin d → F,
        rlUniformShiftWeight (F := F) β d v *
          Real.logb q (rlUniformShiftWeight (F := F) β d v)) =
      (fun β : ℝ =>
        ∑ v : Fin d → F,
          -(rlUniformShiftWeight (F := F) β d v *
            Real.logb q (rlUniformShiftWeight (F := F) β d v))) by
    funext β
    rw [Finset.sum_neg_distrib]]
  apply continuous_finset_sum Finset.univ
  intro v _hv
  exact (rl_continuous_neg_mul_logb q).comp
    (rlUniformShiftWeight_parameter_continuous d v)

def rl_floor_gap_arithmetic
    (q : ℕ) (hq : 2 ≤ q)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (M : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        let H : ℝ := qEntropy q δ
        let g : ℝ := 1 - H - ρ
        let m : ℕ := Nat.floor (H / g - ε) + 1
        0 < g ∧ M ≤ m ∧ (((m - 1 : ℕ) : ℝ) * g < H) ∧ (m : ℝ) * g < 1 := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hδ_one : δ < 1 := by
    have hinv : (0 : ℝ) < 1 / q := by positivity
    linarith
  let H : ℝ := qEntropy q δ
  have hH_pos : 0 < H := by
    dsimp [H]
    exact qEntropy_pos hq hδ_pos hδ_one
  have hH_lt : H < 1 := by
    dsimp [H]
    exact qEntropy_lt_one_of_lt_one_sub_inv q hq δ hδ_pos.le hδ_lt
  let D : ℝ := (M : ℝ) + ε
  have hD_pos : 0 < D := by dsimp [D]; positivity
  let E : ℝ := 1 - ε
  have hE_pos : 0 < E := by dsimp [E]; linarith
  let γ : ℝ := min (H / D) ((1 - H) / E)
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    exact lt_min (div_pos hH_pos hD_pos) (div_pos (sub_pos.mpr hH_lt) hE_pos)
  refine ⟨γ, hγ_pos, ?_⟩
  intro ρ hρ_low hρ_high
  dsimp only
  let g : ℝ := 1 - H - ρ
  have hg_pos : 0 < g := by dsimp [g, H]; linarith
  have hg_lt_γ : g < γ := by dsimp [g, H] at *; linarith
  have hgD : g < H / D := lt_of_lt_of_le hg_lt_γ (min_le_left _ _)
  have hgE : g < (1 - H) / E := lt_of_lt_of_le hg_lt_γ (min_le_right _ _)
  rw [lt_div_iff₀ hD_pos] at hgD
  rw [lt_div_iff₀ hE_pos] at hgE
  let x : ℝ := H / g - ε
  let m : ℕ := Nat.floor x + 1
  have hMx : (M : ℝ) < x := by
    have hprod : ((M : ℝ) + ε) * g < H := by
      dsimp [D] at hgD
      nlinarith
    have hdiv : (M : ℝ) + ε < H / g := (lt_div_iff₀ hg_pos).2 hprod
    dsimp [x]
    linarith
  have hx_nonneg : 0 ≤ x := le_trans (Nat.cast_nonneg M) hMx.le
  have hMfloor : M ≤ Nat.floor x := Nat.le_floor hMx.le
  have hM_m : M ≤ m := by
    dsimp [m]
    exact le_trans hMfloor (Nat.le_succ _)
  have hfloor_le : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hproper : (((m - 1 : ℕ) : ℝ) * g) < H := by
    have hmul : ((Nat.floor x : ℕ) : ℝ) * g ≤ x * g :=
      mul_le_mul_of_nonneg_right hfloor_le hg_pos.le
    have hxmul : x * g = H - ε * g := by
      dsimp [x]
      rw [sub_mul, div_mul_cancel₀ H hg_pos.ne']
    dsimp [m]
    rw [hxmul] at hmul
    nlinarith
  have hm_cast : (m : ℝ) ≤ x + 1 := by
    dsimp [m]
    push_cast
    linarith
  have hm_mul : (m : ℝ) * g ≤ (x + 1) * g :=
    mul_le_mul_of_nonneg_right hm_cast hg_pos.le
  have hxone_mul : (x + 1) * g = H + (1 - ε) * g := by
    dsimp [x]
    rw [add_mul, sub_mul, div_mul_cancel₀ H hg_pos.ne']
    ring
  have hfull : (m : ℝ) * g < 1 := by
    rw [hxone_mul] at hm_mul
    dsimp [E] at hgE
    nlinarith
  exact ⟨hg_pos, hM_m, hproper, hfull⟩

def rl_floor_gap_arithmetic_sharp
    (q : ℕ) (hq : 2 ≤ q)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (M : ℕ) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        let H : ℝ := qEntropy q δ
        let g : ℝ := 1 - H - ρ
        let m : ℕ := Nat.floor (H / g - ε) + 1
        0 < g ∧ 0 < ρ ∧ M ≤ m ∧
          (((m - 1 : ℕ) : ℝ) + ε / 2) * g < H ∧
          (m : ℝ) * g < (1 + H) / 2 := by
  have hδ_one : δ < 1 := by
    have hinv : (0 : ℝ) < 1 / q := by
      have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hq)
      positivity
    linarith
  let H : ℝ := qEntropy q δ
  have hH_pos : 0 < H := by
    dsimp [H]
    exact qEntropy_pos hq hδ_pos hδ_one
  have hH_lt : H < 1 := by
    dsimp [H]
    exact qEntropy_lt_one_of_lt_one_sub_inv q hq δ hδ_pos.le hδ_lt
  let D : ℝ := (M : ℝ) + ε
  have hD_pos : 0 < D := by dsimp [D]; positivity
  let E : ℝ := 1 - ε
  have hE_pos : 0 < E := by dsimp [E]; linarith
  let γ : ℝ := min (H / D) (min ((1 - H) / (2 * E)) ((1 - H) / 2))
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    exact lt_min (div_pos hH_pos hD_pos)
      (lt_min (div_pos (sub_pos.mpr hH_lt) (mul_pos (by norm_num) hE_pos))
        (div_pos (sub_pos.mpr hH_lt) (by norm_num)))
  refine ⟨γ, hγ_pos, ?_⟩
  intro ρ hρ_low hρ_high
  dsimp only
  let g : ℝ := 1 - H - ρ
  have hg_pos : 0 < g := by dsimp [g, H]; linarith
  have hg_lt_γ : g < γ := by dsimp [g, H] at *; linarith
  have hgD : g < H / D :=
    lt_of_lt_of_le hg_lt_γ (min_le_left _ _)
  have hgB : g < (1 - H) / (2 * E) :=
    lt_of_lt_of_le hg_lt_γ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgC : g < (1 - H) / 2 :=
    lt_of_lt_of_le hg_lt_γ (le_trans (min_le_right _ _) (min_le_right _ _))
  rw [lt_div_iff₀ hD_pos] at hgD
  rw [lt_div_iff₀ (mul_pos (by norm_num) hE_pos)] at hgB
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at hgC
  have hρ_pos : 0 < ρ := by
    dsimp [g] at hgC
    nlinarith
  let x : ℝ := H / g - ε
  let m : ℕ := Nat.floor x + 1
  have hMx : (M : ℝ) < x := by
    have hprod : ((M : ℝ) + ε) * g < H := by
      dsimp [D] at hgD
      nlinarith
    have hdiv : (M : ℝ) + ε < H / g := (lt_div_iff₀ hg_pos).2 hprod
    dsimp [x]
    linarith
  have hx_nonneg : 0 ≤ x := le_trans (Nat.cast_nonneg M) hMx.le
  have hM_m : M ≤ m := by
    have hMfloor : M ≤ Nat.floor x := Nat.le_floor hMx.le
    dsimp [m]
    exact le_trans hMfloor (Nat.le_succ _)
  have hfloor_le : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hmul : ((Nat.floor x : ℕ) : ℝ) * g ≤ x * g :=
    mul_le_mul_of_nonneg_right hfloor_le hg_pos.le
  have hxmul : x * g = H - ε * g := by
    dsimp [x]
    rw [sub_mul, div_mul_cancel₀ H hg_pos.ne']
  have hproper : ((((m - 1 : ℕ) : ℝ) + ε / 2) * g) < H := by
    dsimp [m]
    rw [hxmul] at hmul
    nlinarith
  have hm_cast : (m : ℝ) ≤ x + 1 := by
    dsimp [m]
    push_cast
    linarith
  have hm_mul : (m : ℝ) * g ≤ (x + 1) * g :=
    mul_le_mul_of_nonneg_right hm_cast hg_pos.le
  have hxone_mul : (x + 1) * g = H + (1 - ε) * g := by
    dsimp [x]
    rw [add_mul, sub_mul, div_mul_cancel₀ H hg_pos.ne']
    ring
  have hfull : (m : ℝ) * g < (1 + H) / 2 := by
    rw [hxone_mul] at hm_mul
    dsimp [E] at hgB
    nlinarith
  exact ⟨hg_pos, hρ_pos, hM_m, hproper, hfull⟩

def rl_natCard_linearMaps
    (q n s : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q) :
    Nat.card ((Fin n → F) →ₗ[F] (Fin s → F)) = q ^ (n * s) := by
  rw [Module.natCard_eq_pow_finrank
      (K := F) (V := ((Fin n → F) →ₗ[F] (Fin s → F))),
    Nat.card_eq_fintype_card, hF, Module.finrank_linearMap,
    Module.finrank_fin_fun, Module.finrank_fin_fun]

def rl_primepow_two_le (q : ℕ) (hq : IsPrimePow q) : 2 ≤ q :=
  hq.two_le

def rl_profileAlphabet_card_real
    (m : ℕ) {F : Type} [Fintype F] :
    (Fintype.card (F × (Fin m → F)) : ℝ) =
      (Fintype.card F : ℝ) ^ (m + 1) := by
  rw [Fintype.card_prod, Fintype.card_pi_const]
  simp only [Nat.cast_mul, Nat.cast_pow, pow_succ]
  ring

def rlExactTypeProjectedWeight_error_le
    (q : ℕ) (β : ℝ) (m n r : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q)
    (t : rlExactType n (F × (Fin m → F)))
    (ht : rlExactTypeApproximates β m n t)
    (A : (Fin m → F) →ₗ[F] (Fin r → F)) (y : Fin r → F) :
    |rlExactTypePushforwardWeight n t (fun x => A x.2) y -
        rlPushforwardWeight (rlTranslatedRowWeight β m)
          (fun x => A x.2) y| ≤
      (q : ℝ) ^ (m + 1) / (n : ℝ) := by
  have h := rlExactTypePushforwardWeight_error_le β m n t ht
    (fun x : F × (Fin m → F) => A x.2) y
  rw [rl_profileAlphabet_card_real m, hF] at h
  exact h

def rl_profile_budget_eventually
    (q m : ℕ) (β δ : ℝ) (hβδ : β < δ) :
    ∃ n₀ : ℕ,
      ∀ {ι : Type} [Fintype ι] [Nonempty ι],
        n₀ ≤ Fintype.card ι →
          β + (q : ℝ) ^ (m + 1 : ℕ) / (Fintype.card ι : ℝ) ≤ δ := by
  have hgap : 0 < δ - β := sub_pos.mpr hβδ
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((q : ℝ) ^ (m + 1) / (δ - β))
  refine ⟨n₀, ?_⟩
  intro ι _ _ hn
  have hnpos : (0 : ℝ) < Fintype.card ι := by positivity
  have hnR : (n₀ : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hfrac :
      (q : ℝ) ^ (m + 1) / (Fintype.card ι : ℝ) < δ - β := by
    rw [div_lt_iff₀ hnpos]
    have hmul :
        (q : ℝ) ^ (m + 1) < (n₀ : ℝ) * (δ - β) := by
      calc
        (q : ℝ) ^ (m + 1) =
            ((q : ℝ) ^ (m + 1) / (δ - β)) * (δ - β) := by
          field_simp
        _ < (n₀ : ℝ) * (δ - β) := mul_lt_mul_of_pos_right hn₀ hgap
    exact lt_of_lt_of_le hmul (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hnR hgap.le)
  linarith

def rl_surjective_fin_le
    (m r : ℕ) {F : Type} [Field F]
    (A : (Fin m → F) →ₗ[F] (Fin r → F))
    (hA : Function.Surjective A) : r ≤ m :=
  RankCondition.le_of_fin_surjective A hA

def rl_surjective_fin_self_bijective
    (m : ℕ) {F : Type} [Field F]
    (A : (Fin m → F) →ₗ[F] (Fin m → F))
    (hA : Function.Surjective A) : Function.Bijective A := by
  refine ⟨?_, hA⟩
  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A) rfl).2 hA

noncomputable def rl_surjective_fin_self_equiv
    (m : ℕ) {F : Type} [Field F]
    (A : (Fin m → F) →ₗ[F] (Fin m → F))
    (hA : Function.Surjective A) :
    (Fin m → F) ≃ₗ[F] (Fin m → F) :=
  LinearEquiv.ofBijective A
    (rl_surjective_fin_self_bijective m A hA)

def rl_surjective_kernel_finrank
    (n s : ℕ) {F : Type} [Field F]
    (H : (Fin n → F) →ₗ[F] (Fin s → F))
    (hH : Function.Surjective H) :
    Module.finrank F (LinearMap.ker H) = n - s := by
  have hrange : LinearMap.range H = ⊤ :=
    LinearMap.range_eq_top.mpr hH
  have hdim := LinearMap.finrank_range_add_finrank_ker H
  rw [hrange, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hdim
  omega

def rl_uniformContinuousOn_neg_mul_logb (q : ℕ) :
    UniformContinuousOn (fun x : ℝ => -(x * Real.logb q x))
      (Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.uniformContinuousOn_of_continuous
    (rl_continuous_neg_mul_logb q).continuousOn

open scoped BigOperators in
def rlFiniteEntropy_close_of_pointwise_close
    (q N : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ {α : Type} [Fintype α] (p r : α → ℝ),
        Fintype.card α ≤ N →
        (∀ x, p x ∈ Set.Icc (0 : ℝ) 1) →
        (∀ x, r x ∈ Set.Icc (0 : ℝ) 1) →
        (∀ x, |p x - r x| < τ) →
        |rlFiniteEntropy q p - rlFiniteEntropy q r| < e := by
  let f : ℝ → ℝ := fun x => -(x * Real.logb q x)
  have hden : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have heN : 0 < e / ((N : ℝ) + 1) := div_pos he hden
  obtain ⟨τ, hτ, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (rl_uniformContinuousOn_neg_mul_logb q))
      (e / ((N : ℝ) + 1)) heN
  refine ⟨τ, hτ, ?_⟩
  intro α _ p r hcard hp hr hclose
  let d : α → ℝ := fun x =>
    (-(p x * Real.logb q (p x))) - (-(r x * Real.logb q (r x)))
  have hpoint (x : α) : |d x| < e / ((N : ℝ) + 1) := by
    have hd : dist (p x) (r x) < τ := by
      simpa only [Real.dist_eq] using hclose x
    have hout := hmod (p x) (hp x) (r x) (hr x) hd
    simpa only [Real.dist_eq, f, d] using hout
  unfold rlFiniteEntropy
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  change |∑ x : α, d x| < e
  calc
    |∑ x : α, d x| ≤ ∑ x : α, |d x| := by
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _x : α, e / ((N : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro x _hx
      exact (hpoint x).le
    _ = (Fintype.card α : ℝ) * (e / ((N : ℝ) + 1)) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul, Finset.card_univ]
    _ ≤ (N : ℝ) * (e / ((N : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact heN.le
    _ = ((N : ℝ) / ((N : ℝ) + 1)) * e := by ring
    _ < 1 * e := by
      apply mul_lt_mul_of_pos_right _ he
      rw [div_lt_one hden]
      linarith
    _ = e := one_mul e

open scoped BigOperators in
def sum_rlExactTypeWeight
    (n : ℕ) {α : Type} [Fintype α]
    (t : rlExactType n α) (hn : 0 < n) :
    (∑ x : α, rlExactTypeWeight n t x) = 1 := by
  unfold rlExactTypeWeight
  rw [← Finset.sum_div]
  have hsum : (∑ x : α, (t.1 x : ℝ)) = (n : ℝ) := by
    exact_mod_cast t.2
  rw [hsum, div_self]
  exact_mod_cast hn.ne'

def rlExactTypePushforwardWeight_le_one
    (n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (hn : 0 < n) (f : α → κ) :
    ∀ y, rlExactTypePushforwardWeight n t f y ≤ 1 := by
  exact rlPushforwardWeight_le_one (rlExactTypeWeight n t)
    (rlExactTypeWeight_nonneg n t) (sum_rlExactTypeWeight n t hn) f

open scoped BigOperators in
def rlExactTypePushforwardWeight_le_one_all
    (n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (f : α → κ) :
    ∀ y, rlExactTypePushforwardWeight n t f y ≤ 1 := by
  intro y
  by_cases hn : n = 0
  · subst n
    unfold rlExactTypePushforwardWeight rlExactTypeWeight
    have hzero : ∀ x : α, t.1 x = 0 := by
      intro x
      have hcount : t.1 x ≤ 0 := by
        calc
          t.1 x ≤ ∑ z : α, t.1 z :=
            Finset.single_le_sum (fun z _hz => Nat.zero_le (t.1 z))
              (Finset.mem_univ x)
          _ = 0 := t.2
      omega
    simp only [hzero, Nat.cast_zero, zero_div, ite_self, Finset.sum_const_zero]
    norm_num
  · exact rlExactTypePushforwardWeight_le_one n t (Nat.pos_of_ne_zero hn) f y

def rlExactTypePushforwardWeight_mem_Icc
    (n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (hn : 0 < n) (f : α → κ) :
    ∀ y, rlExactTypePushforwardWeight n t f y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y
  exact ⟨rlExactTypePushforwardWeight_nonneg n t f y,
    rlExactTypePushforwardWeight_le_one n t hn f y⟩

def rlExactTypePushforwardWeight_mem_Icc_all
    (n : ℕ) {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (t : rlExactType n α) (f : α → κ) :
    ∀ y, rlExactTypePushforwardWeight n t f y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y
  exact ⟨rlExactTypePushforwardWeight_nonneg n t f y,
    rlExactTypePushforwardWeight_le_one_all n t f y⟩

open scoped BigOperators in
def sum_rlFiniteMarginalLeft
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) :
    (∑ x : α, rlFiniteMarginalLeft p x) = ∑ z : α × κ, p z := by
  unfold rlFiniteMarginalLeft
  exact (Fintype.sum_prod_type p).symm

open scoped BigOperators in
def sum_rlFiniteMarginalRight
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) :
    (∑ y : κ, rlFiniteMarginalRight p y) = ∑ z : α × κ, p z := by
  unfold rlFiniteMarginalRight
  calc
    (∑ y : κ, ∑ x : α, p (x, y)) =
        ∑ x : α, ∑ y : κ, p (x, y) := Finset.sum_comm
    _ = ∑ z : α × κ, p z := (Fintype.sum_prod_type p).symm

open scoped BigOperators in
def sum_rlNoiseWeight
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) : (∑ x : F, rlNoiseWeight β x) = 1 := by
  classical
  have hmem : (0 : F) ∈ (Finset.univ : Finset F) := Finset.mem_univ 0
  rw [← Finset.add_sum_erase (Finset.univ : Finset F) (rlNoiseWeight β) hmem]
  rw [show (∑ x ∈ (Finset.univ : Finset F).erase 0, rlNoiseWeight β x) =
      ∑ _x ∈ (Finset.univ : Finset F).erase 0,
        β / ((Fintype.card F : ℝ) - 1) by
    apply Finset.sum_congr rfl
    intro x hx
    unfold rlNoiseWeight
    rw [if_neg (Finset.mem_erase.mp hx).1]]
  unfold rlNoiseWeight
  rw [if_pos rfl, Finset.sum_const]
  simp only [nsmul_eq_mul]
  have herase : (((Finset.univ : Finset F).erase 0).card : ℝ) =
      (Fintype.card F : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
    norm_num
  rw [herase]
  have hden : (Fintype.card F : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card F := by exact_mod_cast hF
    linarith
  field_simp
  ring

open scoped BigOperators in
def sum_rlNoiseWeight_ne
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) :
    (∑ x : F, if x ≠ 0 then rlNoiseWeight β x else 0) = β := by
  classical
  rw [show (∑ x : F, if x ≠ 0 then rlNoiseWeight β x else 0) =
      ∑ x ∈ (Finset.univ : Finset F).erase 0, rlNoiseWeight β x by
    rw [← Finset.filter_ne' (Finset.univ : Finset F) 0]
    simp only [Finset.sum_filter, ne_eq]]
  rw [show (∑ x ∈ (Finset.univ : Finset F).erase 0, rlNoiseWeight β x) =
      ∑ _x ∈ (Finset.univ : Finset F).erase 0,
        β / ((Fintype.card F : ℝ) - 1) by
    apply Finset.sum_congr rfl
    intro x hx
    unfold rlNoiseWeight
    rw [if_neg (Finset.mem_erase.mp hx).1]]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul]
  have hmem : (0 : F) ∈ (Finset.univ : Finset F) := Finset.mem_univ 0
  have herase : (((Finset.univ : Finset F).erase 0).card : ℝ) =
      (Fintype.card F : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
    norm_num
  rw [herase]
  have hden : (Fintype.card F : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card F := by exact_mod_cast hF
    linarith
  field_simp

open scoped BigOperators in
def sum_rlNoiseWeight_ne_sub
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (a : F) :
    (∑ y : F, if y ≠ a then rlNoiseWeight β (y - a) else 0) = β := by
  calc
    (∑ y : F, if y ≠ a then rlNoiseWeight β (y - a) else 0) =
        ∑ x : F, if x ≠ 0 then rlNoiseWeight β x else 0 := by
      apply Fintype.sum_equiv (Equiv.subRight a)
      intro y
      simp only [Equiv.subRight_apply, sub_ne_zero]
    _ = β := sum_rlNoiseWeight_ne β hF

open scoped BigOperators in
def sum_rlNoiseWeight_sub
    (β : ℝ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (a : F) :
    (∑ y : F, rlNoiseWeight β (y - a)) = 1 := by
  calc
    (∑ y : F, rlNoiseWeight β (y - a)) = ∑ x : F, rlNoiseWeight β x := by
      apply Fintype.sum_equiv (Equiv.subRight a)
      intro y
      rw [Equiv.subRight_apply]
    _ = 1 := sum_rlNoiseWeight β hF

open scoped BigOperators in
def rlTranslatedRowWeight_error_marginal
    (β : ℝ) (m : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (j : Fin m) :
    (∑ x : F × (Fin m → F),
      if x.2 j ≠ x.1 then rlTranslatedRowWeight β m x else 0) = β := by
  classical
  have hinner (a : F) :
      (∑ v : Fin m → F,
        if v j ≠ a then ∏ t, rlNoiseWeight β (v t - a) else 0) = β := by
    calc
      (∑ v : Fin m → F,
          if v j ≠ a then ∏ t, rlNoiseWeight β (v t - a) else 0) =
          ∑ v : Fin m → F,
            ∏ t, if t = j then
              (if v t ≠ a then rlNoiseWeight β (v t - a) else 0)
            else rlNoiseWeight β (v t - a) := by
        apply Finset.sum_congr rfl
        intro v _hv
        by_cases hv : v j ≠ a
        · rw [if_pos hv]
          apply Finset.prod_congr rfl
          intro t _ht
          by_cases ht : t = j
          · subst t
            rw [if_pos rfl, if_pos hv]
          · rw [if_neg ht]
        · rw [if_neg hv]
          symm
          apply Finset.prod_eq_zero (Finset.mem_univ j)
          rw [if_pos rfl, if_neg hv]
      _ = ∏ t : Fin m, ∑ y : F, if t = j then
              (if y ≠ a then rlNoiseWeight β (y - a) else 0)
            else rlNoiseWeight β (y - a) := by
        exact (Fintype.prod_sum (fun t : Fin m => fun y : F =>
          if t = j then
            (if y ≠ a then rlNoiseWeight β (y - a) else 0)
          else rlNoiseWeight β (y - a))).symm
      _ = ∏ t : Fin m, if t = j then β else 1 := by
        apply Finset.prod_congr rfl
        intro t _ht
        by_cases ht : t = j
        · simp only [if_pos ht, sum_rlNoiseWeight_ne_sub β hF a]
        · simp only [if_neg ht, sum_rlNoiseWeight_sub β hF a]
      _ = β := by
        simpa only using (Fintype.prod_ite_eq' j (fun _ : Fin m => β))
  have hcenter (a : F) :
      (∑ v : Fin m → F,
        if v j ≠ a then
          (1 / (Fintype.card F : ℝ)) *
            ∏ t, rlNoiseWeight β (v t - a)
        else 0) =
        (1 / (Fintype.card F : ℝ)) * β := by
    calc
      (∑ v : Fin m → F,
          if v j ≠ a then
            (1 / (Fintype.card F : ℝ)) *
              ∏ t, rlNoiseWeight β (v t - a)
          else 0) =
          ∑ v : Fin m → F,
            (1 / (Fintype.card F : ℝ)) *
              (if v j ≠ a then ∏ t, rlNoiseWeight β (v t - a) else 0) := by
        apply Finset.sum_congr rfl
        intro v _hv
        by_cases hv : v j ≠ a
        · rw [if_pos hv, if_pos hv]
        · rw [if_neg hv, if_neg hv, mul_zero]
      _ = (1 / (Fintype.card F : ℝ)) *
          ∑ v : Fin m → F,
            if v j ≠ a then ∏ t, rlNoiseWeight β (v t - a) else 0 := by
        rw [Finset.mul_sum]
      _ = (1 / (Fintype.card F : ℝ)) * β := by rw [hinner]
  rw [Fintype.sum_prod_type]
  change (∑ a : F, ∑ v : Fin m → F,
    if v j ≠ a then
      (1 / (Fintype.card F : ℝ)) * ∏ t, rlNoiseWeight β (v t - a)
    else 0) = β
  simp_rw [hcenter]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card F : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Fintype.card F := by positivity
    exact ne_of_gt this
  field_simp

open scoped BigOperators in
def rlProfileApprox_column_error_le
    (β : ℝ) (m : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F)
    (R : ι → F × (Fin m → F)) (hR : rlProfileApprox β m R)
    (j : Fin m) :
    ((hammingDist (fun i => (R i).2 j) (fun i => (R i).1) : ℕ) : ℝ) /
        (Fintype.card ι : ℝ) ≤
      β + (Fintype.card (F × (Fin m → F)) : ℝ) /
        (Fintype.card ι : ℝ) := by
  classical
  let S : Finset (F × (Fin m → F)) :=
    Finset.univ.filter (fun x => x.2 j ≠ x.1)
  have hprofile := hR
  unfold rlProfileApprox at hprofile
  have hpoint (x : F × (Fin m → F)) :
      ((Finset.univ.filter (fun i => R i = x)).card : ℝ) /
          (Fintype.card ι : ℝ) ≤
        rlTranslatedRowWeight β m x + 1 / (Fintype.card ι : ℝ) := by
    have hx := (abs_le.mp (hprofile x)).2
    linarith
  have hcountNat :
      (∑ x ∈ S, (Finset.univ.filter (fun i => R i = x)).card) =
        hammingDist (fun i => (R i).2 j) (fun i => (R i).1) := by
    calc
      (∑ x ∈ S, (Finset.univ.filter (fun i => R i = x)).card) =
          (Finset.univ.filter (fun i => R i ∈ S)).card :=
        Finset.sum_card_fiberwise_eq_card_filter Finset.univ S R
      _ = hammingDist (fun i => (R i).2 j) (fun i => (R i).1) := by
        unfold hammingDist
        congr 1
        ext i
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcount :
      (∑ x ∈ S,
        ((Finset.univ.filter (fun i => R i = x)).card : ℝ)) =
        (hammingDist (fun i => (R i).2 j) (fun i => (R i).1) : ℝ) := by
    exact_mod_cast hcountNat
  have hsum :
      (∑ x ∈ S,
        ((Finset.univ.filter (fun i => R i = x)).card : ℝ) /
          (Fintype.card ι : ℝ)) ≤
        ∑ x ∈ S,
          (rlTranslatedRowWeight β m x + 1 / (Fintype.card ι : ℝ)) := by
    apply Finset.sum_le_sum
    intro x _hx
    exact hpoint x
  have hideal :
      (∑ x ∈ S, rlTranslatedRowWeight β m x) = β := by
    dsimp [S]
    rw [Finset.sum_filter]
    exact rlTranslatedRowWeight_error_marginal β m hF j
  have hScard : S.card ≤ Fintype.card (F × (Fin m → F)) := by
    dsimp [S]
    simpa only [Finset.card_univ] using
      (Finset.card_filter_le (Finset.univ : Finset (F × (Fin m → F)))
        (fun x => x.2 j ≠ x.1))
  calc
    ((hammingDist (fun i => (R i).2 j) (fun i => (R i).1) : ℕ) : ℝ) /
        (Fintype.card ι : ℝ) =
        (∑ x ∈ S,
          ((Finset.univ.filter (fun i => R i = x)).card : ℝ)) /
            (Fintype.card ι : ℝ) := by rw [hcount]
    _ = ∑ x ∈ S,
          ((Finset.univ.filter (fun i => R i = x)).card : ℝ) /
            (Fintype.card ι : ℝ) := by
      rw [Finset.sum_div]
    _ ≤ ∑ x ∈ S,
          (rlTranslatedRowWeight β m x + 1 / (Fintype.card ι : ℝ)) := hsum
    _ = β + (S.card : ℝ) / (Fintype.card ι : ℝ) := by
      rw [Finset.sum_add_distrib, hideal, Finset.sum_const]
      simp only [nsmul_eq_mul]
      ring
    _ ≤ β + (Fintype.card (F × (Fin m → F)) : ℝ) /
        (Fintype.card ι : ℝ) := by
      apply add_le_add_right
        (div_le_div_of_nonneg_right (by exact_mod_cast hScard) (by positivity))

def rl_profileApprox_disagreement_le
    (β : ℝ) (m : ℕ)
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (R : ι → F × (Fin m → F)) (hR : rlProfileApprox β m R)
    (j : Fin m) :
    (((Finset.univ.filter (fun i => (R i).2 j ≠ (R i).1)).card : ℝ) /
        (Fintype.card ι : ℝ)) ≤
      β + (Fintype.card F : ℝ) ^ (m + 1) / (Fintype.card ι : ℝ) := by
  have hF : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have h := rlProfileApprox_column_error_le β m hF R hR j
  have hcard :
      (Fintype.card (F × (Fin m → F)) : ℝ) =
        (Fintype.card F : ℝ) ^ (m + 1) := by
    rw [Fintype.card_prod, Fintype.card_pi_const]
    simp only [Nat.cast_mul, Nat.cast_pow, pow_succ]
    ring
  unfold hammingDist at h
  rw [hcard] at h
  exact h

def rlProfileRealized_lambda_lower
    (q : ℕ) {ι F : Type}
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = q) (β δ : ℝ) (m : ℕ)
    (C : Submodule F (ι → F))
    (hbudget : β + (q : ℝ) ^ (m + 1 : ℕ) /
      (Fintype.card ι : ℝ) ≤ δ)
    (hreal : rlProfileRealized β m C) :
    (m : ℕ∞) ≤ Lambda ((C : Set (ι → F))) δ := by
  classical
  rcases hreal with ⟨R, happrox, hinj, hmem⟩
  let z : ι → F := fun i => (R i).1
  let cols : Fin m → ι → F := fun j i => (R i).2 j
  have hclose :
      ∀ j : Fin m, cols j ∈ closeCodewordsRel ((C : Set (ι → F))) z δ := by
    intro j
    refine ⟨hmem j, ?_⟩
    have hdis := rl_profileApprox_disagreement_le β m R happrox j
    rw [hF] at hdis
    have hfrac :
        (((Finset.univ.filter
          (fun i : ι => (R i).2 j ≠ (R i).1)).card : ℝ) /
            (Fintype.card ι : ℝ)) ≤ δ := hdis.trans hbudget
    unfold Code.relHammingBall
    simp only [Set.mem_setOf_eq]
    unfold Code.relHammingDist
    simp only [NNRat.cast_div, NNRat.cast_natCast]
    convert hfrac using 1
    congr 2
    unfold hammingDist
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, z, cols]
    exact ne_comm
  have hrange :
      Set.range cols ⊆ closeCodewordsRel ((C : Set (ι → F))) z δ := by
    rintro _ ⟨j, rfl⟩
    exact hclose j
  have henc :
      (m : ℕ∞) ≤ (closeCodewordsRel ((C : Set (ι → F))) z δ).encard := by
    calc
      (m : ℕ∞) = ENat.card (Fin m) := by simp
      _ ≤ (Set.range cols).encard := hinj.encard_range
      _ ≤ (closeCodewordsRel ((C : Set (ι → F))) z δ).encard :=
        Set.encard_mono hrange
  exact henc.trans (encard_closeCodewordsRel_le_Lambda _ _ _)

def rl_realization_lambda
    (q : ℕ) (_hq : 2 ≤ q) (δ β : ℝ)
    (hβ_pos : 0 < β) (hβδ : β < δ) (m : ℕ) :
    ∃ n₀ : ℕ,
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {F : Type} [Field F] [Fintype F] [DecidableEq F],
        Fintype.card F = q → n₀ ≤ Fintype.card ι →
        ∀ C : Submodule F (ι → F),
          rlProfileRealized β m C →
            (m : ℕ∞) ≤ Lambda ((C : Set (ι → F))) δ := by
  classical
  have hgap : 0 < δ - β := sub_pos.mpr hβδ
  obtain ⟨n₀, hn₀large⟩ :=
    exists_nat_gt ((q : ℝ) ^ (m + 1) / (δ - β))
  refine ⟨n₀, ?_⟩
  intro ι _ _ _ F _ _ _ hF hn C hreal
  have hnpos : (0 : ℝ) < Fintype.card ι := by positivity
  have hn₀R : (n₀ : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  have hpowlt :
      (q : ℝ) ^ (m + 1) / (Fintype.card ι : ℝ) < δ - β := by
    rw [div_lt_iff₀ hnpos]
    have hmul :
        (q : ℝ) ^ (m + 1) < (n₀ : ℝ) * (δ - β) := by
      calc
        (q : ℝ) ^ (m + 1) =
            ((q : ℝ) ^ (m + 1) / (δ - β)) * (δ - β) := by
          field_simp
        _ < (n₀ : ℝ) * (δ - β) :=
          mul_lt_mul_of_pos_right hn₀large hgap
    exact lt_of_lt_of_le hmul (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hn₀R hgap.le)
  rcases hreal with ⟨R, happrox, hinj, hmem⟩
  let z : ι → F := fun i => (R i).1
  let cols : Fin m → ι → F := fun j i => (R i).2 j
  have hclose :
      ∀ j : Fin m, cols j ∈ closeCodewordsRel ((C : Set (ι → F))) z δ := by
    intro j
    refine ⟨hmem j, ?_⟩
    have hdis := rl_profileApprox_disagreement_le β m R happrox j
    rw [hF] at hdis
    have hfrac :
        (((Finset.univ.filter
          (fun i : ι => (R i).2 j ≠ (R i).1)).card : ℝ) /
            (Fintype.card ι : ℝ)) ≤ δ := by
      linarith
    unfold Code.relHammingBall
    simp only [Set.mem_setOf_eq]
    unfold Code.relHammingDist
    simp only [NNRat.cast_div, NNRat.cast_natCast]
    convert hfrac using 1
    congr 2
    unfold hammingDist
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, z, cols]
    exact ne_comm
  have hrange :
      Set.range cols ⊆ closeCodewordsRel ((C : Set (ι → F))) z δ := by
    rintro _ ⟨j, rfl⟩
    exact hclose j
  have henc :
      (m : ℕ∞) ≤ (closeCodewordsRel ((C : Set (ι → F))) z δ).encard := by
    calc
      (m : ℕ∞) = ENat.card (Fin m) := by simp
      _ ≤ (Set.range cols).encard := hinj.encard_range
      _ ≤ (closeCodewordsRel ((C : Set (ι → F))) z δ).encard :=
        Set.encard_mono hrange
  exact henc.trans (encard_closeCodewordsRel_le_Lambda _ _ _)

open scoped BigOperators in
def sum_rlProductWeight
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α → ℝ) (r : κ → ℝ) :
    (∑ z : α × κ, rlProductWeight p r z) =
      (∑ x : α, p x) * (∑ y : κ, r y) := by
  unfold rlProductWeight
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : α, ∑ y : κ, p x * r y) =
        ∑ x : α, p x * ∑ y : κ, r y := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
    _ = (∑ x : α, p x) * (∑ y : κ, r y) := by
      rw [Finset.sum_mul]

open scoped BigOperators in
def sum_rlFiniteMarginalProduct
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp_sum : (∑ z, p z) = 1) :
    (∑ z : α × κ,
      rlProductWeight (rlFiniteMarginalLeft p)
        (rlFiniteMarginalRight p) z) = 1 := by
  rw [sum_rlProductWeight, sum_rlFiniteMarginalLeft,
    sum_rlFiniteMarginalRight, hp_sum, one_mul]

open scoped BigOperators in
def rlFiniteKL_joint_product_eq_log_ratio
    (q : ℕ) {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hp_sum : (∑ z, p z) = 1) :
    rlFiniteKL q p
        (rlProductWeight (rlFiniteMarginalLeft p) (rlFiniteMarginalRight p)) =
      ∑ z : α × κ,
        p z * Real.logb q
          (p z / rlProductWeight (rlFiniteMarginalLeft p)
            (rlFiniteMarginalRight p) z) := by
  apply rlFiniteKL_eq_log_ratio
  · exact hp_sum
  · exact sum_rlFiniteMarginalProduct p hp_sum
  · intro z hz
    rcases z with ⟨x, y⟩
    exact rlFiniteProduct_support p hp x y hz

open scoped BigOperators in
def rlFiniteMutualInfo_eq_kl
    (q : ℕ) (hq : 2 ≤ q)
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hp_sum : (∑ z, p z) = 1) :
    rlFiniteMutualInfo q p =
      rlFiniteKL q p
        (rlProductWeight (rlFiniteMarginalLeft p)
          (rlFiniteMarginalRight p)) := by
  rw [rlFiniteKL_joint_product_eq_log_ratio q p hp hp_sum]
  simp_rw [rlFinite_log_ratio_product_pointwise q p hp]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    rlFiniteMarginalLeft_log_sum q p,
    rlFiniteMarginalRight_log_sum q p]
  unfold rlFiniteMutualInfo rlFiniteEntropy
  ring

open scoped BigOperators in
def rlFiniteMutualInfo_nonneg
    (q : ℕ) (hq : 2 ≤ q)
    {α κ : Type} [Fintype α] [Fintype κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hp_sum : (∑ z, p z) = 1) :
    0 ≤ rlFiniteMutualInfo q p := by
  rw [rlFiniteMutualInfo_eq_kl q hq p hp hp_sum]
  apply rlFiniteKL_nonneg q hq
  · exact hp
  · intro z
    exact mul_nonneg
      (rlFiniteMarginalLeft_nonneg p hp z.1)
      (rlFiniteMarginalRight_nonneg p hp z.2)

open scoped BigOperators in
def sum_rlPushforwardWeight
    {α κ : Type} [Fintype α] [Fintype κ] [DecidableEq κ]
    (p : α → ℝ) (f : α → κ) :
    (∑ y : κ, rlPushforwardWeight p f y) = ∑ x : α, p x := by
  classical
  unfold rlPushforwardWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  exact Fintype.sum_ite_eq (f x) (fun _ : κ => p x)

open scoped BigOperators in
def sum_rlFiniteMapLeftWeight
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq β] [DecidableEq κ]
    (p : α × κ → ℝ) (f : α → β) :
    (∑ z : β × κ, rlFiniteMapLeftWeight p f z) =
      ∑ z : α × κ, p z := by
  calc
    (∑ z : β × κ, rlFiniteMapLeftWeight p f z) =
        ∑ z : β × κ,
          rlPushforwardWeight p (fun t : α × κ => (f t.1, t.2)) z := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact (rlFiniteMapLeftWeight_eq_pushforward_pair p f z).symm
    _ = ∑ z : α × κ, p z :=
      sum_rlPushforwardWeight p (fun t : α × κ => (f t.1, t.2))

open scoped BigOperators in
def rlFiniteMutualInfo_map_left_le
    (q : ℕ) (hq : 2 ≤ q)
    {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    [DecidableEq β] [DecidableEq κ]
    (p : α × κ → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hp_sum : (∑ z, p z) = 1) (f : α → β) :
    rlFiniteMutualInfo q (rlFiniteMapLeftWeight p f) ≤
      rlFiniteMutualInfo q p := by
  classical
  let pm : β × κ → ℝ := rlFiniteMapLeftWeight p f
  let r : α × κ → ℝ :=
    rlProductWeight (rlFiniteMarginalLeft p) (rlFiniteMarginalRight p)
  let g : α × κ → β × κ := fun z => (f z.1, z.2)
  have hpm : ∀ z, 0 ≤ pm z := by
    exact rlFiniteMapLeftWeight_nonneg p hp f
  have hpmsum : (∑ z, pm z) = 1 := by
    dsimp [pm]
    rw [sum_rlFiniteMapLeftWeight p f, hp_sum]
  rw [rlFiniteMutualInfo_eq_kl q hq pm hpm hpmsum,
    rlFiniteMutualInfo_eq_kl q hq p hp hp_sum]
  calc
    rlFiniteKL q pm
        (rlProductWeight (rlFiniteMarginalLeft pm)
          (rlFiniteMarginalRight pm)) =
        rlFiniteKL q (rlPushforwardWeight p g)
          (rlPushforwardWeight r g) := by
      congr 1
      · funext z
        exact (rlFiniteMapLeftWeight_eq_pushforward_pair p f z).symm
      · funext z
        calc
          rlProductWeight (rlFiniteMarginalLeft pm)
              (rlFiniteMarginalRight pm) z =
              rlFiniteMapLeftWeight r f z := by
            dsimp [pm, r]
            exact (rlFiniteMapLeftWeight_product p f z).symm
          _ = rlPushforwardWeight r g z := by
            exact (rlFiniteMapLeftWeight_eq_pushforward_pair r f z).symm
    _ ≤ rlFiniteKL q p r := by
      apply rlFiniteKL_pushforward_le q hq p r hp
      · intro z
        exact mul_nonneg
          (rlFiniteMarginalLeft_nonneg p hp z.1)
          (rlFiniteMarginalRight_nonneg p hp z.2)
      · intro z hz
        rcases z with ⟨x, y⟩
        exact rlFiniteProduct_support p hp x y hz
    _ = rlFiniteKL q p
        (rlProductWeight (rlFiniteMarginalLeft p)
          (rlFiniteMarginalRight p)) := by rfl

open scoped BigOperators in
def sum_rlShiftWeight
    (β θ : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) :
    (∑ v : Fin d → F, rlShiftWeight (F := F) β θ d v) = 1 := by
  classical
  unfold rlShiftWeight
  rw [Finset.sum_comm]
  have hinner (a : F) :
      (∑ v : Fin d → F,
        rlNoiseWeight θ a * ∏ j, rlNoiseWeight β (v j - a)) =
        rlNoiseWeight θ a := by
    calc
      (∑ v : Fin d → F,
          rlNoiseWeight θ a * ∏ j, rlNoiseWeight β (v j - a)) =
          rlNoiseWeight θ a *
            ∑ v : Fin d → F, ∏ j, rlNoiseWeight β (v j - a) := by
              rw [Finset.mul_sum]
      _ = rlNoiseWeight θ a *
          ∏ j : Fin d, ∑ y : F, rlNoiseWeight β (y - a) := by
            rw [Fintype.prod_sum]
      _ = rlNoiseWeight θ a := by
        simp only [sum_rlNoiseWeight_sub β hF a, Finset.prod_const_one, mul_one]
  simp_rw [hinner]
  exact sum_rlNoiseWeight θ hF

open scoped BigOperators in
def sum_rlTranslatedRowWeight
    (β : ℝ) (m : ℕ) {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) :
    (∑ x : F × (Fin m → F), rlTranslatedRowWeight β m x) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : F,
      (∑ v : Fin m → F,
        (1 / (Fintype.card F : ℝ)) *
          ∏ j, rlNoiseWeight β (v j - a)) =
        1 / (Fintype.card F : ℝ) := by
    intro a
    calc
      (∑ v : Fin m → F,
          (1 / (Fintype.card F : ℝ)) *
            ∏ j, rlNoiseWeight β (v j - a)) =
          (1 / (Fintype.card F : ℝ)) *
            ∑ v : Fin m → F, ∏ j, rlNoiseWeight β (v j - a) := by
              rw [Finset.mul_sum]
      _ = (1 / (Fintype.card F : ℝ)) *
          ∏ j : Fin m, ∑ y : F, rlNoiseWeight β (y - a) := by
            rw [Fintype.prod_sum]
      _ = 1 / (Fintype.card F : ℝ) := by
        simp only [sum_rlNoiseWeight_sub β hF a, Finset.prod_const_one, mul_one]
  simp_rw [rlTranslatedRowWeight, hinner]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card F : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Fintype.card F := by positivity
    exact ne_of_gt this
  field_simp

def rlTranslatedPushforwardWeight_mem_Icc
    (β : ℝ) (m : ℕ) {F κ : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype κ] [DecidableEq κ]
    (hF : 2 ≤ Fintype.card F) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (f : F × (Fin m → F) → κ) :
    ∀ y, rlPushforwardWeight (rlTranslatedRowWeight β m) f y ∈
      Set.Icc (0 : ℝ) 1 := by
  intro y
  refine ⟨?_, ?_⟩
  · exact rlPushforwardWeight_nonneg (rlTranslatedRowWeight β m)
      (rlTranslatedRowWeight_nonneg β m hF hβ0 hβ1) f y
  · exact rlPushforwardWeight_le_one (rlTranslatedRowWeight β m)
      (rlTranslatedRowWeight_nonneg β m hF hβ0 hβ1)
      (sum_rlTranslatedRowWeight β m hF) f y

open scoped BigOperators in
def rlExactTypeProjectedEntropy_eventually_close
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (m : ℕ)
    (e : ℝ) (he : 0 < e) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F],
        Fintype.card F = q →
        ∀ t : rlExactType n (F × (Fin m → F)),
          rlExactTypeApproximates β m n t →
          ∀ (r : ℕ), r ≤ m →
            ∀ A : (Fin m → F) →ₗ[F] (Fin r → F),
              |rlExactTypeProjectedEntropy q n t (fun x => A x.2) -
                  rlProjectedEntropy q β m r A| < e := by
  obtain ⟨τ, hτ, hcont⟩ :=
    rlFiniteEntropy_close_of_pointwise_close q (q ^ m) he
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((q : ℝ) ^ (m + 1) / τ)
  refine ⟨n₀, ?_⟩
  intro n hn F _ _ _ hF t ht r hrm A
  have hn₀pos : 0 < n₀ := by
    have hnonneg : 0 ≤ (q : ℝ) ^ (m + 1) / τ := by positivity
    exact_mod_cast (lt_of_le_of_lt hnonneg hn₀)
  have hnpos : 0 < n := lt_of_lt_of_le hn₀pos hn
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have herr : (q : ℝ) ^ (m + 1) / (n : ℝ) < τ := by
    rw [div_lt_iff₀ hnRpos]
    have hbase : (q : ℝ) ^ (m + 1) < (n₀ : ℝ) * τ := by
      calc
        (q : ℝ) ^ (m + 1) =
            ((q : ℝ) ^ (m + 1) / τ) * τ := by
          field_simp [hτ.ne']
        _ < (n₀ : ℝ) * τ := mul_lt_mul_of_pos_right hn₀ hτ
    calc
      (q : ℝ) ^ (m + 1) < (n₀ : ℝ) * τ := hbase
      _ ≤ (n : ℝ) * τ := mul_le_mul_of_nonneg_right hnR hτ.le
      _ = τ * (n : ℝ) := mul_comm _ _
  have hcard : Fintype.card (Fin r → F) ≤ q ^ m := by
    rw [Fintype.card_pi_const, hF]
    exact pow_le_pow_right' (by omega : 1 ≤ q) hrm
  rw [rlExactTypeProjectedEntropy_eq_pushforward,
    rlProjectedEntropy_eq_pushforward]
  unfold rlPushforwardEntropy
  apply hcont
  · exact hcard
  · exact rlExactTypePushforwardWeight_mem_Icc n t hnpos
      (fun x : F × (Fin m → F) => A x.2)
  · have hF2 : 2 ≤ Fintype.card F := by simpa only [hF] using hq
    exact rlTranslatedPushforwardWeight_mem_Icc β m hF2 hβ0.le hβ1.le
      (fun x : F × (Fin m → F) => A x.2)
  · intro y
    exact lt_of_le_of_lt
      (rlExactTypeProjectedWeight_error_le q β m n r hF t ht A y) herr

open scoped BigOperators in
def rlExactTypeNotImplicitlyRare_eventually
    (q : ℕ) (hq : 2 ≤ q) (ρ β η : ℝ) (m : ℕ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hη0 : 0 < η) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F],
        Fintype.card F = q →
        ∀ t : rlExactType n (F × (Fin m → F)),
          rlExactTypeApproximates β m n t →
          rlProfileNotImplicitlyRare (F := F) q (1 - ρ + η) β m →
          rlExactTypeNotImplicitlyRare q n (1 - ρ + η / 2) m t := by
  obtain ⟨n₀, hn₀⟩ :=
    rlExactTypeProjectedEntropy_eventually_close q hq β hβ0 hβ1 m
      (η / 2) (by positivity)
  refine ⟨n₀, ?_⟩
  intro n hn F _ _ _ hF t ht hrare
  unfold rlProfileNotImplicitlyRare at hrare
  unfold rlExactTypeNotImplicitlyRare
  intro r A hA
  by_cases hr0 : r = 0
  · subst r
    norm_num
    unfold rlExactTypeProjectedEntropy
    apply rlFiniteEntropy_nonneg q hq
    exact rlExactTypePushforwardWeight_mem_Icc_all n t
      (fun x : F × (Fin m → F) => A x.2)
  · have hrm : r ≤ m := rl_surjective_fin_le m r A hA
    have hclose := hn₀ n hn hF t ht r hrm A
    have hlower := (abs_lt.mp hclose).1
    have hideal := hrare r A hA
    have hr1 : (1 : ℝ) ≤ r := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr0)
    have hhalf : η / 2 ≤ (η / 2) * (r : ℝ) := by
      nlinarith
    linarith

open scoped BigOperators in
def sum_rlTranslatedRowWeight_center
    (β : ℝ) (m : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (v : Fin m → F) :
    (∑ a : F, rlTranslatedRowWeight β m (a, v)) =
      rlUniformShiftWeight (F := F) β m v := by
  rfl

open scoped BigOperators in
def rlExactTypeColumnMarginal_error_le
    (β : ℝ) (m n : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (t : rlExactType n (F × (Fin m → F)))
    (ht : rlExactTypeApproximates β m n t)
    (v : Fin m → F) :
    |rlExactTypeWeight n (rlExactTypeColumnMarginal n m t) v -
        rlUniformShiftWeight (F := F) β m v| ≤
      (Fintype.card F : ℝ) / (n : ℝ) := by
  rw [rlExactTypeWeight_columnMarginal,
    ← sum_rlTranslatedRowWeight_center]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a : F,
        (rlExactTypeWeight n t (a, v) -
          rlTranslatedRowWeight β m (a, v))| ≤
        ∑ a : F,
          |rlExactTypeWeight n t (a, v) -
            rlTranslatedRowWeight β m (a, v)| := by
      exact Finset.abs_sum_le_sum_abs _ Finset.univ
    _ ≤ ∑ _a : F, 1 / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact ht (a, v)
    _ = (Fintype.card F : ℝ) / (n : ℝ) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul, Finset.card_univ]
      ring

open scoped BigOperators in
def rlProjectedEntropy_rank_eq_uniform
    (q : ℕ) (β : ℝ) (m : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (A : (Fin m → F) →ₗ[F] (Fin m → F))
    (hA : Function.Surjective A) :
    rlProjectedEntropy q β m m A =
      rlUniformShiftEntropy (F := F) q β m := by
  classical
  let e : (Fin m → F) ≃ₗ[F] (Fin m → F) :=
    rl_surjective_fin_self_equiv m A hA
  have hpush (y : Fin m → F) :
      (∑ x : F × (Fin m → F),
        if A x.2 = y then rlTranslatedRowWeight β m x else 0) =
        rlUniformShiftWeight (F := F) β m (e.symm y) := by
    rw [Fintype.sum_prod_type]
    have hinner (a : F) :
        (∑ v : Fin m → F,
          if A v = y then rlTranslatedRowWeight β m (a, v) else 0) =
          rlTranslatedRowWeight β m (a, e.symm y) := by
      calc
        (∑ v : Fin m → F,
            if A v = y then rlTranslatedRowWeight β m (a, v) else 0) =
            ∑ z : Fin m → F,
              if z = y then
                rlTranslatedRowWeight β m (a, e.symm z) else 0 := by
          apply Fintype.sum_equiv e.toEquiv
          intro v
          change (if e v = y then rlTranslatedRowWeight β m (a, v) else 0) =
            (if e v = y then
              rlTranslatedRowWeight β m (a, e.symm (e v)) else 0)
          rw [e.symm_apply_apply]
        _ = rlTranslatedRowWeight β m (a, e.symm y) := by
          exact Fintype.sum_ite_eq' y
            (fun z : Fin m → F => rlTranslatedRowWeight β m (a, e.symm z))
    simp_rw [hinner]
    exact sum_rlTranslatedRowWeight_center β m (e.symm y)
  unfold rlProjectedEntropy rlUniformShiftEntropy
  change rlFiniteEntropy q
      (fun y : Fin m → F =>
        ∑ x : F × (Fin m → F),
          if A x.2 = y then rlTranslatedRowWeight β m x else 0) =
    rlFiniteEntropy q (rlUniformShiftWeight (F := F) β m)
  calc
    rlFiniteEntropy q
        (fun y : Fin m → F =>
          ∑ x : F × (Fin m → F),
            if A x.2 = y then rlTranslatedRowWeight β m x else 0) =
        rlFiniteEntropy q
          (fun y : Fin m → F =>
            rlUniformShiftWeight (F := F) β m (e.symm y)) := by
      apply rlFiniteEntropy_congr
      exact hpush
    _ = rlFiniteEntropy q (rlUniformShiftWeight (F := F) β m) :=
      (rlFiniteEntropy_equiv q
        (rlUniformShiftWeight (F := F) β m) e.toEquiv).symm

open scoped BigOperators in
def sum_rlUniformShiftWeight
    (β : ℝ) (d : ℕ) {F : Type}
    [Field F] [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) :
    (∑ v : Fin d → F, rlUniformShiftWeight (F := F) β d v) = 1 := by
  calc
    (∑ v : Fin d → F, rlUniformShiftWeight (F := F) β d v) =
        ∑ v : Fin d → F,
          rlShiftWeight (F := F) β (1 - 1 / (Fintype.card F : ℝ)) d v := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact (rlShiftWeight_uniform_eq β d hF v).symm
    _ = 1 := sum_rlShiftWeight β (1 - 1 / (Fintype.card F : ℝ)) d hF


/-- **A random linear code of near-capacity rate has a large list** ([ABF26] Theorem 3.11, after
[GLMRSW22, Theorem 4.1]).

The source, verbatim in its own variables: "Fix a prime power `q`, fix `p ∈ (0, 1 − 1/q)`, and fix
`δ ∈ (0, 1)`. There exists `ε_{p,q,δ} > 0` such that for all `ε ∈ (0, ε_{p,q,δ})` and `n`
sufficiently large, a random linear code in `F_q^n` of rate `1 − h_q(p) − ε` is not
`(p, ⌊h_q(p)/ε − δ⌋)`-list-decodable with probability `1 − q^{−Ω(n)}`." Its random model, from §1.1,
is "a random linear code is a uniformly random subspace of `F_q^n` of certain dimension" — so the
counting form below is the source's probability exactly, not an approximation of it. (Its §1.2
working model is the kernel of a uniformly random parity-check matrix, which conditioned on full
rank is the same uniform distribution over dimension-`k` subspaces, by `GL_n`-invariance.)

**One stronger than [GLMRSW22], faithful to [ABF26].** [GLMRSW22] define `(p, L)`-list-decodable
with a **strict** inequality — "`|{c ∈ C : δ(c,z) ≤ p}| < L`" (§1) — so their "not
`(p, ⌊h_q(p)/ε − δ⌋)`-list-decodable" is `Λ ≥ ⌊·⌋`, whereas the bad event `Λ ≤ ⌊·⌋` below makes the
good event `Λ ≥ ⌊·⌋ + 1`. [ABF26] prints the strict `>`, so the Lean tracks ground truth and is one
stronger than the original; recorded, not repaired.

Variable map into the form below: the source's radius `p` is our `δ`, its slack `δ` is our `ε`,
its `ε_{p,q,δ}` is our `γ`, and its rate `1 − h_q(p) − ε` is our `ρ` — so its `ε` is
`1 − H_q(δ) − ρ`, giving the list bound `⌊H_q(δ)/(1 − H_q(δ) − ρ) − ε⌋`.

**Probability as counting.** ArkLib has no probability distribution over linear codes, so the
`1 − q^{−Ω(n)}` statement is carried in its equivalent finite counting form over the uniform
family `{C : Submodule F (ι → F) | finrank C = k}`:

  `#{C : finrank C = k ∧ |Λ(C, δ)| ≤ ⌊…⌋} ≤ q^{−c·n} · #{C : finrank C = k}`

with `c > 0` the `Ω(n)` constant, whose dependence on `q, δ, ε, ρ` is licensed by its binder
position. This is deliberately stronger than bare existence of one witness code, which loses the
high-probability content; that weaker form is *derived* below as
`random_linear_lambda_lower_exists`.

**Dimension pin.** The source's code has rate exactly `ρ`, with dimension `ρ·n` treated as an
integer for exposition. Exact real equality is unsatisfiable at irrational `ρ`, so the dimension is
pinned two-sidedly into `ρ ≤ k/n ≤ ρ + 1/n`, admitting `k = ⌈ρ·n⌉` up to the boundary case. -/
theorem random_linear_lambda_lower (q : ℕ) (_hq_pp : IsPrimePow q)
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
  -- Use the existing compiled deterministic nodes rather than rebuilding the point-list argument. The remaining proof has three phases. First prove the parameter conclusion: choose γ and, for each admissible ρ, choose β<δ and η>0 such that the translated m-column profile is not implicitly rare, where m=floor(qEntropy q δ/(1-qEntropy q δ-ρ)-ε)+1. This phase must keep separate projected-entropy estimates for r<m and r=m; the full-rank branch recovers almost one full q-ary symbol of entropy from the uniform common shift. Second prove the specialized abundance conclusion: a non-implicitly-rare translated profile is unrealized by only an exponentially small fraction of dimension-k submodules. Use a full-support exact column type, method-of-types bounds, annihilating parity-check counts, cancellation of full-rank pair covariances, and an entropy deficit for deficient pairs. Third assemble: apply rl_profile_budget_eventually and rlProfileRealized_lambda_lower, combine length thresholds with max, show every code with Lambda≤floor(...) is profile-unrealized because m=floor(...)+1, then apply Set.ncard_le_ncard and the abundance estimate. The proposition definitions rlProfileParametersConclusion and rlProfileUnrealizedCountConclusion give the intended interfaces for the first two phases.
  sorry -- external admit: [GLMRSW22, Theorem 4.1].

/-- **Existence form of the random-linear-code lower bound**, derived in-tree from the
high-probability counting form `random_linear_lambda_lower`: some linear code `C ⊆ F^n` with
dimension in the band `ρ ≤ finrank/n ≤ ρ + 1/n` satisfies

  `|Λ(C, δ)| > ⌊H_q(δ) / (1 - H_q(δ) - ρ) - ε⌋` .

The bad-event count is below the whole family's, the family `{C | finrank C = ⌈ρ·n⌉}` is nonempty
(a coordinate-kernel subspace realises any dimension `≤ n`), so a good code exists.

The hypothesis `hρ0 : 0 ≤ ρ` is trivially true in the source's regime, where rates approach
capacity `1 − H_q(δ)` from below with small `γ`. It is needed here only because
`Basic/Entropy.lean` does not yet prove `H_q(δ) < 1` for `δ < 1 − 1/q`, which would let `γ` be
shrunk below `1 − H_q(δ)`. -/
theorem random_linear_lambda_lower_exists
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
    random_linear_lambda_lower q hq_pp δ hδ_pos hδ_lt ε hε_pos hε_lt
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
  -- The source's dimension: `k = ⌈ρ·n⌉`, which sits in the band.
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

/-- **Reed-Solomon codes over extension fields have superpolynomial lists** ([ABF26] Theorem 3.12,
after [BKR06, Corollary 2.2]). Fix `0 < α < β < 1`. For infinitely many prime powers `q` there is a
Reed-Solomon code `C := RS[F_q, F_q, ⌊q^α⌋]` and a word `w : F_q → F_q` with

  `|Λ(C, 1 - q^{β-1}, w)| ≥ q^{(α - β²) · log₂ q}` .

**Log base.** The source's logs are base 2: its display continues
`q^{(α-β²)·log q} = 2^{(α-β²)·(log q)²}`, an identity precisely when `log = log₂`, since
`q^x = 2^{x·log₂ q}`. Hence `Real.logb 2 q`; a natural log here would weaken the exponent by a
factor `1/ln 2`.

**Two divergences from [BKR06], both introduced by [ABF26] and followed here** (the paper is the
designated ground truth, so the Lean tracks it rather than the original): [BKR06] defines
`RS[N, K]` by degree **≤ K** and its witnessing family has degree exactly `K = N^δ`, whereas
[ABF26]'s `RS[F, L, k]` is degree **< k** (its own footnote defines it so) and instantiates
`k = ⌊q^α⌋`. Under [ABF26]'s convention — which `ReedSolomon.code domain k` matches exactly — the
witnesses of the cited construction sit one degree above the code. And [BKR06, Corollary 2.2]
requires `α, β` **rational**; [ABF26] states it for real `α, β`. The statement here is faithful to
[ABF26], but the two divergences are of different weights.

The degree convention is **harmless**: [BKR06]'s family consists of monic subspace polynomials
`∏_{a ∈ L}(X − a)` of degree exactly `K`, so subtracting any fixed member gives `|P|` distinct
polynomials of degree `< K` — inside the degree-`< k` code — all agreeing with the shifted word
`w − P₀` on the same `≥ q^v` points. So the cited construction does transfer.

The rationality gap is **not** harmless and may make the real-`α, β` statement false. [BKR06]
Theorem 2.1 gives `|P| ≥ q^{(u+1)m − v²}` for *integers* `0 ≤ u ≤ v ≤ m`, which at exact
`u = αm, v = βm` beats the target `2^{m²(α−β²)}` by a slack of exactly `+m`; rounding to
`u = ⌊αm⌋, v = ⌈βm⌉` costs `−2βm − 1`, the same order, so the naive approximation *falls short
polynomially* rather than merely failing to be tight. It looks recoverable — "for infinitely many
`q`" lets one choose the subsequence of `m`, and by Weyl equidistribution there are infinitely many
`m` with `{αm}` and `{βm}` both near `0` — but that is a Diophantine argument the source does not
contain. Consider taking `α β : ℚ` instead. -/
theorem rs_lambda_superpoly_extension
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < β) (_hβ_lt : β < 1) :
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
  sorry -- external admit: [BKR06, Corollary 2.2].

/-- **Reed-Solomon codes over prime fields have large lists** ([ABF26] Theorem 3.13, after
[GHSZ02, Corollary 20]). Fix `0 < α, β < 1`. For all sufficiently large primes `p` there is a code
`C := RS[F_p, F_p, ⌊p^α⌋]` and a word `w : F_p → F_p` with

  `|Λ(C, 1 - ((1-β)/α) · p^{α-1}, w)| > Ω(p^{p^α · β/2})` .

**Source statement and variable map.** [GHSZ02, Corollary 20] is stated for their asymptotic
quantity `L_q^{poly}` in the variables `ε, γ > 0`; the map is `ε ↦ α`, `γ ↦ β`. Its proof is what
[ABF26] renders: "Use an MDS `[n,k]_q` code with `n = q` and `k = n^ε`, such as a Reed-Solomon
code … Letting `a = (1−γ)n^ε/ε` … the expected number of codewords in a ball of radius `n − a` is
`Ω(n^{(γ/2)·n^ε})`." So the per-`n`, single-code form [ABF26] prints — and which is formalized here
— lives in the source's *proof*, not in its statement, which bounds the asymptotic quantity instead.
The local copy of [GHSZ02] is a scanned two-column paper whose text layer drops relation symbols, so
Corollary 20's own display could not be transcribed verbatim; the proof text above could.

**`_hαβ_le_one` is a source hypothesis [ABF26] drops.** The averaging bound the proof rests on
([GHSZ02] Lemma 19: for an MDS `[n,k]_q` code and `a ≥ k`,
`(1/e)·C(n,a)·q^{k−a} ≤ E_x[|B(x, n−a) ∩ C|] ≤ C(n,a)·q^{k−a}`) requires `a ≥ k`, i.e.
`(1−β)/α ≥ 1`, i.e. `α + β ≤ 1`. It is carried here rather than dropped. (Dropping it looks
harmless — `α + β > 1` gives `a < k`, hence a *larger* ball and a longer list — but the cited
inequality is then outside its stated range, so the admit would no longer follow from the source.)

**Quantifier encoding.** `Ω(·)` is the explicit constant `c > 0` bound *outside* the `∀ p`, and "all
sufficiently large primes" is the explicit threshold `p₀`; `Nat.Prime p` is a conjunct of the
implication's premises, not an antecedent that a non-prime could satisfy vacuously. The list is the
*point* list at the exhibited `w`, as in the source, rather than `Lambda`. -/
theorem rs_lambda_large_prime
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < 1) (_hβ_pos : 0 < β) (_hβ_lt : β < 1)
    (_hαβ_le_one : α + β ≤ 1) :
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
  sorry -- external admit: [GHSZ02, Corollary 20].

/-- **High-rate Reed-Solomon codes cannot be list-decoded past `1/(j+1)`** ([ABF26] Theorem 3.14,
after [JH01, Theorem 2]). Fix an integer `j ≥ 2`. For infinitely many prime powers `q` with
`q ≡ 1 (mod j+1)` there is a code `C := RS[F_q, L, k]` with `|L| = j + 1` and rate `≈ (j-1)/(j+1)`
together with a word `w : L → F_q` such that

  `|Λ(C, 1/(j+1), w)| > j` .

**Encoding of the source's parameters.** Its `|L| = j + 1` is the block length, encoded as
`Fintype.card ι = j + 1`. The dimension is pinned to `k := j` in ArkLib's `ReedSolomon.code domain
k` convention (polynomials of degree `< k`, so dimension `k`). The pin matters in *both*
directions:

* `k = j - 1` (dimension `j - 1`) is **unsatisfiable**: the minimum distance is `n - k + 1 = 3`
  while radius `1/(j+1)` permits a single error, so two list members would be within distance
  `2 < 3` and the list size is at most `1`, never `> j`;
* an unconstrained `∃ k` would let degenerate dimensions (e.g. `k = j + 1`, `C = F^L`) satisfy the
  conclusion trivially.

**The printed rate does not match, and this is a paper defect, not a convention difference.** With
block length `j + 1`, dimension `j` gives rate `j/(j+1)`, whereas [ABF26] prints
`ρ ≈ (j−1)/(j+1)`. No degree convention reconciles the two: degree-`≤ (j−1)` *is* dimension `j`, so
it also yields `j/(j+1)`, and the only dimension yielding `(j−1)/(j+1)` is `j − 1`, which the
argument above shows is unsatisfiable. At `j = 2` the discrepancy is `2/3` versus `1/3`, well
outside "≈". Note [JH01] itself is **not** in the local reference cache, so this could not be
checked against the original.

**The conclusion at this dimension is elementary, and the source's conjuncts are inert.** With
`k = j` the minimum distance is `2`, and radius `1/(j+1)` admits one error. For any `w ∉ C` the
`j + 1` drop-one-coordinate interpolants are codewords within distance `1` of `w`, and they are
pairwise distinct (two coinciding would agree with `w` everywhere, forcing `w ∈ C`), so the list has
`j + 1 > j` elements. This uses **neither** `IsPrimePow (qs i)` **nor** `qs i % (j + 1) = 1`: it
holds for every `q ≥ j + 2`, and `q ≡ 1 (mod j+1)` with `q ≥ 2` already forces `q ≥ j + 2`. So this
admit is elementary rather than external, and correspondingly it does not capture whatever [JH01]
Theorem 2 proves at rate `(j−1)/(j+1)` — the modular condition is exactly the existence condition
for `μ_{j+1} ⊆ F_q^×`, suggesting [JH01] pins `L = μ_{j+1}` and concludes something sharper. Both
ingredients for an in-tree proof are available: `Nat.exists_prime_gt_modEq_one` for the sequence,
and `Lagrange.interpolate` with `Lagrange.degree_interpolate_lt` for the interpolants. -/
theorem rs_lambda_high_rate
    (j : ℕ) (_hj_ge : 2 ≤ j) :
    ∃ qs : ℕ → ℕ, StrictMono qs ∧
      (∀ i, IsPrimePow (qs i)) ∧ (∀ i, qs i % (j + 1) = 1) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = j + 1 →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let C := ReedSolomon.code domain j
            (j : ℕ∞) < (closeCodewordsRel ((C : Set (ι → F))) w (1 / (j + 1 : ℝ))).ncard := by
  sorry -- external admit: [JH01, Theorem 2].

end ReedSolomonBounds

section SubspaceDesignUpperBounds

/-- **Subspace-design codes are list-decodable up to capacity** — [CZ25, Theorem B.5], the
one-integer-parameter form at [CZ25]'s `(k−1)`-level design premise. This is the engine behind
[ABF26] Theorem 3.4 and Corollary 3.5, but it is **not** [ABF26] Theorem 3.4 as printed; see the
last paragraph.

[CZ25, Theorem B.5] verbatim, in its own variables: "Given a `F`-linear code `C ⊆ (F^s)^n` of block
length `n` and rate `R = k/sn`. Assume that `C ⊆ (F^s)^n` is a `(ℓ, ℓ(k−1)/(s−ℓ+1))`-strong
subspace designable code for all `ℓ ≤ s`. Then, `C` is `(L/(L+1) · (1 − sR/(s−L+1)), L)`
(average-radius) list-decodable for any `L ≤ s`." The `IsSubspaceDesign` condition is
`(∑ᵢ dim Aᵢ)/n ≤ dim A · τ(r)`, i.e. a budget of `n · dim A · τ(r)`, so [CZ25]'s
`(ℓ, ℓ(k−1)/(s−ℓ+1))` premise is exactly the profile `τ(ℓ) = (sR − 1/n)/(s−ℓ+1)` — the `(k−1)`
level, since `sR − 1/n = (k−1)/n`. For every integer `1 ≤ L ≤ s`,

  `|Λ(C, L/(L+1) · (1 − sR/(s−L+1)))| ≤ L` .

**Two weakenings of this premise are each FALSE, and both were caught by compiled
counterexamples.** The statement is brittle in exactly one direction, so both are recorded.

*Arbitrary `τ`.* An early version quantified over an arbitrary `τ : ℕ → ℝ` while asserting [CZ25]'s
sharp `L/(L+1)` radius. Over `𝔽₂` with `ι = Fin 2`, `s = 1` and `C = span {(1,1)}`, the profile
`τ ≡ 0` *is* a legitimate subspace design — no nonzero codeword vanishes anywhere, so
`A ⊓ ker (proj i) = ⊥` and every design sum is `0` — yet at `L = s = 1` the radius `1/2 · (1 − 0)`
has absolute radius `⌊1/2 · 2⌋ = 1`, and the ball around `(0,1)` holds both codewords, giving
`Λ ≥ 2 > 1`. `τ ≡ 0` is monotone and non-negative, so **neither monotonicity nor non-negativity
rescues the arbitrary-`τ` form**; what fails is decoupling `τ` from the rate.

*The `k` level.* Pinning `τ` to the rate is still not enough. The profile `sR/(s−r+1)` — [ABF26]
Theorem 2.18's printed profile, one notch weaker than [CZ25]'s — also makes this statement
**false**. Over `𝔽₂` with `ι = Fin 3`, `s = 1` and `C = span {(1,1,0)}` (so `k = 1`, `n = 3`,
`R = 1/3`) the `k`-level condition holds *with equality*: the single vanishing coordinate gives
`(∑ᵢ dim Cᵢ)/n = 1/3 = 1 · τ(1)`. But at `L = 1` the radius `1/2 · (1 − 1/3) = 1/3` has absolute
radius `1`, and `(1,0,0)` is at distance `1` from both `(0,0,0)` and `(1,1,0)`, so `Λ ≥ 2 > 1`. An
exhaustive sweep over `𝔽₂` finds 385 such code/`L` pairs at `(s,n) ∈ {(1,3),(1,4),(2,3)}` — so this
is not an `s = 1` artefact — and every one of them fails the `(k−1)` premise, placing the falsity
exactly and only in that notch. Structurally, at `s = 1` the `k` level says only `d ≥ n − k`, while
unique decoding at `(1−ρ)/2` needs `d ≥ n − k + 1` whenever `n − k` is even.

**Why the level is load-bearing rather than a fidelity nicety.** [CZ25]'s Lemma B.4 derives
`∑ᵢ dim(Hᵢ ∩ W) ≥ ℓk/(s−ℓ+1)` and concludes "this contradicts the assumption that `C` is a
`(ℓ, ℓ(k−1)/(s−ℓ+1))`-strong subspace designable code". At the `k` level the derived bound and the
premise coincide, so there is no contradiction to derive and the argument collapses. Nothing
compensates: `R` is the code's own rate and occurs identically in premise and conclusion, so the `k`
level is unambiguously the weaker premise, hence unambiguously the stronger — and false — claim.

`isSubspaceDesign_frsCode_sub_one` supplies this `(k−1)` premise for folded Reed-Solomon codes; its
Wronskian count derives it directly, `isSubspaceDesign_frsCode` being its `1/n`-relaxation.

The rate is carried as a parameter `R` with its defining equation `_hR`, following
`mds_johnson_lambda_le_of_rate_distance`. The equation is an **equality**, not `≤`: a larger `R`
weakens the design premise *and* the conclusion, so the `≤` form is not implied by the source. `R`
is the alphabet-normalized rate `k/(s·n)` of [ABF26] Definition 2.5, the alphabet being `F^s`.

The `if r ∈ Finset.Icc 1 s` guard is the shape `isSubspaceDesign_frsCode_sub_one` produces, and is
necessary: outside `[1, s]` the expression `(sR − 1/n)/(s−r+1)` is negative, which no code
satisfies.

`1 ≤ L` is implicit in [CZ25] (the proof derives a contradiction from `L + 1 ≥ 2` distinct
polynomials; at `L = 0` the claim fails for any word equal to a codeword), and `L ≤ s` is the stated
range.

**What [ABF26] Theorem 3.4 says, and why it is not this.** The paper prints
`Λ(C, 1 − τ(1/η) − η) ≤ (1 − τ(1/η))/η` for a `τ`-subspace-design code at an **arbitrary** `τ` — no
integer parameter, no rate pin, and `τ` applied to the real argument `1/η`. That is an abstraction
of [CZ25] which [CZ25] does not prove, and it is *not* refuted by either counterexample above: at
`τ ≡ 0` it asserts only `Λ(C, 1−η) ≤ 1/η`, which the length-`n` repetition code satisfies for every
`η`. It remains an open generalization. `subspaceDesign_lambda_le_of_eta` is its shape at the pinned
profile. -/
theorem subspaceDesign_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (_hR : (LinearCode.alphabetRate C : ℝ) = R)
    (_h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (L : ℕ) (_hL_pos : 1 ≤ L) (_hL_le : L ≤ s) :
    Lambda ((C : Set (ι → Fin s → F)))
        ((L : ℝ) / (L + 1) * (1 - s * R / (s - L + 1))) ≤ (L : ℕ∞) := by
  sorry -- external admit: [CZ25, Theorem B.5].

/-- **Real-radius form of the subspace-design bound**, derived in-tree from
`subspaceDesign_lambda_le`. If `t` dominates the rate-derived profile on the integers
`1 ≤ L ≤ 1/η` (and `1/η ≤ s` keeps the chosen integer inside [CZ25]'s range), then

  `|Λ(C, 1 − t − η)| ≤ (1 − t)/η` .

This is the engine behind both the `⌊1/η⌋`-rounded `η`-form (`subspaceDesign_lambda_le_of_eta`) and
the folded-RS corollary (`frs_lambda_le_capacity`, where `t` is the profile evaluated at the *real*
argument `1/η`). The proof instantiates the integer theorem at `L := ⌊(1 − t)/η⌋` and uses
monotonicity of `Λ` in the radius: `L + 1 > (1 − t)/η` makes the integer radius
`L/(L+1)·(1 − sR/(s−L+1))` at least `1 − t − η`, and `L ≤ (1 − t)/η` is the claimed list bound. This
mirrors [CZ25]'s own derivation of its Corollary 2.21 from its Theorem 1.3.

Note this is generic in the *dominating value* `t`, not in the profile: the profile stays pinned,
for the reason spelled out on `subspaceDesign_lambda_le`. -/
theorem subspaceDesign_lambda_le_of_profile_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (hR : (LinearCode.alphabetRate C : ℝ) = R)
    (h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (η t : ℝ) (hη_pos : 0 < η) (ht_nonneg : 0 ≤ t)
    (hτ_le : ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ 1 / η → s * R / (s - L + 1) ≤ t)
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
    have hτL : s * R / ((s : ℝ) - L + 1) ≤ t := hτ_le L hL_pos hL_inv
    have hLs : L ≤ s := by exact_mod_cast hL_inv.trans hs
    have key := subspaceDesign_lambda_le s R C hR h L hL_pos hLs
    -- Radius comparison: `1 − t − η ≤ L/(L+1) · (1 − sR/(s−L+1))`.
    have hfloor : (1 - t) / η < (L : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1t : 1 - t < η * ((L : ℝ) + 1) := by
      rw [div_lt_iff₀ hη_pos] at hfloor
      linarith
    have hrad : 1 - t - η ≤ (L : ℝ) / (L + 1) * (1 - s * R / ((s : ℝ) - L + 1)) := by
      have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hL1]
      have hmul : (L : ℝ) * (s * R / ((s : ℝ) - L + 1)) ≤ (L : ℝ) * t :=
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
      simp only [closeCodewordsRel, Code.relHammingBall, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hball
      exact absurd (hball.trans_lt hrad_neg) (not_lt.mpr (by positivity))
    have hzero : Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) = 0 := by
      simp [Lambda, hempty]
    rw [hzero]
    simp

/-- **The `η`-form of the subspace-design bound**, derived in-tree from
`subspaceDesign_lambda_le`. This is the shape of [ABF26] Theorem 3.4 at the pinned profile: for a
code carrying the `(k−1)`-level design profile and any `η > 0` with `1/η ≤ s`,

  `|Λ(C, 1 − sR/(s−1/η+1) − η)| ≤ (1 − sR/(s−1/η+1))/η` .

**No rounding is involved.** [ABF26] prints the profile at the real argument `1/η`, which is
ill-typed for a `τ : ℕ → ℝ` indexed by a dimension. It does not need to be rounded to be reproduced:
`subspaceDesign_lambda_le_of_profile_le` is generic in the *dominating value*, so instantiating it
at `t := sR/(s − 1/η + 1)` — the profile expression at the real argument — gives the paper's display
verbatim, with the domination hypothesis immediate from `L ≤ 1/η ⇒ s − L + 1 ≥ s − 1/η + 1`.
An earlier version instead rounded `1/η` down in both the radius and the bound; the two roundings
pull in opposite directions (the profile is increasing, so a smaller argument enlarges the radius
but also enlarges the bound), so that statement neither implied nor followed from the paper's. It
also needed `η ≤ 1` to keep `⌊1/η⌋ ≥ 1`, which the real-argument form does not.

Non-negativity of `R` is *proved* rather than hypothesised (`LinearCode.alphabetRate` lands in
`ℚ≥0`). `1/η ≤ s` keeps the instantiation point inside [CZ25]'s range `L ≤ s`; it is the hypothesis
the abstract statement omits and its only instantiation carries as `1/η < s`. -/
theorem subspaceDesign_lambda_le_of_eta
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (hR : (LinearCode.alphabetRate C : ℝ) = R)
    (h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (η : ℝ) (hη_pos : 0 < η) (hηs : 1 / η ≤ (s : ℝ)) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - s * R / ((s : ℝ) - 1 / η + 1) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - s * R / ((s : ℝ) - 1 / η + 1)) / η) := by
  -- `R ≥ 0`: it is a rate, and `alphabetRate` lands in `ℚ≥0`.
  have hR_nonneg : 0 ≤ R := by rw [← hR]; positivity
  have hden_pos : (0 : ℝ) < (s : ℝ) - 1 / η + 1 := by linarith
  have hsR_nonneg : (0 : ℝ) ≤ s * R := by positivity
  refine subspaceDesign_lambda_le_of_profile_le s R C hR h η
    (s * R / ((s : ℝ) - 1 / η + 1)) hη_pos
    (div_nonneg hsR_nonneg hden_pos.le) (fun L hL1 hLle => ?_) hηs
  -- Profile domination: `L ≤ 1/η` shrinks the denominator, so the value only grows.
  exact div_le_div_of_nonneg_left hsR_nonneg hden_pos (by linarith)

/-- **Folded Reed-Solomon codes are list-decodable up to capacity** ([ABF26] Corollary 3.5, after
[CZ25, Corollary 2.21]). For `C := FRS[F, L, k, s, ω]` of rate `ρ` and any `η > 0` with `1/η < s`:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))` .

When `η ≥ √(3/s)` the bound simplifies to `|Λ(C, 1 - ρ - η)| ≤ 1/η`.

**Derived in-tree**, not a separate admit: from `subspaceDesign_lambda_le` (via
`subspaceDesign_lambda_le_of_profile_le` at the real-argument profile value
`t := ρ·s/(s − 1/η + 1)`) together with `isSubspaceDesign_frsCode_sub_one`, whose Wronskian count
delivers exactly the `(k−1)`-level profile this chain needs. The `1/n`-relaxed
`isSubspaceDesign_frsCode` does **not** suffice: at that level `subspaceDesign_lambda_le` is false.
This is the route [CZ25] use for their Corollary 2.21 and [ABF26] for this one. The bound equals
`(1 − t)/η` verbatim, since
`1 − sρ/(s−1/η+1) = (s(1−ρ)+1−1/η)/(s+1−1/η)`.

**Rate convention.** `FRS[F, L, k, s, ω] ⊆ (F^s)^n` has rate `ρ = k / (s·n)`, the alphabet being
`F^s`, **not** `k/n`. With this `ρ` both the radius and the list bound are the source's expressions
verbatim; the radius numerator `ρ·s` is `k/n`.

**Why `_hk_le : k ≤ s·n` is needed.** It is what makes the paper's `ρ = k/(s·n)` equal to
`LinearCode.alphabetRate`, which is `min k (s·n)/(s·n)`. An earlier version avoided this hypothesis
by using only `alphabetRate ≤ ρ` and letting profile domination absorb the gap — but that route
depended on `subspaceDesign_lambda_le` holding at an arbitrary profile, which is **false** (see its
docstring). With the profile pinned to the rate by an equality, the rate must match exactly, so the
below-saturation hypothesis is genuine. It is harmless: the capacity regime has `ρ < 1` anyway.

**Admissibility.** [ABF26] Definition 2.15 bakes `(L, s)`-admissibility of `ω` into the code;
ArkLib's `frsCode` deliberately does not, so it is carried here as `_hadm`. Without it the fold
degenerates — at `ω = 1` all folds collapse — and the capacity bound is false.

**Generator hypothesis.** `_hω_gen : ω` generates `F×` is inherited from
`isSubspaceDesign_frsCode_sub_one`, whose unguarded form is FALSE for low-order `ω` (counterexample
`ω = -1` over `𝔽₁₀₁`; see that declaration's docstring). It is also the classical folded-RS setting
of [CZ25] and Guruswami–Rudra, where the fold element is primitive. `ω ≠ 0` is not a separate
hypothesis, being derivable from it. -/
theorem frs_lambda_le_capacity
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (_hFn : Fintype.card ι < Fintype.card F)
    (_hk_le : k ≤ s * Fintype.card ι)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
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
  -- `ω ≠ 0`, from the generator hypothesis: `|F| ≥ 2` makes `orderOf ω ≠ 0`.
  have hω0 : ω ≠ 0 := by
    intro hzero
    rw [hzero, orderOf_zero] at _hω_gen
    have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
    omega
  -- FRS carries the rate-derived design profile.
  have hdesign := isSubspaceDesign_frsCode_sub_one domain k s ω _hFn _hadm _hω_gen
  -- Below saturation, `alphabetRate = k/(s·n) = ρ`.
  have hrate : (LinearCode.alphabetRate
      (ReedSolomon.Folded.frsCode domain k s ω) : ℝ) = ρ := by
    rw [LinearCode.alphabetRate_cast_eq,
      ReedSolomon.Folded.dim_frsCode domain k s ω _hadm hω0 _hk_le]
  have hρ_nonneg : (0 : ℝ) ≤ ρ := by rw [← hrate]; positivity
  have hρs_nonneg : (0 : ℝ) ≤ ρ * s := by positivity
  have ht_nonneg : 0 ≤ ρ * s / ((s : ℝ) - 1 / η + 1) := div_nonneg hρs_nonneg hdenom_pos.le
  have key := subspaceDesign_lambda_le_of_profile_le s ρ
    (ReedSolomon.Folded.frsCode domain k s ω) hrate (hrate ▸ hdesign) η
    (ρ * s / ((s : ℝ) - 1 / η + 1)) _hη_pos ht_nonneg
    (fun L hL1 hLle => ?_) _hη_lt_s.le
  · -- Convert `key` to the source-display radius and bound.
    have hδ_eq : δ = 1 - ρ * s / ((s : ℝ) - 1 / η + 1) - η := rfl
    have hbound_eq : bound = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η := by
      have hd2 : ((s : ℝ) - 1 / η + 1) ≠ 0 := hdenom_pos.ne'
      have hη0 : η ≠ 0 := _hη_pos.ne'
      -- The `1/η` nested inside `s ± 1/η ± 1` clears to `s·η + η − 1`; `field_simp` needs
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
  · -- Profile domination on `1 ≤ L ≤ 1/η`: a smaller `L` only shrinks the denominator.
    have hLs : (L : ℝ) < (s : ℝ) := lt_of_le_of_lt hLle _hη_lt_s
    have hstep : (s : ℝ) * ρ = ρ * s := by ring
    rw [hstep]
    exact div_le_div_of_nonneg_left hρs_nonneg hdenom_pos (by linarith)

/-- **Univariate multiplicity codes are list-decodable up to capacity** — the corollary [ABF26]
asserts exists without stating it: "*Since folded Reed-Solomon codes are subspace-design codes the
above theorem implies that they are list decodable up to capacity (**a similar corollary can be
derived for univariate multiplicity codes**)*". For `C := UM[F, L, k, s]` of rate `ρ` and any
`η > 0` with `1/η < s`, the same display as Corollary 3.5:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))` .

**Derived in-tree** by the same chain as `frs_lambda_le_capacity`: `subspaceDesign_lambda_le` via
`subspaceDesign_lambda_le_of_profile_le` at `t := ρ·s/(s − 1/η + 1)`, with the `(k−1)`-level design
premise supplied by `isSubspaceDesign_umCode_sub_one`. It therefore inherits that admit.

[CZ25] prove the multiplicity case directly too, as their Theorem 1.5 — "*Let `p` be a prime number.
For any integers `s, n, L ≥ 1`, `k ∈ [n]`, and distinct `α₁, …, α_n ∈ F_p`, the code
`MULT^{(s)}_{n,k}(α₁, …, α_n)` over the alphabet `F_p^s` is `(L/(L+1)(1 − sR/(s−L+1)), L)`
list-decodable*" — with Corollary 1.6 / A.10 as the `(1 − R − ε, O(1/ε))` form. Going through the
field-generic Theorem B.5 instead gives this for **any** field satisfying the characteristic
condition, not only prime fields.

**Hypotheses.** `_hchar` is inherited from `isSubspaceDesign_umCode_sub_one`; it is [ABF26] Theorem
2.18's `char(F) > k`, relaxed to `k ≤ ringChar F`, which is all the Wronskian argument needs (`d!`
must be a unit for `d < k`) and which the disjunction with `ringChar F = 0` keeps from forcing
`k = 0` in characteristic zero. `_hk_le : k ≤ s·n` is what makes the paper's `ρ = k/(s·n)` equal
`LinearCode.alphabetRate`; unlike the folded case there is no admissibility or generator
hypothesis, multiplicity codes needing neither. -/
theorem um_lambda_le_capacity
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ)
    (_hs_pos : 0 < s)
    (_hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (_hk_le : k ≤ s * Fintype.card ι)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt_s : 1 / η < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Multiplicity.umCode domain k s : Set (ι → Fin s → F))) δ : ENNReal) ≤
      ENNReal.ofReal bound := by
  intro n ρ δ bound
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hs_posR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr _hs_pos
  have hdenom_pos : (0 : ℝ) < (s : ℝ) - 1 / η + 1 := by linarith
  -- Multiplicity codes carry the `(k-1)`-level design profile.
  have hdesign := isSubspaceDesign_umCode_sub_one domain k s _hchar
  -- Below saturation, `alphabetRate = k/(s·n) = ρ`.
  have hrate : (LinearCode.alphabetRate (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) = ρ := by
    rw [LinearCode.alphabetRate_cast_eq,
      ReedSolomon.Multiplicity.dim_umCode domain _hchar _hk_le]
  have hρ_nonneg : (0 : ℝ) ≤ ρ := by rw [← hrate]; positivity
  have hρs_nonneg : (0 : ℝ) ≤ ρ * s := by positivity
  have ht_nonneg : 0 ≤ ρ * s / ((s : ℝ) - 1 / η + 1) := div_nonneg hρs_nonneg hdenom_pos.le
  have key := subspaceDesign_lambda_le_of_profile_le s ρ
    (ReedSolomon.Multiplicity.umCode domain k s) hrate (hrate ▸ hdesign) η
    (ρ * s / ((s : ℝ) - 1 / η + 1)) _hη_pos ht_nonneg
    (fun L hL1 hLle => ?_) _hη_lt_s.le
  · -- Convert `key` to the source-display radius and bound, as in `frs_lambda_le_capacity`.
    have hδ_eq : δ = 1 - ρ * s / ((s : ℝ) - 1 / η + 1) - η := rfl
    have hbound_eq : bound = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η := by
      have hd2 : ((s : ℝ) - 1 / η + 1) ≠ 0 := hdenom_pos.ne'
      have hη0 : η ≠ 0 := _hη_pos.ne'
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
    have hstep : (s : ℝ) * ρ = ρ * s := by ring
    rw [hstep]
    exact div_le_div_of_nonneg_left hρs_nonneg hdenom_pos (by linarith)

end SubspaceDesignUpperBounds

section RandomReedSolomon

open scoped ProbabilityTheory

/-- **Reed-Solomon codes on a random evaluation domain are list-decodable near capacity**
([ABF26] Theorem 3.6, after [AGL24, Theorem 1.1]).

The source statement, in its own variables: for `ℓ ≥ 2`, `η ∈ (0,1)`, `k, n ∈ ℕ` and a finite field
with `|F| ≥ n + k · 2^{10ℓ/η}`,

  `Pr[ |Λ(C, ℓ/(ℓ+1) · (1 − ρ − η))| ≤ ℓ ] ≥ 1 − 2^{−ℓn}` ,

where the evaluation domain `L` is drawn uniformly from the size-`n` subsets of `F`, the code is
`C := RS[F, L, k]`, and `ρ := k/n`.

**The random domain is the source's, not a reformulation.** The sample space is literally
`\binom{F}{n}` — the subtype of `Finset F` of cardinality `n`, sampled with `$ᵖ`, and the code is
indexed by that subset itself (`↥S → F`), so no ordering is chosen and no push-forward argument is
needed. An earlier assessment recorded this row as blocked on missing infrastructure for a uniform
distribution over size-`n` subsets; that gap is closed — `Finset F` is a `Fintype`, so the subtype
is one too, and `PMF.uniformOfFintype` applies directly.

`[Nonempty {S : Finset F // S.card = n}]` is what `$ᵖ` needs, and it is implied by the field-size
hypothesis (which forces `n ≤ |F|`, whence `Finset.exists_subset_card_eq` supplies a witness); it is
taken as an instance argument only because a statement cannot discharge an instance from one of its
own hypotheses.

The source's stated consequence — at `ℓ = 2(1−ρ−η)/η` and `|F| ≥ n + k·2^{20(1−ρ−η)/η²}` the code
has `|Λ(C, 1 − ρ − η)| ≤ 2(1−ρ−η)/η` with probability `1 − 2^{−2n(1−ρ−η)/η}` — is not stated
separately: its `ℓ` is real-valued, so it needs a rounding the source does not fix, exactly the
issue [ABF26] Theorem 3.4 raises in its `η`-form. Derive it at a call site with an explicit choice.

[BGM23] (exponential alphabet) and [GZ23] (polynomial-size alphabet) are the preceding results, and
[AGGLZ25] combines them; [ABF26] cites all three as context for this theorem, and none is
formalised. -/
theorem rs_random_domain_lambda_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (η : ℝ) (_hη_pos : 0 < η) (_hη_lt : η < 1)
    (k n : ℕ) (_hn_pos : 0 < n)
    (_hF : (n : ℝ) + (k : ℝ) * 2 ^ ((10 * ℓ : ℝ) / η) ≤ Fintype.card F)
    [Nonempty {S : Finset F // S.card = n}] :
    ENNReal.ofReal (1 - 2 ^ (-(ℓ * n : ℝ))) ≤
      Pr_{ let S ← $ᵖ {S : Finset F // S.card = n} }[
        Lambda ((ReedSolomon.code
              (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) k :
            Set (↥(S : Finset F) → F)))
            ((ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η)) ≤ (ℓ : ℕ∞)] := by
  sorry -- external admit: [AGL24, Theorem 1.1].

end RandomReedSolomon

end CodingTheory

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

import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
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
theorem random_linear_lambda_lower
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

def agreementEdges {ι : Type*} {A : Type*} [DecidableEq A]
    (T : Finset (ι → A)) (y : ι → A) (i : ι) : Finset (ι → A) :=
  T.filter (fun c => c i = y i)

theorem agreementEdges_inter_subset
    {ι : Type*} [Fintype ι] {A : Type*} [DecidableEq A]
    (T H : Finset (ι → A)) (y : ι → A) (i : ι)
    (hHT : H ⊆ T) :
    agreementEdges T y i ∩ H = agreementEdges H y i := by
  ext c
  simp only [agreementEdges, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hcT, hci⟩, hcH⟩
    exact ⟨hcH, hci⟩
  · rintro ⟨hcH, hci⟩
    exact ⟨⟨hHT hcH, hci⟩, hcH⟩

open scoped BigOperators in
def agreementWeight {ι : Type*} {A : Type*} [Fintype ι] [DecidableEq A]
    (y : ι → A) (T : Finset (ι → A)) : ℕ :=
  ∑ i : ι, ((T.filter (fun c => c i = y i)).card - 1)

open scoped BigOperators in
theorem agreementWeight_ge_of_hammingDist_le
    {ι : Type*} {A : Type*} [Fintype ι] [DecidableEq A]
    (δ : ℝ) (y : ι → A) (S : Finset (ι → A))
    (hdist : ∀ c ∈ S,
      (hammingDist c y : ℝ) ≤ δ * Fintype.card ι) :
    (S.card : ℝ) * Fintype.card ι * (1 - δ) - Fintype.card ι ≤
      (agreementWeight y S : ℝ) := by
  classical
  let agree : (ι → A) → ℕ := fun c =>
    (Finset.univ.filter (fun i => c i = y i)).card
  have hagree : ∀ c, agree c + hammingDist c y = Fintype.card ι := by
    intro c
    unfold agree hammingDist
    simpa only [Finset.card_univ] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (fun i : ι => c i = y i) (s := Finset.univ))
  have hpoint : ∀ c ∈ S,
      (Fintype.card ι : ℝ) * (1 - δ) ≤ (agree c : ℝ) := by
    intro c hc
    have hcast : (agree c : ℝ) + hammingDist c y = Fintype.card ι := by
      exact_mod_cast hagree c
    nlinarith [hdist c hc]
  have hlower :
      (S.card : ℝ) * Fintype.card ι * (1 - δ) ≤
        ∑ c ∈ S, (agree c : ℝ) := by
    have hsum := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hsum
  have hdouble :
      (∑ c ∈ S, (agree c : ℝ)) =
        ∑ i : ι, ((S.filter (fun c => c i = y i)).card : ℝ) := by
    unfold agree
    simp_rw [Finset.natCast_card_filter]
    rw [Finset.sum_comm]
  have hfiber : ∀ i : ι,
      ((S.filter (fun c => c i = y i)).card : ℝ) ≤
        (((S.filter (fun c => c i = y i)).card - 1 : ℕ) : ℝ) + 1 := by
    intro i
    exact_mod_cast (show
      (S.filter (fun c => c i = y i)).card ≤
        (S.filter (fun c => c i = y i)).card - 1 + 1 by omega)
  have hupper :
      (∑ i : ι, ((S.filter (fun c => c i = y i)).card : ℝ)) ≤
        (agreementWeight y S : ℝ) + Fintype.card ι := by
    calc
      (∑ i : ι, ((S.filter (fun c => c i = y i)).card : ℝ)) ≤
          ∑ i : ι,
            ((((S.filter (fun c => c i = y i)).card - 1 : ℕ) : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => hfiber i
      _ = (agreementWeight y S : ℝ) + Fintype.card ι := by
        rw [Finset.sum_add_distrib]
        unfold agreementWeight
        rw [Nat.cast_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hdouble] at hlower
  linarith

noncomputable def basisFlagLevel {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] {r : ℕ}
    (b : Module.Basis (Fin r) F V) (x : V) : Fin (r + 1) := by
  classical
  exact Finset.min'
    (Finset.univ.filter (fun k => x ∈ b.flag k))
    (by
      refine ⟨Fin.last r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [b.flag_last]
      exact Submodule.mem_top)

theorem basisFlagLevel_le_of_mem
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) (k : Fin (r + 1))
    (hx : x ∈ b.flag k) : basisFlagLevel b x ≤ k := by
  classical
  unfold basisFlagLevel
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

theorem basisFlagLevel_mem_flag
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) :
    x ∈ b.flag (basisFlagLevel b x) := by
  classical
  unfold basisFlagLevel
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun k => x ∈ b.flag k))
    (by
      refine ⟨Fin.last r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [b.flag_last]
      exact Submodule.mem_top)
  exact (Finset.mem_filter.mp hmem).2

theorem basisFlagLevel_basis
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (j : Fin r) :
    basisFlagLevel b (b j) = j.succ := by
  apply le_antisymm
  · apply basisFlagLevel_le_of_mem
    exact b.self_mem_flag j.castSucc_lt_succ
  · have hmem := basisFlagLevel_mem_flag b (b j)
    have hlt : j.castSucc < basisFlagLevel b (b j) :=
      (b.self_mem_flag_iff).mp hmem
    have hne : j.succ ≠ 0 := Fin.succ_ne_zero j
    have hcast : ((j.succ).pred hne).castSucc < basisFlagLevel b (b j) := by
      simpa only [Fin.pred_succ] using hlt
    exact (Fin.castSucc_pred_lt_iff hne).mp hcast

theorem basisFlagLevel_eq_zero_iff
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) :
    basisFlagLevel b x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hmem := basisFlagLevel_mem_flag b x
    rw [h, b.flag_zero] at hmem
    exact hmem
  · intro hx
    subst x
    apply le_antisymm
    · exact basisFlagLevel_le_of_mem b 0 0 (by simp only [b.flag_zero, Submodule.mem_bot])
    · exact Fin.zero_le _

theorem basisFlagLevel_mem_iff_le
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V) (x : V) (k : Fin (r + 1)) :
    x ∈ b.flag k ↔ basisFlagLevel b x ≤ k := by
  constructor
  · exact basisFlagLevel_le_of_mem b x k
  · intro hle
    exact b.flag_mono hle (basisFlagLevel_mem_flag b x)

theorem exists_minimal_subset_property
    {V : Type*} [DecidableEq V] (P : Finset V → Prop)
    (S : Finset V) (hPS : P S) :
    ∃ T : Finset V, T ⊆ S ∧ P T ∧
      ∀ U : Finset V, U ⊂ T → ¬ P U := by
  classical
  let candidates : Finset (Finset V) := S.powerset.filter P
  have hnonempty : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.rfl, hPS⟩
  obtain ⟨T, hTmin⟩ := candidates.exists_minimal hnonempty
  obtain ⟨hTmem, hminimal⟩ := minimal_iff.mp hTmin
  have hTS : T ⊆ S := (Finset.mem_powerset.mp
    (Finset.mem_filter.mp hTmem).1)
  have hPT : P T := (Finset.mem_filter.mp hTmem).2
  refine ⟨T, hTS, hPT, ?_⟩
  intro U hUT hPU
  have hUS : U ⊆ S := hUT.1.trans hTS
  have hUmem : U ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hUS, hPU⟩
  have heq : T = U := hminimal hUmem hUT.1
  apply hUT.2
  rw [heq]

theorem exists_minimal_linear_heavy_subset
    {V : Type*} [DecidableEq V] (weight : Finset V → ℝ)
    (κ : ℝ) (S : Finset V) (hScard : 2 ≤ S.card)
    (hSheavy : (((S.card - 1 : ℕ) : ℝ)) * κ ≤ weight S) :
    ∃ T : Finset V, T ⊆ S ∧ 2 ≤ T.card ∧
      (((T.card - 1 : ℕ) : ℝ)) * κ ≤ weight T ∧
      ∀ U : Finset V, U ⊂ T → 2 ≤ U.card →
        weight U < (((U.card - 1 : ℕ) : ℝ)) * κ := by
  let P : Finset V → Prop := fun T =>
    2 ≤ T.card ∧ (((T.card - 1 : ℕ) : ℝ)) * κ ≤ weight T
  have hPS : P S := ⟨hScard, hSheavy⟩
  obtain ⟨T, hTS, hPT, hminimal⟩ :=
    exists_minimal_subset_property P S hPS
  refine ⟨T, hTS, hPT.1, hPT.2, ?_⟩
  intro U hUT hUcard
  have hnot := hminimal U hUT
  have hnle : ¬((((U.card - 1 : ℕ) : ℝ)) * κ ≤ weight U) := by
    intro hle
    exact hnot ⟨hUcard, hle⟩
  exact lt_of_not_ge hnle

noncomputable def geometricAffineRank {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] (S : Finset V) : ℕ :=
  Module.finrank F (vectorSpan F (S : Set V))

structure GeometricRankPartition {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    (S : Finset V) where
  blocks : Fin (geometricAffineRank (F := F) S + 1) → Finset V
  nonempty : ∀ a, (blocks a).Nonempty
  subset : ∀ a, blocks a ⊆ S
  disjoint : ∀ a b, a ≠ b → Disjoint (blocks a) (blocks b)
  cover : S = Finset.univ.biUnion blocks
  rank_bound : ∀ e : Finset V, e ⊆ S →
    (Finset.univ.filter (fun a => (e ∩ blocks a).Nonempty)).card ≤
      geometricAffineRank (F := F) e + 1

structure SelectedGeometricFlagBasis
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) where
  base : V
  base_mem : base ∈ S
  basis : Module.Basis (Fin (geometricAffineRank (F := F) S)) F
    (vectorSpan F (S : Set V))
  witness : Fin (geometricAffineRank (F := F) S) → V
  witness_mem : ∀ i, witness i ∈ S
  basis_eq_vsub : ∀ i, ((basis i : vectorSpan F (S : Set V)) : V) =
    witness i - base

theorem exists_selectedGeometricFlagBasis
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (hS : S.Nonempty) :
    Nonempty (SelectedGeometricFlagBasis (F := F) S) := by
  classical
  obtain ⟨a, ha⟩ := hS
  let A : Submodule F V := vectorSpan F (S : Set V)
  let D : Finset V := (S.erase a).image (fun x => x - a)
  have hAD : A = Submodule.span F (D : Set V) := by
    dsimp [A, D]
    exact vectorSpan_eq_span_vsub_finset_right_ne F ha
  letI : FiniteDimensional F (Submodule.span F (D : Set V)) :=
    FiniteDimensional.span_of_finite F D.finite_toSet
  have hex := Submodule.exists_fun_fin_finrank_span_eq F (D : Set V)
  rw [← hAD] at hex
  obtain ⟨v, hvD, hspanv, hlinv⟩ := hex
  have hexw : ∀ i, ∃ x : V, x ∈ S ∧ v i = x - a := by
    intro i
    have hmem : v i ∈ D := hvD i
    dsimp [D] at hmem
    obtain ⟨x, hxer, hx⟩ := Finset.mem_image.mp hmem
    exact ⟨x, Finset.mem_of_mem_erase hxer, hx.symm⟩
  choose w hwS hvw using hexw
  have hvA : ∀ i, v i ∈ A := by
    intro i
    rw [← hspanv]
    exact Submodule.subset_span (Set.mem_range_self i)
  let lift : Fin (Module.finrank F A) → A := fun i => ⟨v i, hvA i⟩
  have hlinlift : LinearIndependent F lift := by
    apply LinearIndependent.of_comp A.subtype
    have hfun : A.subtype ∘ lift = v := by
      funext i
      rfl
    rw [hfun]
    exact hlinv
  have hspanlift : Submodule.span F (Set.range lift) = ⊤ := by
    exact (Submodule.span_range_subtype_eq_top_iff A hvA).2 hspanv
  let b : Module.Basis (Fin (Module.finrank F A)) F A :=
    Module.Basis.mk hlinlift (by rw [hspanlift])
  have hb : ∀ i, ((b i : A) : V) = w i - a := by
    intro i
    dsimp [b]
    rw [Module.Basis.mk_apply]
    exact hvw i
  dsimp [A, geometricAffineRank] at b w hwS hb
  exact ⟨{
    base := a
    base_mem := ha
    basis := b
    witness := w
    witness_mem := hwS
    basis_eq_vsub := hb }⟩

theorem geometricAffineRank_pos_of_two_le_card
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (hS : 2 ≤ S.card) :
    1 ≤ geometricAffineRank (F := F) S := by
  classical
  letI : FiniteDimensional F (vectorSpan F (S : Set V)) :=
    finiteDimensional_vectorSpan_of_finite F S.finite_toSet
  unfold geometricAffineRank
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hv := vsub_mem_vectorSpan F
    (show x ∈ (S : Set V) from hx) (show y ∈ (S : Set V) from hy)
  rw [hbot] at hv
  have hsub : x - y = 0 := hv
  exact hxy (sub_eq_zero.mp hsub)

noncomputable def geometricDensityThreshold (s m : ℕ) (k : ℝ) : ℝ :=
  (((m - 1 : ℕ) : ℝ) * k) / ((s : ℝ) - m + 2)

theorem exists_minimal_heavy_subset
    {V : Type*} [DecidableEq V] (s : ℕ) (k : ℝ)
    (weight : Finset V → ℝ) (S : Finset V)
    (hScard : 2 ≤ S.card)
    (hSheavy : geometricDensityThreshold s S.card k ≤ weight S) :
    ∃ T : Finset V, T ⊆ S ∧ 2 ≤ T.card ∧
      geometricDensityThreshold s T.card k ≤ weight T ∧
      ∀ U : Finset V, U ⊂ T → 2 ≤ U.card →
        weight U < geometricDensityThreshold s U.card k := by
  let P : Finset V → Prop := fun T =>
    2 ≤ T.card ∧ geometricDensityThreshold s T.card k ≤ weight T
  have hPS : P S := ⟨hScard, hSheavy⟩
  obtain ⟨T, hTS, hPT, hminimal⟩ :=
    exists_minimal_subset_property P S hPS
  refine ⟨T, hTS, hPT.1, hPT.2, ?_⟩
  intro U hUT hUcard
  have hnot := hminimal U hUT
  have hnle : ¬geometricDensityThreshold s U.card k ≤ weight U := by
    intro hle
    exact hnot ⟨hUcard, hle⟩
  exact lt_of_not_ge hnle

def geometricEdgeWeight {V : Type*} (S : Finset V) : ℕ :=
  S.card - 1

theorem geometricAffineRank_le_edgeWeight
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) :
    geometricAffineRank (F := F) S ≤ geometricEdgeWeight S := by
  classical
  by_cases hS : S = ∅
  · subst S
    unfold geometricAffineRank geometricEdgeWeight
    rw [Finset.card_empty, Nat.zero_sub]
    have hempty : ((∅ : Finset V) : Set V) = ∅ := by
      ext x
      exact iff_of_false (Finset.notMem_empty x) (Set.notMem_empty x)
    rw [hempty, vectorSpan_empty, finrank_bot]
  · have hcard_pos : 0 < S.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hS)
    have hcard : S.card = (S.card - 1) + 1 := by omega
    have hle := finrank_vectorSpan_image_finset_le (k := F)
      (fun x : V => x) S hcard
    rw [Finset.image_id'] at hle
    exact hle

noncomputable def geometricLoss {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] (S : Finset V) : ℕ :=
  geometricEdgeWeight S - geometricAffineRank (F := F) S

theorem geometricEdgeWeight_eq_rank_add_loss
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) :
    geometricEdgeWeight S =
      geometricAffineRank (F := F) S + geometricLoss (F := F) S := by
  have hle := geometricAffineRank_le_edgeWeight (F := F) S
  unfold geometricLoss
  omega

noncomputable def geometricPartitionCrossing {F : Type*} {V : Type*}
    [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (e : Finset V) : ℕ :=
  (Finset.univ.filter (fun a => (e ∩ P.blocks a).Nonempty)).card - 1

open scoped BigOperators in
theorem geometricEdgeWeight_partition_decomposition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) (e : Finset V) (he : e ⊆ S) :
    geometricEdgeWeight e =
      (∑ a, geometricEdgeWeight (e ∩ P.blocks a)) +
        geometricPartitionCrossing P e := by
  classical
  let q : ℕ :=
    (Finset.univ.filter (fun a => (e ∩ P.blocks a).Nonempty)).card
  have hpair : ((Finset.univ : Finset
      (Fin (geometricAffineRank (F := F) S + 1))) : Set _).PairwiseDisjoint
      (fun a => e ∩ P.blocks a) := by
    intro a _ b _ hab
    exact (P.disjoint a b hab).mono Finset.inter_subset_right
      Finset.inter_subset_right
  have hcover : Finset.univ.biUnion (fun a => e ∩ P.blocks a) = e := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, _, hxi⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hxi).1
    · intro hx
      have hxS : x ∈ S := he hx
      rw [P.cover] at hxS
      obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hxS
      exact Finset.mem_biUnion.mpr
        ⟨a, ha, Finset.mem_inter.mpr ⟨hx, hxa⟩⟩
  have hsum_card :
      (∑ a, (e ∩ P.blocks a).card) = e.card := by
    have hc := Finset.card_biUnion hpair
    rw [hcover] at hc
    simpa only using hc.symm
  have hpoint : ∀ a : Fin (geometricAffineRank (F := F) S + 1),
      geometricEdgeWeight (e ∩ P.blocks a) +
        (if (e ∩ P.blocks a).Nonempty then 1 else 0) =
          (e ∩ P.blocks a).card := by
    intro a
    unfold geometricEdgeWeight
    by_cases hne : (e ∩ P.blocks a).Nonempty
    · rw [if_pos hne]
      have hpos := Finset.card_pos.mpr hne
      omega
    · rw [if_neg hne]
      have hz : (e ∩ P.blocks a).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
      omega
  have hindicator :
      (∑ a : Fin (geometricAffineRank (F := F) S + 1),
        if (e ∩ P.blocks a).Nonempty then 1 else 0) = q := by
    unfold q
    rw [Finset.card_filter]
  have hsum : (∑ a, geometricEdgeWeight (e ∩ P.blocks a)) + q = e.card := by
    rw [← hindicator, ← Finset.sum_add_distrib]
    calc
      (∑ a, (geometricEdgeWeight (e ∩ P.blocks a) +
          if (e ∩ P.blocks a).Nonempty then 1 else 0)) =
          ∑ a, (e ∩ P.blocks a).card :=
        Finset.sum_congr rfl fun a _ => hpoint a
      _ = e.card := hsum_card
  unfold geometricPartitionCrossing
  change geometricEdgeWeight e =
    (∑ a, geometricEdgeWeight (e ∩ P.blocks a)) + (q - 1)
  unfold geometricEdgeWeight at hsum ⊢
  by_cases hene : e.Nonempty
  · obtain ⟨x, hx⟩ := hene
    have hxS : x ∈ S := he hx
    rw [P.cover] at hxS
    obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hxS
    have hqpos : 0 < q := by
      rw [Finset.card_pos]
      refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ?_⟩⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, hxa⟩⟩
    have hepos : 0 < e.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · have he0 : e.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hene)
    have hsum0 :
        (∑ a, ((e ∩ P.blocks a).card - 1)) + q = 0 := by
      simpa only [he0] using hsum
    omega

theorem geometricPartitionCrossing_le_affineRank
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) (e : Finset V) (he : e ⊆ S) :
    geometricPartitionCrossing P e ≤ geometricAffineRank (F := F) e := by
  unfold geometricPartitionCrossing
  have h := P.rank_bound e he
  omega

theorem geometricRankPartition_blocks_ssubset
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) (hS : 2 ≤ S.card) :
    ∀ a, P.blocks a ⊂ S := by
  have hrank := geometricAffineRank_pos_of_two_le_card (F := F) S hS
  have hidx : 1 < Fintype.card
      (Fin (geometricAffineRank (F := F) S + 1)) := by
    rw [Fintype.card_fin]
    omega
  intro a
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card hidx a
  obtain ⟨x, hxb⟩ := P.nonempty b
  refine ⟨P.subset a, ?_⟩
  intro hSa
  have hxS : x ∈ S := P.subset b hxb
  have hxa : x ∈ P.blocks a := hSa hxS
  exact (Finset.disjoint_left.mp (P.disjoint a b hba.symm)) hxa hxb

open scoped BigOperators in
theorem geometricRankPartition_sum_blockWeight
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (P : GeometricRankPartition (F := F) S) :
    (∑ a, geometricEdgeWeight (P.blocks a)) =
      geometricEdgeWeight S - geometricAffineRank (F := F) S := by
  classical
  have hdecomp := geometricEdgeWeight_partition_decomposition P S
    (Finset.Subset.rfl)
  have hinter : ∀ a : Fin (geometricAffineRank (F := F) S + 1),
      S ∩ P.blocks a = P.blocks a := by
    intro a
    exact Finset.inter_eq_right.mpr (P.subset a)
  simp_rw [hinter] at hdecomp
  have hfilter :
      Finset.univ.filter (fun a => (S ∩ P.blocks a).Nonempty) =
        (Finset.univ : Finset (Fin (geometricAffineRank (F := F) S + 1))) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hinter a]
    exact iff_true_intro (P.nonempty a)
  have hcross : geometricPartitionCrossing P S =
      geometricAffineRank (F := F) S := by
    unfold geometricPartitionCrossing
    rw [hfilter, Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcross] at hdecomp
  have hle := geometricAffineRank_le_edgeWeight (F := F) S
  omega

open scoped BigOperators in
noncomputable def geometricTotalLoss {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [DecidableEq V] [Field F] [AddCommGroup V] [Module F V]
    (E : ι → Finset V) (S : Finset V) : ℕ :=
  ∑ i : ι, geometricLoss (F := F) (E i ∩ S)

open scoped BigOperators in
def geometricTotalWeight {ι : Type*} {V : Type*} [Fintype ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset V) : ℕ :=
  ∑ i : ι, geometricEdgeWeight (E i ∩ S)

open scoped BigOperators in
theorem agreementWeight_eq_geometricTotalWeight
    {ι : Type*} {A : Type*} [Fintype ι] [DecidableEq A]
    (y : ι → A) (T : Finset (ι → A)) :
    agreementWeight y T = geometricTotalWeight (agreementEdges T y) T := by
  unfold agreementWeight geometricTotalWeight geometricEdgeWeight agreementEdges
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]

open scoped BigOperators in
theorem geometricTotalWeight_eq_rank_add_totalLoss
    {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [DecidableEq V] [Field F] [AddCommGroup V] [Module F V]
    (E : ι → Finset V) (S : Finset V) :
    geometricTotalWeight E S =
      (∑ i : ι, geometricAffineRank (F := F) (E i ∩ S)) +
        geometricTotalLoss (F := F) E S := by
  unfold geometricTotalWeight geometricTotalLoss
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    geometricEdgeWeight_eq_rank_add_loss (F := F) (E i ∩ S)

open scoped BigOperators in
theorem geometricTotalWeight_eq_zero_of_card_le_one
    {ι : Type*} {V : Type*} [Fintype ι] [DecidableEq V]
    (E : ι → Finset V) (S : Finset V) (hS : S.card ≤ 1) :
    geometricTotalWeight E S = 0 := by
  unfold geometricTotalWeight
  apply Finset.sum_eq_zero
  intro i _
  unfold geometricEdgeWeight
  have hcard : (E i ∩ S).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_right).trans hS
  omega

open scoped BigOperators in
theorem geometricTotalWeight_partition_decomposition
    {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (E : ι → Finset V) :
    geometricTotalWeight E S =
      (∑ a, geometricTotalWeight E (P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
  classical
  have hinter : ∀ (i : ι) (a : Fin (geometricAffineRank (F := F) S + 1)),
      (E i ∩ S) ∩ P.blocks a = E i ∩ P.blocks a := by
    intro i a
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨hxe, _⟩, hxb⟩
      exact ⟨hxe, hxb⟩
    · rintro ⟨hxe, hxb⟩
      exact ⟨⟨hxe, P.subset a hxb⟩, hxb⟩
  unfold geometricTotalWeight
  calc
    (∑ i : ι, geometricEdgeWeight (E i ∩ S)) =
        ∑ i : ι, ((∑ a, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) +
          geometricPartitionCrossing P (E i ∩ S)) := by
      exact Finset.sum_congr rfl fun i _ =>
        geometricEdgeWeight_partition_decomposition P (E i ∩ S)
          Finset.inter_subset_right
    _ = (∑ i : ι, ∑ a, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a, ∑ i : ι, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
      rw [Finset.sum_comm]
    _ = (∑ a, ∑ i : ι, geometricEdgeWeight (E i ∩ P.blocks a)) +
        ∑ i : ι, geometricPartitionCrossing P (E i ∩ S) := by
      have hdouble :
          (∑ a, ∑ i : ι, geometricEdgeWeight ((E i ∩ S) ∩ P.blocks a)) =
            ∑ a, ∑ i : ι, geometricEdgeWeight (E i ∩ P.blocks a) := by
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun i _ => congrArg geometricEdgeWeight (hinter i a)
      rw [hdouble]

def geometricTranslate {V : Type*} [AddGroup V] [DecidableEq V]
    (v : V) (S : Finset V) : Finset V :=
  S.image (fun x => x - v)

open scoped Pointwise in
theorem geometricAffineRank_translate
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (v : V) (S : Finset V) :
    geometricAffineRank (F := F) (geometricTranslate v S) =
      geometricAffineRank (F := F) S := by
  unfold geometricTranslate geometricAffineRank
  rw [Finset.coe_image]
  have hfun : (fun x : V => x - v) = (fun x : V => (-v) +ᵥ x) := by
    funext x
    simp only [vadd_eq_add, sub_eq_add_neg, add_comm]
  rw [hfun, Set.image_vadd, vectorSpan_vadd]

theorem geometricTranslate_card
    {V : Type*} [AddCommGroup V] [DecidableEq V]
    (v : V) (S : Finset V) :
    (geometricTranslate v S).card = S.card := by
  unfold geometricTranslate
  apply Finset.card_image_of_injective
  intro x y hxy
  have h := congrArg (fun z : V => z + v) hxy
  simpa only [sub_add_cancel] using h

theorem linearIndependent_of_strictMono_basisFlagLevels
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r n : ℕ} (b : Module.Basis (Fin r) F V)
    (v : Fin n → V) (level : Fin n → Fin (r + 1))
    (hlevel : StrictMono level) (hpos : ∀ i, level i ≠ 0)
    (hv : ∀ i, basisFlagLevel b (v i) = level i) :
    LinearIndependent F v := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      rw [linearIndependent_finSucc']
      constructor
      · apply ih (v := Fin.init v) (level := fun i => level i.castSucc)
        · intro i j hij
          exact hlevel (Fin.castSucc_lt_castSucc_iff.mpr hij)
        · intro i
          exact hpos i.castSucc
        · intro i
          change basisFlagLevel b (v i.castSucc) = level i.castSucc
          exact hv i.castSucc
      · intro hspan
        let k : Fin (r + 1) := level (Fin.last n)
        have hk : k ≠ 0 := hpos (Fin.last n)
        let predK : Fin (r + 1) := (k.pred hk).castSucc
        have hspan_le : Submodule.span F (Set.range (Fin.init v)) ≤ b.flag predK := by
          rw [Submodule.span_le]
          intro x hx
          rcases hx with ⟨i, rfl⟩
          change v i.castSucc ∈ b.flag predK
          rw [basisFlagLevel_mem_iff_le, hv]
          have hlt : level i.castSucc < k :=
            hlevel (Fin.castSucc_lt_last i)
          change (level i.castSucc).val ≤ (k.pred hk).val
          rw [Fin.val_pred]
          omega
        have hlast : v (Fin.last n) ∉ b.flag predK := by
          rw [basisFlagLevel_mem_iff_le, hv]
          intro hle
          have hkpos : 0 < k.val := Fin.pos_iff_ne_zero.mpr hk
          change k.val ≤ (k.pred hk).val at hle
          rw [Fin.val_pred] at hle
          omega
        exact hlast (hspan_le hspan)

theorem affineIndependent_of_basisFlagLevels
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (b : Module.Basis (Fin r) F V)
    (p : Fin (r + 1) → V)
    (hp : ∀ i, basisFlagLevel b (p i) = i) :
    AffineIndependent F p := by
  have hp0 : p 0 = 0 :=
    (basisFlagLevel_eq_zero_iff b (p 0)).mp (hp 0)
  have hlin : LinearIndependent F (fun i : Fin r => p i.succ) := by
    apply linearIndependent_of_strictMono_basisFlagLevels b
      (fun i : Fin r => p i.succ) (fun i : Fin r => i.succ)
    · exact Fin.strictMono_succ
    · intro i
      exact Fin.succ_ne_zero i
    · intro i
      exact hp i.succ
  rw [affineIndependent_iff_linearIndependent_vsub F p 0]
  let e := finSuccAboveEquiv (0 : Fin (r + 1))
  let q : {x : Fin (r + 1) // x ≠ 0} → V :=
    fun i => p i.1 -ᵥ p 0
  have hcomp : q ∘ e = fun i : Fin r => p i.succ := by
    funext i
    change p ((e i).1) - p 0 = p i.succ
    rw [hp0, sub_zero]
    change p ((0 : Fin (r + 1)).succAbove i) = p i.succ
    rw [Fin.succAbove_zero_apply]
  exact (linearIndependent_equiv' (R := F) e hcomp).mp hlin

open scoped BigOperators in
theorem minimal_linear_heavy_crossing_lower
    {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (E : ι → Finset V) (κ : ℝ)
    (hblocks : ∀ a, P.blocks a ⊂ S)
    (hheavy : (geometricEdgeWeight S : ℝ) * κ ≤
      (geometricTotalWeight E S : ℝ))
    (hminimal : ∀ U : Finset V, U ⊂ S → 2 ≤ U.card →
      (geometricTotalWeight E U : ℝ) <
        (geometricEdgeWeight U : ℝ) * κ) :
    (geometricAffineRank (F := F) S : ℝ) * κ ≤
      ∑ i : ι, (geometricPartitionCrossing P (E i ∩ S) : ℝ) := by
  classical
  have hblock : ∀ a, (geometricTotalWeight E (P.blocks a) : ℝ) ≤
      (geometricEdgeWeight (P.blocks a) : ℝ) * κ := by
    intro a
    by_cases hcard : (P.blocks a).card ≤ 1
    · have hzero := geometricTotalWeight_eq_zero_of_card_le_one
        E (P.blocks a) hcard
      have hwzero : geometricEdgeWeight (P.blocks a) = 0 := by
        unfold geometricEdgeWeight
        omega
      rw [hzero, hwzero]
      norm_num
    · have htwo : 2 ≤ (P.blocks a).card := by omega
      exact (hminimal (P.blocks a) (hblocks a) htwo).le
  have hsum_blocks :
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) ≤
        ∑ a, (geometricEdgeWeight (P.blocks a) : ℝ) * κ :=
    Finset.sum_le_sum fun a _ => hblock a
  have hsum_weight_nat := geometricRankPartition_sum_blockWeight P
  have hrank_le := geometricAffineRank_le_edgeWeight (F := F) S
  have hsum_weight :
      (∑ a, (geometricEdgeWeight (P.blocks a) : ℝ)) =
        (geometricEdgeWeight S : ℝ) -
          (geometricAffineRank (F := F) S : ℝ) := by
    rw [← Nat.cast_sum, hsum_weight_nat, Nat.cast_sub hrank_le]
  have hsum_blocks' :
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) ≤
        ((geometricEdgeWeight S : ℝ) -
          (geometricAffineRank (F := F) S : ℝ)) * κ := by
    calc
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) ≤
          ∑ a, (geometricEdgeWeight (P.blocks a) : ℝ) * κ := hsum_blocks
      _ = (∑ a, (geometricEdgeWeight (P.blocks a) : ℝ)) * κ := by
        rw [Finset.sum_mul]
      _ = ((geometricEdgeWeight S : ℝ) -
          (geometricAffineRank (F := F) S : ℝ)) * κ := by
        rw [hsum_weight]
  have hdecomp_nat := geometricTotalWeight_partition_decomposition P E
  have hdecomp : (geometricTotalWeight E S : ℝ) =
      (∑ a, (geometricTotalWeight E (P.blocks a) : ℝ)) +
        ∑ i : ι, (geometricPartitionCrossing P (E i ∩ S) : ℝ) := by
    exact_mod_cast hdecomp_nat
  linarith

open scoped BigOperators in
theorem minimal_linear_heavy_affineRank_lower_of_partition
    {ι : Type*} {F : Type*} {V : Type*}
    [Fintype ι] [Field F] [AddCommGroup V] [Module F V] [DecidableEq V]
    {S : Finset V} (P : GeometricRankPartition (F := F) S)
    (E : ι → Finset V) (κ : ℝ) (hS : 2 ≤ S.card)
    (hheavy : (geometricEdgeWeight S : ℝ) * κ ≤
      (geometricTotalWeight E S : ℝ))
    (hminimal : ∀ U : Finset V, U ⊂ S → 2 ≤ U.card →
      (geometricTotalWeight E U : ℝ) <
        (geometricEdgeWeight U : ℝ) * κ) :
    (geometricAffineRank (F := F) S : ℝ) * κ ≤
      ∑ i : ι, (geometricAffineRank (F := F) (E i ∩ S) : ℝ) := by
  calc
    (geometricAffineRank (F := F) S : ℝ) * κ ≤
        ∑ i : ι, (geometricPartitionCrossing P (E i ∩ S) : ℝ) :=
      minimal_linear_heavy_crossing_lower P E κ
        (geometricRankPartition_blocks_ssubset P hS) hheavy hminimal
    _ ≤ ∑ i : ι, (geometricAffineRank (F := F) (E i ∩ S) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast geometricPartitionCrossing_le_affineRank P (E i ∩ S)
        Finset.inter_subset_right

noncomputable def selectedGeometricFlagPart
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) (x : V) :
    Fin (geometricAffineRank (F := F) S + 1) :=
  if hx : x ∈ S then
    basisFlagLevel B.basis
      ⟨x - B.base, vsub_mem_vectorSpan F hx B.base_mem⟩
  else 0

theorem affineIndependent_of_selectedGeometricFlagPart_transversal
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S)
    (p : Fin (geometricAffineRank (F := F) S + 1) → V)
    (hpS : ∀ i, p i ∈ S)
    (hpPart : ∀ i, selectedGeometricFlagPart B (p i) = i) :
    AffineIndependent F p := by
  let A : Submodule F V := vectorSpan F (S : Set V)
  let q : Fin (geometricAffineRank (F := F) S + 1) → A :=
    fun i => ⟨p i - B.base, vsub_mem_vectorSpan F (hpS i) B.base_mem⟩
  have hqLevel : ∀ i, basisFlagLevel B.basis (q i) = i := by
    intro i
    have h := hpPart i
    unfold selectedGeometricFlagPart at h
    rw [dif_pos (hpS i)] at h
    exact h
  have hqAI : AffineIndependent F q :=
    affineIndependent_of_basisFlagLevels B.basis q hqLevel
  have hdiff : AffineIndependent F (fun i => p i - B.base) := by
    have hmap := hqAI.map' A.subtype.toAffineMap A.subtype_injective
    have hfun : (fun i => p i - B.base) = A.subtype.toAffineMap ∘ q := by
      funext i
      rfl
    rw [hfun]
    exact hmap
  have htrans := hdiff.vadd F (v := B.base)
  convert htrans using 1
  funext i
  rw [Pi.vadd_apply, vadd_eq_add]
  exact (add_sub_cancel B.base (p i)).symm

theorem selectedGeometricFlagPart_base
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    selectedGeometricFlagPart B B.base = 0 := by
  unfold selectedGeometricFlagPart
  rw [dif_pos B.base_mem]
  rw [basisFlagLevel_eq_zero_iff]
  apply Subtype.ext
  simp only [sub_self, Submodule.coe_zero]

theorem selectedGeometricFlagPart_witness
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S)
    (i : Fin (geometricAffineRank (F := F) S)) :
    selectedGeometricFlagPart B (B.witness i) = i.succ := by
  unfold selectedGeometricFlagPart
  rw [dif_pos (B.witness_mem i)]
  have heq :
      (⟨B.witness i - B.base,
        vsub_mem_vectorSpan F (B.witness_mem i) B.base_mem⟩ :
          vectorSpan F (S : Set V)) = B.basis i := by
    apply Subtype.ext
    exact (B.basis_eq_vsub i).symm
  rw [heq]
  exact basisFlagLevel_basis B.basis i

theorem selectedGeometricFlagPart_image_eq_univ
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    S.image (selectedGeometricFlagPart B) = Finset.univ := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, iff_true]
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨B.base, B.base_mem, selectedGeometricFlagPart_base B⟩
  · exact ⟨B.witness i, B.witness_mem i,
      selectedGeometricFlagPart_witness B i⟩

noncomputable def selectedGeometricFlagRep
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    Fin (geometricAffineRank (F := F) S + 1) → V :=
  Fin.cases B.base B.witness

theorem selectedGeometricFlagPart_rep
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    ∀ i, selectedGeometricFlagPart B (selectedGeometricFlagRep B i) = i := by
  intro i
  refine Fin.cases (selectedGeometricFlagPart_base B) (fun j => ?_) i
  exact selectedGeometricFlagPart_witness B j

theorem selectedGeometricFlagRep_mem
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    ∀ i, selectedGeometricFlagRep B i ∈ S := by
  intro i
  refine Fin.cases B.base_mem (fun j => ?_) i
  exact B.witness_mem j

theorem selectedGeometricFlagPart_image_card_le
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S)
    (E : Finset V) (hES : E ⊆ S) :
    (E.image (selectedGeometricFlagPart B)).card ≤
      geometricAffineRank (F := F) E + 1 := by
  classical
  let part := selectedGeometricFlagPart B
  let J : Finset (Fin (geometricAffineRank (F := F) S + 1)) := E.image part
  have hex : ∀ j : (J : Set _), ∃ x : V, x ∈ E ∧ part x = j.1 := by
    intro j
    have hj : j.1 ∈ E.image part := j.2
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hj
    exact ⟨x, hx, heq⟩
  choose pick hpickE hpickPart using hex
  let p : Fin (geometricAffineRank (F := F) S + 1) → V := fun j =>
    if hj : j ∈ J then pick ⟨j, hj⟩ else selectedGeometricFlagRep B j
  have hpS : ∀ j, p j ∈ S := by
    intro j
    by_cases hj : j ∈ J
    · rw [show p j = pick ⟨j, hj⟩ by simp only [p, dif_pos hj]]
      exact hES (hpickE ⟨j, hj⟩)
    · rw [show p j = selectedGeometricFlagRep B j by simp only [p, dif_neg hj]]
      exact selectedGeometricFlagRep_mem B j
  have hpPart : ∀ j, selectedGeometricFlagPart B (p j) = j := by
    intro j
    by_cases hj : j ∈ J
    · rw [show p j = pick ⟨j, hj⟩ by simp only [p, dif_pos hj]]
      exact hpickPart ⟨j, hj⟩
    · rw [show p j = selectedGeometricFlagRep B j by simp only [p, dif_neg hj]]
      exact selectedGeometricFlagPart_rep B j
  have hpAI : AffineIndependent F p :=
    affineIndependent_of_selectedGeometricFlagPart_transversal B p hpS hpPart
  have hpickAI : AffineIndependent F pick := by
    have hsub := hpAI.subtype (J : Set _)
    convert hsub using 1
    funext j
    have hj : j.1 ∈ J := j.2
    have hval : p j.1 = pick j := by
      dsimp [p]
      rw [if_pos hj]
    exact hval.symm
  have hcard := hpickAI.card_le_finrank_succ
  have hrange : Set.range pick ⊆ (E : Set V) := by
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    exact hpickE j
  have hspan : vectorSpan F (Set.range pick) ≤ vectorSpan F (E : Set V) :=
    vectorSpan_mono F hrange
  letI : FiniteDimensional F (vectorSpan F (E : Set V)) :=
    finiteDimensional_vectorSpan_of_finite F E.finite_toSet
  have hfin := Submodule.finrank_mono hspan
  calc
    (E.image (selectedGeometricFlagPart B)).card = J.card := by
      rfl
    _ = Fintype.card J := (Fintype.card_coe J).symm
    _ ≤ Module.finrank F (vectorSpan F (Set.range pick)) + 1 := hcard
    _ ≤ Module.finrank F (vectorSpan F (E : Set V)) + 1 :=
      Nat.add_le_add_right hfin 1
    _ = geometricAffineRank (F := F) E + 1 := rfl

theorem exists_affineRank_partition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (hS2 : 2 ≤ S.card) :
    let r := Module.finrank F (vectorSpan F (S : Set V))
    ∃ part : V → Fin (r + 1),
      S.image part = Finset.univ ∧
      ∀ E : Finset V, E ⊆ S →
        (E.image part).card ≤
          Module.finrank F (vectorSpan F (E : Set V)) + 1 := by
  dsimp
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B⟩ := exists_selectedGeometricFlagBasis (F := F) S hS
  refine ⟨selectedGeometricFlagPart B,
    selectedGeometricFlagPart_image_eq_univ B, ?_⟩
  intro E hES
  exact selectedGeometricFlagPart_image_card_le B E hES

noncomputable def selectedGeometricFlagRankPartition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] {S : Finset V}
    (B : SelectedGeometricFlagBasis (F := F) S) :
    GeometricRankPartition (F := F) S where
  blocks a := S.filter (fun x => selectedGeometricFlagPart B x = a)
  nonempty a := by
    refine ⟨selectedGeometricFlagRep B a, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨selectedGeometricFlagRep_mem B a, selectedGeometricFlagPart_rep B a⟩
  subset a := Finset.filter_subset _ _
  disjoint a b hab := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have ha := (Finset.mem_filter.mp hxa).2
    have hb := (Finset.mem_filter.mp hxb).2
    exact hab (ha.symm.trans hb)
  cover := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_biUnion.mpr
        ⟨selectedGeometricFlagPart B x, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    · intro hx
      obtain ⟨a, _, hxa⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp hxa).1
  rank_bound e he := by
    have hfilter :
        Finset.univ.filter
            (fun a => (e ∩ S.filter
              (fun x => selectedGeometricFlagPart B x = a)).Nonempty) =
          e.image (selectedGeometricFlagPart B) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨x, hx⟩
        have hxe := (Finset.mem_inter.mp hx).1
        have hpart := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
        exact ⟨x, hxe, hpart⟩
      · rintro ⟨x, hxe, hpart⟩
        refine ⟨x, Finset.mem_inter.mpr ⟨hxe, ?_⟩⟩
        exact Finset.mem_filter.mpr ⟨he hxe, hpart⟩
    rw [hfilter]
    exact selectedGeometricFlagPart_image_card_le B e he

theorem exists_geometricRankPartition
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (hS : S.Nonempty) :
    Nonempty (GeometricRankPartition (F := F) S) := by
  obtain ⟨B⟩ := exists_selectedGeometricFlagBasis (F := F) S hS
  exact ⟨selectedGeometricFlagRankPartition B⟩

open scoped BigOperators in
theorem subspaceDesign_kernelSum_le_finrank_sub_one
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (hR : (LinearCode.alphabetRate C : ℝ) = R)
    (h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (A : Submodule F (ι → Fin s → F)) (hAC : A ≤ C)
    (hA_pos : 1 ≤ Module.finrank F A)
    (hA_le : Module.finrank F A ≤ s) :
    (∑ i : ι, (Module.finrank F
      ↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) ≤
      (Module.finrank F A : ℝ) * ((Module.finrank F C : ℝ) - 1) /
        ((s : ℝ) - Module.finrank F A + 1) := by
  let ell := Module.finrank F A
  have hell_mem : ell ∈ Finset.Icc 1 s :=
    Finset.mem_Icc.mpr ⟨hA_pos, hA_le⟩
  have hdesign := h ell A hAC le_rfl
  simp only [hell_mem, if_true] at hdesign
  have hn_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hs_pos : (0 : ℝ) < s := by
    exact_mod_cast (show 0 < s by omega)
  have hell_le_real : (ell : ℝ) ≤ s := by exact_mod_cast hA_le
  have hden_pos : (0 : ℝ) < (s : ℝ) - ell + 1 := by linarith
  rw [div_le_iff₀ hn_pos] at hdesign
  have hrate := hR
  rw [LinearCode.alphabetRate_cast_eq] at hrate
  have hrate_id : (s : ℝ) * R * Fintype.card ι = Module.finrank F C := by
    rw [← hrate]
    field_simp
  calc
    (∑ i : ι, (Module.finrank F
        ↥(A ⊓ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ))
        ≤ (ell : ℝ) *
            ((s * R - 1 / Fintype.card ι) / ((s : ℝ) - ell + 1)) *
              Fintype.card ι := hdesign
    _ = (ell : ℝ) * ((Module.finrank F C : ℝ) - 1) /
        ((s : ℝ) - ell + 1) := by
      field_simp [hn_pos.ne', hden_pos.ne']
      nlinarith [hrate_id]

open scoped BigOperators in
theorem subspaceDesign_kernelSum_le_profile
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] {s : ℕ} {τ : ℕ → ℝ}
    (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C)
    (A : Submodule F (ι → Fin s → F)) (hAC : A ≤ C) :
    (∑ i : ι, (Module.finrank F
      ↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) ≤
      (Fintype.card ι : ℝ) * (Module.finrank F A : ℝ) *
        τ (Module.finrank F A) := by
  have h := hdesign (Module.finrank F A) A hAC le_rfl
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn] at h
  calc
    (∑ i : ι, (Module.finrank F
      ↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) ≤
        (Module.finrank F A : ℝ) * τ (Module.finrank F A) *
          Fintype.card ι := h
    _ = (Fintype.card ι : ℝ) * (Module.finrank F A : ℝ) *
        τ (Module.finrank F A) := by ring

open scoped Pointwise in
theorem vectorSpan_agreementEdges_le_inf_ker
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Field F] [DecidableEq F]
    (s : ℕ) (T : Finset (ι → Fin s → F)) (f : ι → Fin s → F) (i : ι) :
    vectorSpan F (agreementEdges T f i : Set (ι → Fin s → F)) ≤
      vectorSpan F (T : Set (ι → Fin s → F)) ⊓
        LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) := by
  classical
  apply le_inf
  · apply vectorSpan_mono
    intro c hc
    exact (Finset.mem_filter.mp hc).1
  · rw [vectorSpan_def, Submodule.span_le]
    intro z hz
    rcases Set.mem_vsub.mp hz with ⟨c₁, hc₁, c₂, hc₂, heq⟩
    unfold agreementEdges at hc₁ hc₂
    have h₁ : c₁ i = f i := (Finset.mem_filter.mp hc₁).2
    have h₂ : c₂ i = f i := (Finset.mem_filter.mp hc₂).2
    rw [← heq]
    change c₁ i - c₂ i = 0
    rw [h₁, h₂, sub_self]

theorem vectorSpan_finset_le_submodule_of_subset
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [DecidableEq V] (S : Finset V) (C : Submodule F V)
    (hSC : ∀ x ∈ S, x ∈ C) :
    vectorSpan F (S : Set V) ≤ C := by
  classical
  by_cases hS : S = ∅
  · subst S
    rw [Finset.coe_empty, vectorSpan_empty]
    exact bot_le
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    rw [vectorSpan_eq_span_vsub_finset_right_ne (k := F) hp, Submodule.span_le]
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    change x - p ∈ C
    exact C.sub_mem (hSC x (Finset.mem_of_mem_erase hx)) (hSC p hp)

open scoped BigOperators in
theorem agreementWeight_lt_of_subspaceDesign
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [DecidableEq F]
    {s : ℕ} {τ : ℕ → ℝ} {C : Submodule F (ι → Fin s → F)}
    (hdesign : IsSubspaceDesign s τ C)
    (d : ℕ) (t : ℝ)
    (hτ : ∀ r : ℕ, 1 ≤ r → r ≤ d → τ r < t)
    (y : ι → Fin s → F) (T : Finset (ι → Fin s → F))
    (hcard2 : 2 ≤ T.card) (hcardd : T.card ≤ d + 1)
    (hTC : ∀ c ∈ T, c ∈ C) :
    (agreementWeight y T : ℝ) <
      (Fintype.card ι : ℝ) * (T.card - 1) * t := by
  classical
  by_contra hnot
  let E : ι → Finset (ι → Fin s → F) := agreementEdges T y
  let κ : ℝ := (Fintype.card ι : ℝ) * t
  have hge : (Fintype.card ι : ℝ) * (T.card - 1) * t ≤
      (agreementWeight y T : ℝ) := le_of_not_gt hnot
  have hcastT : ((T.card - 1 : ℕ) : ℝ) = (T.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ T.card)]
    norm_num
  have hheavyT : (geometricEdgeWeight T : ℝ) * κ ≤
      (geometricTotalWeight E T : ℝ) := by
    calc
      (geometricEdgeWeight T : ℝ) * κ =
          (Fintype.card ι : ℝ) * ((T.card : ℝ) - 1) * t := by
        unfold geometricEdgeWeight κ
        rw [hcastT]
        ring
      _ ≤ (agreementWeight y T : ℝ) := hge
      _ = (geometricTotalWeight E T : ℝ) := by
        exact_mod_cast agreementWeight_eq_geometricTotalWeight y T
  obtain ⟨U, hUT, hU2, hUheavy, hUmin⟩ :=
    exists_minimal_linear_heavy_subset
      (fun X => (geometricTotalWeight E X : ℝ)) κ T hcard2 hheavyT
  have hUne : U.Nonempty :=
    Finset.card_pos.mp (show 0 < U.card by omega)
  obtain ⟨P⟩ := exists_geometricRankPartition (F := F) U hUne
  have hlower := minimal_linear_heavy_affineRank_lower_of_partition
    P E κ hU2 hUheavy hUmin
  have hinter : ∀ i : ι, E i ∩ U = agreementEdges U y i := by
    intro i
    exact agreementEdges_inter_subset T U y i hUT
  simp_rw [hinter] at hlower
  let A : Submodule F (ι → Fin s → F) :=
    vectorSpan F (↑U : Set (ι → Fin s → F))
  have hAC : A ≤ C := by
    apply vectorSpan_finset_le_submodule_of_subset
    intro c hc
    exact hTC c (hUT hc)
  letI : FiniteDimensional F A :=
    finiteDimensional_vectorSpan_of_finite F U.finite_toSet
  have hsum :
      (∑ i : ι, (geometricAffineRank (F := F) (agreementEdges U y i) : ℝ)) ≤
        ∑ i : ι, (Module.finrank F
          ↥(A ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have hspan := vectorSpan_agreementEdges_le_inf_ker s U y i
    change (Module.finrank F (vectorSpan F
      (agreementEdges U y i : Set (ι → Fin s → F))) : ℝ) ≤ _
    exact_mod_cast Submodule.finrank_mono hspan
  have hupper := subspaceDesign_kernelSum_le_profile C hdesign A hAC
  change (∑ i : ι, (Module.finrank F
      ↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) : ℝ)) ≤
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
        τ (geometricAffineRank (F := F) U) at hupper
  have hrpos : 1 ≤ geometricAffineRank (F := F) U :=
    geometricAffineRank_pos_of_two_le_card U hU2
  have hrle_weight := geometricAffineRank_le_edgeWeight (F := F) U
  have hcardU : U.card ≤ T.card := Finset.card_le_card hUT
  have hrle : geometricAffineRank (F := F) U ≤ d := by
    unfold geometricEdgeWeight at hrle_weight
    omega
  have hτr := hτ (geometricAffineRank (F := F) U) hrpos hrle
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hrreal : (0 : ℝ) < geometricAffineRank (F := F) U := by
    exact_mod_cast hrpos
  have hnr : (0 : ℝ) < (Fintype.card ι : ℝ) *
      (geometricAffineRank (F := F) U : ℝ) := mul_pos hn hrreal
  have hstrict :
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
          τ (geometricAffineRank (F := F) U) <
        (geometricAffineRank (F := F) U : ℝ) * κ := by
    calc
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
          τ (geometricAffineRank (F := F) U) <
          ((Fintype.card ι : ℝ) *
            (geometricAffineRank (F := F) U : ℝ)) * t :=
        mul_lt_mul_of_pos_left hτr hnr
      _ = (geometricAffineRank (F := F) U : ℝ) * κ := by
        unfold κ
        ring
  have hchain : (geometricAffineRank (F := F) U : ℝ) * κ ≤
      (Fintype.card ι : ℝ) * (geometricAffineRank (F := F) U : ℝ) *
        τ (geometricAffineRank (F := F) U) :=
    hlower.trans (hsum.trans hupper)
  exact (not_lt_of_ge hchain) hstrict

theorem agreementWeight_lt_of_subspaceDesign_rate
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [DecidableEq F]
    {s : ℕ} {R : ℝ} {C : Submodule F (ι → Fin s → F)}
    (hR : (LinearCode.alphabetRate C : ℝ) = R)
    (hdesign : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (d : ℕ) (hdpos : 1 ≤ d) (hds : d ≤ s)
    (y : ι → Fin s → F) (T : Finset (ι → Fin s → F))
    (hcard : T.card = d + 1) (hTC : ∀ c ∈ T, c ∈ C) :
    (agreementWeight y T : ℝ) <
      (Fintype.card ι : ℝ) * d *
        (s * R / ((s : ℝ) - d + 1)) := by
  have hR0 : (0 : ℝ) ≤ R := by
    rw [← hR]
    positivity
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hτ : ∀ r : ℕ, 1 ≤ r → r ≤ d →
      (if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) <
        s * R / ((s : ℝ) - d + 1) := by
    intro r hrpos hrle
    have hrs : r ≤ s := hrle.trans hds
    rw [if_pos (Finset.mem_Icc.mpr ⟨hrpos, hrs⟩)]
    have hdenr : (0 : ℝ) < (s : ℝ) - r + 1 := by
      exact_mod_cast (show 0 < s - r + 1 by omega)
    have hdend : (0 : ℝ) < (s : ℝ) - d + 1 := by
      exact_mod_cast (show 0 < s - d + 1 by omega)
    have hinv : (0 : ℝ) < 1 / Fintype.card ι := one_div_pos.mpr hn
    have hnum : (s : ℝ) * R - 1 / Fintype.card ι < (s : ℝ) * R := by
      linarith
    have hfirst :
        ((s : ℝ) * R - 1 / Fintype.card ι) / ((s : ℝ) - r + 1) <
          (s : ℝ) * R / ((s : ℝ) - r + 1) :=
      div_lt_div_of_pos_right hnum hdenr
    have hdenle : (s : ℝ) - d + 1 ≤ (s : ℝ) - r + 1 := by
      exact_mod_cast (show s - d + 1 ≤ s - r + 1 by omega)
    have hnum0 : (0 : ℝ) ≤ (s : ℝ) * R :=
      mul_nonneg (Nat.cast_nonneg s) hR0
    have hsecond :
        (s : ℝ) * R / ((s : ℝ) - r + 1) ≤
          (s : ℝ) * R / ((s : ℝ) - d + 1) :=
      div_le_div_of_nonneg_left hnum0 hdend hdenle
    exact hfirst.trans_le hsecond
  have hcard2 : 2 ≤ T.card := by omega
  have hcardd : T.card ≤ d + 1 := by omega
  have hgen := agreementWeight_lt_of_subspaceDesign hdesign d
    (s * R / ((s : ℝ) - d + 1)) hτ y T hcard2 hcardd hTC
  rw [hcard] at hgen
  have hcastd : ((d + 1 : ℕ) : ℝ) - 1 = (d : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hcastd] at hgen
  exact hgen


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
theorem subspaceDesign_lambda_le {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (_hR : (LinearCode.alphabetRate C : ℝ) = R)
    (_h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (L : ℕ) (_hL_pos : 1 ≤ L) (_hL_le : L ≤ s) :
    Lambda ((C : Set (ι → Fin s → F)))
        ((L : ℝ) / (L + 1) * (1 - s * R / (s - L + 1))) ≤ (L : ℕ∞) := by
  classical
  letI : DecidableEq (Fin s → F) := Classical.decEq _
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  by_contra hTL
  have hbig : L + 1 ≤ T.card := by omega
  obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hbig
  have hUC : ∀ c ∈ U, c ∈ C := by
    intro c hc
    exact (hT c (hUT hc)).1
  have hUclose : ∀ c ∈ U,
      (Code.relHammingDist y c : ℝ) ≤
        (L : ℝ) / (L + 1) * (1 - s * R / ((s : ℝ) - L + 1)) := by
    intro c hc
    have hcball := (hT c (hUT hc)).2
    simpa only [Code.relHammingBall, Set.mem_setOf_eq] using hcball
  have hupper0 := agreementWeight_lt_of_subspaceDesign_rate
    _hR _h L _hL_pos _hL_le y U hUcard hUC
  have hupper : (agreementWeight y U : ℝ) <
      (Fintype.card ι : ℝ) * L * (s * R / ((s : ℝ) - L + 1)) := by
    convert hupper0 using 1 <;> congr
  have hlower : (Fintype.card ι : ℝ) * L *
      (s * R / ((s : ℝ) - L + 1)) ≤ (agreementWeight y U : ℝ) := by
    have hn : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos
    have hdist : ∀ c ∈ U, (hammingDist y c : ℝ) ≤
        (Fintype.card ι : ℝ) *
          ((L : ℝ) / (L + 1) * (1 - s * R / ((s : ℝ) - L + 1))) := by
      intro c hc
      have hclose := hUclose c hc
      unfold Code.relHammingDist at hclose
      simp only [NNRat.cast_div, NNRat.cast_natCast] at hclose
      rw [div_le_iff₀ hn] at hclose
      simpa only [mul_comm] using hclose
    have hagree_dist : ∀ c : ι → Fin s → F,
        (Finset.univ.filter (fun i => c i = y i)).card + hammingDist y c =
          Fintype.card ι := by
      intro c
      unfold hammingDist
      have hfilter : Finset.univ.filter (fun i => y i ≠ c i) =
          Finset.univ.filter (fun i => ¬ c i = y i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ne_comm
      rw [hfilter]
      exact Finset.filter_card_add_filter_neg_card_eq_card _
    have hagree_lower : ∀ c ∈ U,
        (Fintype.card ι : ℝ) *
            (1 - (L : ℝ) / (L + 1) *
              (1 - s * R / ((s : ℝ) - L + 1))) ≤
          ((Finset.univ.filter (fun i => c i = y i)).card : ℝ) := by
      intro c hc
      have heq : ((Finset.univ.filter (fun i => c i = y i)).card : ℝ) +
          (hammingDist y c : ℝ) = Fintype.card ι := by
        exact_mod_cast hagree_dist c
      nlinarith [hdist c hc]
    have hsum_lower : (U.card : ℝ) *
          ((Fintype.card ι : ℝ) *
            (1 - (L : ℝ) / (L + 1) *
              (1 - s * R / ((s : ℝ) - L + 1)))) ≤
        ∑ c ∈ U, ((Finset.univ.filter (fun i => c i = y i)).card : ℝ) := by
      calc
        (U.card : ℝ) * ((Fintype.card ι : ℝ) *
            (1 - (L : ℝ) / (L + 1) *
              (1 - s * R / ((s : ℝ) - L + 1)))) =
            ∑ c ∈ U, ((Fintype.card ι : ℝ) *
              (1 - (L : ℝ) / (L + 1) *
                (1 - s * R / ((s : ℝ) - L + 1)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ c ∈ U, ((Finset.univ.filter (fun i => c i = y i)).card : ℝ) :=
          Finset.sum_le_sum fun c hc => hagree_lower c hc
    have hdouble : (∑ i : ι, ((U.filter (fun c => c i = y i)).card : ℝ)) =
        ∑ c ∈ U, ((Finset.univ.filter (fun i => c i = y i)).card : ℝ) := by
      simp_rw [Finset.natCast_card_filter]
      rw [Finset.sum_comm]
    have hweight_nat : (∑ i : ι, (U.filter (fun c => c i = y i)).card) ≤
        agreementWeight y U + Fintype.card ι := by
      unfold agreementWeight
      calc
        (∑ i : ι, (U.filter (fun c => c i = y i)).card) ≤
            ∑ i : ι, ((U.filter (fun c => c i = y i)).card - 1 + 1) := by
          apply Finset.sum_le_sum
          intro i _
          omega
        _ = (∑ i : ι, ((U.filter (fun c => c i = y i)).card - 1)) +
              ∑ _i : ι, 1 := by
          rw [Finset.sum_add_distrib]
        _ = (∑ i : ι, ((U.filter (fun c => c i = y i)).card - 1)) +
              Fintype.card ι := by
          simp
    have hweight : (∑ i : ι, ((U.filter (fun c => c i = y i)).card : ℝ)) ≤
        (agreementWeight y U : ℝ) + Fintype.card ι := by
      exact_mod_cast hweight_nat
    have hchain : (U.card : ℝ) *
          ((Fintype.card ι : ℝ) *
            (1 - (L : ℝ) / (L + 1) *
              (1 - s * R / ((s : ℝ) - L + 1)))) ≤
        (agreementWeight y U : ℝ) + Fintype.card ι := by
      calc
        _ ≤ ∑ c ∈ U, ((Finset.univ.filter (fun i => c i = y i)).card : ℝ) :=
          hsum_lower
        _ = ∑ i : ι, ((U.filter (fun c => c i = y i)).card : ℝ) := hdouble.symm
        _ ≤ (agreementWeight y U : ℝ) + Fintype.card ι := hweight
    have halgebra : (U.card : ℝ) *
          ((Fintype.card ι : ℝ) *
            (1 - (L : ℝ) / (L + 1) *
              (1 - s * R / ((s : ℝ) - L + 1)))) =
        (Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) * L *
            (s * R / ((s : ℝ) - L + 1)) := by
      rw [hUcard]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hL1 : (L : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [halgebra] at hchain
    linarith
  exact (not_lt_of_ge hlower) hupper -- external admit: [CZ25, Theorem B.5].

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

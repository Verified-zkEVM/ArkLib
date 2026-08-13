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

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Union
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Finset.Image
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

structure AGLBarrierParameters (ℓ n radius boosted : ℕ) where
  aFamily : ℕ
  aUnion : ℕ
  dZero : ℕ
  dOne : ℕ
  W : ℕ
  center_block_bound : dZero + ℓ * dOne ≤ radius
  other_codeword_bound : n - dZero - dOne - aFamily ≤ radius
  repeated_codeword_contradiction : n - aUnion < boosted

def AGLBinomialRatioEstimate : Prop :=
  ∀ (ℓ M : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < p → p < 1 →
    Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
    (3 * p ^ ℓ / 4) * Nat.choose M ℓ ≤
      Nat.choose (Nat.floor (p * M)) ℓ

def AGLChooseSmoothingBound : Prop :=
  ∀ (ℓ n total : ℕ), 0 < n → 0 < ℓ →
    ∀ a : Fin n → ℕ, total ≤ ∑ i, a i →
      n * Nat.choose (total / n) ℓ ≤ ∑ i, Nat.choose (a i) ℓ

def AGLCloseCodewordsRelEqDistSet : Prop :=
  ∀ {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq A]
    (C : Set (ι → A)) (p : ℝ), 0 ≤ p → ∀ y : ι → A,
      closeCodewordsRel C y p =
        {c : ι → A | c ∈ C ∧
          hammingDist c y ≤ Nat.floor (p * Fintype.card ι)}

def AGLCommonDisagreementIntersection : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (M : ℕ), Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
      ∀ S : Fin M → Finset ι,
        (∀ j, Nat.floor (p * Fintype.card ι) < (S j).card) →
        ∃ J : Finset (Fin M), J.card = ℓ ∧
          Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
            ({i : ι | ∀ j, j ∈ J → i ∈ S j} : Set ι).ncard

structure AGLCoordinateBlocks (ι : Type) [DecidableEq ι]
    (ℓ dZero dOne : ℕ) where
  zero : Finset ι
  other : Fin ℓ → Finset ι
  card_zero : zero.card = dZero
  card_other : ∀ j, (other j).card = dOne
  zero_disjoint : ∀ j, Disjoint zero (other j)
  other_disjoint : ∀ i j, i ≠ j → Disjoint (other i) (other j)

def AGLCoordinateBlocksExistence : Prop :=
  ∀ (ℓ dZero dOne : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
      dZero + ℓ * dOne ≤ Fintype.card ι →
      ∃ blocks : AGLCoordinateBlocks ι ℓ dZero dOne, True

def AGLCoordinateBlocksUsedCard : Prop :=
  ∀ (ℓ dZero dOne : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (blocks : AGLCoordinateBlocks ι ℓ dZero dOne),
      let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
      used.card = dZero + ℓ * dOne

def AGLDisjointEqualBlocks : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (k t : ℕ), k * t ≤ S.card →
      ∃ blocks : Fin k → Finset ι,
        (∀ j, blocks j ⊆ S) ∧
        (∀ j, (blocks j).card = t) ∧
        ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)

def AGLDistinctAlternativesOfBoundedFibers : Prop :=
  ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (W ℓ : ℕ), 0 < W →
      W * ℓ ≤ s.card →
      (∀ y, (s.filter fun x => f x = y).card < W) →
      ℓ ≤ (s.image f).card

def AGLIncidenceDoubleCount : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ℓ : ℕ) (S : κ → Finset ι),
    let incidence : ι → ℕ := fun i => (Finset.univ.filter fun j => i ∈ S j).card
    let common : Finset κ → Finset ι := fun J =>
      Finset.univ.filter fun i => ∀ j ∈ J, i ∈ S j
    ∑ i, Nat.choose (incidence i) ℓ =
      ∑ J ∈ Finset.univ.powersetCard ℓ, (common J).card

def AGLIncidenceMomentLower : Prop :=
  ∀ (ℓ M n : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < n → 0 < p → p < 1 →
    Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
    ∀ a : Fin n → ℕ,
      p * M * n ≤ ∑ i, (a i : ℝ) →
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
        ∑ i, (Nat.choose (a i) ℓ : ℝ)

def AGLIncidencePowerGap : Prop :=
  ∀ (ℓ M : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < p →
    Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
    (3 * p ^ ℓ / 4) * (M : ℝ) ^ ℓ ≤
      (p * M - (ℓ - 1)) ^ ℓ

def AGLIncidenceSumDoubleCount : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : κ → Finset ι),
    ∑ i, (Finset.univ.filter fun j => i ∈ S j).card =
      ∑ j, (S j).card

structure AGLLargeUnionFamily (ι : Type) [DecidableEq ι]
    (W aFamily aUnion : ℕ) where
  sets : Finset (Finset ι)
  card_each : ∀ A ∈ sets, A.card = aFamily
  large_union : ∀ T : Finset (Finset ι), T ⊆ sets → T.card = W →
    aUnion ≤ (T.biUnion id).card

def AGLLargeUnionExistence : Prop :=
  ∀ (α β : ℝ), 0 < α → α < β → β < 1 →
    ∃ W : ℕ, 0 < W ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m →
        ∃ family : AGLLargeUnionFamily (Fin m) W
          (Nat.floor (α * m)) (Nat.ceil (β * m)),
          (2 : ℝ) ^ (γ * m) ≤ family.sets.card

def AGLLargeUnionFamilyResize : Prop :=
  ∀ (W a₀ b₀ a₁ b₁ : ℕ), 0 < W → a₀ ≤ a₁ → a₁ < b₀ → b₁ ≤ b₀ →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι], a₁ ≤ Fintype.card ι →
      ∀ source : AGLLargeUnionFamily ι W a₀ b₀,
        ∃ target : AGLLargeUnionFamily ι W a₁ b₁,
          source.sets.card ≤ W * target.sets.card

def AGLLargeUnionFamilyTransport : Prop :=
  ∀ (ℓ dZero dOne W aFamily aUnion : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (blocks : AGLCoordinateBlocks ι ℓ dZero dOne),
      let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
      ∀ (m : ℕ), m = Fintype.card ι - used.card →
        ∀ source : AGLLargeUnionFamily (Fin m) W aFamily aUnion,
          ∃ target : AGLLargeUnionFamily ι W aFamily aUnion,
            target.sets.card = source.sets.card ∧
            ∀ S ∈ target.sets, Disjoint S blocks.zero ∧
              ∀ j, Disjoint S (blocks.other j)

def AGLRestrictionRangeBound : Prop :=
  ∀ {ι A : Type} [Fintype ι] [Fintype A]
    (C : Set (ι → A)) (S : Finset ι),
      (Set.range (fun c : C => fun i : S => c.1 i.1)).ncard ≤
        Fintype.card A ^ S.card

structure AGLRoundedBarrierData where
  radius : ℕ
  boosted : ℕ
  dZero : ℕ
  dOne : ℕ
  used : ℕ
  unused : ℕ
  aFamily : ℕ
  aUnion : ℕ

def AGLSeparated {ι F : Type} [Fintype ι] [DecidableEq F]
    (D : Set (ι → F)) (d : ℕ) : Prop :=
  ∀ ⦃u : ι → F⦄, u ∈ D → ∀ ⦃v : ι → F⦄, v ∈ D → u ≠ v → d ≤ hammingDist u v

def AGLDeterministicPigeonholeBound : Prop :=
  ∀ (ℓ n radius boosted : ℕ), 2 ≤ ℓ → 0 < n →
    ∀ {ι A : Type} [Fintype ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
      (C : Set (ι → A)), 2 ≤ Fintype.card A →
      Fintype.card ι = n → C.Finite →
      ∀ (params : AGLBarrierParameters ℓ n radius boosted), 0 < params.W →
      ∀ (blocks : AGLCoordinateBlocks ι ℓ params.dZero params.dOne)
        (family : AGLLargeUnionFamily ι params.W params.aFamily params.aUnion),
        (∀ S ∈ family.sets, Disjoint S blocks.zero ∧
          ∀ j, Disjoint S (blocks.other j)) →
        AGLSeparated C boosted →
        2 * Fintype.card A ^ params.aFamily ≤ C.ncard →
        Lambda C ((radius : ℝ) / n) ≤ (ℓ : ℕ∞) →
        family.sets.card ≤
          2 * params.W * ℓ * Fintype.card A ^ params.dZero

def AGLGreedySeparatedExtraction : Prop :=
  ∀ {ι A : Type} [Fintype ι] [DecidableEq A]
    (C : Set (ι → A)) (d B : ℕ), C.Finite →
    (∀ c ∈ C,
      ({x : ι → A | x ∈ C ∧ hammingDist c x ≤ d} : Set (ι → A)).ncard ≤ B) →
    ∃ D : Set (ι → A), D ⊆ C ∧ D.Finite ∧ AGLSeparated D (d + 1) ∧
      C.ncard ≤ B * D.ncard

def AGLShiftedIncidenceMeanLower : Prop :=
  ∀ (ℓ M n : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < n →
    ∀ a : Fin n → ℕ,
      p * M * n ≤ ∑ i, (a i : ℝ) →
      p * M - (ℓ - 1) ≤
        (∑ i, ((a i + 1 - ℓ : ℕ) : ℝ)) / n

def AGLSparseChooseRatioBound : Prop :=
  ∀ (m a b : ℕ), a ≤ b - 1 → b - 1 ≤ m →
    ((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ≤
      ((((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) ^ a)

def AGLSparseLargeUnionExistence : Prop :=
  ∀ (α β : ℝ), 0 < α → α < β → α + β < 1 →
    ∃ W : ℕ, 0 < W ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m →
        ∃ family : AGLLargeUnionFamily (Fin m) W
          (Nat.floor (α * m)) (Nat.ceil (β * m)),
          (2 : ℝ) ^ (γ * m) ≤ family.sets.card

def AGLSparseLargeUnionNumerics : Prop :=
  ∀ (α β : ℝ), 0 < α → α < β → α + β < 1 →
    ∃ W : ℕ, 0 < W ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m →
        let a := Nat.floor (α * m)
        let b := Nat.ceil (β * m)
        let T := 2 ^ (m / W)
        a < b ∧ b ≤ m ∧ W ≤ T ∧
          Nat.choose T W * Nat.choose m (b - 1) *
              Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) <
            Nat.choose m a ^ T ∧
          W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤ T

def AGLSparseLargeUnionExistenceOfNumerics : Prop :=
  AGLSparseLargeUnionNumerics → AGLSparseLargeUnionExistence

def AGLUnusedCoordinatesEquivFin : Prop :=
  ∀ (ℓ dZero dOne : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (blocks : AGLCoordinateBlocks ι ℓ dZero dOne),
      let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
      Nonempty (Fin (Fintype.card ι - used.card) ≃ {i : ι // i ∉ used})

theorem Lambda_mono_code
    {ι A : Type} [Fintype ι] {C D : Set (ι → A)}
    (hDC : D ⊆ C) (δ : ℝ) : Lambda D δ ≤ Lambda C δ := by
  unfold Lambda
  refine iSup_mono fun f => ?_
  exact Set.encard_mono fun c hc => ⟨hDC hc.1, hc.2⟩

theorem aglAlphabetCardGeRpowOfAlphaLeEta
    (α η : ℝ) (hη_pos : 0 < η) (hαη : α ≤ η)
    {A : Type} [Fintype A] (hcard : 2 ≤ Fintype.card A) :
    (Fintype.card A : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  have hexp : α / η ≤ 1 := (div_le_one hη_pos).2 hαη
  have hpow : (2 : ℝ) ^ (α / η) ≤ 2 := by
    calc
      (2 : ℝ) ^ (α / η) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 2 := by norm_num
  have hcardR : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hcard
  exact hpow.trans hcardR

noncomputable def aglBadIndexedFamilies
    (m a T W b : ℕ) :
    Finset (Fin T → {S : Finset (Fin m) // S.card = a}) := by
  classical
  exact Finset.univ.filter fun A =>
    ∃ J : Finset (Fin T), J.card = W ∧
      (J.biUnion fun j => (A j).1).card < b

def AGLBadIndexedFamiliesCardBound : Prop :=
  ∀ (m a T W b : ℕ), 0 < W → W ≤ T → 0 < b → b ≤ m → a < b →
    (aglBadIndexedFamilies m a T W b).card ≤
      Nat.choose T W * Nat.choose m (b - 1) *
        Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W)

def AGLBadIndexedFamiliesWitnessCover : Prop :=
  ∀ (m a T W b : ℕ), 0 < b → b ≤ m →
    ∀ A ∈ aglBadIndexedFamilies m a T W b,
      ∃ J : Finset (Fin T), ∃ U : Finset (Fin m),
        J.card = W ∧ U.card = b - 1 ∧
          ∀ j ∈ J, (A j).val ⊆ U

def AGLGoodIndexedFamilyToLargeUnionFamily : Prop :=
  ∀ (m a T W b : ℕ), 0 < W → a < b →
    ∀ A : Fin T → {S : Finset (Fin m) // S.card = a},
      A ∉ aglBadIndexedFamilies m a T W b →
      ∃ family : AGLLargeUnionFamily (Fin m) W a b,
        T ≤ W * family.sets.card

theorem aglBadIndexedFamiliesWitnessCover :
    AGLBadIndexedFamiliesWitnessCover := by
  classical
  intro m a T W b hb hbm A hA
  have hbad := (Finset.mem_filter.mp hA).2
  obtain ⟨J, hJcard, hUnion⟩ := hbad
  have hUnionCard :
      (J.biUnion fun j => (A j).val).card ≤ b - 1 := by
    omega
  have hbCard : b - 1 ≤ Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using (Nat.sub_le b 1).trans hbm
  obtain ⟨U, hUnionSub, hUcard⟩ :=
    Finset.exists_superset_card_eq hUnionCard hbCard
  refine ⟨J, U, hJcard, hUcard, ?_⟩
  intro j hj x hx
  apply hUnionSub
  exact Finset.mem_biUnion.mpr ⟨j, hj, hx⟩

noncomputable def aglBarrierAlphaDensity (R : ℝ) : ℝ := R / 2

theorem aglBarrierExponentContradiction
    (K M n : ℕ) (γ : ℝ) (hγ : 0 < γ) (hn : 0 < n)
    (hlower : (2 : ℝ) ^ (γ * n) ≤ M)
    (hupper : (M : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ ((γ / 4) * n))
    (habsorb : (K : ℝ) * (2 : ℝ) ^ ((γ / 4) * n) ≤
      (2 : ℝ) ^ ((γ / 2) * n)) : False := by
  have hchain : (2 : ℝ) ^ (γ * n) ≤
      (2 : ℝ) ^ ((γ / 2) * n) := hlower.trans (hupper.trans habsorb)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : (γ / 2) * (n : ℝ) < γ * n := by nlinarith
  have hstrict : (2 : ℝ) ^ ((γ / 2) * n) <
      (2 : ℝ) ^ (γ * n) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  exact (not_lt_of_ge hchain) hstrict

noncomputable def aglBarrierK (ℓ B : ℕ) : ℝ :=
  ((8 * (B + ℓ + 10) : ℕ) : ℝ)

theorem aglBarrierKSlack
    (ℓ B : ℕ) (hℓ : 2 ≤ ℓ) :
    (B : ℝ) + 4 + 1 / (ℓ : ℝ) ≤
      aglBarrierK ℓ B * (1 - 1 / (ℓ : ℝ)) - 1 := by
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hB : (0 : ℝ) ≤ B := by positivity
  unfold aglBarrierK
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp [ne_of_gt hℓpos]
  nlinarith

noncomputable def aglBoostedRadius (ℓ : ℕ) (p : ℝ) : ℝ :=
  p + p ^ ℓ / (2 * ℓ)

def AGLBalancedCenterConstruction : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
    ∀ {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
      (c : ι → A) (v : Fin ℓ → ι → A),
      (∀ j, hammingDist c (v j) ≤
        Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι)) →
      8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι →
      Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
        ({i : ι | ∀ j, c i ≠ v j i} : Set ι).ncard →
      ∃ y : ι → A,
        hammingDist c y ≤ Nat.floor (p * Fintype.card ι) ∧
        ∀ j, hammingDist (v j) y ≤ Nat.floor (p * Fintype.card ι)

def AGLLocalNeighborhoodBound : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {A : Type} [Fintype A] [DecidableEq A]
      (C : Set (ι → A)), Lambda C p ≤ (ℓ : ℕ∞) →
      8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι →
      ∀ c ∈ C,
        ({x : ι → A | x ∈ C ∧
          hammingDist c x ≤
            Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι)} : Set (ι → A)).ncard
          ≤ ℓ + Nat.ceil (4 * ((ℓ : ℝ) ^ 2) / p)

theorem aglBalancedCenterArithmetic
    (ℓ : ℕ) (p : ℝ) (n : ℕ) (hℓ : 2 ≤ ℓ) (hp : 0 < p) (hp_lt : p < 1)
    (hsize : 8 * (ℓ : ℝ) ≤ p ^ ℓ * n) :
    Nat.floor (p * n) ≤ Nat.floor (aglBoostedRadius ℓ p * n) ∧
      Nat.floor (aglBoostedRadius ℓ p * n) -
          (Nat.floor (aglBoostedRadius ℓ p * n) - Nat.floor (p * n)) =
        Nat.floor (p * n) ∧
      ℓ * (Nat.floor (aglBoostedRadius ℓ p * n) - Nat.floor (p * n)) ≤
        Nat.floor (p * n) ∧
      ℓ * (Nat.floor (aglBoostedRadius ℓ p * n) - Nat.floor (p * n)) ≤
        Nat.ceil ((3 * p ^ ℓ / 4) * n) := by
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hnR : (0 : ℝ) < n := by
    by_contra hn
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hn
    have hprod : p ^ ℓ * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hp.le ℓ) hnle
    have hleft : (0 : ℝ) < 8 * ℓ := by positivity
    nlinarith
  have hboost : p ≤ aglBoostedRadius ℓ p := by
    unfold aglBoostedRadius
    have hpow : 0 ≤ p ^ ℓ := by positivity
    have hden : (0 : ℝ) < 2 * ℓ := by positivity
    exact le_add_of_nonneg_right (div_nonneg hpow hden.le)
  have hboostPos : 0 < aglBoostedRadius ℓ p := hp.trans_le hboost
  have hmul : p * n ≤ aglBoostedRadius ℓ p * n :=
    mul_le_mul_of_nonneg_right hboost hnR.le
  have hrle : Nat.floor (p * n) ≤
      Nat.floor (aglBoostedRadius ℓ p * n) := Nat.floor_mono hmul
  refine ⟨hrle, ?_, ?_, ?_⟩
  · omega
  · let r := Nat.floor (p * n)
    let r' := Nat.floor (aglBoostedRadius ℓ p * n)
    let t := r' - r
    have htcast : (t : ℝ) = (r' : ℝ) - r := Nat.cast_sub hrle
    have hr'le : (r' : ℝ) ≤ aglBoostedRadius ℓ p * n :=
      Nat.floor_le (mul_nonneg hboostPos.le hnR.le)
    have hr'le' : (r' : ℝ) ≤ p * n + p ^ ℓ * n / (2 * ℓ) := by
      calc
        (r' : ℝ) ≤ aglBoostedRadius ℓ p * n := hr'le
        _ = p * n + p ^ ℓ * n / (2 * ℓ) := by
          unfold aglBoostedRadius
          ring
    have hrlt : p * n < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    have ht : (t : ℝ) ≤ p ^ ℓ * n / (2 * ℓ) + 1 := by
      rw [htcast]
      linarith
    have hmul_t : (ℓ : ℝ) * t ≤ p ^ ℓ * n / 2 + ℓ := by
      have h := mul_le_mul_of_nonneg_left ht hℓR.le
      calc
        (ℓ : ℝ) * t ≤ (ℓ : ℝ) * (p ^ ℓ * n / (2 * ℓ) + 1) := h
        _ = p ^ ℓ * n / 2 + ℓ := by
          field_simp [ne_of_gt hℓR]
    have hfive : (ℓ : ℝ) * t ≤ 5 * (p ^ ℓ * n) / 8 := by
      nlinarith
    have hpPowLt : p ^ ℓ < p :=
      pow_lt_self_of_lt_one₀ hp hp_lt (by omega)
    have hP_lt : p ^ ℓ * n < p * n :=
      mul_lt_mul_of_pos_right hpPowLt hnR
    have hlt : (ℓ : ℝ) * t < (r : ℝ) + 1 := by
      have hfive_lt : 5 * (p ^ ℓ * n) / 8 < p * n := by
        have hPnonneg : 0 ≤ p ^ ℓ * n := by positivity
        nlinarith
      nlinarith
    have hnat : ℓ * t < r + 1 := by exact_mod_cast hlt
    simpa only [r, r', t] using (Nat.lt_succ_iff.mp hnat)
  · let r := Nat.floor (p * n)
    let r' := Nat.floor (aglBoostedRadius ℓ p * n)
    let t := r' - r
    have htcast : (t : ℝ) = (r' : ℝ) - r := Nat.cast_sub hrle
    have hr'le : (r' : ℝ) ≤ aglBoostedRadius ℓ p * n :=
      Nat.floor_le (mul_nonneg hboostPos.le hnR.le)
    have hr'le' : (r' : ℝ) ≤ p * n + p ^ ℓ * n / (2 * ℓ) := by
      calc
        (r' : ℝ) ≤ aglBoostedRadius ℓ p * n := hr'le
        _ = p * n + p ^ ℓ * n / (2 * ℓ) := by
          unfold aglBoostedRadius
          ring
    have hrlt : p * n < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    have ht : (t : ℝ) ≤ p ^ ℓ * n / (2 * ℓ) + 1 := by
      rw [htcast]
      linarith
    have hmul_t : (ℓ : ℝ) * t ≤ p ^ ℓ * n / 2 + ℓ := by
      have h := mul_le_mul_of_nonneg_left ht hℓR.le
      calc
        (ℓ : ℝ) * t ≤ (ℓ : ℝ) * (p ^ ℓ * n / (2 * ℓ) + 1) := h
        _ = p ^ ℓ * n / 2 + ℓ := by
          field_simp [ne_of_gt hℓR]
    have hthree : (ℓ : ℝ) * t ≤ 3 * (p ^ ℓ * n) / 4 := by
      nlinarith
    have hceil : 3 * (p ^ ℓ * n) / 4 ≤
        (Nat.ceil ((3 * p ^ ℓ / 4) * n) : ℝ) := by
      calc
        3 * (p ^ ℓ * n) / 4 = (3 * p ^ ℓ / 4) * n := by ring
        _ ≤ (Nat.ceil ((3 * p ^ ℓ / 4) * n) : ℝ) :=
          Nat.le_ceil ((3 * p ^ ℓ / 4) * n)
    have hcast : ((ℓ * t : ℕ) : ℝ) ≤
        (Nat.ceil ((3 * p ^ ℓ / 4) * n) : ℝ) := by
      norm_num only [Nat.cast_mul]
      exact hthree.trans hceil
    exact_mod_cast hcast

theorem aglBoostedRadius_gt (ℓ : ℕ) (hℓ_pos : 0 < ℓ)
    (p : ℝ) (hp_pos : 0 < p) : p < aglBoostedRadius ℓ p := by
  unfold aglBoostedRadius
  have hpow : 0 < p ^ ℓ := pow_pos hp_pos ℓ
  have hden : (0 : ℝ) < 2 * ℓ := by positivity
  have hquot : 0 < p ^ ℓ / (2 * ℓ) := div_pos hpow hden
  linarith

theorem aglCeilLinearBound
    (K η : ℝ) (n : ℕ) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hone : 1 ≤ η * n) :
    (Nat.ceil (K * η * n) : ℝ) < (K + 1) * η * n := by
  have hnonneg : 0 ≤ K * η * (n : ℝ) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hunit : K * η * (n : ℝ) + 1 ≤ (K + 1) * η * n := by
    nlinarith
  exact hceil.trans_le hunit

theorem aglChooseDistinctImages
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (f : X → Y) (k : ℕ)
    (hcard : k ≤ (s.image f).card) :
    ∃ sel : Fin k → X, (∀ j, sel j ∈ s) ∧
      Function.Injective (fun j => f (sel j)) := by
  classical
  obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin k ≃ t := (Finset.equivFinOfCardEq htcard).symm
  have hpre : ∀ y : t, ∃ x ∈ s, f x = y.1 := by
    intro y
    exact Finset.mem_image.mp (htsub y.2)
  let pre : t → X := fun y => Classical.choose (hpre y)
  have hpre_mem : ∀ y : t, pre y ∈ s := by
    intro y
    exact (Classical.choose_spec (hpre y)).1
  have hpre_eq : ∀ y : t, f (pre y) = y.1 := by
    intro y
    exact (Classical.choose_spec (hpre y)).2
  let sel : Fin k → X := fun j => pre (e j)
  refine ⟨sel, ?_, ?_⟩
  · intro j
    exact hpre_mem (e j)
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    have hi := hpre_eq (e i)
    have hj := hpre_eq (e j)
    dsimp only [sel] at hij
    exact hi.symm.trans (hij.trans hj)

theorem aglCloseCodewordsRelEqDistSet : AGLCloseCodewordsRelEqDistSet := by
  classical
  intro ι A _ _ _ C p hp y
  ext c
  simp only [closeCodewordsRel, Code.relHammingBall, Set.mem_setOf_eq,
    Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
  refine and_congr_right (fun _ => ?_)
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  rw [div_le_iff₀ (by exact_mod_cast hn), ← Nat.le_floor_iff (by positivity)]
  rw [hammingDist_comm c y]
  constructor <;> intro h <;> convert h using 2

noncomputable def aglConstrainedIndexedFamilies
    (m a T : ℕ) (J : Finset (Fin T)) (U : Finset (Fin m)) :
    Finset (Fin T → {S : Finset (Fin m) // S.card = a}) := by
  classical
  exact Finset.univ.filter fun A => ∀ j ∈ J, (A j).1 ⊆ U

def AGLBadIndexedFamiliesSubsetCover : Prop :=
  ∀ (m a T W b : ℕ), 0 < b → b ≤ m →
    aglBadIndexedFamilies m a T W b ⊆
      (Finset.univ.powersetCard W).biUnion fun J =>
        (Finset.univ.powersetCard (b - 1)).biUnion fun U =>
          aglConstrainedIndexedFamilies m a T J U

def AGLConstrainedIndexedFamiliesCard : Prop :=
  ∀ (m a T W b : ℕ) (J : Finset (Fin T)) (U : Finset (Fin m)),
    J.card = W → U.card = b - 1 →
    (aglConstrainedIndexedFamilies m a T J U).card =
      Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W)

theorem aglBadIndexedFamiliesSubsetCover :
    AGLBadIndexedFamiliesSubsetCover := by
  classical
  intro m a T W b hb hbm A hA
  obtain ⟨J, U, hJcard, hUcard, hconstrained⟩ :=
    aglBadIndexedFamiliesWitnessCover m a T W b hb hbm A hA
  apply Finset.mem_biUnion.mpr
  refine ⟨J, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ J, hJcard⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨U, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ U, hUcard⟩
    · simp only [aglConstrainedIndexedFamilies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hconstrained

theorem aglCoordinateBlocksExists : AGLCoordinateBlocksExistence := by
  classical
  intro ℓ dZero dOne ι _ _ htotal
  let total := dZero + ℓ * dOne
  let e : Fin total ↪ ι := Classical.choice
    (Function.Embedding.nonempty_of_card_le (α := Fin total) (β := ι) (by
      simpa only [Fintype.card_fin] using htotal))
  let z : Fin dZero ↪ Fin total :=
    ⟨fun k => ⟨k, by dsimp only [total]; omega⟩,
      fun a b hab => Fin.ext (congrArg (fun x : Fin total => x.val) hab)⟩
  let o : Fin ℓ → Fin dOne ↪ Fin total := fun j =>
    ⟨fun k => ⟨dZero + j * dOne + k, by
        have hj := j.isLt
        have hk := k.isLt
        dsimp only [total]
        have hmul : (j.val + 1) * dOne ≤ ℓ * dOne :=
          Nat.mul_le_mul_right dOne (Nat.succ_le_iff.mpr hj)
        rw [Nat.add_mul] at hmul
        omega⟩,
      fun a b hab => Fin.ext (by
        have hv := congrArg (fun x : Fin total => x.val) hab
        simpa using hv)⟩
  let zero : Finset ι := Finset.univ.map (z.trans e)
  let other : Fin ℓ → Finset ι := fun j => Finset.univ.map ((o j).trans e)
  refine ⟨{
    zero := zero
    other := other
    card_zero := ?_
    card_other := ?_
    zero_disjoint := ?_
    other_disjoint := ?_ }, trivial⟩
  · simp only [zero, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro j
    simp only [other, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro j
    rw [Finset.disjoint_left]
    intro x hxz hxo
    rcases Finset.mem_map.mp hxz with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxo with ⟨b, hb, hbx⟩
    have heq : z a = o j b := e.injective (hax.trans hbx.symm)
    have hv := congrArg Fin.val heq
    change a.val = dZero + j.val * dOne + b.val at hv
    have ha_lt := a.isLt
    omega
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_map.mp hxi with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxj with ⟨b, hb, hbx⟩
    have heq : o i a = o j b := e.injective (hax.trans hbx.symm)
    have hv := congrArg Fin.val heq
    change dZero + i.val * dOne + a.val = dZero + j.val * dOne + b.val at hv
    have hvne : i.val ≠ j.val := by
      intro h
      apply hij
      exact Fin.ext h
    rcases lt_or_gt_of_ne hvne with hijlt | hjilt
    · have hmul : (i.val + 1) * dOne ≤ j.val * dOne :=
        Nat.mul_le_mul_right dOne (Nat.succ_le_iff.mpr hijlt)
      have hia : i.val * dOne + a.val < (i.val + 1) * dOne := by
        calc
          i.val * dOne + a.val < i.val * dOne + dOne :=
            Nat.add_lt_add_left a.isLt _
          _ = (i.val + 1) * dOne := by rw [Nat.add_mul, one_mul]
      have hcore : i.val * dOne + a.val < j.val * dOne + b.val :=
        hia.trans_le (hmul.trans (Nat.le_add_right _ _))
      have hlt := Nat.add_lt_add_left hcore dZero
      have hv' : dZero + (i.val * dOne + a.val) =
          dZero + (j.val * dOne + b.val) := by
        simpa only [Nat.add_assoc] using hv
      exact (Nat.ne_of_lt hlt) hv'
    · have hmul : (j.val + 1) * dOne ≤ i.val * dOne :=
        Nat.mul_le_mul_right dOne (Nat.succ_le_iff.mpr hjilt)
      have hjb : j.val * dOne + b.val < (j.val + 1) * dOne := by
        calc
          j.val * dOne + b.val < j.val * dOne + dOne :=
            Nat.add_lt_add_left b.isLt _
          _ = (j.val + 1) * dOne := by rw [Nat.add_mul, one_mul]
      have hcore : j.val * dOne + b.val < i.val * dOne + a.val :=
        hjb.trans_le (hmul.trans (Nat.le_add_right _ _))
      have hlt := Nat.add_lt_add_left hcore dZero
      have hv' : dZero + (j.val * dOne + b.val) =
          dZero + (i.val * dOne + a.val) := by
        simpa only [Nat.add_assoc] using hv.symm
      exact (Nat.ne_of_lt hlt) hv'

theorem aglCoordinateBlocksUsedCard : AGLCoordinateBlocksUsedCard := by
  classical
  intro ℓ dZero dOne ι _ _ blocks
  dsimp
  have hpair :
      ((Finset.univ : Finset (Fin ℓ)) : Set (Fin ℓ)).PairwiseDisjoint blocks.other := by
    intro i hi j hj hij
    exact blocks.other_disjoint i j hij
  have hzero : Disjoint blocks.zero (Finset.univ.biUnion blocks.other) := by
    rw [Finset.disjoint_left]
    intro x hx hxu
    simp only [Finset.mem_biUnion] at hxu
    obtain ⟨j, hj, hxj⟩ := hxu
    exact (Finset.disjoint_left.mp (blocks.zero_disjoint j)) hx hxj
  rw [Finset.card_union_of_disjoint hzero, Finset.card_biUnion hpair]
  simp only [blocks.card_zero, blocks.card_other, Finset.sum_const_nat,
    Finset.card_univ, Fintype.card_fin]

theorem aglDisjointEqualBlocks : AGLDisjointEqualBlocks := by
  classical
  intro ι _ _ S k t hcard
  have htotal : 0 + k * t ≤ Fintype.card S := by
    simpa only [zero_add, Fintype.card_coe] using hcard
  obtain ⟨base, hbase⟩ :=
    aglCoordinateBlocksExists k 0 t (ι := S) htotal
  let incl : S ↪ ι := Function.Embedding.subtype (fun x => x ∈ S)
  let blocks : Fin k → Finset ι := fun j => (base.other j).map incl
  refine ⟨blocks, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  · intro j
    simp only [blocks, Finset.card_map, base.card_other]
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_map.mp hxi with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxj with ⟨b, hb, hbx⟩
    have hab : a = b := incl.injective (hax.trans hbx.symm)
    subst b
    exact (Finset.disjoint_left.mp (base.other_disjoint i j hij)) ha hb

theorem aglDistinctAlternativesOfBoundedFibers :
    AGLDistinctAlternativesOfBoundedFibers := by
  intro α β _ _ s f W ℓ hW hcard hfiber
  have hsle : s.card ≤ W * (s.image f).card := by
    apply Finset.card_le_mul_card_image s W
    intro y hy
    exact (hfiber y).le
  have hmul : W * ℓ ≤ W * (s.image f).card := hcard.trans hsle
  exact le_of_mul_le_mul_left hmul hW

theorem aglEtaTimesLengthOne
    (η : ℝ) (n : ℕ) (hη : 0 < η) (hlen : 1 / η ≤ (n : ℝ)) :
    1 ≤ η * n := by
  have h := (div_le_iff₀ hη).mp hlen
  simpa only [one_mul, mul_comm] using h

theorem aglExactSubsetTypeCard (m a : ℕ) :
    Fintype.card {S : Finset (Fin m) // S.card = a} = Nat.choose m a := by
  simpa only [Fintype.card_fin] using
    (Fintype.card_finset_len (α := Fin m) a)

theorem aglFixedFactorRpowAbsorb
    (K : ℕ) (hK : 0 < K) (γ : ℝ) (hγ : 0 < γ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (K : ℝ) * (2 : ℝ) ^ ((γ / 2) * m) ≤
        (2 : ℝ) ^ (γ * m) := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (2 * (K : ℝ) / γ)
  refine ⟨m₀, ?_⟩
  intro m hm
  have hmReal : 2 * (K : ℝ) / γ < (m : ℝ) :=
    hm₀.trans_le (by exact_mod_cast hm)
  have hKm : (K : ℝ) ≤ (γ / 2) * m := by
    have hcross := (div_lt_iff₀ hγ).mp hmReal
    nlinarith
  have hKpowNat : K ≤ 2 ^ K := by
    calc
      K = Nat.choose K 1 := (Nat.choose_one_right K).symm
      _ ≤ 2 ^ K := Nat.choose_le_two_pow K 1
  have hKpow : (K : ℝ) ≤ (2 : ℝ) ^ (K : ℝ) := by
    calc
      (K : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hKpowNat
      _ = (2 : ℝ) ^ (K : ℕ) := by norm_num
      _ = (2 : ℝ) ^ (K : ℝ) := (Real.rpow_natCast _ _).symm
  have hsum : (K : ℝ) + (γ / 2) * m ≤ γ * m := by
    nlinarith
  calc
    (K : ℝ) * (2 : ℝ) ^ ((γ / 2) * m) ≤
        (2 : ℝ) ^ (K : ℝ) * (2 : ℝ) ^ ((γ / 2) * m) :=
      mul_le_mul_of_nonneg_right hKpow (by positivity)
    _ = (2 : ℝ) ^ ((K : ℝ) + (γ / 2) * m) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (γ * m) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hsum

theorem aglFixedSubsetInsideCard (m a : ℕ) (U : Finset (Fin m)) :
    Fintype.card {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} =
      Nat.choose U.card a := by
  classical
  calc
    Fintype.card {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} =
        (U.powersetCard a).card := by
      apply Fintype.card_of_subtype
      intro S
      simp only [Finset.mem_powersetCard]
      aesop
    _ = Nat.choose U.card a := Finset.card_powersetCard a U

theorem aglConstrainedIndexedFamiliesCard :
    AGLConstrainedIndexedFamiliesCard := by
  classical
  intro m a T W b J U hJ hU
  let inside : Finset {S : Finset (Fin m) // S.card = a} :=
    Finset.univ.filter fun S => S.val ⊆ U
  have hinside : inside.card = Nat.choose U.card a := by
    let e : inside ≃ {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} :=
      { toFun := fun S =>
          ⟨((S.val : {S : Finset (Fin m) // S.card = a}).val),
            ⟨(S.val : {S : Finset (Fin m) // S.card = a}).property,
              (Finset.mem_filter.mp S.property).2⟩⟩
        invFun := fun S =>
          ⟨⟨S.val, S.property.1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.property.2⟩⟩
        left_inv := by intro S; apply Subtype.ext; rfl
        right_inv := by intro S; apply Subtype.ext; rfl }
    calc
      inside.card = Fintype.card inside := (Fintype.card_coe inside).symm
      _ = Fintype.card {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} :=
        Fintype.card_congr e
      _ = Nat.choose U.card a := aglFixedSubsetInsideCard m a U
  let allowed : Fin T → Finset {S : Finset (Fin m) // S.card = a} :=
    fun j => if j ∈ J then inside else Finset.univ
  have heq : aglConstrainedIndexedFamilies m a T J U =
      Fintype.piFinset allowed := by
    ext A
    simp only [aglConstrainedIndexedFamilies, Finset.mem_filter,
      Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j ∈ J
      · simpa only [allowed, hj, if_pos, inside, Finset.mem_filter,
          Finset.mem_univ, true_and] using h j hj
      · simp [allowed, hj]
    · intro h j hj
      have hjmem := h j
      simpa only [allowed, hj, if_pos, inside, Finset.mem_filter,
        Finset.mem_univ, true_and] using hjmem
  have hallowed : ∀ j, (allowed j).card =
      if j ∈ J then Nat.choose U.card a else Nat.choose m a := by
    intro j
    by_cases hj : j ∈ J
    · simp only [allowed, hj, if_pos, hinside]
    · simp only [allowed, hj, if_neg, Finset.card_univ]
      exact aglExactSubsetTypeCard m a
  rw [heq, Fintype.card_piFinset]
  calc
    (∏ j, (allowed j).card) =
        ∏ j, if j ∈ J then Nat.choose U.card a else Nat.choose m a := by
      apply Fintype.prod_congr
      intro j
      exact hallowed j
    _ = Nat.choose U.card a ^ J.card *
        Nat.choose m a ^ (T - J.card) := by
      change (∏ j ∈ (Finset.univ : Finset (Fin T)),
        if j ∈ J then Nat.choose U.card a else Nat.choose m a) = _
      rw [Finset.prod_ite]
      have hfilter : (Finset.univ.filter fun j : Fin T => j ∈ J) = J := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfilterCompl :
          (Finset.univ.filter fun j : Fin T => ¬j ∈ J) = Jᶜ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_compl]
      rw [hfilter, hfilterCompl]
      simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]
    _ = Nat.choose (b - 1) a ^ W *
        Nat.choose m a ^ (T - W) := by
      rw [hJ, hU]

theorem aglBadIndexedFamiliesCardBound :
    AGLBadIndexedFamiliesCardBound := by
  classical
  intro m a T W b hW hWT hb hbm hab
  let Js : Finset (Finset (Fin T)) := Finset.univ.powersetCard W
  let Us : Finset (Finset (Fin m)) := Finset.univ.powersetCard (b - 1)
  let cover : Finset (Fin T → {S : Finset (Fin m) // S.card = a}) :=
    Js.biUnion fun J =>
      Us.biUnion fun U => aglConstrainedIndexedFamilies m a T J U
  have hsub : aglBadIndexedFamilies m a T W b ⊆ cover := by
    simpa only [Js, Us, cover] using
      (aglBadIndexedFamiliesSubsetCover m a T W b hb hbm)
  let K : ℕ :=
    Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W)
  have hsum :
      (∑ J ∈ Js, ∑ U ∈ Us,
        (aglConstrainedIndexedFamilies m a T J U).card) =
        Js.card * (Us.card * K) := by
    calc
      (∑ J ∈ Js, ∑ U ∈ Us,
          (aglConstrainedIndexedFamilies m a T J U).card) =
          ∑ J ∈ Js, ∑ U ∈ Us, K := by
        apply Finset.sum_congr rfl
        intro J hJ
        have hJcard : J.card = W :=
          (Finset.mem_powersetCard.mp hJ).2
        apply Finset.sum_congr rfl
        intro U hU
        have hUcard : U.card = b - 1 :=
          (Finset.mem_powersetCard.mp hU).2
        simpa only [K] using
          aglConstrainedIndexedFamiliesCard
            m a T W b J U hJcard hUcard
      _ = ∑ J ∈ Js, Us.card * K := by
        apply Finset.sum_congr rfl
        intro J hJ
        exact Finset.sum_const_nat fun _ _ => rfl
      _ = Js.card * (Us.card * K) :=
        Finset.sum_const_nat fun _ _ => rfl
  calc
    (aglBadIndexedFamilies m a T W b).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ J ∈ Js, (Us.biUnion fun U =>
        aglConstrainedIndexedFamilies m a T J U).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ J ∈ Js, ∑ U ∈ Us,
        (aglConstrainedIndexedFamilies m a T J U).card := by
      apply Finset.sum_le_sum
      intro J hJ
      exact Finset.card_biUnion_le
    _ = Js.card * (Us.card * K) := hsum
    _ = Nat.choose T W * Nat.choose m (b - 1) *
        Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) := by
      have hJs : Js.card = Nat.choose T W := by
        simp only [Js, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]
      have hUs : Us.card = Nat.choose m (b - 1) := by
        simp only [Us, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]
      rw [hJs, hUs]
      dsimp only [K]
      ring

theorem aglFloorDivMulSelf (radius n : ℕ) (hn : 0 < n) :
    Nat.floor (((radius : ℝ) / n) * n) = radius := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hn0, Nat.floor_natCast]

theorem aglFloorRadiusRatioLe
    (p : ℝ) (n : ℕ) (hp : 0 ≤ p) (hn : 0 < n) :
    (Nat.floor (p * n) : ℝ) / n ≤ p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnR]
  exact Nat.floor_le (mul_nonneg hp (Nat.cast_nonneg n))

theorem aglGoodBaseByDoubleCount
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (t : Finset Y) (P : X → Y → Prop) [DecidableRel P]
    (hs : s.Nonempty)
    (hcol : ∀ y ∈ t, s.card ≤
      2 * (s.filter fun x => P x y).card) :
    ∃ x ∈ s, t.card ≤ 2 * (t.filter fun y => P x y).card := by
  by_contra hno
  have hrow : ∀ x ∈ s,
      2 * (t.filter fun y => P x y).card < t.card := by
    intro x hx
    exact Nat.lt_of_not_ge fun hge => hno ⟨x, hx, hge⟩
  have hdouble :
      (∑ y ∈ t, (s.filter fun x => P x y).card) =
        ∑ x ∈ s, (t.filter fun y => P x y).card := by
    calc
      (∑ y ∈ t, (s.filter fun x => P x y).card) =
          ∑ y ∈ t, ∑ x ∈ s, if P x y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.card_filter]
      _ = ∑ x ∈ s, ∑ y ∈ t, if P x y then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ s, (t.filter fun y => P x y).card := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.card_filter]
  have hlower : t.card * s.card ≤
      2 * ∑ x ∈ s, (t.filter fun y => P x y).card := by
    calc
      t.card * s.card = ∑ y ∈ t, s.card := by
        exact (Finset.sum_const_nat fun _ _ => rfl).symm
      _ ≤ ∑ y ∈ t, 2 * (s.filter fun x => P x y).card :=
        Finset.sum_le_sum fun y hy => hcol y hy
      _ = 2 * ∑ y ∈ t, (s.filter fun x => P x y).card := by
        rw [Finset.mul_sum]
      _ = 2 * ∑ x ∈ s, (t.filter fun y => P x y).card := by
        rw [hdouble]
  have hupper :
      2 * ∑ x ∈ s, (t.filter fun y => P x y).card <
        s.card * t.card := by
    calc
      2 * ∑ x ∈ s, (t.filter fun y => P x y).card =
          ∑ x ∈ s, 2 * (t.filter fun y => P x y).card := by
        rw [Finset.mul_sum]
      _ < ∑ x ∈ s, t.card :=
        Finset.sum_lt_sum_of_nonempty hs hrow
      _ = s.card * t.card :=
        Finset.sum_const_nat fun _ _ => rfl
  have hcontra : t.card * s.card < t.card * s.card :=
    hlower.trans_lt (by simpa only [Nat.mul_comm] using hupper)
  exact (Nat.lt_irrefl _ hcontra)

theorem aglGoodIndexedFamilyToLargeUnionFamily :
    AGLGoodIndexedFamilyToLargeUnionFamily := by
  classical
  intro m a T W b hW hab A hgood
  let f : Fin T → Finset (Fin m) := fun j => (A j).1
  have hlarge : ∀ Q : Finset (Finset (Fin m)),
      Q ⊆ Finset.univ.image f → Q.card = W →
        b ≤ (Q.biUnion id).card := by
    intro Q hQsub hQcard
    have hsurj : Set.SurjOn f
        ((Finset.univ : Finset (Fin T)) : Set (Fin T))
        (Q : Set (Finset (Fin m))) := by
      intro S hSQ
      have hSimage := hQsub hSQ
      rcases Finset.mem_image.mp hSimage with ⟨j, hj, hjS⟩
      exact ⟨j, hj, hjS⟩
    obtain ⟨J, hJuniv, hJinj, hJimage⟩ :=
      Finset.exists_subset_injOn_image_eq_of_surjOn
        ((Finset.univ : Finset (Fin T)) : Set (Fin T)) Q hsurj
    have hJcard : J.card = W := by
      calc
        J.card = (J.image f).card :=
          (Finset.card_image_of_injOn hJinj).symm
        _ = Q.card := congrArg Finset.card hJimage
        _ = W := hQcard
    apply Nat.le_of_not_gt
    intro hsmall
    apply hgood
    simp only [aglBadIndexedFamilies, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨J, hJcard, ?_⟩
    have hunion : Q.biUnion id = J.biUnion f := by
      rw [← hJimage, Finset.image_biUnion]
      simp only [id_eq]
    rw [hunion] at hsmall
    exact hsmall
  have hfiber : ∀ S ∈ Finset.univ.image f,
      (Finset.univ.filter fun j => f j = S).card ≤ W := by
    intro S hS
    by_contra hnot
    have hWle : W ≤ (Finset.univ.filter fun j => f j = S).card := by
      exact (Nat.lt_of_not_ge hnot).le
    obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hWle
    apply hgood
    simp only [aglBadIndexedFamilies, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨J, hJcard, ?_⟩
    have hUnionSub : J.biUnion f ⊆ S := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, hjJ, hxj⟩
      have hj := Finset.mem_filter.mp (hJsub hjJ)
      rw [hj.2] at hxj
      exact hxj
    have hScard : S.card = a := by
      rcases Finset.mem_image.mp hS with ⟨j, hj, hjS⟩
      rw [← hjS]
      exact (A j).property
    calc
      (J.biUnion f).card ≤ S.card := Finset.card_le_card hUnionSub
      _ = a := hScard
      _ < b := hab
  let family : AGLLargeUnionFamily (Fin m) W a b :=
    { sets := Finset.univ.image f
      card_each := by
        intro S hS
        rcases Finset.mem_image.mp hS with ⟨j, hj, hjS⟩
        rw [← hjS]
        exact (A j).property
      large_union := hlarge }
  refine ⟨family, ?_⟩
  change T ≤ W * (Finset.univ.image f).card
  have hcard := Finset.card_le_mul_card_image
    (Finset.univ : Finset (Fin T)) W hfiber
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard

theorem aglGreedySeparatedExtraction : AGLGreedySeparatedExtraction := by
  classical
  intro ι A _ _ C d B hC hlocal
  let s := hC.toFinset
  have hsC : (s : Set (ι → A)) = C := hC.coe_toFinset
  have aux : ∀ s : Finset (ι → A), (s : Set (ι → A)) ⊆ C →
      ∃ t : Finset (ι → A), t ⊆ s ∧ AGLSeparated (t : Set (ι → A)) (d + 1) ∧
        s.card ≤ B * t.card := by
    apply Finset.strongInduction
    intro u ih huC
    by_cases hu : u = ∅
    · subst u
      refine ⟨∅, by simp, ?_, by simp⟩
      simp only [AGLSeparated]
      intro x hx
      simp at hx
    · obtain ⟨c, hcu⟩ := Finset.nonempty_iff_ne_empty.mpr hu
      let N : Finset (ι → A) := u.filter fun x => hammingDist c x ≤ d
      let r : Finset (ι → A) := u \ N
      have hcN : c ∈ N := by
        simp only [N, Finset.mem_filter, hcu, true_and]
        simp only [hammingDist_self, zero_le]
      have hNsub : N ⊆ u := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hrproper : r ⊂ u := by
        exact Finset.sdiff_ssubset hNsub ⟨c, hcN⟩
      have hrC : (r : Set (ι → A)) ⊆ C := by
        intro x hx
        exact huC (Finset.sdiff_subset hx)
      obtain ⟨t, htr, hsep, hcard⟩ := ih r hrproper hrC
      have hNset : (N : Set (ι → A)) ⊆
          {x : ι → A | x ∈ C ∧ hammingDist c x ≤ d} := by
        intro x hx
        have hx' := Finset.mem_filter.mp hx
        exact ⟨huC hx'.1, hx'.2⟩
      have hbigfin :
          ({x : ι → A | x ∈ C ∧ hammingDist c x ≤ d} : Set (ι → A)).Finite :=
        hC.subset fun x hx => hx.1
      have hNcard : N.card ≤ B := by
        rw [← Set.ncard_coe_finset]
        exact (Set.ncard_le_ncard hNset hbigfin).trans (hlocal c (huC hcu))
      have hct : c ∉ t := by
        intro hct
        have hcr := htr hct
        exact (Finset.mem_sdiff.mp hcr).2 hcN
      refine ⟨insert c t, ?_, ?_, ?_⟩
      · exact Finset.insert_subset_iff.mpr
          ⟨hcu, htr.trans Finset.sdiff_subset⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
        rcases hx with hxc | hx
        · subst x
          rcases hy with hyc | hy
          · subst y
            exact (hxy rfl).elim
          · have hyr := htr hy
            have hyn := (Finset.mem_sdiff.mp hyr).2
            have hnot : ¬hammingDist c y ≤ d := by
              intro hle
              apply hyn
              simp only [N, Finset.mem_filter]
              exact ⟨Finset.sdiff_subset hyr, hle⟩
            omega
        · rcases hy with hyc | hy
          · subst y
            have hxr := htr hx
            have hxn := (Finset.mem_sdiff.mp hxr).2
            have hnot : ¬hammingDist c x ≤ d := by
              intro hle
              apply hxn
              simp only [N, Finset.mem_filter]
              exact ⟨Finset.sdiff_subset hxr, hle⟩
            rw [hammingDist_comm]
            omega
          · exact hsep hx hy hxy
      · have hpart := Finset.card_sdiff_add_card_eq_card hNsub
        have hins := Finset.card_insert_of_notMem hct
        change r.card + N.card = u.card at hpart
        rw [hins]
        calc
          u.card = r.card + N.card := hpart.symm
          _ ≤ B * t.card + B := Nat.add_le_add hcard hNcard
          _ = B * (t.card + 1) := by rw [Nat.mul_add, Nat.mul_one]
  obtain ⟨t, hts, hsep, hcard⟩ := aux s (by
    intro x hx
    rw [← hsC]
    exact hx)
  refine ⟨(t : Set (ι → A)), ?_, Set.toFinite _, hsep, ?_⟩
  · intro x hx
    rw [← hsC]
    exact hts hx
  · rw [← hsC, Set.ncard_coe_finset, Set.ncard_coe_finset]
    exact hcard

theorem aglHammingCenterFromDisjointBlocks
    (ℓ r r' t : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (c : ι → A) (v : Fin ℓ → ι → A) (S : Finset ι)
    (blocks : Fin ℓ → Finset ι)
    (hblocks_sub : ∀ j, blocks j ⊆ S)
    (hblocks_card : ∀ j, (blocks j).card = t)
    (hblocks_disjoint : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hcommon : ∀ i ∈ S, ∀ j, c i ≠ v j i)
    (hdist : ∀ j, hammingDist c (v j) ≤ r')
    (hcenter : ℓ * t ≤ r) (hother : r' - t ≤ r) :
    ∃ y : ι → A,
      hammingDist c y ≤ r ∧ ∀ j, hammingDist (v j) y ≤ r := by
  classical
  let U : Finset ι := Finset.univ.biUnion blocks
  have hUexists : ∀ i ∈ U, ∃ j, i ∈ blocks j := by
    intro i hi
    simpa only [U, Finset.mem_biUnion, Finset.mem_univ, true_and] using hi
  let owner : {i : ι // i ∈ U} → Fin ℓ := fun i =>
    Classical.choose (hUexists i i.property)
  have howner_mem : ∀ i : {i : ι // i ∈ U}, i.1 ∈ blocks (owner i) := by
    intro i
    exact Classical.choose_spec (hUexists i i.property)
  have howner_eq : ∀ (i : {i : ι // i ∈ U}) (j : Fin ℓ),
      i.1 ∈ blocks j → owner i = j := by
    intro i j hij
    by_contra hne
    exact (Finset.disjoint_left.mp
      (hblocks_disjoint (owner i) j hne)) (howner_mem i) hij
  let y : ι → A := fun i =>
    if hi : i ∈ U then v (owner ⟨i, hi⟩) i else c i
  have hy_block : ∀ (j : Fin ℓ) {i : ι}, i ∈ blocks j → y i = v j i := by
    intro j i hij
    have hiU : i ∈ U := by
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hij⟩
    rw [show y i = v (owner ⟨i, hiU⟩) i by simp only [y, dif_pos hiU]]
    rw [howner_eq ⟨i, hiU⟩ j hij]
  have hpair :
      ((Finset.univ : Finset (Fin ℓ)) : Set (Fin ℓ)).PairwiseDisjoint blocks := by
    intro i hi j hj hij
    exact hblocks_disjoint i j hij
  have hUcard : U.card = ℓ * t := by
    dsimp only [U]
    rw [Finset.card_biUnion hpair]
    simp only [hblocks_card, Finset.sum_const_nat, Finset.card_univ,
      Fintype.card_fin]
  refine ⟨y, ?_, ?_⟩
  · unfold hammingDist
    have hsub : (Finset.univ.filter fun i => c i ≠ y i) ⊆ U := by
      intro i hi
      have hneq := (Finset.mem_filter.mp hi).2
      by_contra hiU
      have hyc : y i = c i := by simp only [y, dif_neg hiU]
      exact hneq hyc.symm
    exact (Finset.card_le_card hsub).trans (hUcard ▸ hcenter)
  · intro j
    let D : Finset ι := Finset.univ.filter fun i => v j i ≠ c i
    have hblockD : blocks j ⊆ D := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hcommon i (hblocks_sub j hi) j).symm⟩
    have hsub : (Finset.univ.filter fun i => v j i ≠ y i) ⊆ D \ blocks j := by
      intro i hi
      have hneq := (Finset.mem_filter.mp hi).2
      apply Finset.mem_sdiff.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_cases hiU : i ∈ U
        · exact (hcommon i (hblocks_sub (owner ⟨i, hiU⟩)
            (howner_mem ⟨i, hiU⟩)) j).symm
        · have hyc : y i = c i := by simp only [y, dif_neg hiU]
          exact fun heq => hneq (heq.trans hyc.symm)
      · intro hij
        exact hneq (hy_block j hij).symm
    have hDle : D.card ≤ r' := by
      change hammingDist (v j) c ≤ r'
      rw [hammingDist_comm]
      exact hdist j
    unfold hammingDist
    calc
      (Finset.univ.filter fun i => v j i ≠ y i).card ≤
          (D \ blocks j).card := Finset.card_le_card hsub
      _ = D.card - (blocks j).card := Finset.card_sdiff_of_subset hblockD
      _ = D.card - t := by rw [hblocks_card]
      _ ≤ r' - t := Nat.sub_le_sub_right hDle t
      _ ≤ r := hother

theorem aglBalancedCenterConstruction : AGLBalancedCenterConstruction := by
  classical
  intro ℓ hℓ p hp hp_lt ι A _ _ _ c v hdist hsize hcommonCard
  let n := Fintype.card ι
  let r := Nat.floor (p * n)
  let r' := Nat.floor (aglBoostedRadius ℓ p * n)
  let t := r' - r
  have harith := aglBalancedCenterArithmetic ℓ p n hℓ hp hp_lt (by
    simpa only [n] using hsize)
  rcases harith with ⟨hrle, hcancel, ht_center, ht_common⟩
  let S : Finset ι := Finset.univ.filter fun i => ∀ j, c i ≠ v j i
  have hScoe : (S : Set ι) = {i : ι | ∀ j, c i ≠ v j i} := by
    ext i
    simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
  have hScard : S.card = ({i : ι | ∀ j, c i ≠ v j i} : Set ι).ncard := by
    rw [← Set.ncard_coe_finset, hScoe]
  have hblocksSize : ℓ * t ≤ S.card := by
    calc
      ℓ * t ≤ Nat.ceil ((3 * p ^ ℓ / 4) * n) := ht_common
      _ ≤ ({i : ι | ∀ j, c i ≠ v j i} : Set ι).ncard := by
        simpa only [n] using hcommonCard
      _ = S.card := hScard.symm
  obtain ⟨blocks, hblocks_sub, hblocks_card, hblocks_disjoint⟩ :=
    aglDisjointEqualBlocks S ℓ t hblocksSize
  obtain ⟨y, hyc, hyv⟩ := aglHammingCenterFromDisjointBlocks
    ℓ r r' t c v S blocks hblocks_sub hblocks_card hblocks_disjoint
    (by
      intro i hi j
      exact (Finset.mem_filter.mp hi).2 j)
    (by
      intro j
      simpa only [r', n] using hdist j)
    ht_center hcancel.le
  refine ⟨y, ?_, ?_⟩
  · simpa only [r, n] using hyc
  · intro j
    simpa only [r, n] using hyv j

theorem aglHammingDistLeCardComplOfAgree
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (u v : ι → A) (S : Finset ι)
    (hagree : ∀ i ∈ S, u i = v i) :
    hammingDist u v ≤ Fintype.card ι - S.card := by
  unfold hammingDist
  have hsub : (Finset.univ.filter fun i => u i ≠ v i) ⊆
      Finset.univ \ S := by
    intro i hi
    have hne := (Finset.mem_filter.mp hi).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hiS
    exact hne (hagree i hiS)
  calc
    (Finset.univ.filter fun i => u i ≠ v i).card ≤
        (Finset.univ \ S).card := Finset.card_le_card hsub
    _ = Finset.univ.card - S.card :=
      Finset.card_sdiff_of_subset (Finset.subset_univ S)
    _ = Fintype.card ι - S.card := by
      rw [Finset.card_univ]

theorem aglAlternativeFiberBound
    (W aFamily aUnion n boosted : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (C : Set (ι → A)) (hn : Fintype.card ι = n)
    (family : AGLLargeUnionFamily ι W aFamily aUnion)
    (c₀ : ι → A) (hc₀ : c₀ ∈ C)
    (alt : Finset ι → ι → A)
    (haltC : ∀ S ∈ family.sets, alt S ∈ C)
    (haltNe : ∀ S ∈ family.sets, alt S ≠ c₀)
    (hagree : ∀ S ∈ family.sets, ∀ i ∈ S, alt S i = c₀ i)
    (hsep : AGLSeparated C boosted)
    (hgap : n - aUnion < boosted) (hW : 0 < W) :
    ∀ z, (family.sets.filter fun S => alt S = z).card < W := by
  classical
  intro z
  by_contra hnot
  have hWle : W ≤ (family.sets.filter fun S => alt S = z).card :=
    Nat.le_of_not_gt hnot
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hWle
  have hTsets : T ⊆ family.sets := by
    intro S hST
    exact (Finset.mem_filter.mp (hTsub hST)).1
  have hlarge := family.large_union T hTsets hTcard
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hTempty
    rw [hTempty] at hTcard
    simp only [Finset.card_empty] at hTcard
    omega
  obtain ⟨S₀, hS₀T⟩ := hTne
  have hS₀filter := Finset.mem_filter.mp (hTsub hS₀T)
  have hzC : z ∈ C := by
    rw [← hS₀filter.2]
    exact haltC S₀ hS₀filter.1
  have hzne : z ≠ c₀ := by
    intro hzc
    exact (haltNe S₀ hS₀filter.1) (hS₀filter.2.trans hzc)
  have hagreeUnion : ∀ i ∈ T.biUnion id, c₀ i = z i := by
    intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨S, hST, hiS⟩
    have hSfilter := Finset.mem_filter.mp (hTsub hST)
    have heq := hagree S hSfilter.1 i hiS
    rw [hSfilter.2] at heq
    exact heq.symm
  have hdist := aglHammingDistLeCardComplOfAgree c₀ z
    (T.biUnion id) hagreeUnion
  have hcomp : Fintype.card ι - (T.biUnion id).card ≤ n - aUnion := by
    rw [hn]
    exact Nat.sub_le_sub_left hlarge n
  have hdistlt : hammingDist c₀ z < boosted :=
    (hdist.trans hcomp).trans_lt hgap
  have hdistge := hsep hc₀ hzC hzne.symm
  omega

theorem aglBarrierCenterFromBlocks
    (ℓ n dZero dOne aFamily : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (hn : Fintype.card ι = n)
    (blocks : AGLCoordinateBlocks ι ℓ dZero dOne)
    (c₀ : ι → A) (chosen : Fin ℓ → Finset ι)
    (u : Fin ℓ → ι → A) (common : blocks.zero → A)
    (hcard : ∀ j, (chosen j).card = aFamily)
    (hdisjoint : ∀ j, Disjoint (chosen j) blocks.zero ∧
      ∀ k, Disjoint (chosen j) (blocks.other k))
    (hagree : ∀ j, ∀ i ∈ chosen j, u j i = c₀ i)
    (hzero : ∀ j, ∀ i, ∀ hi : i ∈ blocks.zero,
      u j i = common ⟨i, hi⟩) :
    ∃ y : ι → A,
      hammingDist c₀ y ≤ dZero + ℓ * dOne ∧
      ∀ j, hammingDist (u j) y ≤ n - dZero - dOne - aFamily := by
  classical
  let U : Finset ι := Finset.univ.biUnion blocks.other
  have hUexists : ∀ i ∈ U, ∃ j, i ∈ blocks.other j := by
    intro i hi
    simpa only [U, Finset.mem_biUnion, Finset.mem_univ, true_and] using hi
  let owner : {i : ι // i ∈ U} → Fin ℓ := fun i =>
    Classical.choose (hUexists i i.property)
  have howner_mem : ∀ i : {i : ι // i ∈ U},
      i.1 ∈ blocks.other (owner i) := by
    intro i
    exact Classical.choose_spec (hUexists i i.property)
  have howner_eq : ∀ (i : {i : ι // i ∈ U}) (j : Fin ℓ),
      i.1 ∈ blocks.other j → owner i = j := by
    intro i j hij
    by_contra hne
    exact (Finset.disjoint_left.mp
      (blocks.other_disjoint (owner i) j hne)) (howner_mem i) hij
  let y : ι → A := fun i =>
    if hi0 : i ∈ blocks.zero then common ⟨i, hi0⟩
    else if hiU : i ∈ U then u (owner ⟨i, hiU⟩) i else c₀ i
  have hyzero : ∀ (j : Fin ℓ) {i : ι}, i ∈ blocks.zero → y i = u j i := by
    intro j i hi
    rw [show y i = common ⟨i, hi⟩ by simp only [y, dif_pos hi]]
    exact (hzero j i hi).symm
  have hyother : ∀ (j : Fin ℓ) {i : ι},
      i ∈ blocks.other j → y i = u j i := by
    intro j i hi
    have hi0 : i ∉ blocks.zero := by
      intro hiz
      exact (Finset.disjoint_left.mp (blocks.zero_disjoint j)) hiz hi
    have hiU : i ∈ U :=
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
    rw [show y i = u (owner ⟨i, hiU⟩) i by
      simp only [y, dif_neg hi0, dif_pos hiU]]
    rw [howner_eq ⟨i, hiU⟩ j hi]
  have hpair :
      ((Finset.univ : Finset (Fin ℓ)) : Set (Fin ℓ)).PairwiseDisjoint
        blocks.other := by
    intro i hi j hj hij
    exact blocks.other_disjoint i j hij
  have hzeroU : Disjoint blocks.zero U := by
    rw [Finset.disjoint_left]
    intro x hxzero hxU
    rcases Finset.mem_biUnion.mp hxU with ⟨j, hj, hxj⟩
    exact (Finset.disjoint_left.mp (blocks.zero_disjoint j)) hxzero hxj
  have hUcard : U.card = ℓ * dOne := by
    dsimp only [U]
    rw [Finset.card_biUnion hpair]
    simp only [blocks.card_other, Finset.sum_const_nat,
      Finset.card_univ, Fintype.card_fin]
  have husedCard : (blocks.zero ∪ U).card = dZero + ℓ * dOne := by
    rw [Finset.card_union_of_disjoint hzeroU, blocks.card_zero, hUcard]
  refine ⟨y, ?_, ?_⟩
  · unfold hammingDist
    have hsub : (Finset.univ.filter fun i => c₀ i ≠ y i) ⊆
        blocks.zero ∪ U := by
      intro i hi
      have hne := (Finset.mem_filter.mp hi).2
      by_contra hnot
      have hi0 : i ∉ blocks.zero := fun h =>
        hnot (Finset.mem_union_left U h)
      have hiU : i ∉ U := fun h =>
        hnot (Finset.mem_union_right blocks.zero h)
      have hy : y i = c₀ i := by simp only [y, dif_neg hi0, dif_neg hiU]
      exact hne hy.symm
    exact (Finset.card_le_card hsub).trans_eq husedCard
  · intro j
    let E : Finset ι := (blocks.zero ∪ blocks.other j) ∪ chosen j
    have hzo : Disjoint blocks.zero (blocks.other j) :=
      blocks.zero_disjoint j
    have hzoChosen : Disjoint (blocks.zero ∪ blocks.other j) (chosen j) := by
      rw [Finset.disjoint_left]
      intro x hx hxs
      rcases Finset.mem_union.mp hx with hx0 | hxj
      · exact (Finset.disjoint_left.mp (hdisjoint j).1) hxs hx0
      · exact (Finset.disjoint_left.mp ((hdisjoint j).2 j)) hxs hxj
    have hEcard : E.card = dZero + dOne + aFamily := by
      dsimp only [E]
      rw [Finset.card_union_of_disjoint hzoChosen,
        Finset.card_union_of_disjoint hzo, blocks.card_zero,
        blocks.card_other, hcard]
    have hagreeE : ∀ i ∈ E, u j i = y i := by
      intro i hi
      rcases Finset.mem_union.mp hi with hblock | hchosen
      · rcases Finset.mem_union.mp hblock with hzeroMem | hotherMem
        · exact (hyzero j hzeroMem).symm
        · exact (hyother j hotherMem).symm
      · have hi0 : i ∉ blocks.zero := by
          intro hi
          exact (Finset.disjoint_left.mp (hdisjoint j).1) hchosen hi
        have hiU : i ∉ U := by
          intro hi
          rcases Finset.mem_biUnion.mp hi with ⟨k, hk, hik⟩
          exact (Finset.disjoint_left.mp ((hdisjoint j).2 k)) hchosen hik
        have hy : y i = c₀ i := by simp only [y, dif_neg hi0, dif_neg hiU]
        exact (hagree j i hchosen).trans hy.symm
    have hd := aglHammingDistLeCardComplOfAgree (u j) y E hagreeE
    rw [hn, hEcard] at hd
    simpa only [Nat.sub_sub] using hd

theorem aglIncidenceDoubleCount : AGLIncidenceDoubleCount := by
  classical
  intro ι κ _ _ _ _ ℓ S
  dsimp
  calc
    (∑ i, Nat.choose ((Finset.univ.filter fun j => i ∈ S j).card) ℓ) =
        ∑ i, ((Finset.univ.filter fun j => i ∈ S j).powersetCard ℓ).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.card_powersetCard ℓ _).symm
    _ = ∑ i, ∑ J ∈ Finset.univ.powersetCard ℓ,
          if J ⊆ Finset.univ.filter (fun j => i ∈ S j) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.card_filter]
      congr 1
      ext J
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
        true_and]
      constructor
      · rintro ⟨hsub, hcard⟩
        exact ⟨hcard, hsub⟩
      · rintro ⟨hcard, hsub⟩
        exact ⟨hsub, hcard⟩
    _ = ∑ J ∈ Finset.univ.powersetCard ℓ, ∑ i,
          if J ⊆ Finset.univ.filter (fun j => i ∈ S j) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ J ∈ Finset.univ.powersetCard ℓ,
          (Finset.univ.filter fun i => ∀ j ∈ J, i ∈ S j).card := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]

theorem aglIncidencePowerGap : AGLIncidencePowerGap := by
  intro ℓ M p hℓ hp hM
  have hℓR : (0 : ℝ) < ℓ := by
    exact_mod_cast (show 0 < ℓ by omega)
  have hℓtwo : (2 : ℝ) ≤ ℓ := by
    exact_mod_cast hℓ
  have hsize : 4 * (ℓ : ℝ) ^ 2 / p ≤ (M : ℝ) :=
    (Nat.ceil_le).mp hM
  have hpm : 4 * (ℓ : ℝ) ^ 2 ≤ p * M := by
    have h := (div_le_iff₀ hp).mp hsize
    nlinarith
  have hden : (0 : ℝ) < 4 * ℓ := by positivity
  have hratio : (ℓ : ℝ) - 1 ≤ p * M / (4 * ℓ) := by
    rw [le_div_iff₀ hden]
    have haux : 4 * (ℓ : ℝ) * ((ℓ : ℝ) - 1) ≤ 4 * (ℓ : ℝ) ^ 2 := by
      nlinarith
    exact (by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using haux.trans hpm)
  let q : ℝ := 1 - 1 / (4 * ℓ)
  have hone : 1 / (4 * (ℓ : ℝ)) ≤ 1 :=
    (div_le_one hden).2 (by nlinarith)
  have hq : 0 ≤ q := by
    dsimp [q]
    linarith
  have hneg : (-2 : ℝ) ≤ -(1 / (4 * (ℓ : ℝ))) := by
    linarith
  have hbern : (3 : ℝ) / 4 ≤ q ^ ℓ := by
    calc
      (3 : ℝ) / 4 =
          1 + (ℓ : ℝ) * (-(1 / (4 * (ℓ : ℝ)))) := by
        field_simp [ne_of_gt hℓR]
        ring
      _ ≤ (1 + -(1 / (4 * (ℓ : ℝ)))) ^ ℓ :=
        one_add_mul_le_pow hneg ℓ
      _ = q ^ ℓ := by congr 1
  have hpM : 0 ≤ p * (M : ℝ) := mul_nonneg hp.le (by positivity)
  have hbase : q * (p * M) ≤ p * M - ((ℓ : ℝ) - 1) := by
    calc
      q * (p * M) = p * M - p * M / (4 * ℓ) := by
        dsimp [q]
        ring
      _ ≤ p * M - ((ℓ : ℝ) - 1) :=
        sub_le_sub_left hratio _
  have hpow : (q * (p * M)) ^ ℓ ≤
      (p * M - ((ℓ : ℝ) - 1)) ^ ℓ :=
    pow_le_pow_left₀ (mul_nonneg hq hpM) hbase ℓ
  calc
    (3 * p ^ ℓ / 4) * (M : ℝ) ^ ℓ =
        ((3 : ℝ) / 4) * (p * M) ^ ℓ := by
      rw [mul_pow]
      ring
    _ ≤ q ^ ℓ * (p * M) ^ ℓ :=
      mul_le_mul_of_nonneg_right hbern (pow_nonneg hpM ℓ)
    _ = (q * (p * M)) ^ ℓ := by simp only [mul_pow]
    _ ≤ (p * M - ((ℓ : ℝ) - 1)) ^ ℓ := hpow

theorem aglIncidenceSumDoubleCount : AGLIncidenceSumDoubleCount := by
  classical
  intro ι κ _ _ _ _ S
  calc
    (∑ i, (Finset.univ.filter fun j => i ∈ S j).card) =
        ∑ i, ∑ j, if i ∈ S j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.card_filter]
    _ = ∑ j, ∑ i, if i ∈ S j then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j, (S j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.card_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem aglInjectiveFamilyOfNcardDiff
    {α : Type} [Fintype α] [DecidableEq α]
    (I B : Set α) (ℓ M : ℕ) (hIB : I ⊆ B)
    (hI : I.ncard ≤ ℓ) (hB : ℓ + M < B.ncard) :
    ∃ v : Fin M → α, Function.Injective v ∧ ∀ j, v j ∈ B \ I := by
  classical
  have hdiff : M ≤ (B \ I).ncard := by
    have hcard := Set.ncard_diff_add_ncard_of_subset hIB (Set.toFinite B)
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_card_eq hdiff
  have hTfin : T.Finite := Set.toFinite T
  let t : Finset α := hTfin.toFinset
  have htcoe : (t : Set α) = T := hTfin.coe_toFinset
  have htcard : t.card = M := by
    rw [← Set.ncard_coe_finset, htcoe, hTcard]
  let e : Fin M ≃ t := (Finset.equivFinOfCardEq htcard).symm
  let v : Fin M → α := fun j => (e j).1
  refine ⟨v, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  · intro j
    apply hTsub
    rw [← htcoe]
    exact (e j).2

open _root_.ListDecodable in
theorem aglLambdaContradictionOfInjectiveCenter
    (ℓ : ℕ)
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (p : ℝ) (hp : 0 ≤ p)
    (c : ι → A) (hc : c ∈ C)
    (u : Fin ℓ → ι → A) (huinj : Function.Injective u)
    (huC : ∀ j, u j ∈ C) (huc : ∀ j, u j ≠ c)
    (y : ι → A)
    (hyc : hammingDist c y ≤ Nat.floor (p * Fintype.card ι))
    (huy : ∀ j, hammingDist (u j) y ≤ Nat.floor (p * Fintype.card ι))
    (hLambda : Lambda C p ≤ (ℓ : ℕ∞)) : False := by
  classical
  have hpoint := (ListDecodable.Lambda_le_iff_forall_ncard_le.mp hLambda) y
  rw [aglCloseCodewordsRelEqDistSet C p hp y] at hpoint
  let image : Finset (ι → A) := Finset.univ.image u
  have hcnot : c ∉ image := by
    intro hcimage
    rcases Finset.mem_image.mp hcimage with ⟨j, hj, hju⟩
    exact (huc j) hju
  let t : Finset (ι → A) := insert c image
  have himagecard : image.card = ℓ := by
    dsimp only [image]
    rw [Finset.card_image_of_injective _ huinj]
    simp only [Finset.card_univ, Fintype.card_fin]
  have htcard : t.card = ℓ + 1 := by
    dsimp only [t]
    rw [Finset.card_insert_of_notMem hcnot, himagecard]
  have hsub : (t : Set (ι → A)) ⊆
      {x : ι → A | x ∈ C ∧
        hammingDist x y ≤ Nat.floor (p * Fintype.card ι)} := by
    intro x hx
    change x ∈ insert c image at hx
    rcases Finset.mem_insert.mp hx with hxc | hximage
    · subst x
      exact ⟨hc, hyc⟩
    · rcases Finset.mem_image.mp hximage with ⟨j, hj, hju⟩
      subst x
      exact ⟨huC j, huy j⟩
  have hle : t.card ≤
      ({x : ι → A | x ∈ C ∧
        hammingDist x y ≤ Nat.floor (p * Fintype.card ι)} : Set (ι → A)).ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub hpoint.1
  rw [htcard] at hle
  omega

theorem aglLargeFiberOfImageBound
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (f : X → Y) (B k : ℕ)
    (hs : s.Nonempty) (himage : (s.image f).card ≤ B)
    (hlarge : B * k ≤ s.card) :
    ∃ y ∈ s.image f, k ≤ (s.filter fun x => f x = y).card := by
  have himul : (s.image f).card * k ≤ s.card := by
    exact (Nat.mul_le_mul_right k himage).trans hlarge
  apply Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := s) (t := s.image f) (f := f)
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · exact hs.image f
  · exact himul

theorem aglLargeUnionFamilyResize : AGLLargeUnionFamilyResize := by
  classical
  intro W a₀ b₀ a₁ b₁ hW ha hlt hb ι _ _ ha₁ source
  have hext : ∀ A ∈ source.sets,
      ∃ E : Finset ι, A ⊆ E ∧ E.card = a₁ := by
    intro A hA
    apply Finset.exists_superset_card_eq
    · simpa only [source.card_each A hA] using ha
    · exact ha₁
  let extend : Finset ι → Finset ι := fun A =>
    if hA : A ∈ source.sets then Classical.choose (hext A hA) else ∅
  have hextend : ∀ A ∈ source.sets,
      A ⊆ extend A ∧ (extend A).card = a₁ := by
    intro A hA
    dsimp only [extend]
    rw [dif_pos hA]
    exact Classical.choose_spec (hext A hA)
  let targetSets : Finset (Finset ι) := source.sets.image extend
  have hcard_each : ∀ E ∈ targetSets, E.card = a₁ := by
    intro E hE
    rcases Finset.mem_image.mp hE with ⟨A, hA, rfl⟩
    exact (hextend A hA).2
  have hfiber : ∀ E ∈ targetSets,
      (source.sets.filter fun A => extend A = E).card ≤ W := by
    intro E hE
    by_contra hle
    have hWle : W ≤ (source.sets.filter fun A => extend A = E).card := by
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hWle
    have hTsource : T ⊆ source.sets := by
      intro A hA
      exact (Finset.mem_filter.mp (hTsub hA)).1
    have hlarge := source.large_union T hTsource hTcard
    have hUsub : T.biUnion id ⊆ E := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨A, hAT, hxA⟩
      have hAf := Finset.mem_filter.mp (hTsub hAT)
      have hAE := (hextend A hAf.1).1 hxA
      simpa only [hAf.2] using hAE
    have hUcard : (T.biUnion id).card ≤ E.card := Finset.card_le_card hUsub
    rcases Finset.mem_image.mp hE with ⟨A, hA, hAE⟩
    have hEcard : E.card = a₁ := by
      rw [← hAE]
      exact (hextend A hA).2
    rw [hEcard] at hUcard
    omega
  have htarget_large : ∀ T : Finset (Finset ι), T ⊆ targetSets → T.card = W →
      b₁ ≤ (T.biUnion id).card := by
    intro T hTsub hTcard
    have hpre : ∀ E ∈ T, ∃ A ∈ source.sets, extend A = E := by
      intro E hE
      rcases Finset.mem_image.mp (hTsub hE) with ⟨A, hA, hAE⟩
      exact ⟨A, hA, hAE⟩
    let pre : Finset ι → Finset ι := fun E =>
      if hE : E ∈ T then Classical.choose (hpre E hE) else ∅
    have hpre_spec : ∀ E ∈ T,
        pre E ∈ source.sets ∧ extend (pre E) = E := by
      intro E hE
      dsimp only [pre]
      rw [dif_pos hE]
      exact Classical.choose_spec (hpre E hE)
    let U : Finset (Finset ι) := T.image pre
    have hUsub : U ⊆ source.sets := by
      intro A hA
      rcases Finset.mem_image.mp hA with ⟨E, hE, rfl⟩
      exact (hpre_spec E hE).1
    have hpreinj : Set.InjOn pre (T : Set (Finset ι)) := by
      intro E hE E' hE' hEq
      have h1 := (hpre_spec E hE).2
      have h2 := (hpre_spec E' hE').2
      rw [← h1, ← h2, hEq]
    have hUcard : U.card = W := by
      rw [show U = T.image pre by rfl, Finset.card_image_of_injOn hpreinj, hTcard]
    have hlarge := source.large_union U hUsub hUcard
    have hUnionSub : U.biUnion id ⊆ T.biUnion id := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨A, hAU, hxA⟩
      rcases Finset.mem_image.mp hAU with ⟨E, hET, rfl⟩
      have hsub := (hextend (pre E) (hpre_spec E hET).1).1 hxA
      have hEq := (hpre_spec E hET).2
      apply Finset.mem_biUnion.mpr
      refine ⟨E, hET, ?_⟩
      change x ∈ E
      rw [← hEq]
      exact hsub
    exact hb.trans (hlarge.trans (Finset.card_le_card hUnionSub))
  let target : AGLLargeUnionFamily ι W a₁ b₁ :=
    { sets := targetSets
      card_each := hcard_each
      large_union := htarget_large }
  refine ⟨target, ?_⟩
  change source.sets.card ≤ W * targetSets.card
  exact Finset.card_le_mul_card_image source.sets W hfiber

theorem aglNatQuotientWindow
    (ℓ radius dZero n : ℕ) (hℓ : 0 < ℓ)
    (hdZero : dZero ≤ radius) (hradius : radius ≤ n) :
    let dOne := (radius - dZero) / ℓ
    let used := dZero + ℓ * dOne
    let m := n - used
    used ≤ radius ∧ radius < used + ℓ ∧
      n - radius ≤ m ∧ m ≤ n - radius + (ℓ - 1) := by
  dsimp only
  have hmod := Nat.mod_add_div (radius - dZero) ℓ
  have hrem := Nat.mod_lt (radius - dZero) hℓ
  omega

noncomputable def aglRadius (ℓ : ℕ) (ρ η : ℝ) : ℝ :=
  (ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)

def AGLBarrierPackageExistence : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (R : ℝ), 0 < R → R < 1 →
    ∀ (B : ℕ), 0 < B →
    ∃ ηCut : ℝ, 0 < ηCut ∧
      ∃ γ : ℝ, 0 < γ ∧ ∃ K : ℝ, 0 < K ∧
        ∃ Wmax : ℕ, 0 < Wmax ∧ ∃ n₀ : ℕ,
          ∀ (η : ℝ), 0 < η → η < ηCut →
            ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι],
              n₀ ≤ Fintype.card ι →
              1 / η ≤ (Fintype.card ι : ℝ) →
              ∃ params : AGLBarrierParameters ℓ (Fintype.card ι)
                  (Nat.floor (aglRadius ℓ R η * Fintype.card ι))
                  (Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * Fintype.card ι)),
                0 < params.W ∧ params.W ≤ Wmax ∧
                params.aFamily + (B + 1) ≤ Nat.floor (R * Fintype.card ι) ∧
                params.dZero ≤ Nat.ceil (K * η * Fintype.card ι) ∧
                ∃ blocks : AGLCoordinateBlocks ι ℓ params.dZero params.dOne,
                  ∃ family : AGLLargeUnionFamily ι params.W
                      params.aFamily params.aUnion,
                    (∀ S ∈ family.sets, Disjoint S blocks.zero ∧
                      ∀ j, Disjoint S (blocks.other j)) ∧
                    (2 : ℝ) ^ (γ * Fintype.card ι) ≤ family.sets.card

def AGLMinimumDistanceBarrierStatement : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (R : ℝ), 0 < R → R < 1 →
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (η : ℝ), 0 < η →
        ∀ {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          [Fintype A] [DecidableEq A]
          (C : Set (ι → A)),
          2 ≤ Fintype.card A →
          n₀ ≤ Fintype.card ι →
          1 / η ≤ (Fintype.card ι : ℝ) →
          (C.ncard : ℝ) =
            (Fintype.card A : ℝ) ^ (R * Fintype.card ι) →
          AGLSeparated C
            (Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * Fintype.card ι)) →
          Lambda C (aglRadius ℓ R η) ≤ (ℓ : ℕ∞) →
          (Fintype.card A : ℝ) ≥ (2 : ℝ) ^ (α / η)

def AGLRobustMinimumDistanceBarrierStatement : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (R : ℝ), 0 < R → R < 1 →
    ∀ (B : ℕ), 0 < B →
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (η : ℝ), 0 < η →
        ∀ {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          [Fintype A] [DecidableEq A]
          (C : Set (ι → A)),
          2 ≤ Fintype.card A →
          n₀ ≤ Fintype.card ι →
          1 / η ≤ (Fintype.card ι : ℝ) →
          (Fintype.card A : ℝ) ^ (R * Fintype.card ι) ≤
            (B : ℝ) * (C.ncard : ℝ) →
          AGLSeparated C
            (Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * Fintype.card ι)) →
          Lambda C (aglRadius ℓ R η) ≤ (ℓ : ℕ∞) →
          (Fintype.card A : ℝ) ≥ (2 : ℝ) ^ (α / η)

theorem aglRadiusBalance
    (ℓ : ℕ) (hℓ : 0 < ℓ) (R η : ℝ) :
    R + aglRadius ℓ R η + aglRadius ℓ R η / ℓ = 1 - η := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  unfold aglRadius
  field_simp [ne_of_gt hℓR]
  ring

theorem aglRadius_pos (ℓ : ℕ) (hℓ_pos : 0 < ℓ)
    (ρ η : ℝ) (hη_lt : η < 1 - ρ) : 0 < aglRadius ℓ ρ η := by
  unfold aglRadius
  have hℓ_real : (0 : ℝ) < ℓ := by exact_mod_cast hℓ_pos
  have hden : (0 : ℝ) < ℓ + 1 := by positivity
  have hgap : 0 < 1 - ρ - η := by linarith
  exact mul_pos (div_pos hℓ_real hden) hgap

theorem aglRateLossToCardinality
    (q B a n N : ℕ) (R : ℝ)
    (hq : 2 ≤ q) (hB : 0 < B) (hR : 0 ≤ R)
    (ha : a + (B + 1) ≤ Nat.floor (R * n))
    (hsize : (q : ℝ) ^ (R * n) ≤ (B : ℝ) * N) :
    2 * q ^ a ≤ N := by
  have hBpow : B ≤ 2 ^ B := by
    calc
      B = Nat.choose B 1 := (Nat.choose_one_right B).symm
      _ ≤ 2 ^ B := Nat.choose_le_two_pow B 1
  have htwoB : 2 * B ≤ q ^ (B + 1) := by
    calc
      2 * B ≤ 2 * 2 ^ B := Nat.mul_le_mul_left 2 hBpow
      _ = 2 ^ (B + 1) := by rw [pow_succ]; ring
      _ ≤ q ^ (B + 1) := pow_le_pow_left' hq (B + 1)
  have hnat : B * (2 * q ^ a) ≤ q ^ (a + (B + 1)) := by
    calc
      B * (2 * q ^ a) = (2 * B) * q ^ a := by ring
      _ ≤ q ^ (B + 1) * q ^ a :=
        Nat.mul_le_mul_right (q ^ a) htwoB
      _ = q ^ (a + (B + 1)) := by
        rw [← pow_add]
        congr 1
        omega
  have hRn : 0 ≤ R * (n : ℝ) := mul_nonneg hR (by positivity)
  have hexp : ((a + (B + 1) : ℕ) : ℝ) ≤ R * n := by
    calc
      ((a + (B + 1) : ℕ) : ℝ) ≤ Nat.floor (R * n) := by
        exact_mod_cast ha
      _ ≤ R * n := Nat.floor_le hRn
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hpow : ((q ^ (a + (B + 1)) : ℕ) : ℝ) ≤
      (q : ℝ) ^ (R * n) := by
    calc
      ((q ^ (a + (B + 1)) : ℕ) : ℝ) =
          (q : ℝ) ^ (a + (B + 1) : ℕ) := by norm_num
      _ = (q : ℝ) ^ ((a + (B + 1) : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ (q : ℝ) ^ (R * n) :=
        Real.rpow_le_rpow_of_exponent_le hqOne hexp
  have hreal : (B : ℝ) * (2 * q ^ a : ℕ) ≤ (B : ℝ) * N := by
    calc
      (B : ℝ) * (2 * q ^ a : ℕ) ≤
          (q ^ (a + (B + 1)) : ℕ) := by exact_mod_cast hnat
      _ ≤ (q : ℝ) ^ (R * n) := hpow
      _ ≤ (B : ℝ) * N := hsize
  have hcancel : ((2 * q ^ a : ℕ) : ℝ) ≤ (N : ℝ) :=
    le_of_mul_le_mul_left hreal (by exact_mod_cast hB)
  exact_mod_cast hcancel

theorem aglRestrictionRangeBound : AGLRestrictionRangeBound := by
  classical
  intro ι A _ _ C S
  calc
    (Set.range (fun c : C => fun i : S => c.1 i.1)).ncard ≤
        Nat.card (S → A) := Set.ncard_le_card _
    _ = Fintype.card A ^ S.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]

noncomputable def aglRoundedBarrierBasicThreshold (R : ℝ) (B : ℕ) : ℕ :=
  Nat.ceil (((B + 1 : ℕ) : ℝ) / R)

noncomputable def aglRoundedBarrierData
    (ℓ : ℕ) (R η K : ℝ) (B n : ℕ) : AGLRoundedBarrierData :=
  let radius := Nat.floor (aglRadius ℓ R η * n)
  let boosted := Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * n)
  let dZero := Nat.ceil (K * η * n)
  let dOne := (radius - dZero) / ℓ
  let used := dZero + ℓ * dOne
  { radius := radius
    boosted := boosted
    dZero := dZero
    dOne := dOne
    used := used
    unused := n - used
    aFamily := Nat.floor (R * n) - (B + 1)
    aUnion := n + 1 - boosted }

theorem aglRoundedBarrierOtherCodewordBoundCore
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R η : ℝ) (B n : ℕ)
    (hone : 1 ≤ η * n)
    (hrate : B + 1 ≤ Nat.floor (R * n))
    (hdZero : Nat.ceil (aglBarrierK ℓ B * η * n) ≤
      Nat.floor (aglRadius ℓ R η * n)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    n - d.dZero - d.dOne - d.aFamily ≤ d.radius := by
  dsimp only [aglRoundedBarrierData]
  let p := aglRadius ℓ R η
  let K := aglBarrierK ℓ B
  let r := Nat.floor (p * n)
  let z := Nat.ceil (K * η * n)
  let o := (r - z) / ℓ
  let a := Nat.floor (R * n) - (B + 1)
  change n - z - o - a ≤ r
  change z ≤ r at hdZero
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hcoefPos : (0 : ℝ) < 1 + 1 / (ℓ : ℝ) := by positivity
  have hcoefNonneg : (0 : ℝ) ≤ 1 - 1 / (ℓ : ℝ) := by
    have hℓTwo : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have honeDiv : 1 / (ℓ : ℝ) ≤ 1 := by
      apply (div_le_one hℓR).2
      linarith
    linarith
  have hrFloor : p * n < (r : ℝ) + 1 := by
    simpa only [r] using Nat.lt_floor_add_one (p * n)
  have hrLower : p * n - 1 < (r : ℝ) := by linarith
  have hrWeighted :
      (p * n - 1) * (1 + 1 / (ℓ : ℝ)) <
        (r : ℝ) * (1 + 1 / (ℓ : ℝ)) :=
    mul_lt_mul_of_pos_right hrLower hcoefPos
  have hzLower : K * η * n ≤ (z : ℝ) := by
    simpa only [z] using Nat.le_ceil (K * η * n)
  have hzWeighted :
      K * η * n * (1 - 1 / (ℓ : ℝ)) ≤
        (z : ℝ) * (1 - 1 / (ℓ : ℝ)) :=
    mul_le_mul_of_nonneg_right hzLower hcoefNonneg
  have hmod := Nat.mod_add_div (r - z) ℓ
  have hrem := Nat.mod_lt (r - z) hℓpos
  have hquotNat : r - z < ℓ * (o + 1) := by
    calc
      r - z = (r - z) % ℓ + ℓ * ((r - z) / ℓ) := hmod.symm
      _ < ℓ + ℓ * ((r - z) / ℓ) := Nat.add_lt_add_right hrem _
      _ = ℓ * (((r - z) / ℓ) + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ = ℓ * (o + 1) := by rfl
  have hquotReal :
      ((r - z : ℕ) : ℝ) < ((ℓ * (o + 1) : ℕ) : ℝ) := by
    exact_mod_cast hquotNat
  norm_num only [Nat.cast_sub hdZero, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] at hquotReal
  have hquotDiv :
      ((r : ℝ) - z) / (ℓ : ℝ) < (o : ℝ) + 1 := by
    rw [div_lt_iff₀ hℓR]
    simpa only [mul_comm] using hquotReal
  have hoLower :
      (r : ℝ) / (ℓ : ℝ) - (z : ℝ) / (ℓ : ℝ) - 1 < o := by
    rw [← sub_div]
    linarith
  have hrateEq : Nat.floor (R * n) = a + (B + 1) := by
    dsimp only [a]
    exact (Nat.sub_add_cancel hrate).symm
  have hrateFloor : R * n < (Nat.floor (R * n) : ℝ) + 1 :=
    Nat.lt_floor_add_one (R * n)
  have haLower : R * n - ((B : ℝ) + 2) < (a : ℝ) := by
    rw [hrateEq] at hrateFloor
    norm_num only [Nat.cast_add, Nat.cast_one] at hrateFloor
    linarith
  have hbalance : R + p + p / (ℓ : ℝ) = 1 - η := by
    simpa only [p] using aglRadiusBalance ℓ hℓpos R η
  have hbalanceN :
      R * n + p * n + (p / (ℓ : ℝ)) * n =
        (n : ℝ) - η * n := by
    have h := congrArg (fun x : ℝ => x * (n : ℝ)) hbalance
    nlinarith
  have hslack := aglBarrierKSlack ℓ B hℓ
  change (B : ℝ) + 4 + 1 / (ℓ : ℝ) ≤
    K * (1 - 1 / (ℓ : ℝ)) - 1 at hslack
  have hconstNonneg :
      (0 : ℝ) ≤ (B : ℝ) + 4 + 1 / (ℓ : ℝ) := by positivity
  have hfactorNonneg :
      (0 : ℝ) ≤ K * (1 - 1 / (ℓ : ℝ)) - 1 :=
    hconstNonneg.trans hslack
  have hfactorGrow :
      K * (1 - 1 / (ℓ : ℝ)) - 1 ≤
        (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) := by
    nlinarith [mul_nonneg hfactorNonneg (sub_nonneg.mpr hone)]
  have hbudget :
      (B : ℝ) + 4 + 1 / (ℓ : ℝ) ≤
        (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) :=
    hslack.trans hfactorGrow
  let L : ℝ :=
    (R * n - ((B : ℝ) + 2)) +
      (p * n - 1) * (1 + 1 / (ℓ : ℝ)) +
      K * η * n * (1 - 1 / (ℓ : ℝ)) - 1
  have hLFormula : L =
      (n : ℝ) +
        (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) -
        ((B : ℝ) + 4 + 1 / (ℓ : ℝ)) := by
    dsimp only [L]
    calc
      (R * n - ((B : ℝ) + 2)) +
          (p * n - 1) * (1 + 1 / (ℓ : ℝ)) +
          K * η * n * (1 - 1 / (ℓ : ℝ)) - 1 =
        (R * n + p * n + (p / (ℓ : ℝ)) * n) +
          K * η * n * (1 - 1 / (ℓ : ℝ)) -
          ((B : ℝ) + 4 + 1 / (ℓ : ℝ)) := by ring
      _ = (n : ℝ) +
          (K * (1 - 1 / (ℓ : ℝ)) - 1) * (η * n) -
          ((B : ℝ) + 4 + 1 / (ℓ : ℝ)) := by
        rw [hbalanceN]
        ring
  have hLeL : (n : ℝ) ≤ L := by
    rw [hLFormula]
    linarith
  let U : ℝ :=
    (a : ℝ) + (r : ℝ) * (1 + 1 / (ℓ : ℝ)) +
      (z : ℝ) * (1 - 1 / (ℓ : ℝ)) - 1
  have hAR :
      (R * n - ((B : ℝ) + 2)) +
          (p * n - 1) * (1 + 1 / (ℓ : ℝ)) <
        (a : ℝ) + (r : ℝ) * (1 + 1 / (ℓ : ℝ)) :=
    add_lt_add haLower hrWeighted
  have hLltU : L < U := by
    dsimp only [L, U]
    exact sub_lt_sub_right
      (add_lt_add_of_lt_of_le hAR hzWeighted) 1
  have hsumDiff :
      ((r : ℝ) + z + o + a) - U =
        (o : ℝ) -
          ((r : ℝ) / (ℓ : ℝ) - (z : ℝ) / (ℓ : ℝ) - 1) := by
    dsimp only [U]
    ring
  have hUltSum : U < (r : ℝ) + z + o + a := by
    apply sub_pos.mp
    rw [hsumDiff]
    exact sub_pos.mpr hoLower
  have hsumReal : (n : ℝ) < (r : ℝ) + z + o + a :=
    hLeL.trans_lt (hLltU.trans hUltSum)
  have hsumNat : n < r + z + o + a := by
    exact_mod_cast hsumReal
  omega

theorem aglShiftedIncidenceMeanLower : AGLShiftedIncidenceMeanLower := by
  intro ℓ M n p hℓ hn a hsum
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hpoint : ∀ i : Fin n,
      (a i : ℝ) ≤ ((a i + 1 - ℓ : ℕ) : ℝ) + (ℓ - 1 : ℕ) := by
    intro i
    exact_mod_cast (show a i ≤ a i + 1 - ℓ + (ℓ - 1) by omega)
  have hsum_le : (∑ i, (a i : ℝ)) ≤
      ∑ i, (((a i + 1 - ℓ : ℕ) : ℝ) + (ℓ - 1 : ℕ)) := by
    exact Finset.sum_le_sum fun i _ => hpoint i
  rw [Finset.sum_add_distrib] at hsum_le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum_le
  have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast] at hsum_le
  rw [le_div_iff₀ hnR]
  nlinarith

theorem aglIncidenceMomentLower : AGLIncidenceMomentLower := by
  intro ℓ M n p hℓ hn hp hp_lt hM a hsum
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  let b : Fin n → ℝ := fun i => (a i + 1 - ℓ : ℕ)
  have hmean : p * M - (ℓ - 1) ≤ (∑ i, b i) / n := by
    simpa only [b] using
      (aglShiftedIncidenceMeanLower ℓ M n p hℓ hn a hsum)
  have hℓR : (0 : ℝ) < ℓ := by
    exact_mod_cast (show 0 < ℓ by omega)
  have hsize : 4 * (ℓ : ℝ) ^ 2 / p ≤ (M : ℝ) :=
    (Nat.ceil_le).mp hM
  have hpm : 4 * (ℓ : ℝ) ^ 2 ≤ p * M := by
    have h := (div_le_iff₀ hp).mp hsize
    nlinarith
  have hgap_nonneg : 0 ≤ p * M - ((ℓ : ℝ) - 1) := by
    have hℓtwo : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    nlinarith
  have hmeanpow :
      (p * M - ((ℓ : ℝ) - 1)) ^ ℓ ≤ ((∑ i, b i) / n) ^ ℓ :=
    pow_le_pow_left₀ hgap_nonneg hmean ℓ
  let w : Fin n → ℝ := fun _ => 1 / n
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i := by
    intro i hi
    dsimp [w]
    positivity
  have hwsum : ∑ i ∈ (Finset.univ : Finset (Fin n)), w i = 1 := by
    dsimp [w]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [ne_of_gt hnR]
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ b i := by
    intro i hi
    dsimp [b]
    positivity
  have hj := Real.pow_arith_mean_le_arith_mean_pow
    (Finset.univ : Finset (Fin n)) w b hw hwsum hb ℓ
  have hleft :
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i) =
        (∑ i, b i) / n := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)), b i / n := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        ring
      _ = (∑ i, b i) / n := by rw [Finset.sum_div]
  have hright :
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i ^ ℓ) =
        (∑ i, b i ^ ℓ) / n := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin n)), w i * b i ^ ℓ) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)), b i ^ ℓ / n := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        ring
      _ = (∑ i, b i ^ ℓ) / n := by rw [Finset.sum_div]
  rw [hleft, hright] at hj
  have hfact : (0 : ℝ) < Nat.factorial ℓ := by positivity
  have hchooseM : (Nat.choose M ℓ : ℝ) ≤
      (M : ℝ) ^ ℓ / Nat.factorial ℓ := by
    exact Nat.choose_le_pow_div ℓ M
  have hcoeff : 0 ≤ 3 * p ^ ℓ / 4 := by positivity
  have hgap := aglIncidencePowerGap ℓ M p hℓ hp hM
  have hfirst :
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
        (p * M - ((ℓ : ℝ) - 1)) ^ ℓ / Nat.factorial ℓ := by
    calc
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
          (3 * p ^ ℓ / 4) * ((M : ℝ) ^ ℓ / Nat.factorial ℓ) :=
        mul_le_mul_of_nonneg_left hchooseM hcoeff
      _ = ((3 * p ^ ℓ / 4) * (M : ℝ) ^ ℓ) /
          Nat.factorial ℓ := by ring
      _ ≤ (p * M - ((ℓ : ℝ) - 1)) ^ ℓ /
          Nat.factorial ℓ :=
        div_le_div_of_nonneg_right hgap hfact.le
  have hchoose : ∀ i : Fin n,
      b i ^ ℓ / Nat.factorial ℓ ≤ (Nat.choose (a i) ℓ : ℝ) := by
    intro i
    simpa only [b] using (Nat.pow_le_choose (α := ℝ) ℓ (a i))
  have hsumchoose :
      (∑ i, b i ^ ℓ) / Nat.factorial ℓ ≤
        ∑ i, (Nat.choose (a i) ℓ : ℝ) := by
    calc
      (∑ i, b i ^ ℓ) / Nat.factorial ℓ =
          ∑ i, b i ^ ℓ / Nat.factorial ℓ := by
        rw [Finset.sum_div]
      _ ≤ ∑ i, (Nat.choose (a i) ℓ : ℝ) :=
        Finset.sum_le_sum fun i hi => hchoose i
  have hcore :
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
        (∑ i, (Nat.choose (a i) ℓ : ℝ)) / n := by
    calc
      (3 * p ^ ℓ / 4) * (Nat.choose M ℓ : ℝ) ≤
          (p * M - ((ℓ : ℝ) - 1)) ^ ℓ / Nat.factorial ℓ := hfirst
      _ ≤ ((∑ i, b i) / n) ^ ℓ / Nat.factorial ℓ :=
        div_le_div_of_nonneg_right hmeanpow hfact.le
      _ ≤ ((∑ i, b i ^ ℓ) / n) / Nat.factorial ℓ :=
        div_le_div_of_nonneg_right hj hfact.le
      _ = ((∑ i, b i ^ ℓ) / Nat.factorial ℓ) / n := by ring
      _ ≤ (∑ i, (Nat.choose (a i) ℓ : ℝ)) / n :=
        div_le_div_of_nonneg_right hsumchoose hnR.le
  simpa only [mul_assoc] using (le_div_iff₀ hnR).mp hcore

theorem aglCommonDisagreementIntersection : AGLCommonDisagreementIntersection := by
  classical
  intro ℓ hℓ p hp hp_lt ι _ _ M hM S hS
  let n := Fintype.card ι
  have hℓR : (0 : ℝ) < ℓ := by
    exact_mod_cast (show 0 < ℓ by omega)
  have hℓOne : (1 : ℝ) ≤ ℓ := by
    exact_mod_cast (show 1 ≤ ℓ by omega)
  have hℓBound : (ℓ : ℝ) ≤ 4 * (ℓ : ℝ) ^ 2 / p := by
    rw [le_div_iff₀ hp]
    calc
      (ℓ : ℝ) * p ≤ (ℓ : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hp_lt.le hℓR.le
      _ = (ℓ : ℝ) := by ring
      _ = (ℓ : ℝ) * 1 := by ring
      _ ≤ (ℓ : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_left hℓOne hℓR.le
      _ = (ℓ : ℝ) ^ 2 := by ring
      _ ≤ 4 * (ℓ : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (ℓ : ℝ)]
  have hℓCeil : ℓ ≤ Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) := by
    exact_mod_cast hℓBound.trans (Nat.le_ceil (4 * (ℓ : ℝ) ^ 2 / p))
  have hℓM : ℓ ≤ M := hℓCeil.trans hM
  have hMpos : 0 < M := lt_of_lt_of_le (by omega : 0 < ℓ) hℓM
  let j0 : Fin M := ⟨0, hMpos⟩
  have hn : 0 < n := by
    have hcardPos : 0 < (S j0).card := Nat.zero_lt_of_lt (hS j0)
    have hle : (S j0).card ≤ Fintype.card ι := Finset.card_le_univ _
    simpa only [n] using hcardPos.trans_le hle
  let incidence : ι → ℕ := fun i =>
    (Finset.univ.filter fun j => i ∈ S j).card
  have hpoint : ∀ j : Fin M, p * n < ((S j).card : ℝ) := by
    intro j
    exact Nat.lt_of_floor_lt (hS j)
  have hsumSets : p * M * n ≤ ∑ j, ((S j).card : ℝ) := by
    have hconst : (∑ _j : Fin M, p * n) = p * M * n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    rw [← hconst]
    exact Finset.sum_le_sum fun j hj => (hpoint j).le
  have hincReal :
      (∑ i, (incidence i : ℝ)) = ∑ j, ((S j).card : ℝ) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (aglIncidenceSumDoubleCount S)
    simpa only [incidence, Nat.cast_sum] using h
  have hsumInc : p * M * n ≤ ∑ i, (incidence i : ℝ) := by
    calc
      p * M * n ≤ ∑ j, ((S j).card : ℝ) := hsumSets
      _ = ∑ i, (incidence i : ℝ) := hincReal.symm
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let a : Fin n → ℕ := fun k => incidence (e.symm k)
  have hreindexReal :
      (∑ i, (incidence i : ℝ)) = ∑ k, (a k : ℝ) := by
    simpa only [a, Equiv.symm_apply_apply] using
      (e.sum_comp fun k => (a k : ℝ))
  have hsumA : p * M * n ≤ ∑ k, (a k : ℝ) :=
    hsumInc.trans_eq hreindexReal
  have hmomentA :=
    aglIncidenceMomentLower ℓ M n p hℓ hn hp hp_lt hM a hsumA
  have hreindexChoose :
      (∑ i, (Nat.choose (incidence i) ℓ : ℝ)) =
        ∑ k, (Nat.choose (a k) ℓ : ℝ) := by
    simpa only [a, Equiv.symm_apply_apply] using
      (e.sum_comp fun k => (Nat.choose (a k) ℓ : ℝ))
  have hmomentInc :
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
        ∑ i, (Nat.choose (incidence i) ℓ : ℝ) := by
    calc
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
          ∑ k, (Nat.choose (a k) ℓ : ℝ) := hmomentA
      _ = ∑ i, (Nat.choose (incidence i) ℓ : ℝ) := hreindexChoose.symm
  let common : Finset (Fin M) → Finset ι := fun J =>
    Finset.univ.filter fun i => ∀ j ∈ J, i ∈ S j
  have hdoubleReal :
      (∑ i, (Nat.choose (incidence i) ℓ : ℝ)) =
        ∑ J ∈ Finset.univ.powersetCard ℓ, ((common J).card : ℝ) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (aglIncidenceDoubleCount ℓ S)
    norm_num only [Nat.cast_sum] at h
    dsimp only [incidence, common]
    convert h using 1 <;> congr!
  have hmomentCommon :
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
        ∑ J ∈ Finset.univ.powersetCard ℓ, ((common J).card : ℝ) :=
    hmomentInc.trans_eq hdoubleReal
  let P : Finset (Finset (Fin M)) := Finset.univ.powersetCard ℓ
  have hPnonempty : P.Nonempty := by
    apply Finset.powersetCard_nonempty_of_le
    simpa only [P, Finset.card_univ, Fintype.card_fin] using hℓM
  let x : ℝ := (3 * p ^ ℓ / 4) * n
  by_cases hex : ∃ J ∈ P, Nat.ceil x ≤ (common J).card
  · obtain ⟨J, hJP, hJbound⟩ := hex
    have hJcard : J.card = ℓ :=
      (Finset.mem_powersetCard.mp hJP).2
    have hcoe : (common J : Set ι) =
        {i : ι | ∀ j, j ∈ J → i ∈ S j} := by
      ext i
      simp only [common, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq]
    have hncard :
        ({i : ι | ∀ j, j ∈ J → i ∈ S j} : Set ι).ncard =
          (common J).card := by
      rw [← Set.ncard_coe_finset, hcoe]
    refine ⟨J, hJcard, ?_⟩
    rw [hncard]
    simpa only [x, n] using hJbound
  · have hltNat : ∀ J ∈ P, (common J).card < Nat.ceil x := by
      intro J hJP
      exact Nat.lt_of_not_ge fun hge => hex ⟨J, hJP, hge⟩
    have hltReal : ∀ J ∈ P, ((common J).card : ℝ) < x := by
      intro J hJP
      rw [← Nat.add_one_le_ceil_iff]
      exact Nat.succ_le_iff.mpr (hltNat J hJP)
    have hsumLt :
        (∑ J ∈ P, ((common J).card : ℝ)) < ∑ J ∈ P, x :=
      Finset.sum_lt_sum_of_nonempty hPnonempty hltReal
    have hconst :
        (∑ J ∈ P, x) = (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n := by
      simp only [P, x, Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hupper :
        (∑ J ∈ Finset.univ.powersetCard ℓ, ((common J).card : ℝ)) <
          (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n := by
      simpa only [P, hconst] using hsumLt
    exfalso
    exact (not_lt_of_ge hmomentCommon) hupper

theorem aglBalancedCenterFromFarFamily
    (ℓ M : ℕ) (hℓ : 2 ≤ ℓ) (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (hM : Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (c : ι → A) (v : Fin M → ι → A)
    (hfar : ∀ j, Nat.floor (p * Fintype.card ι) < hammingDist c (v j))
    (hnear : ∀ j, hammingDist c (v j) ≤
      Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι))
    (hsize : 8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι) :
    ∃ sel : Fin ℓ → Fin M, Function.Injective sel ∧
      ∃ y : ι → A,
        hammingDist c y ≤ Nat.floor (p * Fintype.card ι) ∧
        ∀ k, hammingDist (v (sel k)) y ≤
          Nat.floor (p * Fintype.card ι) := by
  classical
  let S : Fin M → Finset ι := fun j =>
    Finset.univ.filter fun i => c i ≠ v j i
  have hScard : ∀ j, Nat.floor (p * Fintype.card ι) < (S j).card := by
    intro j
    simpa only [S, hammingDist] using hfar j
  obtain ⟨J, hJcard, hcommon⟩ :=
    aglCommonDisagreementIntersection ℓ hℓ p hp hp_lt M hM S hScard
  let e : Fin ℓ ≃ J := (Finset.equivFinOfCardEq hJcard).symm
  let sel : Fin ℓ → Fin M := fun k => (e k).1
  have hselinj : Function.Injective sel := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  let u : Fin ℓ → ι → A := fun k => v (sel k)
  have hcommonSet :
      ({i : ι | ∀ j, j ∈ J → i ∈ S j} : Set ι) =
        {i : ι | ∀ k, c i ≠ u k i} := by
    ext i
    constructor
    · intro hi k
      have hik := hi (sel k) (e k).2
      exact (Finset.mem_filter.mp hik).2
    · intro hi j hj
      let q : J := ⟨j, hj⟩
      obtain ⟨k, hk⟩ := e.surjective q
      have hsel : sel k = j := by
        exact congrArg Subtype.val hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hik := hi k
      simpa only [u, hsel] using hik
  have hcommonU :
      Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
        ({i : ι | ∀ k, c i ≠ u k i} : Set ι).ncard := by
    rw [← hcommonSet]
    exact hcommon
  obtain ⟨y, hyc, hyu⟩ :=
    aglBalancedCenterConstruction ℓ hℓ p hp hp_lt c u
      (by
        intro k
        simpa only [u] using hnear (sel k))
      hsize hcommonU
  refine ⟨sel, hselinj, y, hyc, ?_⟩
  intro k
  simpa only [u] using hyu k

open _root_.ListDecodable in
theorem aglLocalNeighborhoodBound : AGLLocalNeighborhoodBound := by
  classical
  intro ℓ hℓ p hp hp_lt ι _ _ _ A _ _ C hLambda hsize c hc
  let n := Fintype.card ι
  let r := Nat.floor (p * n)
  let r' := Nat.floor (aglBoostedRadius ℓ p * n)
  let M := Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p)
  let I : Set (ι → A) :=
    {x : ι → A | x ∈ C ∧ hammingDist c x ≤ r}
  let B : Set (ι → A) :=
    {x : ι → A | x ∈ C ∧ hammingDist c x ≤ r'}
  have hpoint := (ListDecodable.Lambda_le_iff_forall_ncard_le.mp hLambda) c
  have hcloseI : closeCodewordsRel C c p = I := by
    simpa only [I, r, n, hammingDist_comm] using
      aglCloseCodewordsRelEqDistSet C p hp.le c
  rw [hcloseI] at hpoint
  have hIcard : I.ncard ≤ ℓ := hpoint.2
  have harith := aglBalancedCenterArithmetic ℓ p n hℓ hp hp_lt (by
    simpa only [n] using hsize)
  have hrle : r ≤ r' := by
    simpa only [r, r'] using harith.1
  have hIB : I ⊆ B := by
    intro x hx
    change x ∈ C ∧ hammingDist c x ≤ r at hx
    change x ∈ C ∧ hammingDist c x ≤ r'
    exact ⟨hx.1, hx.2.trans hrle⟩
  change B.ncard ≤ ℓ + M
  by_contra hnot
  have hBlarge : ℓ + M < B.ncard := Nat.lt_of_not_ge hnot
  obtain ⟨v, hvinj, hvBI⟩ :=
    aglInjectiveFamilyOfNcardDiff I B ℓ M hIB hIcard hBlarge
  have hvC : ∀ j, v j ∈ C := by
    intro j
    have hvB := (hvBI j).1
    change v j ∈ C ∧ hammingDist c (v j) ≤ r' at hvB
    exact hvB.1
  have hvnear : ∀ j, hammingDist c (v j) ≤
      Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι) := by
    intro j
    have hvB := (hvBI j).1
    change v j ∈ C ∧ hammingDist c (v j) ≤ r' at hvB
    simpa only [r', n] using hvB.2
  have hvfar : ∀ j, Nat.floor (p * Fintype.card ι) <
      hammingDist c (v j) := by
    intro j
    have hvnotI := (hvBI j).2
    have hnotle : ¬hammingDist c (v j) ≤ r := by
      intro hle
      apply hvnotI
      change v j ∈ C ∧ hammingDist c (v j) ≤ r
      exact ⟨hvC j, hle⟩
    simpa only [r, n] using Nat.lt_of_not_ge hnotle
  obtain ⟨sel, hselinj, y, hyc, hyu⟩ :=
    aglBalancedCenterFromFarFamily ℓ M hℓ p hp hp_lt
      (by exact le_rfl) c v hvfar hvnear hsize
  let u : Fin ℓ → ι → A := fun k => v (sel k)
  have huinj : Function.Injective u := hvinj.comp hselinj
  have huC : ∀ k, u k ∈ C := by
    intro k
    exact hvC (sel k)
  have huc : ∀ k, u k ≠ c := by
    intro k hEq
    have hpos := hvfar (sel k)
    change Nat.floor (p * Fintype.card ι) < hammingDist c (u k) at hpos
    rw [hEq, hammingDist_self] at hpos
    omega
  exact aglLambdaContradictionOfInjectiveCenter ℓ C p hp.le c hc u
    huinj huC huc y hyc (by
      intro k
      simpa only [u] using hyu k) hLambda

theorem aglSingletonFiberCardLeImage
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (s.filter fun x => ∀ y ∈ s, f y = f x → y = x).card ≤
      (s.image f).card := by
  let good : Finset α :=
    s.filter fun x => ∀ y ∈ s, f y = f x → y = x
  have hinj : Set.InjOn f (good : Set α) := by
    intro x hx y hy hxy
    have hxgood := (Finset.mem_filter.mp hx).2
    have hys := (Finset.mem_filter.mp hy).1
    exact (hxgood y hys hxy.symm).symm
  have himage : (good.image f).card = good.card :=
    Finset.card_image_of_injOn hinj
  have hsub : good.image f ⊆ s.image f := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hxgood, rfl⟩
    exact Finset.mem_image.mpr
      ⟨x, (Finset.mem_filter.mp hxgood).1, rfl⟩
  change good.card ≤ (s.image f).card
  rw [← himage]
  exact Finset.card_le_card hsub

theorem aglManyNonsingletonFibers
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (f : X → Y) (B : ℕ)
    (himage : (s.image f).card ≤ B) (hlarge : 2 * B ≤ s.card) :
    s.card ≤ 2 *
      (s.filter fun x => ∃ y ∈ s, y ≠ x ∧ f y = f x).card := by
  classical
  let single : Finset X :=
    s.filter fun x => ∀ y ∈ s, f y = f x → y = x
  let multi : Finset X :=
    s.filter fun x => ∃ y ∈ s, y ≠ x ∧ f y = f x
  have hsingle : single.card ≤ B := by
    exact (aglSingletonFiberCardLeImage s f).trans himage
  have hcomp : single = s \ multi := by
    ext x
    simp only [single, multi, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxs, huniq⟩
      refine ⟨hxs, ?_⟩
      rintro ⟨_, y, hys, hyne, heq⟩
      exact hyne (huniq y hys heq)
    · rintro ⟨hxs, hnot⟩
      refine ⟨hxs, ?_⟩
      intro y hys heq
      by_contra hyne
      apply hnot
      exact ⟨hxs, y, hys, hyne, heq⟩
  have hpart : single.card + multi.card = s.card := by
    rw [hcomp]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  change s.card ≤ 2 * multi.card
  omega

theorem aglManyRestrictionAlternatives
    {ι A : Type} [Fintype ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (hC : C.Finite) (S : Finset ι)
    (aFamily : ℕ) (hScard : S.card = aFamily)
    (hmany : 2 * Fintype.card A ^ aFamily ≤ C.ncard) :
    C.ncard ≤ 2 *
      (hC.toFinset.filter fun c =>
        ∃ z ∈ hC.toFinset, z ≠ c ∧ ∀ i ∈ S, z i = c i).card := by
  classical
  let code : Finset (ι → A) := hC.toFinset
  let restrict : (ι → A) → (S → A) := fun c i => c i.1
  have hcodecard : code.card = C.ncard := by
    rw [← Set.ncard_coe_finset, hC.coe_toFinset]
  have himage : (code.image restrict).card ≤
      Fintype.card A ^ aFamily := by
    calc
      (code.image restrict).card ≤ Fintype.card (S → A) :=
        Finset.card_le_univ _
      _ = Fintype.card A ^ aFamily := by
        rw [Fintype.card_fun, Fintype.card_coe, hScard]
  have hlarge : 2 * Fintype.card A ^ aFamily ≤ code.card := by
    rw [hcodecard]
    exact hmany
  have hmulti := aglManyNonsingletonFibers code restrict
    (Fintype.card A ^ aFamily) himage hlarge
  have hfilter :
      code.filter (fun c =>
        ∃ z ∈ code, z ≠ c ∧ restrict z = restrict c) =
      code.filter (fun c =>
        ∃ z ∈ code, z ≠ c ∧ ∀ i ∈ S, z i = c i) := by
    ext c
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨z, hz, hne, heq⟩
      refine ⟨z, hz, hne, ?_⟩
      intro i hi
      exact congrFun heq ⟨i, hi⟩
    · rintro ⟨z, hz, hne, hagree⟩
      refine ⟨z, hz, hne, ?_⟩
      funext i
      exact hagree i.1 i.2
  rw [hfilter] at hmulti
  simpa only [code, hcodecard] using hmulti

theorem aglGoodBaseWord
    (W aFamily aUnion : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (hC : C.Finite) (hA : 2 ≤ Fintype.card A)
    (family : AGLLargeUnionFamily ι W aFamily aUnion)
    (hmany : 2 * Fintype.card A ^ aFamily ≤ C.ncard) :
    ∃ c₀ : ι → A, c₀ ∈ C ∧
      ∃ good : Finset (Finset ι), good ⊆ family.sets ∧
        family.sets.card ≤ 2 * good.card ∧
        ∃ alt : Finset ι → ι → A,
          ∀ S ∈ good, alt S ∈ C ∧ alt S ≠ c₀ ∧
            ∀ i ∈ S, alt S i = c₀ i := by
  classical
  let code : Finset (ι → A) := hC.toFinset
  let P : (ι → A) → Finset ι → Prop := fun c S =>
    ∃ z ∈ code, z ≠ c ∧ ∀ i ∈ S, z i = c i
  have hcodecard : code.card = C.ncard := by
    rw [← Set.ncard_coe_finset, hC.coe_toFinset]
  have hqpos : 0 < Fintype.card A := by omega
  have hleftpos : 0 < 2 * Fintype.card A ^ aFamily :=
    Nat.mul_pos (by omega) (pow_pos hqpos aFamily)
  have hcodepos : 0 < code.card := by
    rw [hcodecard]
    exact hleftpos.trans_le hmany
  have hcode : code.Nonempty := Finset.card_pos.mp hcodepos
  have hcol : ∀ S ∈ family.sets,
      code.card ≤ 2 * (code.filter fun c => P c S).card := by
    intro S hS
    have h := aglManyRestrictionAlternatives C hC S aFamily
      (family.card_each S hS) hmany
    simpa only [code, P, hcodecard] using h
  obtain ⟨c₀, hc₀code, hc₀good⟩ :=
    aglGoodBaseByDoubleCount code family.sets P hcode hcol
  let good : Finset (Finset ι) := family.sets.filter fun S => P c₀ S
  have hgoodsub : good ⊆ family.sets := Finset.filter_subset _ _
  have hgoodcard : family.sets.card ≤ 2 * good.card := by
    simpa only [good] using hc₀good
  have haltExists : ∀ S ∈ good,
      ∃ z ∈ code, z ≠ c₀ ∧ ∀ i ∈ S, z i = c₀ i := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hAnonempty : Nonempty A := Fintype.card_pos_iff.mp hqpos
  let defaultWord : ι → A := fun _ => Classical.choice hAnonempty
  let alt : Finset ι → ι → A := fun S =>
    if hS : S ∈ good then Classical.choose (haltExists S hS) else defaultWord
  have haltSpec : ∀ S ∈ good,
      alt S ∈ code ∧ alt S ≠ c₀ ∧ ∀ i ∈ S, alt S i = c₀ i := by
    intro S hS
    dsimp only [alt]
    rw [dif_pos hS]
    exact Classical.choose_spec (haltExists S hS)
  refine ⟨c₀, ?_, good, hgoodsub, hgoodcard, alt, ?_⟩
  · rw [← hC.coe_toFinset]
    exact hc₀code
  · intro S hS
    have hs := haltSpec S hS
    refine ⟨?_, hs.2.1, hs.2.2⟩
    rw [← hC.coe_toFinset]
    exact hs.1

open _root_.ListDecodable in
theorem aglDeterministicPigeonholeBound :
    AGLDeterministicPigeonholeBound := by
  classical
  unfold AGLDeterministicPigeonholeBound
  intro ℓ n radius boosted hℓ hn ι A _ _ _ _ C hA hcard hC
    params hW blocks family hfamilyDisjoint hsep hmany hLambda
  obtain ⟨c₀, hc₀, good, hgoodSub, hgoodCard, alt, halt⟩ :=
    aglGoodBaseWord params.W params.aFamily params.aUnion
      C hC hA family hmany
  let goodFamily : AGLLargeUnionFamily ι params.W
      params.aFamily params.aUnion :=
    { sets := good
      card_each := by
        intro S hS
        exact family.card_each S (hgoodSub hS)
      large_union := by
        intro T hT hTcard
        exact family.large_union T (hT.trans hgoodSub) hTcard }
  have haltC : ∀ S ∈ goodFamily.sets, alt S ∈ C := by
    intro S hS
    exact (halt S hS).1
  have haltNe : ∀ S ∈ goodFamily.sets, alt S ≠ c₀ := by
    intro S hS
    exact (halt S hS).2.1
  have haltAgree : ∀ S ∈ goodFamily.sets,
      ∀ i ∈ S, alt S i = c₀ i := by
    intro S hS
    exact (halt S hS).2.2
  have hAltFiber := aglAlternativeFiberBound
    params.W params.aFamily params.aUnion n boosted C hcard
    goodFamily c₀ hc₀ alt haltC haltNe haltAgree hsep
    params.repeated_codeword_contradiction hW
  by_contra hnot
  have hstrict :
      2 * params.W * ℓ * Fintype.card A ^ params.dZero <
        family.sets.card := Nat.lt_of_not_ge hnot
  let K : ℕ := params.W * ℓ * Fintype.card A ^ params.dZero
  have hstrictK : 2 * K < family.sets.card := by
    simpa only [K, Nat.mul_assoc] using hstrict
  have htwice : 2 * K < 2 * good.card :=
    hstrictK.trans_le hgoodCard
  have hKgood : K < good.card := by omega
  have hqpos : 0 < Fintype.card A := by omega
  have hprodPos :
      0 < Fintype.card A ^ params.dZero * (params.W * ℓ) := by
    exact Nat.mul_pos (pow_pos hqpos params.dZero)
      (Nat.mul_pos hW (by omega))
  have hlargeFiber :
      Fintype.card A ^ params.dZero * (params.W * ℓ) ≤ good.card := by
    have heq : Fintype.card A ^ params.dZero * (params.W * ℓ) = K := by
      dsimp only [K]
      ring
    rw [heq]
    omega
  have hgoodNonempty : good.Nonempty := by
    apply Finset.card_pos.mp
    exact hprodPos.trans_le hlargeFiber
  let restrictZero : Finset ι → (blocks.zero → A) := fun S i => alt S i.1
  have hrestrictImage : (good.image restrictZero).card ≤
      Fintype.card A ^ params.dZero := by
    calc
      (good.image restrictZero).card ≤ Fintype.card (blocks.zero → A) :=
        Finset.card_le_univ _
      _ = Fintype.card A ^ params.dZero := by
        rw [Fintype.card_fun, Fintype.card_coe, blocks.card_zero]
  obtain ⟨common, hcommonImage, hsameCard⟩ :=
    aglLargeFiberOfImageBound good restrictZero
      (Fintype.card A ^ params.dZero) (params.W * ℓ)
      hgoodNonempty hrestrictImage hlargeFiber
  let same : Finset (Finset ι) :=
    good.filter fun S => restrictZero S = common
  have hsameSub : same ⊆ good := Finset.filter_subset _ _
  have hsameCard' : params.W * ℓ ≤ same.card := by
    simpa only [same] using hsameCard
  have hsameFiber : ∀ z,
      (same.filter fun S => alt S = z).card < params.W := by
    intro z
    have hsub :
        same.filter (fun S => alt S = z) ⊆
          good.filter (fun S => alt S = z) := by
      intro S hS
      have hs := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨hsameSub hs.1, hs.2⟩
    exact (Finset.card_le_card hsub).trans_lt (hAltFiber z)
  have hdistinct : ℓ ≤ (same.image alt).card :=
    aglDistinctAlternativesOfBoundedFibers same alt params.W ℓ
      hW hsameCard' hsameFiber
  obtain ⟨chosen, hchosenSame, huinj⟩ :=
    aglChooseDistinctImages same alt ℓ hdistinct
  let u : Fin ℓ → ι → A := fun j => alt (chosen j)
  have hchosenGood : ∀ j, chosen j ∈ good := by
    intro j
    exact hsameSub (hchosenSame j)
  have hchosenFamily : ∀ j, chosen j ∈ family.sets := by
    intro j
    exact hgoodSub (hchosenGood j)
  have hchosenCard : ∀ j, (chosen j).card = params.aFamily := by
    intro j
    exact family.card_each (chosen j) (hchosenFamily j)
  have hchosenDisjoint : ∀ j,
      Disjoint (chosen j) blocks.zero ∧
        ∀ k, Disjoint (chosen j) (blocks.other k) := by
    intro j
    exact hfamilyDisjoint (chosen j) (hchosenFamily j)
  have huAgree : ∀ j, ∀ i ∈ chosen j, u j i = c₀ i := by
    intro j
    exact (halt (chosen j) (hchosenGood j)).2.2
  have huZero : ∀ j, ∀ i, ∀ hi : i ∈ blocks.zero,
      u j i = common ⟨i, hi⟩ := by
    intro j i hi
    have hsame := (Finset.mem_filter.mp (hchosenSame j)).2
    exact congrFun hsame ⟨i, hi⟩
  obtain ⟨y, hyc, hyu⟩ := aglBarrierCenterFromBlocks
    ℓ n params.dZero params.dOne params.aFamily hcard blocks
    c₀ chosen u common hchosenCard hchosenDisjoint huAgree huZero
  have hycRadius : hammingDist c₀ y ≤ radius :=
    hyc.trans params.center_block_bound
  have hyuRadius : ∀ j, hammingDist (u j) y ≤ radius := by
    intro j
    exact (hyu j).trans params.other_codeword_bound
  have hιpos : 0 < Fintype.card ι := by
    rw [hcard]
    exact hn
  letI : Nonempty ι := Fintype.card_pos_iff.mp hιpos
  have hp : 0 ≤ (radius : ℝ) / n := by positivity
  have hfloor :
      Nat.floor (((radius : ℝ) / n) * Fintype.card ι) = radius := by
    rw [hcard]
    exact aglFloorDivMulSelf radius n hn
  have huC : ∀ j, u j ∈ C := by
    intro j
    exact (halt (chosen j) (hchosenGood j)).1
  have huc : ∀ j, u j ≠ c₀ := by
    intro j
    exact (halt (chosen j) (hchosenGood j)).2.1
  have huinj' : Function.Injective u := by
    simpa only [u] using huinj
  exact aglLambdaContradictionOfInjectiveCenter
    ℓ C ((radius : ℝ) / n) hp c₀ hc₀ u huinj' huC huc y
    (by simpa only [hfloor] using hycRadius)
    (by intro j; simpa only [hfloor] using hyuRadius j) hLambda

theorem aglSmallAlphabetPowerBound
    (q dZero n : ℕ) (α η K γ : ℝ)
    (hα : 0 ≤ α) (hη : 0 < η) (hK : 0 ≤ K)
    (hq : (q : ℝ) < (2 : ℝ) ^ (α / η))
    (hdZero : dZero ≤ Nat.ceil (K * η * n))
    (hone : 1 ≤ η * n)
    (hbudget : α * (K + 1) ≤ γ / 4) :
    ((q ^ dZero : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((γ / 4) * n) := by
  have hceil := aglCeilLinearBound K η n hK hη.le hone
  have hdZeroR : (dZero : ℝ) < (K + 1) * η * n := by
    have hcast : (dZero : ℝ) ≤
        (Nat.ceil (K * η * n) : ℝ) := by exact_mod_cast hdZero
    exact hcast.trans_lt hceil
  have hfactor : 0 ≤ α / η := div_nonneg hα hη.le
  have hexpMid : (α / η) * (dZero : ℝ) ≤
      α * (K + 1) * n := by
    calc
      (α / η) * (dZero : ℝ) ≤
          (α / η) * ((K + 1) * η * n) :=
        mul_le_mul_of_nonneg_left hdZeroR.le hfactor
      _ = α * (K + 1) * n := by
        field_simp [ne_of_gt hη]
  have hbudgetN : α * (K + 1) * (n : ℝ) ≤
      (γ / 4) * n :=
    mul_le_mul_of_nonneg_right hbudget (by positivity)
  have hexp : (α / η) * (dZero : ℝ) ≤ (γ / 4) * n :=
    hexpMid.trans hbudgetN
  have hqpow : (q : ℝ) ^ dZero ≤
      ((2 : ℝ) ^ (α / η)) ^ dZero :=
    pow_le_pow_left₀ (by positivity) hq.le dZero
  calc
    ((q ^ dZero : ℕ) : ℝ) = (q : ℝ) ^ dZero := by norm_num
    _ ≤ ((2 : ℝ) ^ (α / η)) ^ dZero := hqpow
    _ = (2 : ℝ) ^ ((α / η) * (dZero : ℝ)) :=
      (Real.rpow_mul_natCast (by norm_num) (α / η) dZero).symm
    _ ≤ (2 : ℝ) ^ ((γ / 4) * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

noncomputable def aglSmallRadius (ℓ : ℕ) (ρ : ℝ) : ℝ :=
  (ℓ : ℝ) / (ℓ + 1) * ((1 - ρ) / 2)

noncomputable def aglBarrierEtaCut (ℓ : ℕ) (R : ℝ) (B : ℕ) : ℝ :=
  min ((1 - R) / 2)
    (aglSmallRadius ℓ R / (2 * (aglBarrierK ℓ B + 1)))

theorem aglBarrierRadiusWindow
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (η : ℝ) (hηpos : 0 < η) (hηcut : η < (1 - R) / 2) :
    0 < aglSmallRadius ℓ R ∧
      aglSmallRadius ℓ R ≤ aglRadius ℓ R η ∧
      0 < aglRadius ℓ R η ∧
      aglRadius ℓ R η < (ℓ : ℝ) / (ℓ + 1) ∧
      aglRadius ℓ R η < aglBoostedRadius ℓ (aglRadius ℓ R η) ∧
      aglBoostedRadius ℓ (aglRadius ℓ R η) < 1 := by
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hcoef : (0 : ℝ) < (ℓ : ℝ) / (ℓ + 1) := by positivity
  have hcoef1 : (ℓ : ℝ) / (ℓ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hgapSmall : 0 < (1 - R) / 2 := by positivity
  have hsmall : 0 < aglSmallRadius ℓ R := by
    unfold aglSmallRadius
    exact mul_pos hcoef hgapSmall
  have hsmallLe : aglSmallRadius ℓ R ≤ aglRadius ℓ R η := by
    unfold aglSmallRadius aglRadius
    apply mul_le_mul_of_nonneg_left _ hcoef.le
    linarith
  have hηlt : η < 1 - R := by linarith
  have hp : 0 < aglRadius ℓ R η :=
    aglRadius_pos ℓ hℓpos R η hηlt
  have hgapOne : 1 - R - η < 1 := by linarith
  have hpcoef : aglRadius ℓ R η < (ℓ : ℝ) / (ℓ + 1) := by
    unfold aglRadius
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hgapOne hcoef
  have hpOne : aglRadius ℓ R η < 1 := hpcoef.trans hcoef1
  have hboost : aglRadius ℓ R η <
      aglBoostedRadius ℓ (aglRadius ℓ R η) :=
    aglBoostedRadius_gt ℓ hℓpos _ hp
  have hpow : aglRadius ℓ R η ^ ℓ ≤ aglRadius ℓ R η :=
    pow_le_of_le_one hp.le hpOne.le (Nat.ne_of_gt hℓpos)
  have hdiv : aglRadius ℓ R η ^ ℓ / (2 * ℓ) ≤
      aglRadius ℓ R η / (2 * ℓ) :=
    div_le_div_of_nonneg_right hpow
      (show (0 : ℝ) ≤ 2 * ℓ by positivity)
  have hfacPos : (0 : ℝ) < 1 + 1 / (2 * ℓ) := by positivity
  have hcoefFac :
      ((ℓ : ℝ) / (ℓ + 1)) * (1 + 1 / (2 * ℓ)) < 1 := by
    field_simp [ne_of_gt hℓR]
    nlinarith
  have hboostOne : aglBoostedRadius ℓ (aglRadius ℓ R η) < 1 := by
    unfold aglBoostedRadius
    calc
      aglRadius ℓ R η + aglRadius ℓ R η ^ ℓ / (2 * ℓ) ≤
          aglRadius ℓ R η + aglRadius ℓ R η / (2 * ℓ) :=
        add_le_add le_rfl hdiv
      _ = aglRadius ℓ R η * (1 + 1 / (2 * ℓ)) := by ring
      _ < ((ℓ : ℝ) / (ℓ + 1)) * (1 + 1 / (2 * ℓ)) :=
        mul_lt_mul_of_pos_right hpcoef hfacPos
      _ < 1 := hcoefFac
  exact ⟨hsmall, hsmallLe, hp, hpcoef, hboost, hboostOne⟩

noncomputable def aglBarrierXiDensity (ℓ : ℕ) (R : ℝ) : ℝ :=
  aglSmallRadius ℓ R ^ ℓ / (8 * ℓ)

noncomputable def aglBarrierBetaDensity (ℓ : ℕ) (R : ℝ) : ℝ :=
  1 - aglBarrierXiDensity ℓ R

theorem aglBarrierConstantBounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) :
    0 < aglBarrierK ℓ B ∧
      0 < aglBarrierEtaCut ℓ R B ∧
      aglBarrierEtaCut ℓ R B ≤ (1 - R) / 2 ∧
      aglBarrierEtaCut ℓ R B ≤
        aglSmallRadius ℓ R / (2 * (aglBarrierK ℓ B + 1)) ∧
      0 < aglBarrierAlphaDensity R ∧
      aglBarrierAlphaDensity R < aglBarrierBetaDensity ℓ R ∧
      aglBarrierBetaDensity ℓ R < 1 ∧
      0 < aglBarrierXiDensity ℓ R := by
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hℓTwo : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hcoef : (0 : ℝ) < (ℓ : ℝ) / (ℓ + 1) := by positivity
  have hcoeflt : (ℓ : ℝ) / (ℓ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hgap : 0 < (1 - R) / 2 := by linarith
  have hgaplt : (1 - R) / 2 < 1 := by linarith
  have hpMin : 0 < aglSmallRadius ℓ R := by
    unfold aglSmallRadius
    exact mul_pos hcoef hgap
  have hpMinlt : aglSmallRadius ℓ R < 1 := by
    unfold aglSmallRadius
    calc
      (ℓ : ℝ) / (ℓ + 1) * ((1 - R) / 2) <
          1 * ((1 - R) / 2) := mul_lt_mul_of_pos_right hcoeflt hgap
      _ < 1 := by simpa only [one_mul] using hgaplt
  have hK : 0 < aglBarrierK ℓ B := by
    unfold aglBarrierK
    positivity
  have hsecond :
      0 < aglSmallRadius ℓ R / (2 * (aglBarrierK ℓ B + 1)) := by
    positivity
  have hEta : 0 < aglBarrierEtaCut ℓ R B := by
    unfold aglBarrierEtaCut
    exact lt_min hgap hsecond
  have hAlpha : 0 < aglBarrierAlphaDensity R := by
    unfold aglBarrierAlphaDensity
    positivity
  have hXi : 0 < aglBarrierXiDensity ℓ R := by
    unfold aglBarrierXiDensity
    positivity
  have hpow : aglSmallRadius ℓ R ^ ℓ ≤ aglSmallRadius ℓ R :=
    pow_le_of_le_one hpMin.le hpMinlt.le (Nat.ne_of_gt hℓpos)
  have hXiHalf : aglBarrierXiDensity ℓ R < (1 : ℝ) / 2 := by
    unfold aglBarrierXiDensity
    have hden : (0 : ℝ) < 8 * ℓ := by positivity
    rw [div_lt_iff₀ hden]
    have hpOne : aglSmallRadius ℓ R ^ ℓ < 1 := hpow.trans_lt hpMinlt
    nlinarith
  have hAlphaHalf : aglBarrierAlphaDensity R < (1 : ℝ) / 2 := by
    unfold aglBarrierAlphaDensity
    linarith
  have hAlphaBeta :
      aglBarrierAlphaDensity R < aglBarrierBetaDensity ℓ R := by
    unfold aglBarrierBetaDensity
    linarith
  have hBetaOne : aglBarrierBetaDensity ℓ R < 1 := by
    unfold aglBarrierBetaDensity
    linarith
  exact ⟨hK, hEta, min_le_left _ _, min_le_right _ _, hAlpha,
    hAlphaBeta, hBetaOne, hXi⟩

theorem aglBarrierDensityRealGaps
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) :
    let p := aglRadius ℓ R η
    let p₀ := aglSmallRadius ℓ R
    let ξ := aglBarrierXiDensity ℓ R
    let β := aglBarrierBetaDensity ℓ R
    R < β * (1 - p) ∧
      1 - aglBoostedRadius ℓ p + 3 * ξ ≤ β * (1 - p) := by
  dsimp only
  let p := aglRadius ℓ R η
  let p₀ := aglSmallRadius ℓ R
  let ξ := aglBarrierXiDensity ℓ R
  let β := aglBarrierBetaDensity ℓ R
  change R < β * (1 - p) ∧
    1 - aglBoostedRadius ℓ p + 3 * ξ ≤ β * (1 - p)
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  rcases aglBarrierConstantBounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBeta, hXi⟩
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases aglBarrierRadiusWindow ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hp₀, hp₀le, hp, hpCoef, hBoost, hBoostOne⟩
  change 0 < p₀ at hp₀
  change p₀ ≤ p at hp₀le
  change 0 < p at hp
  change p < aglBoostedRadius ℓ p at hBoost
  have hpOne : p < 1 := hBoost.trans hBoostOne
  have hp₀One : p₀ < 1 := hp₀le.trans_lt hpOne
  change 0 < ξ at hXi
  have hbalance : R + p + p / (ℓ : ℝ) = 1 - η := by
    simpa only [p] using aglRadiusBalance ℓ hℓpos R η
  have hp₀pow : p₀ ^ ℓ ≤ p₀ :=
    pow_le_of_le_one hp₀.le hp₀One.le (Nat.ne_of_gt hℓpos)
  have hpowLeP : p₀ ^ ℓ ≤ p := hp₀pow.trans hp₀le
  have hxiLe : ξ ≤ p / (8 * (ℓ : ℝ)) := by
    dsimp only [ξ, p₀, aglBarrierXiDensity]
    exact div_le_div_of_nonneg_right hpowLeP (by positivity)
  have hpDivStrict : p / (8 * (ℓ : ℝ)) < p / (ℓ : ℝ) := by
    field_simp [ne_of_gt hℓR]
    nlinarith
  have hxiLt : ξ < p / (ℓ : ℝ) := hxiLe.trans_lt hpDivStrict
  have hxiMul : ξ * (1 - p) ≤ ξ := by
    nlinarith [mul_nonneg hXi.le hp.le]
  have hxiMulLt : ξ * (1 - p) < p / (ℓ : ℝ) :=
    hxiMul.trans_lt hxiLt
  have hgapOne :
      β * (1 - p) - R =
        η + p / (ℓ : ℝ) - ξ * (1 - p) := by
    dsimp only [β, aglBarrierBetaDensity]
    nlinarith [hbalance]
  have hpowMono : p₀ ^ ℓ ≤ p ^ ℓ :=
    pow_le_pow_left₀ hp₀.le hp₀le ℓ
  have hfourXi : 4 * ξ ≤ p ^ ℓ / (2 * (ℓ : ℝ)) := by
    calc
      4 * ξ = p₀ ^ ℓ / (2 * (ℓ : ℝ)) := by
        dsimp only [ξ, aglBarrierXiDensity]
        ring
      _ ≤ p ^ ℓ / (2 * (ℓ : ℝ)) :=
        div_le_div_of_nonneg_right hpowMono (by positivity)
  have hxiFour : ξ * (4 - p) ≤ p ^ ℓ / (2 * (ℓ : ℝ)) := by
    calc
      ξ * (4 - p) ≤ ξ * 4 :=
        mul_le_mul_of_nonneg_left (by linarith) hXi.le
      _ = 4 * ξ := by ring
      _ ≤ p ^ ℓ / (2 * (ℓ : ℝ)) := hfourXi
  have hgapTwo :
      β * (1 - p) - (1 - aglBoostedRadius ℓ p + 3 * ξ) =
        p ^ ℓ / (2 * (ℓ : ℝ)) - ξ * (4 - p) := by
    dsimp only [β, aglBarrierBetaDensity, aglBoostedRadius]
    ring
  constructor
  · apply sub_pos.mp
    rw [hgapOne]
    linarith
  · apply sub_nonneg.mp
    rw [hgapTwo]
    exact sub_nonneg.mpr hxiFour

noncomputable def aglLocalLengthThreshold (ℓ : ℕ) (ρ : ℝ) : ℕ :=
  Nat.ceil (8 * (ℓ : ℝ) / (aglSmallRadius ℓ ρ) ^ ℓ)

noncomputable def aglNeighborhoodCap (ℓ : ℕ) (ρ : ℝ) : ℕ :=
  ℓ + Nat.ceil (4 * (ℓ : ℝ) ^ 2 / aglSmallRadius ℓ ρ)

theorem aglRoundedBarrierBasicBounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) (n : ℕ)
    (hn : aglRoundedBarrierBasicThreshold R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n := by
  dsimp only [aglRoundedBarrierData]
  rcases aglBarrierConstantBounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBeta, hXi⟩
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases aglBarrierRadiusWindow ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  have hone : 1 ≤ η * (n : ℝ) :=
    aglEtaTimesLengthOne η n hηpos hlen
  have hnR : (0 : ℝ) < n := by
    by_contra hnot
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hprod : η * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hηpos.le hnle
    linarith
  have hrateCeil : (((B + 1 : ℕ) : ℝ) / R) ≤ (n : ℝ) := by
    apply (Nat.ceil_le).mp
    simpa only [aglRoundedBarrierBasicThreshold] using hn
  have hrateReal : ((B + 1 : ℕ) : ℝ) ≤ R * n := by
    have h := (div_le_iff₀ hRpos).mp hrateCeil
    simpa only [mul_comm] using h
  have hrateFloor : B + 1 ≤ Nat.floor (R * n) := by
    exact (Nat.le_floor_iff (mul_nonneg hRpos.le hnR.le)).2 hrateReal
  have hden : 0 < 2 * (aglBarrierK ℓ B + 1) := by positivity
  have hηSecondStrict :
      η < aglSmallRadius ℓ R /
        (2 * (aglBarrierK ℓ B + 1)) := hηcut.trans_le hEtaSecond
  have hcross := (lt_div_iff₀ hden).mp hηSecondStrict
  have hKeta :
      (aglBarrierK ℓ B + 1) * η < aglSmallRadius ℓ R / 2 := by
    nlinarith
  have hKetaN :
      (aglBarrierK ℓ B + 1) * η * n <
        aglSmallRadius ℓ R / 2 * n :=
    mul_lt_mul_of_pos_right hKeta hnR
  have hhalfP : aglSmallRadius ℓ R / 2 < aglRadius ℓ R η := by
    nlinarith [hpMinLe]
  have hhalfPN : aglSmallRadius ℓ R / 2 * n <
      aglRadius ℓ R η * n :=
    mul_lt_mul_of_pos_right hhalfP hnR
  have hceil := aglCeilLinearBound
    (aglBarrierK ℓ B) η n hK.le hηpos.le hone
  have hdZero : Nat.ceil (aglBarrierK ℓ B * η * n) ≤
      Nat.floor (aglRadius ℓ R η * n) := by
    apply (Nat.le_floor_iff (mul_nonneg hp.le hnR.le)).2
    exact (hceil.trans (hKetaN.trans hhalfPN)).le
  have hBoostPosReal :
      0 < aglBoostedRadius ℓ (aglRadius ℓ R η) * n :=
    mul_pos (hp.trans hBoost) hnR
  have hBoostPos :
      0 < Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * n) :=
    (Nat.ceil_pos).2 hBoostPosReal
  have hBoostLe :
      Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * n) ≤ n := by
    apply (Nat.ceil_le).2
    have h := mul_le_mul_of_nonneg_right hBoostOne.le hnR.le
    simpa only [one_mul] using h
  have hCoefOne : (ℓ : ℝ) / (ℓ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hpOne : aglRadius ℓ R η < 1 := hpCoef.trans hCoefOne
  have hRadiusLe : Nat.floor (aglRadius ℓ R η * n) ≤ n := by
    have hmul : aglRadius ℓ R η * n ≤ (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hpOne.le hnR.le
      simpa only [one_mul] using h
    have hfloor := Nat.floor_mono hmul
    simpa only [Nat.floor_natCast] using hfloor
  exact ⟨hone, hrateFloor, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩

noncomputable def aglRoundedBarrierDensityThreshold
    (ℓ : ℕ) (R : ℝ) (B : ℕ) : ℕ :=
  max (aglRoundedBarrierBasicThreshold R B)
    (max
      (Nat.ceil (((2 * (B + 2) : ℕ) : ℝ) / R))
      (Nat.ceil (1 / (3 * aglBarrierXiDensity ℓ R))))

theorem aglRoundedBarrierDensityThresholdBounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (n : ℕ)
    (hn : aglRoundedBarrierDensityThreshold ℓ R B ≤ n) :
    aglRoundedBarrierBasicThreshold R B ≤ n ∧
      ((2 * (B + 2) : ℕ) : ℝ) ≤ R * n ∧
      1 ≤ 3 * aglBarrierXiDensity ℓ R * n := by
  have hBasic : aglRoundedBarrierBasicThreshold R B ≤ n := by
    dsimp only [aglRoundedBarrierDensityThreshold] at hn
    omega
  have hRateCeil :
      Nat.ceil (((2 * (B + 2) : ℕ) : ℝ) / R) ≤ n := by
    dsimp only [aglRoundedBarrierDensityThreshold] at hn
    omega
  have hRateDiv : ((2 * (B + 2) : ℕ) : ℝ) / R ≤ n :=
    (Nat.ceil_le).mp hRateCeil
  have hRate : ((2 * (B + 2) : ℕ) : ℝ) ≤ R * n := by
    have h := (div_le_iff₀ hRpos).mp hRateDiv
    simpa only [mul_comm] using h
  rcases aglBarrierConstantBounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBeta, hXi⟩
  have hXiCeil :
      Nat.ceil (1 / (3 * aglBarrierXiDensity ℓ R)) ≤ n := by
    dsimp only [aglRoundedBarrierDensityThreshold] at hn
    omega
  have hXiDiv :
      1 / (3 * aglBarrierXiDensity ℓ R) ≤ (n : ℝ) :=
    (Nat.ceil_le).mp hXiCeil
  have hden : 0 < 3 * aglBarrierXiDensity ℓ R := by positivity
  have hXiBound : 1 ≤ 3 * aglBarrierXiDensity ℓ R * n := by
    have h := (div_le_iff₀ hden).mp hXiDiv
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using h
  exact ⟨hBasic, hRate, hXiBound⟩

theorem aglRoundedBarrierLowerFamilyDensity
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) (n : ℕ)
    (hn : aglRoundedBarrierDensityThreshold ℓ R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    Nat.floor (aglBarrierAlphaDensity R * d.unused) ≤ d.aFamily := by
  let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
  change Nat.floor (aglBarrierAlphaDensity R * d.unused) ≤ d.aFamily
  have hRateCeil :
      Nat.ceil (((2 * (B + 2) : ℕ) : ℝ) / R) ≤ n := by
    dsimp only [aglRoundedBarrierDensityThreshold] at hn
    omega
  have hRateDiv : (((2 * (B + 2) : ℕ) : ℝ) / R) ≤ (n : ℝ) :=
    (Nat.ceil_le).mp hRateCeil
  have hRate : ((2 * (B + 2) : ℕ) : ℝ) ≤ R * n := by
    have h := (div_le_iff₀ hRpos).mp hRateDiv
    simpa only [mul_comm] using h
  have hmle : d.unused ≤ n := by
    dsimp only [d, aglRoundedBarrierData]
    exact Nat.sub_le _ _
  have hmleR : (d.unused : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmle
  have hhalf :
      (R / 2) * (d.unused : ℝ) + (B + 1 : ℕ) ≤ R * n := by
    have hmhalf : (R / 2) * (d.unused : ℝ) ≤ (R / 2) * n :=
      mul_le_mul_of_nonneg_left hmleR (by positivity)
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hRate ⊢
    nlinarith
  have htermNonneg : 0 ≤ (R / 2) * (d.unused : ℝ) := by positivity
  have hfloorTerm :
      (Nat.floor ((R / 2) * (d.unused : ℝ)) : ℝ) ≤
        (R / 2) * (d.unused : ℝ) := Nat.floor_le htermNonneg
  have hRn : 0 ≤ R * (n : ℝ) := by positivity
  have hsumReal :
      ((Nat.floor ((R / 2) * (d.unused : ℝ)) + (B + 1) : ℕ) : ℝ) ≤
        R * n := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hhalf ⊢
    linarith
  have hsum :
      Nat.floor ((R / 2) * (d.unused : ℝ)) + (B + 1) ≤
        Nat.floor (R * n) :=
    (Nat.le_floor_iff hRn).2 hsumReal
  have hfamily : d.aFamily = Nat.floor (R * n) - (B + 1) := by
    rfl
  rw [hfamily]
  unfold aglBarrierAlphaDensity
  omega

theorem aglRoundedBarrierOtherCodewordBound
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) (n : ℕ)
    (hn : aglRoundedBarrierBasicThreshold R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    n - d.dZero - d.dOne - d.aFamily ≤ d.radius := by
  have hbasic := aglRoundedBarrierBasicBounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  dsimp only at hbasic ⊢
  exact aglRoundedBarrierOtherCodewordBoundCore
    ℓ hℓ R η B n hbasic.1 hbasic.2.1 hbasic.2.2.1

theorem aglBarrierParametersExist
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) (n W : ℕ) (hW : 0 < W)
    (hn : aglRoundedBarrierBasicThreshold R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    ∃ params : AGLBarrierParameters ℓ n d.radius d.boosted,
      0 < params.W ∧ params.W = W ∧
      params.aFamily = d.aFamily ∧ params.aUnion = d.aUnion ∧
      params.dZero = d.dZero ∧ params.dOne = d.dOne := by
  let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
  change ∃ params : AGLBarrierParameters ℓ n d.radius d.boosted,
    0 < params.W ∧ params.W = W ∧
    params.aFamily = d.aFamily ∧ params.aUnion = d.aUnion ∧
    params.dZero = d.dZero ∧ params.dOne = d.dOne
  have hbasic :
      1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
        d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
        d.boosted ≤ n ∧ d.radius ≤ n := by
    simpa only [d] using aglRoundedBarrierBasicBounds
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  have hℓpos : 0 < ℓ := by omega
  have hquot := aglNatQuotientWindow
    ℓ d.radius d.dZero n hℓpos hdZero hRadiusLe
  have hcenter : d.dZero + ℓ * d.dOne ≤ d.radius := by
    simpa only [d, aglRoundedBarrierData] using hquot.1
  have hother : n - d.dZero - d.dOne - d.aFamily ≤ d.radius := by
    simpa only [d] using aglRoundedBarrierOtherCodewordBound
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  have hrepeated : n - d.aUnion < d.boosted := by
    dsimp only [d, aglRoundedBarrierData] at hBoostPos hBoostLe ⊢
    omega
  let params : AGLBarrierParameters ℓ n d.radius d.boosted :=
    { aFamily := d.aFamily
      aUnion := d.aUnion
      dZero := d.dZero
      dOne := d.dOne
      W := W
      center_block_bound := hcenter
      other_codeword_bound := hother
      repeated_codeword_contradiction := hrepeated }
  refine ⟨params, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [params] using hW
  all_goals rfl

theorem aglRoundedBarrierQuotientBounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B n : ℕ) (η : ℝ) (hηpos : 0 < η)
    (hηhalf : η < (1 - R) / 2)
    (hdZero :
      (aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n).dZero ≤
        (aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n).radius)
    (hradius :
      (aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n).radius ≤ n) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    d.used ≤ d.radius ∧ d.radius < d.used + ℓ ∧
      n - d.radius ≤ d.unused ∧
      d.unused ≤ n - d.radius + (ℓ - 1) ∧
      Nat.floor (R * n) ≤ d.unused ∧ d.aFamily ≤ d.unused ∧
      n ≤ (ℓ + 1) * d.unused := by
  dsimp only [aglRoundedBarrierData] at hdZero hradius ⊢
  have hℓpos : 0 < ℓ := by omega
  by_cases hnzero : n = 0
  · subst n
    simp [Nat.zero_div, hℓpos]
  have hn : 0 < n := Nat.pos_of_ne_zero hnzero
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  rcases aglNatQuotientWindow ℓ
      (Nat.floor (aglRadius ℓ R η * n))
      (Nat.ceil (aglBarrierK ℓ B * η * n)) n hℓpos hdZero hradius with
    ⟨hused, hrUsed, hmLower, hmUpper⟩
  rcases aglBarrierRadiusWindow ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  have hbalance := aglRadiusBalance ℓ hℓpos R η
  have hpDiv : 0 < aglRadius ℓ R η / (ℓ : ℝ) :=
    div_pos hp hℓR
  have hRp : R + aglRadius ℓ R η < 1 := by linarith
  have hRfloor : (Nat.floor (R * n) : ℝ) ≤ R * n :=
    Nat.floor_le (mul_nonneg hRpos.le hnR.le)
  have hPfloor : (Nat.floor (aglRadius ℓ R η * n) : ℝ) ≤
      aglRadius ℓ R η * n :=
    Nat.floor_le (mul_nonneg hp.le hnR.le)
  have hRpN : (R + aglRadius ℓ R η) * n < (n : ℝ) := by
    have h := mul_lt_mul_of_pos_right hRp hnR
    simpa only [one_mul] using h
  have hsumReal :
      (Nat.floor (R * n) : ℝ) +
          Nat.floor (aglRadius ℓ R η * n) < n := by
    calc
      (Nat.floor (R * n) : ℝ) +
          Nat.floor (aglRadius ℓ R η * n) ≤
          R * n + aglRadius ℓ R η * n := add_le_add hRfloor hPfloor
      _ = (R + aglRadius ℓ R η) * n := by ring
      _ < n := hRpN
  have hsumNat :
      Nat.floor (R * n) + Nat.floor (aglRadius ℓ R η * n) ≤ n := by
    exact_mod_cast hsumReal.le
  have hfloorM : Nat.floor (R * n) ≤
      n - (Nat.ceil (aglBarrierK ℓ B * η * n) +
        ℓ * ((Nat.floor (aglRadius ℓ R η * n) -
          Nat.ceil (aglBarrierK ℓ B * η * n)) / ℓ)) := by
    omega
  have haM : Nat.floor (R * n) - (B + 1) ≤
      n - (Nat.ceil (aglBarrierK ℓ B * η * n) +
        ℓ * ((Nat.floor (aglRadius ℓ R η * n) -
          Nat.ceil (aglBarrierK ℓ B * η * n)) / ℓ)) := by
    exact (Nat.sub_le _ _).trans hfloorM
  have hden : (0 : ℝ) < ℓ + 1 := by positivity
  have hpCross : aglRadius ℓ R η * ((ℓ : ℝ) + 1) < ℓ := by
    exact (lt_div_iff₀ hden).mp hpCoef
  have hpCrossN :
      (aglRadius ℓ R η * ((ℓ : ℝ) + 1)) * n < (ℓ : ℝ) * n :=
    mul_lt_mul_of_pos_right hpCross hnR
  have hscaledReal :
      ((ℓ + 1 : ℕ) : ℝ) * Nat.floor (aglRadius ℓ R η * n) <
        (ℓ : ℝ) * n := by
    calc
      ((ℓ + 1 : ℕ) : ℝ) * Nat.floor (aglRadius ℓ R η * n) ≤
          ((ℓ : ℝ) + 1) * (aglRadius ℓ R η * n) := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        exact mul_le_mul_of_nonneg_left hPfloor (by positivity)
      _ = (aglRadius ℓ R η * ((ℓ : ℝ) + 1)) * n := by ring
      _ < (ℓ : ℝ) * n := hpCrossN
  have hnLowerReal : (n : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) *
      (n - Nat.floor (aglRadius ℓ R η * n) : ℕ) := by
    rw [Nat.cast_sub hradius]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hnLower : n ≤ (ℓ + 1) *
      (n - Nat.floor (aglRadius ℓ R η * n)) := by
    exact_mod_cast hnLowerReal
  have hnM : n ≤ (ℓ + 1) *
      (n - (Nat.ceil (aglBarrierK ℓ B * η * n) +
        ℓ * ((Nat.floor (aglRadius ℓ R η * n) -
          Nat.ceil (aglBarrierK ℓ B * η * n)) / ℓ))) := by
    exact hnLower.trans
      (Nat.mul_le_mul_left (ℓ + 1) hmLower)
  exact ⟨hused, hrUsed, hmLower, hmUpper, hfloorM, haM, hnM⟩

theorem aglRoundedBarrierUpperFamilyDensity
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) (n : ℕ)
    (hn : aglRoundedBarrierDensityThreshold ℓ R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    d.aFamily < Nat.ceil (aglBarrierBetaDensity ℓ R * d.unused) := by
  let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
  let p := aglRadius ℓ R η
  let β := aglBarrierBetaDensity ℓ R
  change d.aFamily < Nat.ceil (β * d.unused)
  rcases aglRoundedBarrierDensityThresholdBounds
      ℓ hℓ R hRpos hRlt B hB n hn with
    ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
  have hbasic := aglRoundedBarrierBasicBounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hBasicThreshold hlen
  change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n at hbasic
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  rcases aglBarrierConstantBounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  have hBetaPos : 0 < β := by
    change 0 < aglBarrierBetaDensity ℓ R
    exact hAlpha.trans hAlphaBeta
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases aglRoundedBarrierQuotientBounds
      ℓ hℓ R hRpos hRlt B n η hηpos hηhalf
      (by simpa only [d] using hdZero)
      (by simpa only [d] using hRadiusLe) with
    ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
  rcases aglBarrierDensityRealGaps
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut with
    ⟨hRateGap, hUnionGap⟩
  change R < β * (1 - p) at hRateGap
  rcases aglBarrierRadiusWindow
      ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  change 0 < p at hp
  have hnR : (0 : ℝ) < n := by
    by_contra hnot
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hprod : η * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hηpos.le hnle
    linarith
  have hAFloor : d.aFamily ≤ Nat.floor (R * n) := by
    dsimp only [d, aglRoundedBarrierData]
    exact Nat.sub_le _ _
  have hAReal : (d.aFamily : ℝ) ≤ R * n := by
    calc
      (d.aFamily : ℝ) ≤ (Nat.floor (R * n) : ℝ) := by
        exact_mod_cast hAFloor
      _ ≤ R * n := Nat.floor_le (by positivity)
  have hRadiusFloor : (d.radius : ℝ) ≤ p * n := by
    dsimp only [d, aglRoundedBarrierData, p]
    exact Nat.floor_le (by positivity)
  have hSubCast : ((n - d.radius : ℕ) : ℝ) =
      (n : ℝ) - d.radius := Nat.cast_sub hRadiusLe
  have hOneP : (1 - p) * (n : ℝ) ≤ (n - d.radius : ℕ) := by
    rw [hSubCast]
    nlinarith
  have hmLowerR : ((n - d.radius : ℕ) : ℝ) ≤ d.unused := by
    exact_mod_cast hmLower
  have hGapN : R * (n : ℝ) < β * ((1 - p) * n) := by
    calc
      R * (n : ℝ) < (β * (1 - p)) * n :=
        mul_lt_mul_of_pos_right hRateGap hnR
      _ = β * ((1 - p) * n) := by ring
  have hBetaSub : β * ((1 - p) * n) ≤ β * d.unused := by
    apply mul_le_mul_of_nonneg_left _ hBetaPos.le
    exact hOneP.trans hmLowerR
  apply (Nat.lt_ceil).2
  exact hAReal.trans_lt (hGapN.trans_le hBetaSub)

theorem aglRoundedBarrierUpperUnionDensity
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) (n : ℕ)
    (hn : aglRoundedBarrierDensityThreshold ℓ R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    d.aUnion ≤ Nat.ceil (aglBarrierBetaDensity ℓ R * d.unused) := by
  let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
  let p := aglRadius ℓ R η
  let p' := aglBoostedRadius ℓ p
  let ξ := aglBarrierXiDensity ℓ R
  let β := aglBarrierBetaDensity ℓ R
  change d.aUnion ≤ Nat.ceil (β * d.unused)
  rcases aglRoundedBarrierDensityThresholdBounds
      ℓ hℓ R hRpos hRlt B hB n hn with
    ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
  change 1 ≤ 3 * ξ * n at hXiBudget
  have hbasic := aglRoundedBarrierBasicBounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hBasicThreshold hlen
  change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n at hbasic
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  rcases aglBarrierConstantBounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  have hBetaPos : 0 < β := by
    change 0 < aglBarrierBetaDensity ℓ R
    exact hAlpha.trans hAlphaBeta
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases aglRoundedBarrierQuotientBounds
      ℓ hℓ R hRpos hRlt B n η hηpos hηhalf
      (by simpa only [d] using hdZero)
      (by simpa only [d] using hRadiusLe) with
    ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
  rcases aglBarrierDensityRealGaps
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut with
    ⟨hRateGap, hUnionGap⟩
  change 1 - p' + 3 * ξ ≤ β * (1 - p) at hUnionGap
  rcases aglBarrierRadiusWindow
      ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  change 0 < p at hp
  have hnR : (0 : ℝ) < n := by
    by_contra hnot
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hprod : η * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hηpos.le hnle
    linarith
  have hBoostLower : p' * (n : ℝ) ≤ (d.boosted : ℝ) := by
    dsimp only [d, aglRoundedBarrierData, p', p]
    exact Nat.le_ceil _
  have hBoostLeSucc : d.boosted ≤ n + 1 := hBoostLe.trans (Nat.le_succ n)
  have hBoostLeSucc' :
      Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * n) ≤ n + 1 := by
    simpa only [d, aglRoundedBarrierData] using hBoostLeSucc
  have hAUnionCast : (d.aUnion : ℝ) =
      (n : ℝ) + 1 - d.boosted := by
    dsimp only [d, aglRoundedBarrierData]
    rw [Nat.cast_sub hBoostLeSucc']
    norm_num
  have hUnionBase : (d.aUnion : ℝ) ≤ (1 - p') * n + 1 := by
    rw [hAUnionCast]
    nlinarith
  have hUnionBudget : (1 - p') * n + 1 ≤
      (1 - p' + 3 * ξ) * n := by
    nlinarith
  have hGapN : (1 - p' + 3 * ξ) * n ≤
      β * ((1 - p) * n) := by
    calc
      (1 - p' + 3 * ξ) * (n : ℝ) ≤ (β * (1 - p)) * n :=
        mul_le_mul_of_nonneg_right hUnionGap hnR.le
      _ = β * ((1 - p) * n) := by ring
  have hRadiusFloor : (d.radius : ℝ) ≤ p * n := by
    dsimp only [d, aglRoundedBarrierData, p]
    exact Nat.floor_le (by positivity)
  have hSubCast : ((n - d.radius : ℕ) : ℝ) =
      (n : ℝ) - d.radius := Nat.cast_sub hRadiusLe
  have hOneP : (1 - p) * (n : ℝ) ≤ (n - d.radius : ℕ) := by
    rw [hSubCast]
    nlinarith
  have hmLowerR : ((n - d.radius : ℕ) : ℝ) ≤ d.unused := by
    exact_mod_cast hmLower
  have hBetaSub : β * ((1 - p) * n) ≤ β * d.unused := by
    apply mul_le_mul_of_nonneg_left _ hBetaPos.le
    exact hOneP.trans hmLowerR
  have hUnionReal : (d.aUnion : ℝ) ≤ β * d.unused :=
    hUnionBase.trans (hUnionBudget.trans (hGapN.trans hBetaSub))
  have hCeilReal : (d.aUnion : ℝ) ≤
      (Nat.ceil (β * d.unused) : ℝ) :=
    hUnionReal.trans (Nat.le_ceil _)
  exact_mod_cast hCeilReal

theorem aglRoundedBarrierDensityWindow
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < aglBarrierEtaCut ℓ R B) (n : ℕ)
    (hn : aglRoundedBarrierDensityThreshold ℓ R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    Nat.floor (aglBarrierAlphaDensity R * d.unused) ≤ d.aFamily ∧
      d.aFamily < Nat.ceil (aglBarrierBetaDensity ℓ R * d.unused) ∧
      d.aUnion ≤ Nat.ceil (aglBarrierBetaDensity ℓ R * d.unused) ∧
      d.aFamily ≤ d.unused := by
  let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
  change Nat.floor (aglBarrierAlphaDensity R * d.unused) ≤ d.aFamily ∧
    d.aFamily < Nat.ceil (aglBarrierBetaDensity ℓ R * d.unused) ∧
    d.aUnion ≤ Nat.ceil (aglBarrierBetaDensity ℓ R * d.unused) ∧
    d.aFamily ≤ d.unused
  have hLower := aglRoundedBarrierLowerFamilyDensity
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  change Nat.floor (aglBarrierAlphaDensity R * d.unused) ≤
    d.aFamily at hLower
  have hUpperFamily := aglRoundedBarrierUpperFamilyDensity
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  change d.aFamily < Nat.ceil
    (aglBarrierBetaDensity ℓ R * d.unused) at hUpperFamily
  have hUpperUnion := aglRoundedBarrierUpperUnionDensity
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  change d.aUnion ≤ Nat.ceil
    (aglBarrierBetaDensity ℓ R * d.unused) at hUpperUnion
  rcases aglRoundedBarrierDensityThresholdBounds
      ℓ hℓ R hRpos hRlt B hB n hn with
    ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
  have hbasic := aglRoundedBarrierBasicBounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hBasicThreshold hlen
  change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n at hbasic
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  rcases aglBarrierConstantBounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases aglRoundedBarrierQuotientBounds
      ℓ hℓ R hRpos hRlt B n η hηpos hηhalf
      (by simpa only [d] using hdZero)
      (by simpa only [d] using hRadiusLe) with
    ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
  exact ⟨hLower, hUpperFamily, hUpperUnion, haM⟩

theorem aglSparseCeilRpowBudget
    (x : ℝ) (k : ℕ) (hx : x ≤ ((k / 2 : ℕ) : ℝ)) :
    Nat.ceil ((2 : ℝ) ^ x) ≤ 2 ^ (k / 2) := by
  apply (Nat.ceil_le).2
  calc
    (2 : ℝ) ^ x ≤ (2 : ℝ) ^ ((k / 2 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hx
    _ = (2 : ℝ) ^ (k / 2 : ℕ) := Real.rpow_natCast _ _
    _ = ((2 ^ (k / 2) : ℕ) : ℝ) := by norm_num

theorem aglSparseChooseRatioBound : AGLSparseChooseRatioBound := by
  intro m a b hab hbm
  have ham : a ≤ m := hab.trans hbm
  have hchooseNat : 0 < Nat.choose m a := Nat.choose_pos ham
  have hchoose : (0 : ℝ) < Nat.choose m a := by
    exact_mod_cast hchooseNat
  have hbaseNat : 0 < m + 1 - a := by omega
  have hbase : (0 : ℝ) < (m + 1 - a : ℕ) := by
    exact_mod_cast hbaseNat
  have hfac : (0 : ℝ) < Nat.factorial a := by positivity
  have hfacne : (Nat.factorial a : ℝ) ≠ 0 := ne_of_gt hfac
  have hnum : (Nat.choose (b - 1) a : ℝ) ≤
      ((b - 1 : ℕ) : ℝ) ^ a / Nat.factorial a := by
    exact Nat.choose_le_pow_div a (b - 1)
  have hden : (((m + 1 - a : ℕ) : ℝ) ^ a) / Nat.factorial a ≤
      (Nat.choose m a : ℝ) := by
    exact Nat.pow_le_choose a m
  have hdenLower :
      0 < (((m + 1 - a : ℕ) : ℝ) ^ a) / Nat.factorial a := by
    exact div_pos (pow_pos hbase a) hfac
  calc
    (Nat.choose (b - 1) a : ℝ) / Nat.choose m a ≤
        (((b - 1 : ℕ) : ℝ) ^ a / Nat.factorial a) /
          ((((m + 1 - a : ℕ) : ℝ) ^ a) / Nat.factorial a) := by
      exact div_le_div₀ (by positivity) hnum hdenLower hden
    _ = (((b - 1 : ℕ) : ℝ) ^ a) /
        (((m + 1 - a : ℕ) : ℝ) ^ a) := by
      exact div_div_div_cancel_right₀ hfacne _ _
    _ = ((((b - 1 : ℕ) : ℝ) /
        ((m + 1 - a : ℕ) : ℝ)) ^ a) := by
      exact (div_pow _ _ a).symm

theorem aglSparseClearDenominator
    (C₁ C₂ X U W T : ℕ) (hU : 0 < U) (hWT : W ≤ T)
    (hcoeff :
      (C₁ : ℝ) * C₂ * (((X : ℝ) / U) ^ W) < 1) :
    C₁ * C₂ * X ^ W * U ^ (T - W) < U ^ T := by
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  have hUne : (U : ℝ) ≠ 0 := ne_of_gt hUR
  have hpowSplit : (U : ℝ) ^ T =
      (U : ℝ) ^ W * (U : ℝ) ^ (T - W) := by
    rw [← pow_add, Nat.add_sub_of_le hWT]
  have hmul := mul_lt_mul_of_pos_right hcoeff (pow_pos hUR T)
  have hleft :
      ((C₁ : ℝ) * C₂ * (((X : ℝ) / U) ^ W)) * (U : ℝ) ^ T =
        (C₁ : ℝ) * C₂ * (X : ℝ) ^ W * (U : ℝ) ^ (T - W) := by
    rw [hpowSplit, div_pow]
    field_simp [pow_ne_zero W hUne]
  have hreal :
      (C₁ : ℝ) * C₂ * (X : ℝ) ^ W * (U : ℝ) ^ (T - W) <
        (U : ℝ) ^ T := by
    calc
      (C₁ : ℝ) * C₂ * (X : ℝ) ^ W * (U : ℝ) ^ (T - W) =
          ((C₁ : ℝ) * C₂ * (((X : ℝ) / U) ^ W)) *
            (U : ℝ) ^ T := hleft.symm
      _ < 1 * (U : ℝ) ^ T := hmul
      _ = (U : ℝ) ^ T := one_mul _
  exact_mod_cast hreal

theorem aglSparseConstants
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hsum : α + β < 1) :
    ∃ s W : ℕ, 0 < W ∧
      0 < β / (1 - α) ∧ β / (1 - α) < 1 ∧
      (β / (1 - α)) ^ s < (1 : ℝ) / 8 ∧
      (s : ℝ) < α * W := by
  have hβ : 0 < β := hα.trans hαβ
  have hden : 0 < 1 - α := by linarith
  have hθpos : 0 < β / (1 - α) := div_pos hβ hden
  have hθlt : β / (1 - α) < 1 := by
    rw [div_lt_one hden]
    linarith
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one
    (x := (1 : ℝ) / 8) (y := β / (1 - α)) (by norm_num) hθlt
  obtain ⟨W, hWgt⟩ := exists_nat_gt ((s : ℝ) / α)
  have hWreal : (0 : ℝ) < W := by
    exact (div_nonneg (Nat.cast_nonneg s) hα.le).trans_lt hWgt
  have hW : 0 < W := by exact_mod_cast hWreal
  have hsW : (s : ℝ) < α * W := by
    have h := (div_lt_iff₀ hα).mp hWgt
    simpa only [mul_comm] using h
  exact ⟨s, W, hW, hθpos, hθlt, hs, hsW⟩

theorem aglSparseFloorExponentBudget
    (α : ℝ) (hα : 0 < α) (s W : ℕ)
    (hgap : (s : ℝ) < α * W) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      s * m ≤ Nat.floor (α * m) * W := by
  have hprod : (0 : ℝ) < α * W :=
    (Nat.cast_nonneg s).trans_lt hgap
  have hWreal : (0 : ℝ) < W := by
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · exact (not_lt_of_ge hα.le h.1).elim
  let δ : ℝ := α * W - s
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact sub_pos.mpr hgap
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt ((W : ℝ) / δ)
  refine ⟨m₀, ?_⟩
  intro m hm
  have hmreal : (W : ℝ) / δ < m :=
    hm₀.trans_le (by exact_mod_cast hm)
  have hWδ : (W : ℝ) < δ * m := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hmreal
  have hfloor : α * m < (Nat.floor (α * m) : ℝ) + 1 :=
    Nat.lt_floor_add_one (α * m)
  have hmul := mul_lt_mul_of_pos_right hfloor hWreal
  have hreal : ((s * m : ℕ) : ℝ) <
      ((Nat.floor (α * m) * W : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul]
    dsimp only [δ] at hWδ
    nlinarith
  exact_mod_cast hreal.le

theorem aglSparseLargeUnionExistenceOfNumerics :
    AGLSparseLargeUnionExistenceOfNumerics := by
  intro hNumerics
  intro α β hα hαβ hsum
  obtain ⟨W, hW, γ, hγ, m₀, hnum⟩ :=
    hNumerics α β hα hαβ hsum
  refine ⟨W, hW, γ, hγ, m₀, ?_⟩
  intro m hm
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  let T := 2 ^ (m / W)
  have hpack := hnum m hm
  change a < b ∧ b ≤ m ∧ W ≤ T ∧
      Nat.choose T W * Nat.choose m (b - 1) *
          Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) <
        Nat.choose m a ^ T ∧
      W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤ T at hpack
  rcases hpack with ⟨hab, hbm, hWT, hbadCoeff, hgrowth⟩
  have hb : 0 < b := by omega
  have hbadBound := aglBadIndexedFamiliesCardBound
    m a T W b hW hWT hb hbm hab
  have htypeCard :
      Fintype.card (Fin T → {S : Finset (Fin m) // S.card = a}) =
        Nat.choose m a ^ T := by
    rw [Fintype.card_fun, aglExactSubsetTypeCard, Fintype.card_fin]
  have hbadlt :
      (aglBadIndexedFamilies m a T W b).card <
        (Finset.univ : Finset
          (Fin T → {S : Finset (Fin m) // S.card = a})).card := by
    rw [Finset.card_univ, htypeCard]
    exact hbadBound.trans_lt hbadCoeff
  obtain ⟨A, hAuniv, hAgood⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hbadlt
  obtain ⟨family, hfamily⟩ :=
    aglGoodIndexedFamilyToLargeUnionFamily
      m a T W b hW hab A hAgood
  refine ⟨family, ?_⟩
  have hmul :
      W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤
        W * family.sets.card := hgrowth.trans hfamily
  have hceil : Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤
      family.sets.card := le_of_mul_le_mul_left hmul hW
  exact (Nat.ceil_le).mp hceil

theorem aglSparsePowerBudget (m W k : ℕ) :
    Nat.choose (2 ^ (m / W)) W ≤ 2 ^ m ∧
      Nat.choose m k ≤ 2 ^ m := by
  constructor
  · calc
      Nat.choose (2 ^ (m / W)) W ≤ (2 ^ (m / W)) ^ W :=
        Nat.choose_le_pow (2 ^ (m / W)) W
      _ = 2 ^ ((m / W) * W) := by rw [pow_mul]
      _ ≤ 2 ^ m :=
        pow_le_pow_right' (by omega) (Nat.div_mul_le_self m W)
  · exact Nat.choose_le_two_pow m k

theorem aglSparseBadCoefficientLtOne
    (m a b W : ℕ) (hm : 0 < m)
    (hWT : W ≤ 2 ^ (m / W)) (hbm : b - 1 ≤ m)
    (hratio :
      (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) <
        ((1 : ℝ) / 8) ^ m) :
    (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
        (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) < 1 := by
  obtain ⟨hchooseT, hchooseM⟩ := aglSparsePowerBudget m W (b - 1)
  have hchooseTR : (Nat.choose (2 ^ (m / W)) W : ℝ) ≤
      (2 : ℝ) ^ m := by
    exact_mod_cast hchooseT
  have hchooseMR : (Nat.choose m (b - 1) : ℝ) ≤
      (2 : ℝ) ^ m := by
    exact_mod_cast hchooseM
  have hchooseTPos : (0 : ℝ) < Nat.choose (2 ^ (m / W)) W := by
    exact_mod_cast Nat.choose_pos hWT
  have hchooseMPos : (0 : ℝ) < Nat.choose m (b - 1) := by
    exact_mod_cast Nat.choose_pos hbm
  have hstrict :
      (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
          (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) <
        (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
          ((1 : ℝ) / 8) ^ m := by
    exact mul_lt_mul_of_pos_left hratio (mul_pos hchooseTPos hchooseMPos)
  have hcoeff :
      (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) ≤
        (2 : ℝ) ^ m * (2 : ℝ) ^ m :=
    mul_le_mul hchooseTR hchooseMR (by positivity) (by positivity)
  have hupper :
      (Nat.choose (2 ^ (m / W)) W : ℝ) * Nat.choose m (b - 1) *
          ((1 : ℝ) / 8) ^ m ≤
        (2 : ℝ) ^ m * (2 : ℝ) ^ m * ((1 : ℝ) / 8) ^ m :=
    mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hnormalize :
      (2 : ℝ) ^ m * (2 : ℝ) ^ m * ((1 : ℝ) / 8) ^ m =
        ((1 : ℝ) / 2) ^ m := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have hhalf : ((1 : ℝ) / 2) ^ m < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hm)
  exact hstrict.trans_le hupper |>.trans_eq hnormalize |>.trans hhalf

theorem aglSparseQuotientWindow
    (W m : ℕ) (hW : 0 < W) (hm : 2 * W * W ≤ m) :
    (2 * W ≤ m / W) ∧
      (m < (m / W + 1) * W) ∧
      (W ≤ m / W - (m / W) / 2) := by
  have hlow : 2 * W ≤ m / W := by
    apply (Nat.le_div_iff_mul_le hW).2
    simpa only [Nat.mul_assoc] using hm
  have hupp : m < (m / W + 1) * W := by
    apply ((Nat.galoisConnection_mul_div hW).lt_iff_lt).2
    exact Nat.lt_succ_self (m / W)
  refine ⟨hlow, hupp, ?_⟩
  omega

theorem aglSparseGrowthBudget (W : ℕ) (hW : 0 < W) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤ 2 ^ (m / W) := by
  refine ⟨1 / (8 * (W : ℝ)), by positivity, 2 * W * W, ?_⟩
  intro m hm
  let k := m / W
  obtain ⟨h2W, hmUpper, hWrem⟩ :=
    aglSparseQuotientWindow W m hW hm
  have hkTwo : 2 ≤ k := by
    dsimp only [k]
    omega
  have hnat : k + 1 ≤ 8 * (k / 2) := by omega
  have hmNat : m ≤ (k / 2) * (8 * W) := by
    calc
      m ≤ (k + 1) * W := hmUpper.le
      _ ≤ (8 * (k / 2)) * W := Nat.mul_le_mul_right W hnat
      _ = (k / 2) * (8 * W) := by ring
  have hden : (0 : ℝ) < 8 * W := by positivity
  have hexp :
      (1 / (8 * (W : ℝ))) * m ≤ ((k / 2 : ℕ) : ℝ) := by
    rw [show (1 / (8 * (W : ℝ))) * (m : ℝ) =
      (m : ℝ) / (8 * W) by ring]
    rw [div_le_iff₀ hden]
    exact_mod_cast hmNat
  have hceil :
      Nat.ceil ((2 : ℝ) ^
        ((1 / (8 * (W : ℝ))) * m)) ≤ 2 ^ (k / 2) :=
    aglSparseCeilRpowBudget _ k hexp
  have hWpow : W ≤ 2 ^ (k - k / 2) := by
    calc
      W = Nat.choose W 1 := (Nat.choose_one_right W).symm
      _ ≤ 2 ^ W := Nat.choose_le_two_pow W 1
      _ ≤ 2 ^ (k - k / 2) :=
        pow_le_pow_right' (by omega) hWrem
  calc
    W * Nat.ceil ((2 : ℝ) ^
        ((1 / (8 * (W : ℝ))) * m)) ≤
        2 ^ (k - k / 2) * 2 ^ (k / 2) :=
      Nat.mul_le_mul hWpow hceil
    _ = 2 ^ ((k - k / 2) + k / 2) := (pow_add _ _ _).symm
    _ = 2 ^ k := by rw [Nat.sub_add_cancel (Nat.div_le_self k 2)]
    _ = 2 ^ (m / W) := by rfl

theorem aglSparseRatioBaseBound
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (m : ℕ) (hm : 0 < m) :
    let a := Nat.floor (α * m)
    let b := Nat.ceil (β * m)
    (((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) <
      β / (1 - α) := by
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hβ : 0 < β := hα.trans hαβ
  have hα1 : α < 1 := hαβ.trans hβ1
  have hdenBase : 0 < 1 - α := by linarith
  have hβm : 0 < β * m := mul_pos hβ hmR
  have hbPos : 0 < b := by
    dsimp only [b]
    exact (Nat.ceil_pos).2 hβm
  have hnum : ((b - 1 : ℕ) : ℝ) < β * m := by
    have hceil := Nat.ceil_lt_add_one hβm.le
    have hbOne : 1 ≤ b := by omega
    rw [Nat.cast_sub hbOne]
    norm_num only [Nat.cast_one]
    linarith
  have hαmNonneg : 0 ≤ α * m := mul_nonneg hα.le hmR.le
  have haReal : (a : ℝ) ≤ α * m := by
    dsimp only [a]
    exact Nat.floor_le hαmNonneg
  have haLt : a < m := by
    dsimp only [a]
    apply (Nat.floor_lt hαmNonneg).2
    have h := mul_lt_mul_of_pos_right hα1 hmR
    simpa only [one_mul] using h
  have haLe : a ≤ m + 1 := by omega
  have hdenLower : (1 - α) * m < ((m + 1 - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub haLe]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hdenPos : (0 : ℝ) < (m + 1 - a : ℕ) :=
    (mul_pos hdenBase hmR).trans hdenLower
  apply (div_lt_div_iff₀ hdenPos hdenBase).2
  calc
    ((b - 1 : ℕ) : ℝ) * (1 - α) <
        (β * m) * (1 - α) :=
      mul_lt_mul_of_pos_right hnum hdenBase
    _ = β * ((1 - α) * m) := by ring
    _ < β * ((m + 1 - a : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hdenLower hβ

theorem aglSparseRatioDecay
    (m a b s W : ℕ) (θ : ℝ)
    (hm : 0 < m) (ha : 0 < a) (hW : 0 < W)
    (hab : a ≤ b - 1) (hbm : b - 1 ≤ m)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hbase : (((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) < θ)
    (hexp : s * m ≤ a * W) (hθpow : θ ^ s < (1 : ℝ) / 8) :
    (((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ^ W) <
      ((1 : ℝ) / 8) ^ m := by
  let q : ℝ := (Nat.choose (b - 1) a : ℝ) / Nat.choose m a
  let r : ℝ := ((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)
  have hchoose : q ≤ r ^ a := by
    simpa only [q, r] using aglSparseChooseRatioBound m a b hab hbm
  have hqNonneg : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hrNonneg : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hfirst : q ^ W ≤ (r ^ a) ^ W :=
    pow_le_pow_left₀ hqNonneg hchoose W
  have hpowBase : (r ^ a) ^ W = r ^ (a * W) := by
    exact (pow_mul r a W).symm
  have hstrict : r ^ (a * W) < θ ^ (a * W) := by
    exact pow_lt_pow_left₀ hbase hrNonneg
      (Nat.mul_ne_zero (Nat.ne_of_gt ha) (Nat.ne_of_gt hW))
  have hθexp : θ ^ (a * W) ≤ θ ^ (s * m) :=
    (pow_le_pow_iff_right_of_lt_one₀ hθ0 hθ1).2 hexp
  have hθsplit : θ ^ (s * m) = (θ ^ s) ^ m := pow_mul θ s m
  have hlast : (θ ^ s) ^ m < ((1 : ℝ) / 8) ^ m := by
    exact pow_lt_pow_left₀ hθpow (pow_nonneg hθ0.le s)
      (Nat.ne_of_gt hm)
  calc
    q ^ W ≤ (r ^ a) ^ W := hfirst
    _ = r ^ (a * W) := hpowBase
    _ < θ ^ (a * W) := hstrict
    _ ≤ θ ^ (s * m) := hθexp
    _ = (θ ^ s) ^ m := hθsplit
    _ < ((1 : ℝ) / 8) ^ m := hlast

theorem aglSparseRoundedSetup
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (s W : ℕ) (hW : 0 < W) (hgap : (s : ℝ) < α * W) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      let a := Nat.floor (α * m)
      let b := Nat.ceil (β * m)
      let T := 2 ^ (m / W)
      0 < m ∧ 0 < a ∧ a < b ∧ b ≤ m ∧ a ≤ b - 1 ∧
        b - 1 ≤ m ∧ W ≤ T ∧ s * m ≤ a * W := by
  obtain ⟨mExp, hExp⟩ :=
    aglSparseFloorExponentBudget α hα s W hgap
  obtain ⟨mFloor, hFloor⟩ := exists_nat_gt ((1 : ℝ) / α)
  let m₀ := max (max 1 (W * W)) (max mFloor mExp)
  refine ⟨m₀, ?_⟩
  intro m hm
  have hmpos : 0 < m := by
    dsimp only [m₀] at hm
    omega
  have hWW : W * W ≤ m := by
    dsimp only [m₀] at hm
    omega
  have hmFloor : mFloor ≤ m := by
    dsimp only [m₀] at hm
    omega
  have hmExp : mExp ≤ m := by
    dsimp only [m₀] at hm
    omega
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  let T := 2 ^ (m / W)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hαm : (1 : ℝ) < α * m := by
    have hfrac : (1 : ℝ) / α < m :=
      hFloor.trans_le (by exact_mod_cast hmFloor)
    have h := (div_lt_iff₀ hα).mp hfrac
    simpa only [mul_comm] using h
  have haPos : 0 < a := by
    dsimp only [a]
    exact (Nat.floor_pos).2 hαm.le
  have hβ : 0 < β := hα.trans hαβ
  have hab : a < b := by
    dsimp only [a, b]
    exact Nat.floor_lt_ceil_of_lt_of_pos
      (mul_lt_mul_of_pos_right hαβ hmR) (mul_pos hβ hmR)
  have hbm : b ≤ m := by
    dsimp only [b]
    apply (Nat.ceil_le).2
    have h := mul_le_mul_of_nonneg_right hβ1.le hmR.le
    simpa only [one_mul] using h
  have habSub : a ≤ b - 1 := by omega
  have hbSub : b - 1 ≤ m := by omega
  have hdiv : W ≤ m / W := by
    exact (Nat.le_div_iff_mul_le hW).2
      (by simpa only [Nat.mul_comm] using hWW)
  have hWT : W ≤ T := by
    dsimp only [T]
    calc
      W = Nat.choose W 1 := (Nat.choose_one_right W).symm
      _ ≤ 2 ^ W := Nat.choose_le_two_pow W 1
      _ ≤ 2 ^ (m / W) := pow_le_pow_right' (by omega) hdiv
  have hsm : s * m ≤ a * W := by
    simpa only [a] using hExp m hmExp
  exact ⟨hmpos, haPos, hab, hbm, habSub, hbSub, hWT, hsm⟩

theorem aglSparseCountingInequality
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hsum : α + β < 1) :
    ∃ W : ℕ, 0 < W ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      let a := Nat.floor (α * m)
      let b := Nat.ceil (β * m)
      let T := 2 ^ (m / W)
      a < b ∧ b ≤ m ∧ W ≤ T ∧
        Nat.choose T W * Nat.choose m (b - 1) *
            Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) <
          Nat.choose m a ^ T := by
  obtain ⟨s, W, hW, hθ0, hθ1, hθpow, hgap⟩ :=
    aglSparseConstants α β hα hαβ hsum
  have hβ1 : β < 1 := by linarith
  obtain ⟨m₀, hsetup⟩ :=
    aglSparseRoundedSetup α β hα hαβ hβ1 s W hW hgap
  refine ⟨W, hW, m₀, ?_⟩
  intro m hm
  let a := Nat.floor (α * m)
  let b := Nat.ceil (β * m)
  let T := 2 ^ (m / W)
  have hpack := hsetup m hm
  change 0 < m ∧ 0 < a ∧ a < b ∧ b ≤ m ∧ a ≤ b - 1 ∧
      b - 1 ≤ m ∧ W ≤ T ∧ s * m ≤ a * W at hpack
  rcases hpack with
    ⟨hmpos, haPos, hab, hbm, habSub, hbSub, hWT, hsm⟩
  have hbase :
      (((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) <
        β / (1 - α) := by
    simpa only [a, b] using
      aglSparseRatioBaseBound α β hα hαβ hβ1 m hmpos
  have hratio := aglSparseRatioDecay m a b s W (β / (1 - α))
    hmpos haPos hW habSub hbSub hθ0 hθ1 hbase hsm hθpow
  have hbad := aglSparseBadCoefficientLtOne
    m a b W hmpos (by simpa only [T] using hWT) hbSub hratio
  have haM : a ≤ m := hab.le.trans hbm
  have hchoose : 0 < Nat.choose m a := Nat.choose_pos haM
  have hcoeff := aglSparseClearDenominator
    (Nat.choose T W) (Nat.choose m (b - 1))
    (Nat.choose (b - 1) a) (Nat.choose m a) W T
    hchoose hWT (by simpa only [T] using hbad)
  exact ⟨hab, hbm, hWT, hcoeff⟩

theorem aglSparseLargeUnionNumerics : AGLSparseLargeUnionNumerics := by
  unfold AGLSparseLargeUnionNumerics
  intro α β hα hαβ hsum
  obtain ⟨W, hW, mCount, hCount⟩ :=
    aglSparseCountingInequality α β hα hαβ hsum
  obtain ⟨γ, hγ, mGrowth, hGrowth⟩ :=
    aglSparseGrowthBudget W hW
  refine ⟨W, hW, γ, hγ, max mCount mGrowth, ?_⟩
  intro m hm
  have hmCount : mCount ≤ m := by omega
  have hmGrowth : mGrowth ≤ m := by omega
  have hc := hCount m hmCount
  have hg := hGrowth m hmGrowth
  dsimp only at hc ⊢
  rcases hc with ⟨hab, hbm, hWT, hcoeff⟩
  exact ⟨hab, hbm, hWT, hcoeff, hg⟩

theorem aglSparseLargeUnionExistence : AGLSparseLargeUnionExistence :=
  aglSparseLargeUnionExistenceOfNumerics aglSparseLargeUnionNumerics

theorem aglLargeUnionExistence : AGLLargeUnionExistence := by
  unfold AGLLargeUnionExistence
  intro α β hα hαβ hβ1
  let α₀ : ℝ := min (α / 2) ((1 - β) / 4)
  let β₀ : ℝ := (1 + β) / 2
  have hα₀ : 0 < α₀ := by
    dsimp only [α₀]
    exact lt_min (by positivity) (by positivity)
  have hβ₀ : 0 < β₀ := by
    dsimp only [β₀]
    linarith
  have hβ₀1 : β₀ < 1 := by
    dsimp only [β₀]
    linarith
  have hα₀β₀ : α₀ < β₀ := by
    have hle : α₀ ≤ α / 2 := by
      dsimp only [α₀]
      exact min_le_left _ _
    dsimp only [β₀]
    linarith
  have hsum : α₀ + β₀ < 1 := by
    have hle : α₀ ≤ (1 - β) / 4 := by
      dsimp only [α₀]
      exact min_le_right _ _
    dsimp only [β₀]
    linarith
  obtain ⟨W, hW, γ₀, hγ₀, mSparse, hSparse⟩ :=
    aglSparseLargeUnionExistence α₀ β₀ hα₀ hα₀β₀ hsum
  obtain ⟨mAbsorb, hAbsorb⟩ :=
    aglFixedFactorRpowAbsorb W hW γ₀ hγ₀
  refine ⟨W, hW, γ₀ / 2, by positivity,
    max 1 (max mSparse mAbsorb), ?_⟩
  intro m hm
  have hmPos : 0 < m := by omega
  have hmSparse : mSparse ≤ m := by omega
  have hmAbsorb : mAbsorb ≤ m := by omega
  obtain ⟨source, hsource⟩ := hSparse m hmSparse
  let a₀ := Nat.floor (α₀ * m)
  let b₀ := Nat.ceil (β₀ * m)
  let a₁ := Nat.floor (α * m)
  let b₁ := Nat.ceil (β * m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
  have ha : a₀ ≤ a₁ := by
    dsimp only [a₀, a₁]
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right
      ((min_le_left (α / 2) ((1 - β) / 4)).trans
        (by linarith : α / 2 ≤ α)) hmR.le
  have hab : a₁ < b₀ := by
    dsimp only [a₁, b₀]
    apply Nat.floor_lt_ceil_of_lt_of_pos
    · apply mul_lt_mul_of_pos_right _ hmR
      have hαβ₀ : α < β₀ := by
        dsimp only [β₀]
        linarith
      exact hαβ₀
    · exact mul_pos hβ₀ hmR
  have hb : b₁ ≤ b₀ := by
    dsimp only [b₁, b₀]
    apply Nat.ceil_mono
    apply mul_le_mul_of_nonneg_right _ hmR.le
    dsimp only [β₀]
    linarith
  have ha₁m : a₁ ≤ m := by
    have hα1 : α < 1 := hαβ.trans hβ1
    have hfloor : (a₁ : ℝ) ≤ α * m := by
      dsimp only [a₁]
      exact Nat.floor_le (mul_nonneg hα.le hmR.le)
    have hmul : α * m ≤ m := by
      have h := mul_le_mul_of_nonneg_right hα1.le hmR.le
      simpa only [one_mul] using h
    exact_mod_cast hfloor.trans hmul
  obtain ⟨target, hresize⟩ :=
    aglLargeUnionFamilyResize W a₀ b₀ a₁ b₁ hW ha hab hb
      (ι := Fin m) (by simpa only [Fintype.card_fin] using ha₁m) source
  refine ⟨target, ?_⟩
  have hresizeR : (source.sets.card : ℝ) ≤
      (W : ℝ) * target.sets.card := by
    exact_mod_cast hresize
  have hmul : (W : ℝ) * (2 : ℝ) ^ ((γ₀ / 2) * m) ≤
      (W : ℝ) * target.sets.card :=
    (hAbsorb m hmAbsorb).trans (hsource.trans hresizeR)
  exact le_of_mul_le_mul_left hmul (by exact_mod_cast hW)

theorem aglUnusedCoordinatesEquivFin : AGLUnusedCoordinatesEquivFin := by
  classical
  intro ℓ dZero dOne ι _ _ blocks
  dsimp
  let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
  let ecomp : {i : ι // i ∈ usedᶜ} ≃ {i : ι // i ∉ used} :=
    { toFun := fun x => ⟨x.1, by simpa only [Finset.mem_compl] using x.2⟩
      invFun := fun x => ⟨x.1, by simpa only [Finset.mem_compl] using x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  exact ⟨(Finset.equivFinOfCardEq (Finset.card_compl used)).symm.trans ecomp⟩

theorem aglLargeUnionFamilyTransport : AGLLargeUnionFamilyTransport := by
  classical
  intro ℓ dZero dOne W aFamily aUnion ι _ _ blocks
  dsimp
  intro m hm source
  subst m
  have heq := aglUnusedCoordinatesEquivFin ℓ dZero dOne blocks
  dsimp at heq
  obtain ⟨e⟩ := heq
  let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
  let incl : {i : ι // i ∉ used} ↪ ι := Function.Embedding.subtype _
  let emb : Fin (Fintype.card ι - used.card) ↪ ι := e.toEmbedding.trans incl
  let mapSet : Finset (Fin (Fintype.card ι - used.card)) ↪ Finset ι :=
    (Finset.mapEmbedding emb).toEmbedding
  let target : AGLLargeUnionFamily ι W aFamily aUnion :=
    { sets := source.sets.map mapSet
      card_each := by
        intro A hA
        rcases Finset.mem_map.mp hA with ⟨B, hB, rfl⟩
        change (B.map emb).card = aFamily
        rw [Finset.card_map]
        exact source.card_each B hB
      large_union := by
        intro T hT hTcard
        let U := source.sets.filter fun B => mapSet B ∈ T
        have hUsub : U ⊆ source.sets := Finset.filter_subset _ _
        have hmap : U.map mapSet = T := by
          ext A
          constructor
          · intro hA
            rcases Finset.mem_map.mp hA with ⟨B, hBU, hBA⟩
            have hBT := (Finset.mem_filter.mp hBU).2
            simpa only [hBA] using hBT
          · intro hA
            have hAtarget := hT hA
            rcases Finset.mem_map.mp hAtarget with ⟨B, hB, hBA⟩
            apply Finset.mem_map.mpr
            refine ⟨B, ?_, hBA⟩
            exact Finset.mem_filter.mpr ⟨hB, by simpa only [hBA] using hA⟩
        have hUcard : U.card = W := by
          rw [← hTcard, ← hmap, Finset.card_map]
        have hlarge := source.large_union U hUsub hUcard
        refine hlarge.trans ?_
        calc
          (U.biUnion id).card = ((U.biUnion id).map emb).card :=
            (Finset.card_map _).symm
          _ ≤ (T.biUnion id).card := by
            apply Finset.card_le_card
            intro x hx
            rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
            simp only [Finset.mem_biUnion] at hy ⊢
            obtain ⟨B, hBU, hyB⟩ := hy
            refine ⟨mapSet B, (Finset.mem_filter.mp hBU).2, ?_⟩
            change emb y ∈ B.map emb
            exact (Finset.mem_map' emb).2 hyB }
  refine ⟨target, ?_, ?_⟩
  · simp only [target, Finset.card_map]
  · intro A hA
    change A ∈ source.sets.map mapSet at hA
    rcases Finset.mem_map.mp hA with ⟨B, hB, rfl⟩
    constructor
    · rw [Finset.disjoint_left]
      intro x hx hzero
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hunused : emb y ∉ used := (e y).property
      exact hunused (Finset.mem_union_left _ hzero)
    · intro j
      rw [Finset.disjoint_left]
      intro x hx hother
      rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hunused : emb y ∉ used := (e y).property
      apply hunused
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hother⟩

theorem aglBarrierPackageExistence : AGLBarrierPackageExistence := by
  unfold AGLBarrierPackageExistence
  intro ℓ hℓ R hRpos hRlt B hB
  rcases aglBarrierConstantBounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  obtain ⟨W, hW, γ₀, hγ₀, mSource, hSource⟩ :=
    aglLargeUnionExistence
      (aglBarrierAlphaDensity R) (aglBarrierBetaDensity ℓ R)
      hAlpha hAlphaBeta hBetaOne
  obtain ⟨mAbsorb, hAbsorb⟩ :=
    aglFixedFactorRpowAbsorb W hW γ₀ hγ₀
  let γ : ℝ := γ₀ / (2 * (ℓ + 1))
  let n₀ : ℕ := max (aglRoundedBarrierDensityThreshold ℓ R B)
    (max ((ℓ + 1) * mSource) ((ℓ + 1) * mAbsorb))
  refine ⟨aglBarrierEtaCut ℓ R B, hEta, γ, ?_,
    aglBarrierK ℓ B, hK, W, hW, n₀, ?_⟩
  · dsimp only [γ]
    positivity
  · intro η hη hηcut ι _ _ _ hn hlen
    let n := Fintype.card ι
    let d := aglRoundedBarrierData ℓ R η (aglBarrierK ℓ B) B n
    let m := d.unused
    change n₀ ≤ n at hn
    change 1 / η ≤ (n : ℝ) at hlen
    have hnDensity : aglRoundedBarrierDensityThreshold ℓ R B ≤ n := by
      dsimp only [n₀] at hn
      omega
    have hnSource : (ℓ + 1) * mSource ≤ n := by
      dsimp only [n₀] at hn
      omega
    have hnAbsorb : (ℓ + 1) * mAbsorb ≤ n := by
      dsimp only [n₀] at hn
      omega
    rcases aglRoundedBarrierDensityThresholdBounds
        ℓ hℓ R hRpos hRlt B hB n hnDensity with
      ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
    have hbasic := aglRoundedBarrierBasicBounds
      ℓ hℓ R hRpos hRlt B hB η hη hηcut n hBasicThreshold hlen
    change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
        d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
        d.boosted ≤ n ∧ d.radius ≤ n at hbasic
    rcases hbasic with
      ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
    have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
    rcases aglRoundedBarrierQuotientBounds
        ℓ hℓ R hRpos hRlt B n η hη hηhalf
        (by simpa only [d] using hdZero)
        (by simpa only [d] using hRadiusLe) with
      ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
    change n ≤ (ℓ + 1) * m at hnM
    have hmSource : mSource ≤ m := by
      apply le_of_mul_le_mul_left (hnSource.trans hnM)
      omega
    have hmAbsorb : mAbsorb ≤ m := by
      apply le_of_mul_le_mul_left (hnAbsorb.trans hnM)
      omega
    obtain ⟨source, hsource⟩ := hSource m hmSource
    have hwindow := aglRoundedBarrierDensityWindow
      ℓ hℓ R hRpos hRlt B hB η hη hηcut n hnDensity hlen
    change Nat.floor (aglBarrierAlphaDensity R * m) ≤ d.aFamily ∧
      d.aFamily < Nat.ceil (aglBarrierBetaDensity ℓ R * m) ∧
      d.aUnion ≤ Nat.ceil (aglBarrierBetaDensity ℓ R * m) ∧
      d.aFamily ≤ m at hwindow
    rcases hwindow with ⟨hLower, hUpperFamily, hUpperUnion, haUnused⟩
    obtain ⟨resized, hresize⟩ := aglLargeUnionFamilyResize
      W (Nat.floor (aglBarrierAlphaDensity R * m))
      (Nat.ceil (aglBarrierBetaDensity ℓ R * m))
      d.aFamily d.aUnion hW hLower hUpperFamily hUpperUnion
      (ι := Fin m) (by simpa only [Fintype.card_fin] using haUnused)
      source
    obtain ⟨params, hpW, hpWEq, hpa, hpu, hpz, hpo⟩ :=
      aglBarrierParametersExist
        ℓ hℓ R hRpos hRlt B hB η hη hηcut n W hW
        hBasicThreshold hlen
    change params.aFamily = d.aFamily at hpa
    change params.aUnion = d.aUnion at hpu
    change params.dZero = d.dZero at hpz
    change params.dOne = d.dOne at hpo
    have hRateParam :
        params.aFamily + (B + 1) ≤ Nat.floor (R * n) := by
      rw [hpa]
      dsimp only [d, aglRoundedBarrierData]
      omega
    have hZeroParam :
        params.dZero ≤ Nat.ceil (aglBarrierK ℓ B * η * n) := by
      rw [hpz]
      rfl
    obtain ⟨blocks, hblocksTrue⟩ := aglCoordinateBlocksExists
      ℓ params.dZero params.dOne (ι := ι)
      (params.center_block_bound.trans (by
        simpa only [d] using hRadiusLe))
    let used : Finset ι :=
      blocks.zero ∪ Finset.univ.biUnion blocks.other
    have hUsedCard := aglCoordinateBlocksUsedCard
      ℓ params.dZero params.dOne blocks
    change used.card = params.dZero + ℓ * params.dOne at hUsedCard
    have hUsedEq : used.card = d.used := by
      calc
        used.card = params.dZero + ℓ * params.dOne := hUsedCard
        _ = d.dZero + ℓ * d.dOne := by rw [hpz, hpo]
        _ = d.used := by rfl
    have hmUsed : m = Fintype.card ι - used.card := by
      calc
        m = n - d.used := by rfl
        _ = Fintype.card ι - used.card := by rw [hUsedEq]
    obtain ⟨target, hTargetCard, hTargetDisjoint⟩ :=
      aglLargeUnionFamilyTransport
        ℓ params.dZero params.dOne W d.aFamily d.aUnion
        blocks m hmUsed resized
    let family : AGLLargeUnionFamily ι params.W
        params.aFamily params.aUnion :=
      { sets := target.sets
        card_each := by
          intro A hA
          rw [hpa]
          exact target.card_each A hA
        large_union := by
          intro T hT hTcard
          rw [hpu]
          apply target.large_union T hT
          simpa only [hpWEq] using hTcard }
    have hFamilyDisjoint : ∀ S ∈ family.sets,
        Disjoint S blocks.zero ∧
          ∀ j, Disjoint S (blocks.other j) := by
      intro S hS
      exact hTargetDisjoint S hS
    have hresizeR : (source.sets.card : ℝ) ≤
        (W : ℝ) * resized.sets.card := by
      exact_mod_cast hresize
    have hmul : (W : ℝ) * (2 : ℝ) ^ ((γ₀ / 2) * m) ≤
        (W : ℝ) * resized.sets.card :=
      (hAbsorb m hmAbsorb).trans (hsource.trans hresizeR)
    have hWReal : (0 : ℝ) < W := by exact_mod_cast hW
    have hresizedLower : (2 : ℝ) ^ ((γ₀ / 2) * m) ≤
        resized.sets.card := le_of_mul_le_mul_left hmul hWReal
    have hnMR : (n : ℝ) ≤ ((ℓ + 1) * m : ℕ) := by
      exact_mod_cast hnM
    have hγnonneg : 0 ≤ γ := by
      dsimp only [γ]
      positivity
    have hγexp : γ * (n : ℝ) ≤ (γ₀ / 2) * m := by
      calc
        γ * (n : ℝ) ≤ γ * (((ℓ + 1) * m : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hnMR hγnonneg
        _ = (γ₀ / 2) * m := by
          dsimp only [γ]
          norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp <;> ring
    have hPowWeak : (2 : ℝ) ^ (γ * n) ≤
        (2 : ℝ) ^ ((γ₀ / 2) * m) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hγexp
    have hTargetCardR : (target.sets.card : ℝ) =
        (resized.sets.card : ℝ) := by exact_mod_cast hTargetCard
    have hFamilyLower : (2 : ℝ) ^ (γ * n) ≤ family.sets.card := by
      change (2 : ℝ) ^ (γ * n) ≤ target.sets.card
      calc
        (2 : ℝ) ^ (γ * n) ≤ (2 : ℝ) ^ ((γ₀ / 2) * m) := hPowWeak
        _ ≤ resized.sets.card := hresizedLower
        _ = target.sets.card := hTargetCardR.symm
    refine ⟨params, hpW, hpWEq.le, hRateParam, hZeroParam,
      blocks, family, hFamilyDisjoint, hFamilyLower⟩

open _root_.ListDecodable in
theorem aglRobustMinimumDistanceBarrier :
    AGLRobustMinimumDistanceBarrierStatement := by
  unfold AGLRobustMinimumDistanceBarrierStatement
  intro ℓ hℓ R hRpos hRlt B hB
  obtain ⟨ηCut, hηCut, γ, hγ, K, hK, Wmax, hWmax,
      nPackage, hPackage⟩ :=
    aglBarrierPackageExistence ℓ hℓ R hRpos hRlt B hB
  let ηUse : ℝ := min ηCut ((1 - R) / 2)
  have hηUse : 0 < ηUse := by
    dsimp only [ηUse]
    exact lt_min hηCut (by linarith)
  let Kfac : ℕ := 2 * Wmax * ℓ
  have hKfac : 0 < Kfac := by
    dsimp only [Kfac]
    positivity
  obtain ⟨nAbsorb, hAbsorb⟩ :=
    aglFixedFactorRpowAbsorb Kfac hKfac (γ / 2) (by positivity)
  let α : ℝ := min (ηUse / 2) (γ / (16 * (K + 1)))
  let n₀ : ℕ := max nPackage nAbsorb
  have hα : 0 < α := by
    dsimp only [α]
    exact lt_min (by positivity) (by positivity)
  refine ⟨α, hα, n₀, ?_⟩
  intro η hη ι A _ _ _ _ _ C hA hn hlen hsize hsep hLambda
  let n := Fintype.card ι
  let q := Fintype.card A
  change n₀ ≤ n at hn
  change 1 / η ≤ (n : ℝ) at hlen
  change (q : ℝ) ^ (R * n) ≤ (B : ℝ) * C.ncard at hsize
  change AGLSeparated C
    (Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * n)) at hsep
  change Lambda C (aglRadius ℓ R η) ≤ (ℓ : ℕ∞) at hLambda
  by_cases hηlarge : ηUse ≤ η
  · apply aglAlphabetCardGeRpowOfAlphaLeEta α η hη
    · have hαcut : α ≤ ηUse / 2 := min_le_left _ _
      linarith
    · simpa only [q] using hA
  · have hηsmall : η < ηUse := lt_of_not_ge hηlarge
    have hηPackage : η < ηCut :=
      hηsmall.trans_le (min_le_left _ _)
    have hηHalf : η < (1 - R) / 2 :=
      hηsmall.trans_le (min_le_right _ _)
    have hnPackage : nPackage ≤ n := by
      dsimp only [n₀] at hn
      omega
    have hnAbsorb : nAbsorb ≤ n := by
      dsimp only [n₀] at hn
      omega
    obtain ⟨params, hpW, hpWmax, hrate, hdZero,
        blocks, family, hdisjoint, hlower⟩ :=
      hPackage η hη hηPackage (ι := ι) hnPackage hlen
    have hnNat : 0 < n := by
      dsimp only [n]
      exact Fintype.card_pos
    have hone : 1 ≤ η * n := aglEtaTimesLengthOne η n hη hlen
    have hmany : 2 * q ^ params.aFamily ≤ C.ncard :=
      aglRateLossToCardinality q B params.aFamily n C.ncard R
        (by simpa only [q] using hA) hB hRpos.le hrate hsize
    have hp : 0 < aglRadius ℓ R η := by
      apply aglRadius_pos ℓ (by omega) R η
      linarith
    have hratio :
        (Nat.floor (aglRadius ℓ R η * n) : ℝ) / n ≤
          aglRadius ℓ R η :=
      aglFloorRadiusRatioLe (aglRadius ℓ R η) n hp.le hnNat
    have hLambdaRounded :
        Lambda C ((Nat.floor (aglRadius ℓ R η * n) : ℝ) / n) ≤
          (ℓ : ℕ∞) :=
      (ListDecodable.Lambda_mono hratio).trans hLambda
    have hpigeon := aglDeterministicPigeonholeBound
      ℓ n (Nat.floor (aglRadius ℓ R η * n))
      (Nat.ceil (aglBoostedRadius ℓ (aglRadius ℓ R η) * n))
      hℓ hnNat C (by simpa only [q] using hA) rfl
      (Set.toFinite C) params hpW blocks family hdisjoint hsep
      hmany hLambdaRounded
    by_contra hnot
    have hqSmall : (q : ℝ) < (2 : ℝ) ^ (α / η) :=
      lt_of_not_ge hnot
    have hαK : α * (K + 1) ≤ γ / 4 := by
      have hαSecond : α ≤ γ / (16 * (K + 1)) :=
        min_le_right _ _
      have hKOne : 0 < K + 1 := by positivity
      calc
        α * (K + 1) ≤ (γ / (16 * (K + 1))) * (K + 1) :=
          mul_le_mul_of_nonneg_right hαSecond hKOne.le
        _ = γ / 16 := by
          field_simp [ne_of_gt hKOne]
        _ ≤ γ / 4 := by nlinarith
    have hqPower := aglSmallAlphabetPowerBound
      q params.dZero n α η K γ hα.le hη hK.le hqSmall
      hdZero hone hαK
    have hCoeffNat : 2 * params.W * ℓ ≤ Kfac := by
      dsimp only [Kfac]
      exact Nat.mul_le_mul_right ℓ
        (Nat.mul_le_mul_left 2 hpWmax)
    have hCoeff : ((2 * params.W * ℓ : ℕ) : ℝ) ≤ (Kfac : ℝ) := by
      exact_mod_cast hCoeffNat
    have hpigeonR : (family.sets.card : ℝ) ≤
        ((2 * params.W * ℓ : ℕ) : ℝ) *
          ((q ^ params.dZero : ℕ) : ℝ) := by
      exact_mod_cast hpigeon
    have hupper : (family.sets.card : ℝ) ≤
        (Kfac : ℝ) * (2 : ℝ) ^ ((γ / 4) * n) := by
      calc
        (family.sets.card : ℝ) ≤
            ((2 * params.W * ℓ : ℕ) : ℝ) *
              ((q ^ params.dZero : ℕ) : ℝ) := hpigeonR
        _ ≤ (Kfac : ℝ) * (2 : ℝ) ^ ((γ / 4) * n) :=
          mul_le_mul hCoeff hqPower (by positivity) (by positivity)
    have habsorbRaw := hAbsorb n hnAbsorb
    have habsorb : (Kfac : ℝ) *
        (2 : ℝ) ^ ((γ / 4) * n) ≤
          (2 : ℝ) ^ ((γ / 2) * n) := by
      convert habsorbRaw using 1 <;> ring
    exact aglBarrierExponentContradiction
      Kfac family.sets.card n γ hγ hnNat hlower hupper habsorb

theorem alphabet_card_ge_rpow_of_alpha_le_eta
    (α η : ℝ) (hα_nonneg : 0 ≤ α) (hη_pos : 0 < η) (hαη : α ≤ η)
    {F : Type} [Field F] [Fintype F] :
    (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  have hexp : α / η ≤ 1 := (div_le_one hη_pos).2 hαη
  have hpow : (2 : ℝ) ^ (α / η) ≤ 2 := by
    calc
      (2 : ℝ) ^ (α / η) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 2 := by norm_num
  have hcard : (2 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card
  exact hpow.trans hcard

theorem large_alphabet_large_eta
    (ρ α η : ℝ) (hρ_lt : ρ < 1) (hα_nonneg : 0 ≤ α)
    (hα_le : α ≤ 1 - ρ) (hη_pos : 0 < η) (hη_large : 1 - ρ ≤ η)
    {F : Type} [Field F] [Fintype F] :
    (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  have hexp : α / η ≤ 1 := by
    apply (div_le_one hη_pos).2
    exact hα_le.trans hη_large
  have hpow : (2 : ℝ) ^ (α / η) ≤ 2 := by
    calc
      (2 : ℝ) ^ (α / η) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 2 := by norm_num
  have hcard : (2 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card
  exact hpow.trans hcard

theorem submodule_ncard_eq_rpow_finrank
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F]
    (C : Submodule F (ι → F)) :
    ((C : Set (ι → F)).ncard : ℝ) =
      (Fintype.card F : ℝ) ^ (Module.finrank F C : ℝ) := by
  have hcard_nat : (C : Set (ι → F)).ncard =
      Fintype.card F ^ Module.finrank F C := by
    have h1 : (C : Set (ι → F)).ncard = Nat.card C := by
      rw [← Nat.card_coe_set_eq]
      rfl
    rw [h1, ← Nat.card_eq_fintype_card (α := F)]
    exact Module.natCard_eq_pow_finrank (K := F) (V := C)
  rw [hcard_nat, Nat.cast_pow]
  exact (Real.rpow_natCast _ _).symm

open _root_.ListDecodable in
theorem large_alphabet_lambda_lower__proved
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (η : ℝ), 0 < η →
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F]
            (C : Submodule F (ι → F)),
            n₀ ≤ Fintype.card ι →
            1 / η ≤ (Fintype.card ι : ℝ) →
            (Module.finrank F C : ℝ) = ρ * Fintype.card ι →
            Lambda ((C : Set (ι → F)))
              ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  classical
  let p₀ : ℝ := aglSmallRadius ℓ ρ
  let B₀ : ℕ := aglNeighborhoodCap ℓ ρ
  let Nlocal : ℕ := aglLocalLengthThreshold ℓ ρ
  have hp₀ : 0 < p₀ := by
    dsimp only [p₀, aglSmallRadius]
    have hℓpos : (0 : ℝ) < ℓ := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) _hℓ_ge)
    have hgap : 0 < 1 - ρ := by linarith
    positivity
  have hB₀ : 0 < B₀ := by
    dsimp only [B₀, aglNeighborhoodCap]
    omega
  obtain ⟨αsep, hαsep, nsep, hsep⟩ :=
    aglRobustMinimumDistanceBarrier
      ℓ _hℓ_ge ρ _hρ_pos _hρ_lt B₀ hB₀
  refine ⟨min αsep ((1 - ρ) / 2), ?_, max Nlocal nsep, ?_⟩
  · exact lt_min hαsep (by linarith)
  · intro η hη
    intro ι _ _ _ F _ _ _ C hn hηn hrate hLambda
    by_cases hlarge : (1 - ρ) / 2 ≤ η
    · apply alphabet_card_ge_rpow_of_alpha_le_eta
      · exact le_of_lt (lt_min hαsep (by linarith))
      · exact hη
      · exact (min_le_right _ _).trans hlarge
    · have hsmall : η < (1 - ρ) / 2 := lt_of_not_ge hlarge
      let p : ℝ := aglRadius ℓ ρ η
      have hℓpos : (0 : ℝ) < ℓ := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) _hℓ_ge)
      have hfacpos : 0 < (ℓ : ℝ) / (ℓ + 1) := by positivity
      have hfaclt : (ℓ : ℝ) / (ℓ + 1) < 1 := by
        apply (div_lt_one (by positivity)).2
        linarith
      have hp₀p : p₀ ≤ p := by
        dsimp only [p₀, p, aglSmallRadius, aglRadius]
        apply mul_le_mul_of_nonneg_left _ hfacpos.le
        linarith
      have hp : 0 < p := lt_of_lt_of_le hp₀ hp₀p
      have hplt : p < 1 := by
        dsimp only [p, aglRadius]
        have hgaplt : 1 - ρ - η < 1 := by linarith
        have hmul : (ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η) <
            (ℓ : ℝ) / (ℓ + 1) * 1 :=
          mul_lt_mul_of_pos_left hgaplt hfacpos
        nlinarith
      have hnlocal : Nlocal ≤ Fintype.card ι :=
        le_trans (le_max_left Nlocal nsep) hn
      have hnsep : nsep ≤ Fintype.card ι :=
        le_trans (le_max_right Nlocal nsep) hn
      have hdiv : 8 * (ℓ : ℝ) / p₀ ^ ℓ ≤ (Fintype.card ι : ℝ) := by
        calc
          8 * (ℓ : ℝ) / p₀ ^ ℓ ≤
              (Nat.ceil (8 * (ℓ : ℝ) / p₀ ^ ℓ) : ℝ) := Nat.le_ceil _
          _ = (Nlocal : ℝ) := by rfl
          _ ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hnlocal
      have hlocalLength : 8 * (ℓ : ℝ) ≤
          p ^ ℓ * Fintype.card ι := by
        have hp₀pow : 0 < p₀ ^ ℓ := pow_pos hp₀ _
        have hbase : 8 * (ℓ : ℝ) ≤
            p₀ ^ ℓ * Fintype.card ι := by
          apply (div_le_iff₀ hp₀pow).mp at hdiv
          nlinarith
        have hpow : p₀ ^ ℓ ≤ p ^ ℓ :=
          pow_le_pow_left₀ hp₀.le hp₀p ℓ
        have hnnonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hpow hnnonneg]
      have hlocal := aglLocalNeighborhoodBound ℓ _hℓ_ge p hp hplt
        (C : Set (ι → F))
        (by simpa only [p, aglRadius] using hLambda) hlocalLength
      have hcap : ∀ c ∈ (C : Set (ι → F)),
          ({x : ι → F | x ∈ (C : Set (ι → F)) ∧
            hammingDist c x ≤
              Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι)} :
            Set (ι → F)).ncard ≤ B₀ := by
        intro c hc
        have hnum : 0 ≤ 4 * ((ℓ : ℝ) ^ 2) := by positivity
        have hfrac : 4 * ((ℓ : ℝ) ^ 2) / p ≤
            4 * ((ℓ : ℝ) ^ 2) / p₀ :=
          div_le_div_of_nonneg_left hnum hp₀ hp₀p
        have hceil := Nat.ceil_mono hfrac
        have hc0 := hlocal c hc
        dsimp only [B₀, aglNeighborhoodCap]
        exact hc0.trans (Nat.add_le_add_left hceil ℓ)
      obtain ⟨D, hDC, hDfin, hDsep, hcard⟩ :=
        aglGreedySeparatedExtraction
          (C : Set (ι → F))
          (Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι)) B₀
          (Set.toFinite _) hcap
      have hDsep' : AGLSeparated D
          (Nat.ceil (aglBoostedRadius ℓ p * Fintype.card ι)) := by
        intro u hu v hv huv
        exact (Nat.ceil_le_floor_add_one
          (aglBoostedRadius ℓ p * Fintype.card ι)).trans
          (hDsep hu hv huv)
      have hDlambda : Lambda D p ≤ (ℓ : ℕ∞) := by
        exact (Lambda_mono_code hDC p).trans
          (by simpa only [p, aglRadius] using hLambda)
      have hcardR : ((C : Set (ι → F)).ncard : ℝ) ≤
          (B₀ : ℝ) * (D.ncard : ℝ) := by
        exact_mod_cast hcard
      have hrateCard : (Fintype.card F : ℝ) ^
          (ρ * Fintype.card ι) ≤ (B₀ : ℝ) * (D.ncard : ℝ) := by
        calc
          (Fintype.card F : ℝ) ^ (ρ * Fintype.card ι) =
              (Fintype.card F : ℝ) ^ (Module.finrank F C : ℝ) := by
            rw [hrate]
          _ = ((C : Set (ι → F)).ncard : ℝ) :=
            (submodule_ncard_eq_rpow_finrank C).symm
          _ ≤ (B₀ : ℝ) * (D.ncard : ℝ) := hcardR
      have hFcard : 2 ≤ Fintype.card F := by
        have h := Fintype.one_lt_card (α := F)
        omega
      have hbar := hsep η hη D hFcard hnsep hηn hrateCard hDsep'
        (by simpa only [p, aglRadius] using hDlambda)
      have hexp : min αsep ((1 - ρ) / 2) / η ≤ αsep / η :=
        (div_le_div_iff_of_pos_right hη).2 (min_le_left _ _)
      have hpow : (2 : ℝ) ^
          (min αsep ((1 - ρ) / 2) / η) ≤
            (2 : ℝ) ^ (αsep / η) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      exact hpow.trans hbar


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
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) :=
  large_alphabet_lambda_lower__proved ℓ _hℓ_ge ρ _hρ_pos _hρ_lt

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
